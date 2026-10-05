#include "borrow.hpp"
#include <map>
#include <sstream>
#include <set>
#include <fstream>
#include <iomanip>
#include <filesystem>

namespace mir {

namespace {

bool before(BlockId ab, uint32_t as, BlockId bb, uint32_t bs) {
    if (ab != bb) return ab < bb;
    return as < bs;
}

bool operand_is_value(const Operand& o) {
    return o.kind != Operand::Kind::Constant;
}

std::vector<Operand> call_operands(const Terminator& t) {
    std::vector<Operand> ops;
    if (t.call_receiver) ops.push_back(Operand::make_copy(*t.call_receiver));
    ops.insert(ops.end(), t.call_args.begin(), t.call_args.end());
    return ops;
}

} // namespace

struct Loan {
    Place place;
    LocalId holder = 0;
    std::set<LocalId> holders;
    bool is_mut = false;
    BlockId create_block = 0;
    uint32_t create_stmt = 0;
    bool two_phase = false;
    std::optional<Origin> activation;
};

struct Access {
    Place place;
    bool is_write = false;
    BlockId block = 0;
    uint32_t stmt = 0;
    std::string description;
    std::optional<Origin> reservation;
};

ReturnBorrowSummaries compute_return_borrow_summaries(const std::vector<Body>& bodies) {
    ReturnBorrowSummaries summaries;
    // An empty summary for a body-bearing function means "returns none of its
    // parameters so far" during fixed-point iteration. Keep external or
    // bodyless declarations absent so callers can use the conservative fallback.
    for (const Body& body : bodies) summaries.emplace(body.summary_key.empty() ? body.name : body.summary_key, std::set<size_t>{});
    auto successors = [](const Body& body, size_t b) {
        std::vector<BlockId> out;
        const auto& t = body.blocks[b].terminator;
        if (t.kind == Terminator::Kind::Goto || t.kind == Terminator::Kind::Call || t.kind == Terminator::Kind::Drop) out.push_back(t.target);
        if (t.kind == Terminator::Kind::SwitchInt) {
            for (const auto& x : t.switch_targets) out.push_back(x.target);
            out.push_back(t.switch_default);
        }
        if (t.kind == Terminator::Kind::Throw && t.target != INVALID_BLOCK) out.push_back(t.target);
        return out;
    };

    bool summaries_changed = true;
    while (summaries_changed) {
        summaries_changed = false;
        for (const Body& body : bodies) {
            if (body.blocks.empty()) continue;
            std::vector<LocalId> params;
            for (LocalId l = 0; l < body.locals.size(); ++l)
                if (body.locals[l].is_arg) params.push_back(l);
            for (size_t pi = 0; pi < params.size(); ++pi) {
                using Bits = std::vector<bool>;
                std::vector<Bits> in(body.blocks.size(), Bits(body.locals.size(), false));
                std::vector<Bits> out(body.blocks.size(), Bits(body.locals.size(), false));
                auto call_input_ops = [](const Terminator& t) {
                    std::vector<Operand> ops;
                    if (t.call_receiver) ops.push_back(Operand::make_copy(*t.call_receiver));
                    ops.insert(ops.end(), t.call_args.begin(), t.call_args.end());
                    return ops;
                };
                auto transfer = [&](size_t b, Bits state) {
                    const auto& bb = body.blocks[b];
                    for (const auto& st : bb.statements) {
                        if (st.kind == Statement::Kind::StorageDead) {
                            if (st.local < state.size()) state[st.local] = false;
                            continue;
                        }
                        if (st.kind != Statement::Kind::Assign || !st.place || !st.rvalue) continue;
                        const Rvalue& rv = *st.rvalue;
                        LocalId dst = st.place->local;
                        bool carries = false;
                        auto carries_operand = [&](const Operand& op) {
                            return op.kind != Operand::Kind::Constant && op.place.local < state.size() && state[op.place.local];
                        };
                        if (rv.kind == Rvalue::Kind::Ref && rv.ref_place)
                            carries = rv.ref_place->local < state.size() && state[rv.ref_place->local];
                        if (rv.kind == Rvalue::Kind::Use && rv.operand) carries = carries_operand(*rv.operand);
                        if (rv.kind == Rvalue::Kind::Cast && rv.operand) carries = carries_operand(*rv.operand);
                        if (rv.kind == Rvalue::Kind::Aggregate && rv.aggregate)
                            for (const auto& e : rv.aggregate->elements) carries = carries || carries_operand(e);
                        if (dst < state.size()) state[dst] = carries;
                        if (rv.kind == Rvalue::Kind::Use && rv.operand && rv.operand->kind == Operand::Kind::Move
                            && rv.operand->place.local < state.size() && rv.operand->place.local != dst)
                            state[rv.operand->place.local] = false;
                    }
                    const Terminator& t = bb.terminator;
                    if (t.kind == Terminator::Kind::Call && t.call_destination) {
                        auto ops = call_input_ops(t);
                        auto summary = summaries.find(t.call_summary_key.empty() ? t.call_callee : t.call_summary_key);
                        bool carries = false;
                        for (size_t ai = 0; ai < ops.size(); ++ai) {
                            if (summary != summaries.end() && !summary->second.count(ai)) continue;
                            const auto& op = ops[ai];
                            if (op.kind != Operand::Kind::Constant && op.place.local < state.size()) carries = carries || state[op.place.local];
                        }
                        if (t.call_destination->local < state.size()) state[t.call_destination->local] = carries;
                    }
                    return state;
                };
                bool changed = true;
                while (changed) {
                    changed = false;
                    for (size_t b = 0; b < body.blocks.size(); ++b) {
                        Bits joined(body.locals.size(), false);
                        for (size_t p = 0; p < body.blocks.size(); ++p)
                            for (BlockId s : successors(body, p)) if (s == b)
                                for (size_t l = 0; l < joined.size(); ++l) joined[l] = joined[l] || out[p][l];
                        if (b == body.start_block && params[pi] < joined.size()) joined[params[pi]] = true;
                        Bits next = transfer(b, joined);
                        if (joined != in[b] || next != out[b]) { in[b] = std::move(joined); out[b] = std::move(next); changed = true; }
                    }
                }
                bool returned = false;
                for (size_t b = 0; b < body.blocks.size(); ++b) {
                    Bits state = transfer(b, in[b]);
                    const auto& t = body.blocks[b].terminator;
                    if (t.kind == Terminator::Kind::Return && t.return_value
                        && t.return_value->kind != Operand::Kind::Constant
                        && t.return_value->place.local < state.size() && state[t.return_value->place.local])
                        returned = true;
                }
                const std::string key = body.summary_key.empty() ? body.name : body.summary_key;
                if (returned && summaries[key].insert(pi).second) summaries_changed = true;
            }
        }
    }
    return summaries;
}

std::vector<BorrowDiagnostic> check_borrows(const Body& body, const ReturnBorrowSummaries& summaries) {
    std::vector<BorrowDiagnostic> diags;

    std::vector<Loan> loans;
    std::map<Origin, size_t> origin_to_loan;
    std::vector<Access> accesses;
    // ---- Pass 1: collect static loan sites and memory accesses ----
    for (size_t bi = 0; bi < body.blocks.size(); ++bi) {
        const auto& bb = body.blocks[bi];
        BlockId blk = static_cast<BlockId>(bi);

        for (size_t si = 0; si < bb.statements.size(); ++si) {
            const auto& st = bb.statements[si];
            uint32_t idx = static_cast<uint32_t>(si);

            if (st.kind == Statement::Kind::Assign && st.rvalue && st.place) {
                const auto& rv = *st.rvalue;

                // Reads from RHS.
                if (rv.kind != Rvalue::Kind::Ref) {
                    auto read = [&](const Operand& o, const std::string& what) {
                        if (!operand_is_value(o)) return;
                        accesses.push_back({o.place, false, blk, idx, what});
                    };
                    if (rv.operand) read(*rv.operand, "read");
                    if (rv.lhs)     read(*rv.lhs, "read");
                    if (rv.rhs)     read(*rv.rhs, "read");
                    if (rv.aggregate)
                        for (const auto& el : rv.aggregate->elements) read(el, "aggregate element");
                }

                if (rv.kind == Rvalue::Kind::Ref) {
                    Origin O{blk, idx};
                    Loan L;
                    L.place = *rv.ref_place;
                    L.holder = st.place->local;
                    L.holders.insert(st.place->local);
                    L.is_mut = rv.ref_mut.value_or(false);
                    L.create_block = blk;
                    L.create_stmt = idx;
                    origin_to_loan[O] = loans.size();
                    loans.push_back(L);
                } else {
                    // Ordinary write.
                    accesses.push_back({*st.place, true, blk, idx, "write"});

                }
            } else if (st.kind == Statement::Kind::StorageDead) {
                accesses.push_back({Place{st.local, {}}, true, blk, idx, "storage end"});
            } else if (st.kind == Statement::Kind::ReserveBorrow && st.place) {
                Origin O{blk, idx};
                Loan L;
                L.place = *st.place;
                L.holder = st.place->local;
                L.holders.insert(st.place->local);
                L.is_mut = st.reserve_mut;
                L.create_block = blk;
                L.create_stmt = idx;
                L.two_phase = true;
                origin_to_loan[O] = loans.size();
                loans.push_back(std::move(L));
            }
        }

        // Terminator reads, writes, and loan creation.
        uint32_t tidx = static_cast<uint32_t>(bb.statements.size());
        const auto& t = bb.terminator;

        if (t.receiver_reservation) {
            auto it = origin_to_loan.find(*t.receiver_reservation);
            if (it != origin_to_loan.end()) loans[it->second].activation = Origin{blk, tidx};
        }

        auto read_operand = [&](const Operand& o, const std::string& what) {
            if (!operand_is_value(o)) return;
            accesses.push_back({o.place, false, blk, tidx, what});
        };

        if (t.kind == Terminator::Kind::Return && t.return_value)
            read_operand(*t.return_value, "return");
        if (t.kind == Terminator::Kind::SwitchInt && t.switch_on)
            read_operand(*t.switch_on, "switch");
        for (const auto& a : t.call_args) read_operand(a, "call arg");

        if (t.kind == Terminator::Kind::Call && t.call_receiver) {
            std::string what = t.call_receiver_is_mut
                ? "mutable call to '" + t.call_callee + "'"
                : "const call to '" + t.call_callee + "'";
            accesses.push_back({*t.call_receiver, t.call_receiver_is_mut,
                                blk, tidx, what, t.receiver_reservation});
        }

    }

    // Forward may-origin analysis. Run one boolean dataflow per loan so a
    // definition on one branch is retained at joins even when another branch
    // overwrites the same local with a null or unrelated value.
    auto cfg_successors = [&](size_t b) {
        std::vector<BlockId> out;
        const auto& t = body.blocks[b].terminator;
        if (t.kind == Terminator::Kind::Goto || t.kind == Terminator::Kind::Call || t.kind == Terminator::Kind::Drop) out.push_back(t.target);
        if (t.kind == Terminator::Kind::SwitchInt) {
            for (auto x : t.switch_targets) out.push_back(x.target);
            out.push_back(t.switch_default);
        }
        if (t.kind == Terminator::Kind::Throw && t.target != INVALID_BLOCK) out.push_back(t.target);
        return out;
    };
    std::vector<bool> reachable(body.blocks.size(), false);
    if (body.start_block < body.blocks.size()) {
        std::vector<BlockId> worklist{body.start_block};
        while (!worklist.empty()) {
            BlockId b = worklist.back(); worklist.pop_back();
            if (b >= body.blocks.size() || reachable[b]) continue;
            reachable[b] = true;
            for (BlockId succ : cfg_successors(b)) worklist.push_back(succ);
        }
    }
    std::set<std::pair<BlockId, uint32_t>> calls_with_borrowed_args;
    for (size_t li = 0; li < loans.size(); ++li) {
        const Origin O{loans[li].create_block, loans[li].create_stmt};
        if (O.create_block >= reachable.size() || !reachable[O.create_block]) continue;
        using Bits = std::vector<bool>;
        std::vector<Bits> in(body.blocks.size(), Bits(body.locals.size(), false));
        std::vector<Bits> out(body.blocks.size(), Bits(body.locals.size(), false));
        auto transfer = [&](size_t b, Bits state, bool collect_holders) {
            const auto& bb = body.blocks[b];
            for (size_t si = 0; si < bb.statements.size(); ++si) {
                const auto& st = bb.statements[si];
                if (st.kind == Statement::Kind::StorageDead) {
                    if (st.local < state.size()) state[st.local] = false;
                    continue;
                }
                if (st.kind != Statement::Kind::Assign || !st.place || !st.rvalue) continue;
                const auto& rv = *st.rvalue;
                LocalId dst = st.place->local;
                bool carries = false;
                if (rv.kind == Rvalue::Kind::Ref) {
                    carries = b == O.create_block && si == O.create_stmt;
                } else if (dst < body.locals.size()) {
                    const auto k = body.locals[dst].type.kind;
                    bool can_carry = k == Type::Kind::Ref || k == Type::Kind::RawPtr || k == Type::Kind::Struct
                                  || k == Type::Kind::Container || k == Type::Kind::Unknown;
                    auto operand_carries = [&](const Operand& op) { return op.kind != Operand::Kind::Constant && op.place.local < state.size() && state[op.place.local]; };
                    if (can_carry && rv.kind == Rvalue::Kind::Use && rv.operand) carries = operand_carries(*rv.operand);
                    if (can_carry && rv.kind == Rvalue::Kind::Cast && rv.operand) carries = operand_carries(*rv.operand);
                    if (can_carry && rv.kind == Rvalue::Kind::Aggregate && rv.aggregate)
                        for (const auto& e : rv.aggregate->elements) carries = carries || operand_carries(e);
                }
                if (dst < state.size()) state[dst] = carries;
                if (rv.kind == Rvalue::Kind::Use && rv.operand && rv.operand->kind == Operand::Kind::Move
                    && rv.operand->place.local < state.size() && rv.operand->place.local != dst)
                    state[rv.operand->place.local] = false;
                if (collect_holders)
                    for (LocalId l = 0; l < state.size(); ++l) if (state[l]) loans[li].holders.insert(l);
            }
            const auto& t = bb.terminator;
            if (collect_holders && t.kind == Terminator::Kind::Call) {
                for (const Operand& op : call_operands(t))
                    if (op.kind != Operand::Kind::Constant && op.place.local < state.size()
                        && state[op.place.local])
                        calls_with_borrowed_args.emplace(static_cast<BlockId>(b),
                            static_cast<uint32_t>(bb.statements.size()));
            }
            if (t.kind == Terminator::Kind::Call && t.call_destination) {
                LocalId d = t.call_destination->local;
                bool carries = false;
                auto ops = call_operands(t);
                auto summary = summaries.find(t.call_summary_key.empty() ? t.call_callee : t.call_summary_key);
                for (size_t ai = 0; ai < ops.size(); ++ai) {
                    if (summary != summaries.end() && !summary->second.count(ai)) continue;
                    const auto& a = ops[ai];
                    if (a.kind != Operand::Kind::Constant && a.place.local < state.size()) carries = carries || state[a.place.local];
                }
                if (d < state.size()) state[d] = carries;
            }
            if (collect_holders && t.kind == Terminator::Kind::Drop && t.drop_place
                && t.drop_place->local < state.size() && state[t.drop_place->local])
                loans[li].holders.insert(t.drop_place->local);
            return state;
        };
        bool changed = true;
        while (changed) {
            changed = false;
            for (size_t b = 0; b < body.blocks.size(); ++b) {
                if (!reachable[b]) continue;
                Bits joined(body.locals.size(), false);
                for (size_t p = 0; p < body.blocks.size(); ++p)
                    if (reachable[p]) for (BlockId s : cfg_successors(p)) if (s == b)
                        for (size_t l = 0; l < joined.size(); ++l) joined[l] = joined[l] || out[p][l];
                Bits next = transfer(b, joined, false);
                if (joined != in[b] || next != out[b]) { in[b] = std::move(joined); out[b] = std::move(next); changed = true; }
            }
        }
        for (size_t b = 0; b < body.blocks.size(); ++b)
            if (reachable[b]) transfer(b, in[b], true);
    }

    for (size_t b = 0; b < body.blocks.size(); ++b) {
        if (!reachable[b]) continue;
        const auto& t = body.blocks[b].terminator;
        if (t.kind != Terminator::Kind::Call || !t.call_destination
            || !t.call_destination->is_plain_local()) continue;
        const std::string key = t.call_summary_key.empty() ? t.call_callee : t.call_summary_key;
        if (summaries.find(key) != summaries.end()) continue;
        LocalId dest = t.call_destination->local;
        const bool pointer_result = dest < body.locals.size()
            && (body.locals[dest].type.kind == Type::Kind::RawPtr
                || body.locals[dest].type.kind == Type::Kind::Ref);
        const auto site = std::make_pair(static_cast<BlockId>(b),
                                         static_cast<uint32_t>(body.blocks[b].statements.size()));
        if (pointer_result || calls_with_borrowed_args.count(site))
            diags.push_back({"call to '" + t.call_callee + "' has no borrow/effect summary; return origins are conservative, and argument mutation or retention cannot be verified",
                             site.first, site.second, true});
    }

    // ---- NLL: backward local liveness over the control-flow graph ----
    // A reference loan is active exactly while its holder can still be used.
    // Solve block liveness to a fixed point so loops and branch joins work.
    using LocalSet = std::set<LocalId>;
    const size_t n = body.blocks.size();
    std::vector<LocalSet> use(n), def(n), live_in(n), live_out(n);
    for (size_t b = 0; b < n; ++b) {
        if (!reachable[b]) continue;
        auto note = [&](const Operand& o) { if (o.kind != Operand::Kind::Constant && !def[b].count(o.place.local)) use[b].insert(o.place.local); };
        const auto& bb = body.blocks[b];
        for (const auto& s : bb.statements) {
            if (s.kind == Statement::Kind::Assign && s.rvalue) {
                const auto& rv = *s.rvalue;
                if (rv.operand) note(*rv.operand);
                if (rv.lhs) note(*rv.lhs);
                if (rv.rhs) note(*rv.rhs);
                if (rv.aggregate) for (const auto& e : rv.aggregate->elements) note(e);
                if (s.place) {
                    if (s.place->is_plain_local()) def[b].insert(s.place->local);
                    else if (!def[b].count(s.place->local)) use[b].insert(s.place->local);
                    for (const auto& proj : s.place->projections)
                        if (proj.kind == ProjectionKind::Index && !def[b].count(proj.index_local))
                            use[b].insert(proj.index_local);
                }
            } else if (s.kind == Statement::Kind::StorageDead) def[b].insert(s.local);
            else if (s.kind == Statement::Kind::ReserveBorrow && s.place
                     && !def[b].count(s.place->local)) use[b].insert(s.place->local);
        }
        const auto& t = bb.terminator;
        if (t.switch_on) note(*t.switch_on);
        if (t.return_value) note(*t.return_value);
        for (const auto& a : t.call_args) note(a);
        if (t.call_receiver) note(Operand::make_copy(*t.call_receiver));
        if (t.drop_place && !def[b].count(t.drop_place->local)) use[b].insert(t.drop_place->local);
        if (t.call_destination) def[b].insert(t.call_destination->local);
    }
    auto successors = [&](size_t b) {
        std::vector<BlockId> out;
        const auto& t = body.blocks[b].terminator;
        if (t.kind == Terminator::Kind::Goto || t.kind == Terminator::Kind::Call || t.kind == Terminator::Kind::Drop) out.push_back(t.target);
        if (t.kind == Terminator::Kind::SwitchInt) {
            for (auto x : t.switch_targets) out.push_back(x.target);
            out.push_back(t.switch_default);
        }
        if (t.kind == Terminator::Kind::Throw && t.target != INVALID_BLOCK) out.push_back(t.target);
        return out;
    };
    bool changed = true;
    while (changed) {
        changed = false;
        for (size_t rb = n; rb-- > 0;) {
            if (!reachable[rb]) continue;
            LocalSet out;
            for (BlockId succ : successors(rb))
                if (succ < n && reachable[succ]) out.insert(live_in[succ].begin(), live_in[succ].end());
            LocalSet in = use[rb];
            for (LocalId l : out) if (!def[rb].count(l)) in.insert(l);
            if (out != live_out[rb] || in != live_in[rb]) { live_out[rb] = std::move(out); live_in[rb] = std::move(in); changed = true; }
        }
    }
    std::vector<std::vector<LocalSet>> live_at(n);
    for (size_t b = 0; b < n; ++b) {
        const auto& ss = body.blocks[b].statements;
        live_at[b].resize(ss.size() + 1);
        if (!reachable[b]) continue;
        LocalSet live = live_out[b];
        // Terminator uses are live at the terminator point.
        const auto& t = body.blocks[b].terminator;
        if (t.switch_on && t.switch_on->kind != Operand::Kind::Constant) live.insert(t.switch_on->place.local);
        if (t.return_value && t.return_value->kind != Operand::Kind::Constant) live.insert(t.return_value->place.local);
        for (const auto& a : t.call_args) if (a.kind != Operand::Kind::Constant) live.insert(a.place.local);
        if (t.call_receiver) live.insert(t.call_receiver->local);
        if (t.drop_place) live.insert(t.drop_place->local);
        live_at[b][ss.size()] = live;
        for (size_t ri = ss.size(); ri-- > 0;) {
            const auto& s = ss[ri];
            if (s.kind == Statement::Kind::Assign) {
                if (s.place) {
                    if (s.place->is_plain_local()) live.erase(s.place->local);
                    else live.insert(s.place->local);
                    for (const auto& proj : s.place->projections)
                        if (proj.kind == ProjectionKind::Index) live.insert(proj.index_local);
                }
                if (s.rvalue) {
                    const auto& rv = *s.rvalue;
                    if (rv.operand && rv.operand->kind != Operand::Kind::Constant) live.insert(rv.operand->place.local);
                    if (rv.lhs && rv.lhs->kind != Operand::Kind::Constant) live.insert(rv.lhs->place.local);
                    if (rv.rhs && rv.rhs->kind != Operand::Kind::Constant) live.insert(rv.rhs->place.local);
                    if (rv.aggregate) for (const auto& e : rv.aggregate->elements) if (e.kind != Operand::Kind::Constant) live.insert(e.place.local);
                }
            } else if (s.kind == Statement::Kind::StorageDead) live.erase(s.local);
            else if (s.kind == Statement::Kind::ReserveBorrow && s.place) live.insert(s.place->local);
            live_at[b][ri] = live;
        }
    }

    // ---- Pass 2: access vs. live loans ----
    for (const auto& L : loans) {
        for (const auto& A : accesses) {
            if (A.block >= reachable.size() || !reachable[A.block]) continue;
            bool after_create = before(L.create_block, L.create_stmt, A.block, A.stmt);
            if (L.two_phase) {
                if (!L.activation || !after_create || !before(A.block, A.stmt,
                        L.activation->create_block, L.activation->create_stmt)) continue;
                if (A.reservation) continue; // the nested reservation is checked as a loan below
                if (!L.is_mut || !A.is_write) continue; // reservations permit shared reads
            }
            if (!after_create || A.block >= live_at.size() || A.stmt >= live_at[A.block].size()) continue;
            bool holder_live = false;
            for (LocalId h : L.holders) holder_live = holder_live || live_at[A.block][A.stmt].count(h);
            if (!holder_live) continue;

            if (!Place::overlaps(A.place, L.place)) continue;

            // Write conflicts with any live loan; read conflicts with a
            // live mutable loan.
            bool conflict = A.is_write || L.is_mut;
            if (!conflict) continue;

            std::ostringstream oss;
            oss << (A.is_write ? "mutation" : "read")
                << " of place (local _" << A.place.local << ")"
                << " conflicts with live "
                << (L.is_mut ? "mutable" : "shared")
                << " loan on (local _" << L.place.local << ")"
                << " from bb" << L.create_block << ":" << L.create_stmt;
            diags.push_back({oss.str(), A.block, A.stmt});
        }
    }

    // ---- Pass 3: loan vs. live loan ----
    for (size_t i = 0; i < loans.size(); ++i) {
        const auto& L1 = loans[i];
        if (L1.create_block >= reachable.size() || !reachable[L1.create_block]) continue;
        bool l1_live = false;
        if (L1.create_block < live_at.size() && L1.create_stmt + 1 < live_at[L1.create_block].size())
            for (LocalId h : L1.holders) l1_live = l1_live || live_at[L1.create_block][L1.create_stmt + 1].count(h);
        if (!l1_live) continue;

        for (size_t j = 0; j < loans.size(); ++j) {
            if (i == j) continue;
            const auto& L2 = loans[j];
            if (L2.create_block >= reachable.size() || !reachable[L2.create_block]) continue;
            bool after_create_L2 = before(L2.create_block, L2.create_stmt,
                                          L1.create_block, L1.create_stmt);
            bool l2_live = false;
            if (L1.create_block < live_at.size() && L1.create_stmt + 1 < live_at[L1.create_block].size())
                for (LocalId h : L2.holders) l2_live = l2_live || live_at[L1.create_block][L1.create_stmt + 1].count(h);
            if (!after_create_L2 || !l2_live) continue;

            if (!Place::overlaps(L1.place, L2.place)) continue;

            if (L1.two_phase) {
                if (!L1.activation || !before(L2.create_block, L2.create_stmt,
                        L1.activation->create_block, L1.activation->create_stmt)) continue;
                if (!L2.is_mut) continue; // a shared loan may coexist with a reservation
            }

            if (!L1.is_mut && !L2.is_mut) continue;

            std::ostringstream oss;
            oss << "loan on (local _" << L1.place.local << ")"
                << " created at bb" << L1.create_block << ":" << L1.create_stmt
                << " conflicts with live loan on (local _" << L2.place.local << ")"
                << " from bb" << L2.create_block << ":" << L2.create_stmt;
            diags.push_back({oss.str(), L1.create_block, L1.create_stmt});
        }
    }

    return diags;
}

std::vector<BorrowDiagnostic> check_borrows(const Body& body) {
    return check_borrows(body, ReturnBorrowSummaries{});
}

bool load_return_borrow_summaries(const std::string& path, ReturnBorrowSummaries& summaries, std::string& error) {
    std::ifstream in(path);
    if (!in) { error = "cannot open borrow summary input '" + path + "'"; return false; }
    std::string magic;
    unsigned version = 0;
    if (!(in >> magic >> version) || magic != "SAFECPP_BORROW_SUMMARIES" || version != 1) {
        error = "unsupported or malformed borrow summary file '" + path + "'";
        return false;
    }
    std::string line;
    std::getline(in, line);
    size_t line_number = 1;
    while (std::getline(in, line)) {
        ++line_number;
        if (line.empty()) continue;
        std::istringstream row(line);
        std::string key;
        size_t count = 0;
        if (!(row >> std::quoted(key) >> count) || key.empty()) {
            error = "malformed borrow summary row at " + path + ":" + std::to_string(line_number);
            return false;
        }
        std::set<size_t> positions;
        for (size_t i = 0, pos = 0; i < count; ++i) {
            if (!(row >> pos)) {
                error = "truncated borrow summary row at " + path + ":" + std::to_string(line_number);
                return false;
            }
            positions.insert(pos);
        }
        std::string extra;
        if (row >> extra) {
            error = "extra data in borrow summary row at " + path + ":" + std::to_string(line_number);
            return false;
        }
        auto& dst = summaries[key];
        dst.insert(positions.begin(), positions.end());
    }
    if (in.bad()) { error = "failed while reading borrow summary file '" + path + "'"; return false; }
    return true;
}

bool write_return_borrow_summaries(const std::string& path, const ReturnBorrowSummaries& summaries, std::string& error) {
    namespace fs = std::filesystem;
    const std::string tmp = path + ".tmp";
    {
        std::ofstream out(tmp, std::ios::trunc);
        if (!out) { error = "cannot open borrow summary output '" + tmp + "'"; return false; }
        out << "SAFECPP_BORROW_SUMMARIES 1\n";
        for (const auto& [key, positions] : summaries) {
            out << std::quoted(key) << ' ' << positions.size();
            for (size_t pos : positions) out << ' ' << pos;
            out << '\n';
        }
        out.flush();
        if (!out) { error = "failed while writing borrow summary output '" + tmp + "'"; return false; }
    }
    std::error_code ec;
    fs::rename(tmp, path, ec);
    if (ec) {
        fs::remove(tmp);
        error = "cannot install borrow summary output '" + path + "': " + ec.message();
        return false;
    }
    return true;
}

} // namespace mir
