#include "borrow.hpp"
#include <map>
#include <sstream>
#include <set>
#include <fstream>
#include <iomanip>
#include <filesystem>

namespace mir {

namespace {

bool operand_is_value(const Operand& o) {
    return o.kind != Operand::Kind::Constant;
}

std::vector<Operand> call_operands(const Terminator& t) {
    std::vector<Operand> ops;
    if (t.call_receiver) ops.push_back(Operand::make_copy(*t.call_receiver));
    ops.insert(ops.end(), t.call_args.begin(), t.call_args.end());
    return ops;
}

bool borrow_places_overlap(const Place& a, const Place& b) {
    if (a.local == b.local) return Place::overlaps(a, b);
    auto crosses_indirection = [](const Place& place) {
        for (const Projection& projection : place.projections)
            if (projection.kind == ProjectionKind::Deref) return true;
        return false;
    };
    // Without a points-to relation, a reference dereference may designate any
    // local. Treat it as may-alias; this is conservative and preserves the
    // affine rule at function boundaries.
    return crosses_indirection(a) || crosses_indirection(b);
}

bool path_prefix(const Place& prefix, const Place& path) {
    if (prefix.local != path.local || prefix.projections.size() > path.projections.size())
        return false;
    for (size_t i = 0; i < prefix.projections.size(); ++i)
        if (!prefix.projections[i].same_as(path.projections[i])) return false;
    return true;
}

bool shallow_prefix(const Place& prefix, const Place& path) {
    if (!path_prefix(prefix, path)) return false;
    if (prefix.projections.size() == path.projections.size()) return true;
    return path.projections[prefix.projections.size()].kind != ProjectionKind::Deref;
}

} // namespace

struct Loan {
    Place place;
    std::optional<Place> source_ref;
    RegionId region = INVALID_REGION;
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
    bool deep = true;
};

namespace {
bool access_relevant_to_loan(const Access& access, const Place& loan) {
    if (access.place.local != loan.local)
        return access.deep && borrow_places_overlap(access.place, loan);
    if (path_prefix(loan, access.place)) return true;
    return access.deep ? path_prefix(access.place, loan)
                       : shallow_prefix(access.place, loan);
}
} // namespace

// A MIR point is the location immediately before a statement, with the
// terminator at index `statements.size()`. Regions are sets of these points.
using Point = std::pair<BlockId, uint32_t>;
using PointSet = std::set<Point>;

struct Region {
    PointSet points;
    std::set<std::string> end_regions;
};

struct OutlivesConstraint {
    size_t sup = 0;
    size_t sub = 0;
    Point at;
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
        if (t.false_unwind_target) out.push_back(*t.false_unwind_target);
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
                        if (st.kind == Statement::Kind::StorageDead
                            || st.kind == Statement::Kind::StorageLive) {
                            // MIR may emit StorageLive for parameter locals at
                            // entry; it starts their stack slot without
                            // discarding the caller-supplied borrow origin.
                            if (st.local < state.size() && !body.locals[st.local].is_arg)
                                state[st.local] = false;
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

DropEffectSummaries compute_drop_effect_summaries(const std::vector<Body>& bodies) {
    DropEffectSummaries summaries;
    for (const Body& body : bodies) {
        const std::string key = body.summary_key.empty() ? body.name : body.summary_key;
        summaries[key] = {};
    }
    auto same_effect = [](const DropEffect& a, const DropEffect& b) {
        if (a.argument_index != b.argument_index || a.is_write != b.is_write
            || a.deep != b.deep || a.projections.size() != b.projections.size()) return false;
        for (size_t i = 0; i < a.projections.size(); ++i)
            if (!a.projections[i].same_as(b.projections[i])) return false;
        return true;
    };
    auto add_effect = [&](std::vector<DropEffect>& into, DropEffect effect) {
        if (std::any_of(into.begin(), into.end(), [&](const DropEffect& old) {
                return same_effect(old, effect);
            })) return false;
        into.push_back(std::move(effect));
        return true;
    };
    bool changed = true;
    while (changed) {
        changed = false;
        for (const Body& body : bodies) {
            const std::string key = body.summary_key.empty() ? body.name : body.summary_key;
            auto& effects = summaries[key];
            std::map<LocalId, size_t> parameters;
            size_t next = 0;
            for (LocalId l = 0; l < body.locals.size(); ++l)
                if (body.locals[l].is_arg) parameters.emplace(l, next++);
            auto record = [&](const Place& p, bool write, bool deep) {
                auto it = parameters.find(p.local);
                if (it == parameters.end()) return;
                const bool is_this = p.local < body.locals.size() && body.locals[p.local].is_this;
                if (!body.is_destructor && !is_this
                    && body.locals[p.local].type.kind != Type::Kind::Ref) return;
                DropEffect e;
                e.argument_index = it->second;
                e.projections = p.projections;
                if (is_this
                    && !e.projections.empty() && e.projections.front().kind == ProjectionKind::Deref)
                    e.projections.erase(e.projections.begin());
                e.is_write = write;
                e.deep = deep;
                changed = add_effect(effects, std::move(e)) || changed;
            };
            auto record_operand = [&](const Operand& o) {
                if (o.kind != Operand::Kind::Constant) record(o.place, o.kind == Operand::Kind::Move, true);
            };
            for (size_t b = 0; b < body.blocks.size(); ++b) {
                for (const Statement& st : body.blocks[b].statements) {
                    if (st.kind != Statement::Kind::Assign || !st.rvalue) continue;
                    if (st.place) record(*st.place, true, false);
                    const Rvalue& rv = *st.rvalue;
                    if (rv.kind == Rvalue::Kind::Ref && rv.ref_place)
                        record(*rv.ref_place, rv.ref_mut.value_or(false), true);
                    if (rv.operand) record_operand(*rv.operand);
                    if (rv.lhs) record_operand(*rv.lhs);
                    if (rv.rhs) record_operand(*rv.rhs);
                    if (rv.aggregate) for (const Operand& o : rv.aggregate->elements) record_operand(o);
                }
                const Terminator& t = body.blocks[b].terminator;
                if (t.kind != Terminator::Kind::Call) continue;
                std::vector<Place> actuals;
                std::vector<bool> actual_is_referent;
                if (t.call_receiver) actuals.push_back(*t.call_receiver);
                for (const Operand& o : t.call_args) {
                    Place p;
                    bool referent = false;
                    if (o.kind != Operand::Kind::Constant) {
                        p = o.place;
                        const std::optional<Origin> origin = p.local < body.locals.size()
                            ? body.locals[p.local].origin : std::nullopt;
                        if (origin) {
                            for (size_t rb = 0; rb < body.blocks.size(); ++rb)
                                for (size_t rs = 0; rs < body.blocks[rb].statements.size(); ++rs) {
                                    const Statement& st = body.blocks[rb].statements[rs];
                                    if (Origin{static_cast<BlockId>(rb), static_cast<uint32_t>(rs)}
                                        == *origin && st.rvalue && st.rvalue->ref_place) {
                                        p = *st.rvalue->ref_place;
                                        referent = true;
                                        break;
                                    }
                                }
                        }
                    } else p.local = INVALID_BLOCK;
                    actuals.push_back(std::move(p));
                    actual_is_referent.push_back(referent);
                }
                if (t.call_receiver) actual_is_referent.insert(actual_is_referent.begin(), false);
                auto callee = summaries.find(t.call_summary_key.empty() ? t.call_callee : t.call_summary_key);
                if (callee == summaries.end() || t.call_is_virtual || t.call_callee == "<indirect>") {
                    for (Place p : actuals) if (p.local < body.locals.size()) {
                        if (body.locals[p.local].type.kind == Type::Kind::Ref)
                            p.projections.push_back({ProjectionKind::Deref, 0, 0});
                        record(p, true, true);
                    }
                    continue;
                }
                for (const DropEffect& ce : callee->second) {
                    if (ce.argument_index >= actuals.size()) continue;
                    Place p = actuals[ce.argument_index];
                    if (p.local >= body.locals.size()) continue;
                    size_t first = actual_is_referent[ce.argument_index] && !ce.projections.empty()
                        && ce.projections.front().kind == ProjectionKind::Deref ? 1 : 0;
                    p.projections.insert(p.projections.end(), ce.projections.begin() + first, ce.projections.end());
                    if (p.projections.size() > 16) p.projections.clear();
                    record(p, ce.is_write, ce.deep);
                }
            }
            if (body.is_destructor) for (const DropField& field : body.drop_fields) {
                auto child = summaries.find(field.summary_key);
                if (child == summaries.end()) {
                    DropEffect e;
                    e.argument_index = 0;
                    e.projections.push_back({ProjectionKind::Field, field.field_index, 0});
                    e.is_write = e.deep = true;
                    changed = add_effect(effects, std::move(e)) || changed;
                } else for (const DropEffect& ce : child->second) if (ce.argument_index == 0) {
                    DropEffect e = ce;
                    e.argument_index = 0;
                    e.projections.insert(e.projections.begin(), {ProjectionKind::Field, field.field_index, 0});
                    changed = add_effect(effects, std::move(e)) || changed;
                }
            }
        }
    }
    return summaries;
}

std::vector<BorrowDiagnostic> check_borrows(const Body& body,
    const ReturnBorrowSummaries& summaries, const DropEffectSummaries& drop_effects) {
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
                        accesses.push_back({o.place, o.kind == Operand::Kind::Move,
                                            blk, idx, what});
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
                    L.source_ref = *rv.ref_place;
                    L.region = rv.borrow_region.value_or(INVALID_REGION);
                    L.is_mut = rv.ref_mut.value_or(false);
                    L.create_block = blk;
                    L.create_stmt = idx;
                    origin_to_loan[O] = loans.size();
                    accesses.push_back({*rv.ref_place, rv.ref_mut.value_or(false),
                                        blk, idx, "borrow", std::nullopt, true});
                    loans.push_back(L);
                } else {
                    // Ordinary write.
                    accesses.push_back({*st.place, true, blk, idx, "write", std::nullopt, false});

                }
            } else if (st.kind == Statement::Kind::StorageDead) {
                accesses.push_back({Place{st.local, {}}, true, blk, idx, "storage end",
                                    std::nullopt, false});
            } else if (st.kind == Statement::Kind::ReserveBorrow && st.place) {
                Origin O{blk, idx};
                Loan L;
                L.place = *st.place;
                L.source_ref = *st.place;
                L.region = st.borrow_region.value_or(INVALID_REGION);
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
            accesses.push_back({o.place, o.kind == Operand::Kind::Move,
                                blk, tidx, what});
        };

        if (t.kind == Terminator::Kind::Return && t.return_value)
            read_operand(*t.return_value, "return");
        if (t.kind == Terminator::Kind::SwitchInt && t.switch_on)
            read_operand(*t.switch_on, "switch");
        for (const auto& a : t.call_args) read_operand(a, "call arg");

        if (t.kind == Terminator::Kind::Drop && t.drop_place) {
            const LocalId local = t.drop_place->local;
            auto effects = local < body.locals.size()
                ? drop_effects.find(body.locals[local].drop_summary_key)
                : drop_effects.end();
            if (effects == drop_effects.end()) {
                // Missing destructor MIR/effects cannot establish that dropping
                // this value is harmless to an active borrow.
                accesses.push_back({*t.drop_place, true, blk, tidx,
                                    "unmodeled destructor", std::nullopt, true});
            } else {
                for (const DropEffect& effect : effects->second) {
                    Place affected = *t.drop_place;
                    affected.projections.insert(affected.projections.end(),
                        effect.projections.begin(), effect.projections.end());
                    accesses.push_back({std::move(affected), effect.is_write,
                        blk, tidx, "destructor effect", std::nullopt, effect.deep});
                }
            }
        }

        if (t.kind == Terminator::Kind::Call && t.call_receiver) {
            std::string what = t.call_receiver_is_mut
                ? "mutable call to '" + t.call_callee + "'"
                : "const call to '" + t.call_callee + "'";
            accesses.push_back({*t.call_receiver, t.call_receiver_is_mut,
                                blk, tidx, what, t.receiver_reservation});
        }

        if (t.kind == Terminator::Kind::Call) {
            const std::string key = t.call_summary_key.empty() ? t.call_callee : t.call_summary_key;
            auto summary = drop_effects.find(key);
            if (summary != drop_effects.end() && !t.call_is_virtual && t.call_callee != "<indirect>") {
                std::vector<Place> actuals;
                std::vector<bool> actual_is_referent;
                if (t.call_receiver) actuals.push_back(*t.call_receiver);
                for (const Operand& arg : t.call_args) {
                    if (arg.kind == Operand::Kind::Constant) {
                        actuals.emplace_back();
                        actual_is_referent.push_back(false);
                        continue;
                    }
                    Place actual = arg.place;
                    bool referent = false;
                    const std::optional<Origin> origin = actual.local < body.locals.size()
                        ? body.locals[actual.local].origin : std::nullopt;
                    if (origin) {
                        for (size_t rb = 0; rb < body.blocks.size(); ++rb)
                            for (size_t rs = 0; rs < body.blocks[rb].statements.size(); ++rs) {
                                const Statement& st = body.blocks[rb].statements[rs];
                                if (Origin{static_cast<BlockId>(rb), static_cast<uint32_t>(rs)}
                                    == *origin && st.rvalue && st.rvalue->ref_place) {
                                    actual = *st.rvalue->ref_place;
                                    referent = true;
                                    break;
                                }
                            }
                    }
                    actuals.push_back(std::move(actual));
                    actual_is_referent.push_back(referent);
                }
                if (t.call_receiver) actual_is_referent.insert(actual_is_referent.begin(), false);
                for (const DropEffect& effect : summary->second) {
                    if (effect.argument_index >= actuals.size()) continue;
                    Place affected = actuals[effect.argument_index];
                    size_t first = actual_is_referent[effect.argument_index]
                        && !effect.projections.empty()
                        && effect.projections.front().kind == ProjectionKind::Deref ? 1 : 0;
                    affected.projections.insert(affected.projections.end(),
                        effect.projections.begin() + first, effect.projections.end());
                    accesses.push_back({std::move(affected), effect.is_write, blk, tidx,
                        "inferred effect of call to '" + t.call_callee + "'",
                        std::nullopt, effect.deep});
                }
            } else {
                // Unknown/indirect callees may access through any reference argument.
                if (t.call_receiver)
                    accesses.push_back({*t.call_receiver, true, blk, tidx,
                        "unknown receiver call effect", t.receiver_reservation, true});
                for (const Operand& arg : t.call_args)
                    if (arg.kind != Operand::Kind::Constant) {
                        Place unknown = arg.place;
                        if (unknown.local < body.locals.size()
                            && body.locals[unknown.local].type.kind == Type::Kind::Ref)
                            unknown.projections.push_back({ProjectionKind::Deref, 0, 0});
                        accesses.push_back({std::move(unknown), true, blk, tidx,
                            "unknown call effect", std::nullopt, true});
                    }
            }
        }

        // A method may return a reference derived from its implicit receiver.
        // Materialize that summary edge as a loan rooted in the caller's
        // receiver and held by the call result.
        if (t.kind == Terminator::Kind::Call && t.call_receiver
            && t.call_destination && t.call_destination->is_plain_local()
            && t.call_destination->local < body.locals.size()
            && body.locals[t.call_destination->local].type.kind == Type::Kind::Ref) {
            const std::string key = t.call_summary_key.empty() ? t.call_callee : t.call_summary_key;
            auto summary = summaries.find(key);
            if (summary != summaries.end() && summary->second.count(0)) {
                Loan loan;
                loan.place = *t.call_receiver;
                loan.source_ref = *t.call_receiver;
                if (t.call_destination->local < body.locals.size()
                    && body.locals[t.call_destination->local].reference_region)
                    loan.region = *body.locals[t.call_destination->local].reference_region;
                loan.is_mut = t.call_result_ref_mut;
                loan.create_block = blk;
                loan.create_stmt = tidx;
                origin_to_loan[Origin{blk, tidx}] = loans.size();
                loans.push_back(std::move(loan));
                if (t.call_receiver->local < body.locals.size()
                    && body.locals[t.call_receiver->local].is_temp)
                    diags.push_back({"returned reference may refer to a temporary receiver",
                                     blk, tidx});
            }
        }

    }

    RegionId next_region = static_cast<RegionId>(body.regions.size());
    for (Loan& loan : loans)
        if (loan.region == INVALID_REGION) loan.region = next_region++;

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
        if (t.false_unwind_target) out.push_back(*t.false_unwind_target);
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
    // A region is represented at each MIR point by the locals that carry its
    // origin. Liveness is intersected with this relation below.
    using LocalSet = std::set<LocalId>;
    std::vector<std::vector<std::vector<LocalSet>>> region_holders(
        loans.size(), std::vector<std::vector<LocalSet>>(body.blocks.size()));
    for (size_t li = 0; li < loans.size(); ++li)
        for (size_t b = 0; b < body.blocks.size(); ++b)
            region_holders[li][b].resize(body.blocks[b].statements.size() + 1);
    for (size_t li = 0; li < loans.size(); ++li) {
        const Origin O{loans[li].create_block, loans[li].create_stmt};
        if (O.create_block >= reachable.size() || !reachable[O.create_block]) continue;
        using Bits = std::vector<bool>;
        std::vector<Bits> in(body.blocks.size(), Bits(body.locals.size(), false));
        std::vector<Bits> out(body.blocks.size(), Bits(body.locals.size(), false));
        auto transfer = [&](size_t b, Bits state, bool collect_holders) {
            const auto& bb = body.blocks[b];
            for (size_t si = 0; si < bb.statements.size(); ++si) {
                if (collect_holders)
                    for (LocalId l = 0; l < state.size(); ++l)
                        if (state[l]) region_holders[li][b][si].insert(l);
                const auto& st = bb.statements[si];
                if (st.kind == Statement::Kind::StorageDead
                    || st.kind == Statement::Kind::StorageLive) {
                    if (st.local < state.size() && !body.locals[st.local].is_arg)
                        state[st.local] = false;
                    continue;
                }
                if (st.kind == Statement::Kind::ReserveBorrow) {
                    if (st.place && b == O.create_block && si == O.create_stmt
                        && st.place->local < state.size()) state[st.place->local] = true;
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
            }
            const auto& t = bb.terminator;
            if (collect_holders)
                for (LocalId l = 0; l < state.size(); ++l)
                    if (state[l]) region_holders[li][b][bb.statements.size()].insert(l);
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
                const std::string key = t.call_summary_key.empty() ? t.call_callee : t.call_summary_key;
                auto returned = summaries.find(key);
                if (b == O.create_block && bb.statements.size() == O.create_stmt
                    && returned != summaries.end() && returned->second.count(0)
                    && d < state.size()) state[d] = true;
            }
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
    // Each inferred region is the set of MIR points where an origin-carrying
    // local is live, instead of a function-wide union of holder locals.
    // Solve block liveness to a fixed point so loops and branch joins work.
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
            } else if (s.kind == Statement::Kind::StorageDead
                       || s.kind == Statement::Kind::StorageLive) def[b].insert(s.local);
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
        if (t.false_unwind_target) out.push_back(*t.false_unwind_target);
        return out;
    };
    auto point_can_reach = [&](BlockId from_block, uint32_t from_point,
                               BlockId to_block, uint32_t to_point) {
        if (from_block >= n || to_block >= n) return false;
        if (from_block == to_block) return from_point < to_point;
        std::vector<bool> seen(n, false);
        std::vector<BlockId> work = successors(from_block);
        while (!work.empty()) {
            BlockId b = work.back(); work.pop_back();
            if (b >= n || seen[b]) continue;
            if (b == to_block) return true;
            seen[b] = true;
            auto next = successors(b);
            work.insert(work.end(), next.begin(), next.end());
        }
        return false;
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
            } else if (s.kind == Statement::Kind::StorageDead
                       || s.kind == Statement::Kind::StorageLive) live.erase(s.local);
            else if (s.kind == Statement::Kind::ReserveBorrow && s.place) live.insert(s.place->local);
            live_at[b][ri] = live;
        }
    }

    auto is_reborrow_of = [&](size_t parent, const Loan& child) {
        if (!child.source_ref || child.source_ref->local >= body.locals.size()
            || body.locals[child.source_ref->local].type.kind != Type::Kind::Ref
            || child.create_block >= region_holders[parent].size()
            || child.create_stmt >= region_holders[parent][child.create_block].size()) return false;
        return region_holders[parent][child.create_block][child.create_stmt]
            .count(child.source_ref->local) != 0;
    };

    // Build RFC-style region variables. A reference-typed MIR local has a
    // region in its type; every borrow expression has a separate region.
    // Named input/return regions cover the local CFG and carry an external
    // end-region marker. Inferred regions begin empty.
    std::vector<Region> regions(next_region);
    const PointSet all_points = [&] {
        PointSet points;
        for (size_t b = 0; b < n; ++b) {
            if (!reachable[b]) continue;
            for (size_t p = 0; p < live_at[b].size(); ++p)
                points.emplace(static_cast<BlockId>(b), static_cast<uint32_t>(p));
        }
        return points;
    }();
    for (RegionId r = 0; r < body.regions.size(); ++r) {
        if (!body.regions[r].named) continue;
        regions[r].points = all_points;
        if (body.regions[r].name.rfind("param_", 0) == 0)
            regions[r].end_regions.insert(body.regions[r].name);
    }

    // Local liveness contributes point constraints to the lifetime carried
    // by each reference-typed local.
    for (LocalId local = 0; local < body.locals.size(); ++local) {
        if (!body.locals[local].reference_region) continue;
        RegionId r = *body.locals[local].reference_region;
        if (r >= regions.size()) continue;
        for (size_t b = 0; b < n; ++b)
            for (size_t p = 0; p < live_at[b].size(); ++p)
                if (live_at[b][p].count(local))
                    regions[r].points.emplace(static_cast<BlockId>(b),
                                              static_cast<uint32_t>(p));
    }
    // Two-phase receiver reservations are not stored in a reference local;
    // their region is the live interval of the reserved receiver holder.
    for (size_t li = 0; li < loans.size(); ++li) {
        if (!loans[li].two_phase || loans[li].region >= regions.size()) continue;
        for (size_t b = 0; b < n; ++b)
            for (size_t p = 0; p < live_at[b].size(); ++p)
                for (LocalId holder : region_holders[li][b][p])
                    if (live_at[b][p].count(holder)) {
                        regions[loans[li].region].points.emplace(
                            static_cast<BlockId>(b), static_cast<uint32_t>(p));
                        break;
                    }
    }

    std::vector<OutlivesConstraint> outlives;
    auto add_outlives = [&](RegionId sup, RegionId sub, Point at) {
        if (sup < regions.size() && sub < regions.size())
            outlives.push_back({sup, sub, at});
    };
    for (size_t b = 0; b < n; ++b) {
        if (!reachable[b]) continue;
        const auto& bb = body.blocks[b];
        for (size_t si = 0; si < bb.statements.size(); ++si) {
            const Statement& st = bb.statements[si];
            if (st.kind != Statement::Kind::Assign || !st.place || !st.rvalue
                || st.place->local >= body.locals.size()) continue;
            const Rvalue& rv = *st.rvalue;
            const auto dest_region = body.locals[st.place->local].reference_region;
            const Point after{static_cast<BlockId>(b), static_cast<uint32_t>(si + 1)};
            if (rv.kind == Rvalue::Kind::Ref && rv.borrow_region) {
                if (dest_region) add_outlives(*rv.borrow_region, *dest_region, after);
                if (rv.ref_place && rv.ref_place->local < body.locals.size()
                    && body.locals[rv.ref_place->local].reference_region
                    && std::any_of(rv.ref_place->projections.begin(), rv.ref_place->projections.end(),
                        [](const Projection& projection) {
                            return projection.kind == ProjectionKind::Deref;
                        })) {
                    add_outlives(*body.locals[rv.ref_place->local].reference_region,
                                 *rv.borrow_region, after);
                }
            } else if (dest_region && rv.operand
                       && rv.operand->kind != Operand::Kind::Constant
                       && rv.operand->place.local < body.locals.size()
                       && body.locals[rv.operand->place.local].reference_region) {
                add_outlives(*body.locals[rv.operand->place.local].reference_region,
                             *dest_region, after);
            }
        }

        const Terminator& t = bb.terminator;
        const Point term{static_cast<BlockId>(b), static_cast<uint32_t>(bb.statements.size())};
        if (t.kind == Terminator::Kind::Call && t.call_destination
            && t.call_destination->local < body.locals.size()
            && body.locals[t.call_destination->local].reference_region
            && t.target < n) {
            const std::string key = t.call_summary_key.empty() ? t.call_callee : t.call_summary_key;
            auto summary = summaries.find(key);
            const std::vector<Operand> ops = call_operands(t);
            if (summary != summaries.end()) {
                for (size_t ai : summary->second) {
                    if (ai >= ops.size() || ops[ai].kind == Operand::Kind::Constant
                        || ops[ai].place.local >= body.locals.size()
                        || !body.locals[ops[ai].place.local].reference_region) continue;
                    add_outlives(*body.locals[ops[ai].place.local].reference_region,
                        *body.locals[t.call_destination->local].reference_region,
                        Point{t.target, 0});
                }
            }
        }
        if (t.kind == Terminator::Kind::Return && t.return_value
            && t.return_value->kind != Operand::Kind::Constant
            && t.return_value->place.local < body.locals.size()
            && body.return_region && body.locals[t.return_value->place.local].reference_region)
            add_outlives(*body.locals[t.return_value->place.local].reference_region,
                         *body.return_region, term);
    }

    // Seed the synthetic return region with the inferred C++ parameter
    // origins. This represents the caller-side end regions that a Rust
    // signature would name explicitly.
    if (body.return_region && *body.return_region < regions.size()) {
        const std::string key = body.summary_key.empty() ? body.name : body.summary_key;
        auto returned = summaries.find(key);
        std::vector<LocalId> params;
        for (LocalId local = 0; local < body.locals.size(); ++local)
            if (body.locals[local].is_arg) params.push_back(local);
        if (returned != summaries.end()) {
            for (size_t pi : returned->second) {
                if (pi < params.size() && body.locals[params[pi]].reference_region) {
                    RegionId r = *body.locals[params[pi]].reference_region;
                    regions[*body.return_region].end_regions.insert(body.regions[r].name);
                }
            }
        }
    }

    // Evaluate a location-sensitive outlives constraint. Propagation walks
    // only through points already in the target region, so an assignment
    // that kills an old reference interrupts the old borrow's region.
    auto reachable_in_region = [&](Point start, const Region& target) {
        PointSet reached;
        if (!target.points.count(start)) return reached;
        std::vector<Point> work{start};
        while (!work.empty()) {
            Point point = work.back();
            work.pop_back();
            if (!target.points.count(point) || !reached.insert(point).second) continue;
            if (point.first >= n) continue;
            const size_t count = body.blocks[point.first].statements.size();
            if (point.second < count) {
                work.emplace_back(point.first, point.second + 1);
            } else {
                for (BlockId succ : successors(point.first))
                    if (succ < n) work.emplace_back(succ, 0);
            }
        }
        return reached;
    };
    bool regions_changed = true;
    while (regions_changed) {
        regions_changed = false;
        for (const OutlivesConstraint& constraint : outlives) {
            if (constraint.sup >= regions.size() || constraint.sub >= regions.size()) continue;
            const PointSet required = reachable_in_region(constraint.at, regions[constraint.sub]);
            for (const Point& point : required)
                if (regions[constraint.sup].points.insert(point).second)
                    regions_changed = true;
            // An external lifetime end escapes this function only when the
            // CFG exit is reachable through the target region.
            if (!required.empty()) {
                bool reaches_return = false;
                for (size_t b = 0; b < n && !reaches_return; ++b) {
                    const Terminator& t = body.blocks[b].terminator;
                    if (t.kind == Terminator::Kind::Return
                        && required.count(Point{static_cast<BlockId>(b),
                            static_cast<uint32_t>(body.blocks[b].statements.size())}))
                        reaches_return = true;
                }
                if (reaches_return)
                    for (const std::string& end : regions[constraint.sub].end_regions)
                        if (regions[constraint.sup].end_regions.insert(end).second)
                            regions_changed = true;
            }
        }
    }
    auto loan_live_at = [&](size_t li, size_t b, size_t p) {
        return li < loans.size() && loans[li].region < regions.size()
            && regions[loans[li].region].points.count(
                Point{static_cast<BlockId>(b), static_cast<uint32_t>(p)}) != 0;
    };

    // C++ permits returning a reference to a local, so validate that every
    // reference-return path is rooted in a parameter under this profile.
    if (body.return_type.find('&') != std::string::npos) {
        for (size_t b = 0; b < n; ++b) {
            if (!reachable[b]) continue;
            const Terminator& t = body.blocks[b].terminator;
            if (t.kind != Terminator::Kind::Return || !t.return_value
                || t.return_value->kind == Operand::Kind::Constant) continue;
            const LocalId returned = t.return_value->place.local;
            if (returned < body.locals.size() && body.locals[returned].is_arg
                && (body.locals[returned].type.kind == Type::Kind::Ref
                    || body.locals[returned].is_this)) continue;
            bool rooted_in_parameter = false;
            const size_t point = body.blocks[b].statements.size();
            for (size_t li = 0; li < loans.size(); ++li) {
                if (loans[li].place.local >= body.locals.size()
                    || !body.locals[loans[li].place.local].is_arg
                    || (body.locals[loans[li].place.local].type.kind != Type::Kind::Ref
                        && !body.locals[loans[li].place.local].is_this)) continue;
                if (point >= live_at[b].size() || !live_at[b][point].count(returned)) continue;
                if (region_holders[li][b][point].count(returned)) {
                    rooted_in_parameter = true;
                    break;
                }
            }
            if (!rooted_in_parameter)
                diags.push_back({"returned reference may outlive its local referent", static_cast<BlockId>(b),
                                 static_cast<uint32_t>(point)});
        }
    }

    // A returned reference to a temporary bound to a reference parameter is
    // dangling after the call's full-expression. Reject this escape even when
    // the callee's parameter-origin summary is otherwise valid.
    for (size_t b = 0; b < n; ++b) {
        if (!reachable[b]) continue;
        const Terminator& t = body.blocks[b].terminator;
        if (t.kind != Terminator::Kind::Call || !t.call_destination
            || t.call_destination->local >= body.locals.size()
            || body.locals[t.call_destination->local].type.kind != Type::Kind::Ref) continue;
        const std::string key = t.call_summary_key.empty() ? t.call_callee : t.call_summary_key;
        auto summary = summaries.find(key);
        if (summary == summaries.end()) continue;
        const size_t point = body.blocks[b].statements.size();
        const std::vector<Operand> ops = call_operands(t);
        bool reported = false;
        for (size_t ai : summary->second) {
            if (ai >= ops.size() || ops[ai].kind == Operand::Kind::Constant) continue;
            for (size_t li = 0; li < loans.size(); ++li) {
                if (loans[li].place.local >= body.locals.size()
                    || !body.locals[loans[li].place.local].is_temp
                    || !region_holders[li][b][point].count(ops[ai].place.local)) continue;
                diags.push_back({"returned reference may refer to a temporary argument",
                                 static_cast<BlockId>(b), static_cast<uint32_t>(point)});
                reported = true;
                break;
            }
            if (reported) break;
        }
    }

    // ---- Pass 2: access vs. live loans ----
    for (size_t li = 0; li < loans.size(); ++li) {
        const auto& L = loans[li];
        for (const auto& A : accesses) {
            if (A.block >= reachable.size() || !reachable[A.block]) continue;
            if (L.two_phase) {
                if (!L.activation || !point_can_reach(A.block, A.stmt,
                        L.activation->create_block, L.activation->create_stmt)) continue;
                if (A.reservation) continue; // the nested reservation is checked as a loan below
                if (!L.is_mut || !A.is_write) continue; // reservations permit shared reads
            }
            if (A.block >= live_at.size() || A.stmt >= live_at[A.block].size()) continue;
            if (!regions[li].points.count(Point{A.block, A.stmt})) continue;

            // Access through this reference (or a local that carries the same
            // origin) is the authorized use of the loan itself.
            const bool access_through_holder = A.place.local < body.locals.size()
                && body.locals[A.place.local].type.kind == Type::Kind::Ref
                && region_holders[li][A.block][A.stmt].count(A.place.local)
                && std::any_of(A.place.projections.begin(), A.place.projections.end(),
                    [](const Projection& p) { return p.kind == ProjectionKind::Deref; });
            if (access_through_holder) {
                if (L.is_mut) {
                    for (size_t child = 0; child < loans.size(); ++child) {
                        if (child == li || !is_reborrow_of(li, loans[child])
                            || !loan_live_at(child, A.block, A.stmt)
                            || region_holders[child][A.block][A.stmt].count(A.place.local)) continue;
                        std::ostringstream oss;
                        oss << "use through mutable reference local _" << A.place.local
                            << " conflicts with its active reborrow from bb"
                            << loans[child].create_block << ":" << loans[child].create_stmt;
                        diags.push_back({oss.str(), A.block, A.stmt});
                        break;
                    }
                }
                continue;
            }

            if (!access_relevant_to_loan(A, L.place)) continue;

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
    // Check region intersection over reachable MIR locations.
    for (size_t i = 0; i < loans.size(); ++i) {
        const auto& L1 = loans[i];
        if (L1.create_block >= reachable.size() || !reachable[L1.create_block]) continue;
        for (size_t j = 0; j < loans.size(); ++j) {
            if (i == j) continue;
            const auto& L2 = loans[j];
            if (L2.create_block >= reachable.size() || !reachable[L2.create_block]) continue;
            if (!borrow_places_overlap(L1.place, L2.place)) continue;
            if (!L1.is_mut && !L2.is_mut) continue;

            if (is_reborrow_of(i, L2) || is_reborrow_of(j, L1)) continue;

            bool regions_overlap = false;
            for (size_t b = 0; b < body.blocks.size() && !regions_overlap; ++b) {
                if (!reachable[b]) continue;
                for (size_t p = 0; p < live_at[b].size(); ++p) {
                    if (!loan_live_at(i, b, p) || !loan_live_at(j, b, p)) continue;
                    if (L1.two_phase) {
                        if (!L1.activation) continue;
                        // Before activation, receiver reservations allow
                        // shared loans but still reject mutable loans.
                        const bool before_activation = point_can_reach(static_cast<BlockId>(b),
                                static_cast<uint32_t>(p),
                                L1.activation->create_block,
                                L1.activation->create_stmt);
                        const bool at_activation = b == L1.activation->create_block
                            && p == L1.activation->create_stmt;
                        if (!before_activation && !at_activation) continue;
                        if (before_activation && !L2.is_mut) continue;
                    }
                    regions_overlap = true;
                    break;
                }
            }
            if (!regions_overlap) continue;

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

std::vector<BorrowDiagnostic> check_borrows(const Body& body,
    const ReturnBorrowSummaries& summaries) {
    return check_borrows(body, summaries, DropEffectSummaries{});
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
