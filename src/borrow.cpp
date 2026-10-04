#include "borrow.hpp"
#include <map>
#include <sstream>

namespace mir {

namespace {

bool before(BlockId ab, uint32_t as, BlockId bb, uint32_t bs) {
    if (ab != bb) return ab < bb;
    return as < bs;
}

bool operand_is_value(const Operand& o) {
    return o.kind != Operand::Kind::Constant;
}

} // namespace

struct Loan {
    Place place;
    bool is_mut = false;
    BlockId create_block = 0;
    uint32_t create_stmt = 0;
    BlockId last_use_block = INVALID_BLOCK;
    uint32_t last_use_stmt = 0;
    bool has_use = false;
};

struct Access {
    Place place;
    bool is_write = false;
    BlockId block = 0;
    uint32_t stmt = 0;
    std::string description;
};

std::vector<BorrowDiagnostic> check_borrows(const Body& body) {
    std::vector<BorrowDiagnostic> diags;

    std::vector<Loan> loans;
    std::map<Origin, size_t> origin_to_loan;
    std::vector<Access> accesses;
    std::vector<std::optional<Origin>> cur_origin(body.locals.size());

    auto record_use = [&](const Place& p, BlockId blk, uint32_t stmt) {
        LocalId lid = p.local;
        if (lid >= cur_origin.size()) return;
        if (!cur_origin[lid]) return;
        auto it = origin_to_loan.find(*cur_origin[lid]);
        if (it == origin_to_loan.end()) return;
        auto& L = loans[it->second];
        L.has_use = true;
        L.last_use_block = blk;
        L.last_use_stmt = stmt;
    };

    // ---- Pass 1: linear replay, collect loans and accesses ----
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
                        record_use(o.place, blk, idx);
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
                    L.is_mut = rv.ref_mut.value_or(false);
                    L.create_block = blk;
                    L.create_stmt = idx;
                    origin_to_loan[O] = loans.size();
                    loans.push_back(L);
                    if (st.place->local < cur_origin.size())
                        cur_origin[st.place->local] = O;
                } else {
                    // Ordinary write.
                    accesses.push_back({*st.place, true, blk, idx, "write"});

                    if (rv.kind == Rvalue::Kind::Use && rv.operand
                        && rv.operand->kind != Operand::Kind::Constant
                        && rv.operand->place.is_plain_local()) {
                        LocalId src = rv.operand->place.local;
                        if (src < cur_origin.size()) {
                            cur_origin[st.place->local] = cur_origin[src];
                            if (rv.operand->kind == Operand::Kind::Move)
                                cur_origin[src] = std::nullopt;
                        } else {
                            cur_origin[st.place->local] = std::nullopt;
                        }
                    } else {
                        cur_origin[st.place->local] = std::nullopt;
                    }
                }
            } else if (st.kind == Statement::Kind::StorageDead) {
                if (st.local < cur_origin.size())
                    cur_origin[st.local] = std::nullopt;
            }
        }

        // Terminator reads, writes, and loan creation.
        uint32_t tidx = static_cast<uint32_t>(bb.statements.size());
        const auto& t = bb.terminator;

        auto read_operand = [&](const Operand& o, const std::string& what) {
            if (!operand_is_value(o)) return;
            record_use(o.place, blk, tidx);
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
                                blk, tidx, what});
        }

        if (t.kind == Terminator::Kind::Call && t.call_destination
            && t.call_destination->is_plain_local()) {
            LocalId d = t.call_destination->local;
            if (d < cur_origin.size()) cur_origin[d] = std::nullopt;
        }
    }

    // ---- Pass 2: access vs. live loans ----
    for (const auto& L : loans) {
        if (!L.has_use) continue;

        for (const auto& A : accesses) {
            bool after_create = before(L.create_block, L.create_stmt, A.block, A.stmt);
            bool before_use   = before(A.block, A.stmt, L.last_use_block, L.last_use_stmt);
            if (!after_create || !before_use) continue;

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
        if (!L1.has_use) continue;

        for (size_t j = 0; j < loans.size(); ++j) {
            if (i == j) continue;
            const auto& L2 = loans[j];
            if (!L2.has_use) continue;

            bool after_create_L2 = before(L2.create_block, L2.create_stmt,
                                          L1.create_block, L1.create_stmt);
            bool before_use_L2   = before(L1.create_block, L1.create_stmt,
                                          L2.last_use_block, L2.last_use_stmt);
            if (!after_create_L2 || !before_use_L2) continue;

            if (!Place::overlaps(L1.place, L2.place)) continue;

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

} // namespace mir
