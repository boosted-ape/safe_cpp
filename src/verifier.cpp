#include "verifier.hpp"

namespace mir {

namespace {
struct Ctx {
    VerifyResult r;
    const Body* body;
    void err(const std::string& msg) {
        r.ok = false;
        r.errors.push_back(msg);
    }
    void check_local(LocalId l, const std::string& where) {
        if (l >= body->locals.size())
            err(where + ": local _" + std::to_string(l) + " not declared");
    }
    void check_block(BlockId b, const std::string& where) {
        if (b >= body->blocks.size())
            err(where + ": block bb" + std::to_string(b) + " does not exist");
    }
    void check_place(const Place& p, const std::string& where) {
        check_local(p.local, where);
        for (const auto& proj : p.projections)
            if (proj.kind == ProjectionKind::Index)
                check_local(proj.index_local, where + " (index)");
    }
    void check_operand(const Operand& o, const std::string& where) {
        if (o.kind != Operand::Kind::Constant) check_place(o.place, where);
    }
};
} // namespace

VerifyResult verify_body(const Body& body) {
    Ctx ctx{{true, {}}, &body};

    if (body.blocks.empty()) {
        ctx.err("body has no basic blocks");
        return ctx.r;
    }
    if (body.start_block >= body.blocks.size())
        ctx.err("start block bb" + std::to_string(body.start_block) + " does not exist");

    for (size_t i = 0; i < body.blocks.size(); ++i) {
        const auto& bb = body.blocks[i];
        std::string where = "bb" + std::to_string(i);

        if (!bb.terminated) {
            ctx.err(where + ": block is not terminated");
            continue;
        }

        for (const auto& s : bb.statements) {
            switch (s.kind) {
                case Statement::Kind::StorageLive:
                case Statement::Kind::StorageDead:
                    ctx.check_local(s.local, where);
                    break;
                case Statement::Kind::Assign:
                    if (!s.place) ctx.err(where + ": assignment has no destination");
                    else ctx.check_place(*s.place, where + " (destination)");
                    if (!s.rvalue) ctx.err(where + ": assignment has no rvalue");
                    else {
                        const auto& rv = *s.rvalue;
                        if (rv.operand) ctx.check_operand(*rv.operand, where);
                        if (rv.lhs)     ctx.check_operand(*rv.lhs, where);
                        if (rv.rhs)     ctx.check_operand(*rv.rhs, where);
                        if (rv.ref_place) ctx.check_place(*rv.ref_place, where);
                        if (rv.aggregate)
                            for (const auto& el : rv.aggregate->elements)
                                ctx.check_operand(el, where);
                    }
                    break;
                case Statement::Kind::ReserveBorrow:
                    if (s.place) ctx.check_place(*s.place, where);
                    else ctx.err(where + ": borrow reservation has no place");
                    break;
                case Statement::Kind::Nop: break;
            }
        }

        const auto& t = bb.terminator;
        switch (t.kind) {
            case Terminator::Kind::Goto:
                ctx.check_block(t.target, where); break;
            case Terminator::Kind::SwitchInt:
                if (!t.switch_on) ctx.err(where + ": switch has no discriminant");
                else ctx.check_operand(*t.switch_on, where + " (switch)");
                for (const auto& st : t.switch_targets) ctx.check_block(st.target, where);
                ctx.check_block(t.switch_default, where);
                break;
            case Terminator::Kind::Return:
                if (t.return_value) ctx.check_operand(*t.return_value, where);
                break;
            case Terminator::Kind::Call:
                ctx.check_block(t.target, where);
                if (t.call_destination) ctx.check_place(*t.call_destination, where + " (call destination)");
                else if (!t.call_is_destructor)
                    ctx.err(where + ": call has no destination");
                if (t.call_receiver)    ctx.check_place(*t.call_receiver, where);
                for (const auto& a : t.call_args) ctx.check_operand(a, where);
                break;
            case Terminator::Kind::Unreachable:
                break;
            case Terminator::Kind::Drop:
                if (!t.drop_place) ctx.err(where + ": drop has no place");
                else ctx.check_place(*t.drop_place, where + " (drop)");
                ctx.check_block(t.target, where);
                break;
            case Terminator::Kind::Throw:
                if (t.thrown_value) ctx.check_operand(*t.thrown_value, where);
                if (t.target != INVALID_BLOCK) ctx.check_block(t.target, where);
                break;
        }

    }
    if (!ctx.r.ok) return ctx.r;

    // Definite initialization is a forward must-analysis over reachable CFG
    // blocks. Joins intersect predecessor states, so a local is initialized
    // only if every incoming path initializes it.
    const size_t count = body.blocks.size();
    std::vector<std::vector<BlockId>> successors(count), predecessors(count);
    for (size_t b = 0; b < count; ++b) {
        const auto& t = body.blocks[b].terminator;
        auto add = [&](BlockId target) {
            if (target < count) {
                successors[b].push_back(target);
                predecessors[target].push_back(static_cast<BlockId>(b));
            }
        };
        if (t.kind == Terminator::Kind::Goto || t.kind == Terminator::Kind::Call || t.kind == Terminator::Kind::Drop) add(t.target);
        if (t.kind == Terminator::Kind::SwitchInt) {
            for (const auto& target : t.switch_targets) add(target.target);
            add(t.switch_default);
        }
        if (t.kind == Terminator::Kind::Throw && t.target != INVALID_BLOCK) add(t.target);
    }
    std::vector<bool> reachable(count, false);
    std::vector<BlockId> worklist{body.start_block};
    while (!worklist.empty()) {
        BlockId b = worklist.back(); worklist.pop_back();
        if (b >= count || reachable[b]) continue;
        reachable[b] = true;
        worklist.insert(worklist.end(), successors[b].begin(), successors[b].end());
    }

    using Init = std::vector<bool>;
    Init initial(body.locals.size(), false);
    for (LocalId l = 0; l < body.locals.size(); ++l)
        if (body.locals[l].is_arg) initial[l] = true;
    std::vector<Init> in(count, Init(body.locals.size(), true));
    std::vector<Init> out(count, Init(body.locals.size(), true));
    if (body.start_block < count) in[body.start_block] = initial;

    auto transfer = [&](size_t b, Init state, bool report) {
        const std::string where = "bb" + std::to_string(b);
        auto read_local = [&](LocalId local) {
            if (local < state.size() && report && !state[local])
                ctx.err(where + ": use of local _" + std::to_string(local) + " before initialization");
        };
        auto read_operand = [&](const Operand& operand) {
            if (operand.kind == Operand::Kind::Constant) return;
            read_local(operand.place.local);
            for (const auto& proj : operand.place.projections)
                if (proj.kind == ProjectionKind::Index) read_local(proj.index_local);
        };
        auto read_place = [&](const Place& place) {
            read_local(place.local);
            for (const auto& proj : place.projections)
                if (proj.kind == ProjectionKind::Index) read_local(proj.index_local);
        };
        for (const auto& s : body.blocks[b].statements) {
            if (s.kind == Statement::Kind::StorageLive) {
                if (s.local < state.size()) state[s.local] = body.locals[s.local].is_arg;
            } else if (s.kind == Statement::Kind::StorageDead) {
                if (s.local < state.size()) state[s.local] = false;
            } else if (s.kind == Statement::Kind::Assign && s.place && s.rvalue) {
                const Rvalue& rv = *s.rvalue;
                if (rv.kind == Rvalue::Kind::Ref && rv.ref_place) {
                    read_place(*rv.ref_place);
                } else {
                    if (rv.operand) read_operand(*rv.operand);
                    if (rv.lhs) read_operand(*rv.lhs);
                    if (rv.rhs) read_operand(*rv.rhs);
                    if (rv.aggregate)
                        for (const auto& element : rv.aggregate->elements) read_operand(element);
                }
                if (s.place->is_plain_local() && s.place->local < state.size())
                    state[s.place->local] = true;
                auto consume = [&](const Operand& operand) {
                    if (operand.kind == Operand::Kind::Move && operand.place.is_plain_local()
                        && operand.place.local < state.size() && operand.place.local != s.place->local)
                        state[operand.place.local] = false;
                };
                if (rv.operand) consume(*rv.operand);
                if (rv.lhs) consume(*rv.lhs);
                if (rv.rhs) consume(*rv.rhs);
                if (rv.aggregate) for (const auto& element : rv.aggregate->elements) consume(element);
            } else if (s.kind == Statement::Kind::ReserveBorrow && s.place) {
                read_place(*s.place);
            }
        }
        const auto& t = body.blocks[b].terminator;
        if (t.switch_on) read_operand(*t.switch_on);
        if (t.return_value) read_operand(*t.return_value);
        if (t.thrown_value) read_operand(*t.thrown_value);
        for (const auto& arg : t.call_args) read_operand(arg);
        if (t.call_receiver) read_place(*t.call_receiver);
        if (t.drop_place) read_place(*t.drop_place);
        if (t.kind == Terminator::Kind::Call && t.call_destination
            && t.call_destination->is_plain_local() && t.call_destination->local < state.size())
            state[t.call_destination->local] = true;
        if (t.kind == Terminator::Kind::Call) {
            auto consume = [&](const Operand& operand) {
                if (operand.kind == Operand::Kind::Move && operand.place.is_plain_local()
                    && operand.place.local < state.size()
                    && (!t.call_destination || operand.place.local != t.call_destination->local))
                    state[operand.place.local] = false;
            };
            for (const auto& arg : t.call_args) consume(arg);
        }
        return state;
    };

    bool init_changed = true;
    while (init_changed) {
        init_changed = false;
        for (size_t b = 0; b < count; ++b) {
            if (!reachable[b]) continue;
            Init next_in(body.locals.size(), true);
            bool has_pred = false;
            if (b == body.start_block) { next_in = initial; has_pred = true; }
            for (BlockId pred : predecessors[b]) {
                if (!reachable[pred]) continue;
                has_pred = true;
                for (size_t l = 0; l < next_in.size(); ++l) next_in[l] = next_in[l] && out[pred][l];
            }
            if (!has_pred) std::fill(next_in.begin(), next_in.end(), false);
            Init next_out = transfer(b, next_in, false);
            if (next_in != in[b] || next_out != out[b]) {
                in[b] = std::move(next_in);
                out[b] = std::move(next_out);
                init_changed = true;
            }
        }
    }
    for (size_t b = 0; b < count; ++b)
        if (reachable[b]) transfer(b, in[b], true);
    return ctx.r;
}

} // namespace mir
