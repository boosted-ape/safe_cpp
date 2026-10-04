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
                    if (s.place) ctx.check_place(*s.place, where);
                    if (s.rvalue) {
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
                case Statement::Kind::Nop: break;
            }
        }

        const auto& t = bb.terminator;
        switch (t.kind) {
            case Terminator::Kind::Goto:
                ctx.check_block(t.target, where); break;
            case Terminator::Kind::SwitchInt:
                if (t.switch_on) ctx.check_operand(*t.switch_on, where);
                for (const auto& st : t.switch_targets) ctx.check_block(st.target, where);
                ctx.check_block(t.switch_default, where);
                break;
            case Terminator::Kind::Return:
                if (t.return_value) ctx.check_operand(*t.return_value, where);
                break;
            case Terminator::Kind::Call:
                ctx.check_block(t.target, where);
                if (t.call_destination) ctx.check_place(*t.call_destination, where);
                if (t.call_receiver)    ctx.check_place(*t.call_receiver, where);
                for (const auto& a : t.call_args) ctx.check_operand(a, where);
                break;
            case Terminator::Kind::Unreachable:
                break;
            case Terminator::Kind::Drop:
                if (t.drop_place) ctx.check_place(*t.drop_place, where);
                ctx.check_block(t.target, where);
                break;
        }
    }
    return ctx.r;
}

} // namespace mir
