#include "printer.hpp"

namespace mir {

static const char* binop_str(BinOp op) {
    switch (op) {
        case BinOp::Add: return "+";
        case BinOp::Sub: return "-";
        case BinOp::Mul: return "*";
        case BinOp::Div: return "/";
        case BinOp::Mod: return "%";
        case BinOp::Eq:  return "==";
        case BinOp::Ne:  return "!=";
        case BinOp::Lt:  return "<";
        case BinOp::Le:  return "<=";
        case BinOp::Gt:  return ">";
        case BinOp::Ge:  return ">=";
        default:         return "?";
    }
}

static const char* unop_str(UnOp op) {
    switch (op) {
        case UnOp::Neg: return "-";
        case UnOp::Not: return "!";
    }
    return "?";
}

static void print_place(const Place& p, std::ostream& os) {
    os << "_" << p.local;
    for (const auto& proj : p.projections) {
        switch (proj.kind) {
            case ProjectionKind::Deref: os << ".*"; break;
            case ProjectionKind::Field: os << "." << proj.field_idx; break;
            case ProjectionKind::Index: os << "[" << "_" << proj.index_local << "]"; break;
        }
    }
}

static void print_operand(const Operand& op, std::ostream& os) {
    switch (op.kind) {
        case Operand::Kind::Copy:     os << "copy "; print_place(op.place, os); break;
        case Operand::Kind::Move:     os << "move "; print_place(op.place, os); break;
        case Operand::Kind::Constant: os << "const " << op.constant; break;
    }
}

static void print_rvalue(const Rvalue& rv, std::ostream& os) {
    switch (rv.kind) {
        case Rvalue::Kind::Use:
            print_operand(*rv.operand, os);
            break;
        case Rvalue::Kind::BinaryOp:
            os << "(";
            print_operand(*rv.lhs, os);
            os << " " << binop_str(*rv.binop) << " ";
            print_operand(*rv.rhs, os);
            os << ")";
            break;
        case Rvalue::Kind::UnaryOp:
            os << unop_str(*rv.unop);
            print_operand(*rv.operand, os);
            break;
        case Rvalue::Kind::Ref:
            os << (rv.ref_mut && *rv.ref_mut ? "&mut " : "&");
            print_place(*rv.ref_place, os);
            break;
        case Rvalue::Kind::Aggregate: {
            const auto& agg = *rv.aggregate;
            os << (agg.kind == Aggregate::Kind::Struct ? agg.struct_name : "[");
            os << " { ";
            for (size_t i = 0; i < agg.elements.size(); ++i) {
                if (i) os << ", ";
                print_operand(agg.elements[i], os);
            }
            os << " }";
            break;
        }
    }
}

static void print_statement(const Statement& s, std::ostream& os) {
    switch (s.kind) {
        case Statement::Kind::StorageLive: os << "StorageLive(_" << s.local << ")"; break;
        case Statement::Kind::StorageDead: os << "StorageDead(_" << s.local << ")"; break;
        case Statement::Kind::Assign:
            print_place(*s.place, os);
            os << " = ";
            print_rvalue(*s.rvalue, os);
            break;
        case Statement::Kind::Nop: os << "nop"; break;
    }
}

static void print_terminator(const Terminator& t, std::ostream& os) {
    switch (t.kind) {
        case Terminator::Kind::Goto:
            os << "goto -> bb" << t.target;
            break;
        case Terminator::Kind::SwitchInt:
            os << "switchInt(";
            print_operand(*t.switch_on, os);
            os << ") -> [";
            for (size_t i = 0; i < t.switch_targets.size(); ++i) {
                if (i) os << ", ";
                os << t.switch_targets[i].value << ": bb" << t.switch_targets[i].target;
            }
            os << "] otherwise: bb" << t.switch_default;
            break;
        case Terminator::Kind::Return:
            os << "return";
            if (t.return_value) { os << " ("; print_operand(*t.return_value, os); os << ")"; }
            break;
        case Terminator::Kind::Call: {
            if (t.call_destination) { print_place(*t.call_destination, os); os << " = "; }
            os << "call " << t.call_callee << "(";
            bool first = true;
            if (t.call_receiver) {
                os << (t.call_receiver_is_mut ? "&mut " : "&");
                print_place(*t.call_receiver, os);
                first = false;
            }
            for (const auto& a : t.call_args) {
                if (!first) os << ", ";
                first = false;
                print_operand(a, os);
            }
            os << ")";
            if (t.call_is_virtual) os << " [virtual]";
            os << " -> bb" << t.target;
            break;
        }
        case Terminator::Kind::Unreachable:
            os << "unreachable";
            break;
        case Terminator::Kind::Drop:
            os << "drop(";
            print_place(*t.drop_place, os);
            os << ") -> bb" << t.target;
            break;
    }
}

void print_body(const Body& body, std::ostream& os) {
    os << "fn " << body.name << "() -> " << body.return_type << " {\n";

    os << "    // locals\n";
    for (size_t i = 0; i < body.locals.size(); ++i) {
        const auto& l = body.locals[i];
        os << "    let _" << i << ": " << l.type_name;
        if (!l.name.empty()) os << "  // " << l.name;
        if (l.is_arg)  os << "  // arg";
        if (l.is_temp) os << "  // tmp";
        os << ";\n";
    }
    os << "\n";

    for (size_t i = 0; i < body.blocks.size(); ++i) {
        os << "    bb" << i << ": {\n";
        for (const auto& s : body.blocks[i].statements) {
            os << "        ";
            print_statement(s, os);
            os << ";\n";
        }
        if (body.blocks[i].terminated) {
            os << "        ";
            print_terminator(body.blocks[i].terminator, os);
            os << ";\n";
        }
        os << "    }\n";
    }

    os << "}\n";
}

} // namespace mir
