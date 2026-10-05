#pragma once
#include <algorithm>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <vector>

namespace mir {

using LocalId = uint32_t;
using BlockId = uint32_t;
constexpr BlockId INVALID_BLOCK = ~BlockId(0);

// ---------- Origin: identifies the source of a loan ----------
struct Origin {
    BlockId create_block = 0;
    uint32_t create_stmt = 0;

    bool operator==(const Origin& o) const {
        return create_block == o.create_block && create_stmt == o.create_stmt;
    }
    bool operator<(const Origin& o) const {
        if (create_block != o.create_block) return create_block < o.create_block;
        return create_stmt < o.create_stmt;
    }
};

// ---------- Projections / Places ----------
enum class ProjectionKind { Deref, Field, Index };

struct Projection {
    ProjectionKind kind = ProjectionKind::Field;
    uint32_t field_idx = 0;
    LocalId index_local = 0;

    bool same_as(const Projection& o) const {
        if (kind != o.kind) return false;
        if (kind == ProjectionKind::Field) return field_idx == o.field_idx;
        return true;
    }
};

struct Place {
    LocalId local = 0;
    std::vector<Projection> projections;

    bool is_plain_local() const { return projections.empty(); }

    // Two places overlap iff they share a base local and one's projection
    // list is a prefix of the other's (or they are equal). This is the
    // standard Rust definition of aliasing for borrow-check purposes.
    static bool overlaps(const Place& a, const Place& b) {
        if (a.local != b.local) return false;
        size_t n = std::min(a.projections.size(), b.projections.size());
        for (size_t i = 0; i < n; ++i)
            if (!a.projections[i].same_as(b.projections[i])) return false;
        return true;
    }

    bool operator==(const Place& o) const {
        if (local != o.local) return false;
        if (projections.size() != o.projections.size()) return false;
        for (size_t i = 0; i < projections.size(); ++i)
            if (!projections[i].same_as(o.projections[i])) return false;
        return true;
    }
};

// ---------- Types ----------
struct Type {
    enum class Kind {
        Void, Int, Bool, Float, Ref, RawPtr, OwningPtr, Struct, Array, Container, Unknown
    } kind = Kind::Unknown;
    bool is_mut = false;
    std::string name;
    std::shared_ptr<Type> pointee;
    std::shared_ptr<Type> element;
    uint64_t array_len = 0;
};

// ---------- Operands / Rvalues ----------
struct Operand {
    enum class Kind { Copy, Move, Constant } kind = Kind::Copy;
    Place place{};
    int64_t constant = 0;
    std::string type_name;

    static Operand make_copy(Place p, std::string t = "int") {
        return Operand{Kind::Copy, std::move(p), 0, std::move(t)};
    }
    static Operand make_move(Place p, std::string t = "int") {
        return Operand{Kind::Move, std::move(p), 0, std::move(t)};
    }
    static Operand make_const(int64_t v, std::string t = "int") {
        return Operand{Kind::Constant, {}, v, std::move(t)};
    }
};

enum class BinOp { Add, Sub, Mul, Div, Mod, Eq, Ne, Lt, Le, Gt, Ge, Unknown };
enum class UnOp  { Neg, Not };

struct Aggregate {
    enum class Kind { Struct, Array } kind = Kind::Struct;
    std::string struct_name;
    std::vector<Operand> elements;
};

struct Rvalue {
    enum class Kind { Use, BinaryOp, UnaryOp, Ref, Cast, Aggregate } kind = Kind::Use;

    std::optional<Operand> operand;
    std::optional<BinOp> binop;
    std::optional<UnOp>  unop;
    std::optional<Operand> lhs, rhs;
    std::optional<Place> ref_place;
    std::optional<bool>  ref_mut;
    std::string cast_type;
    std::optional<Aggregate> aggregate;

    static Rvalue use(Operand op) {
        Rvalue r; r.kind = Kind::Use; r.operand = std::move(op); return r;
    }
    static Rvalue binary(BinOp op, Operand l, Operand r_) {
        Rvalue r; r.kind = Kind::BinaryOp; r.binop = op;
        r.lhs = std::move(l); r.rhs = std::move(r_); return r;
    }
    static Rvalue unary(UnOp op, Operand v) {
        Rvalue r; r.kind = Kind::UnaryOp; r.unop = op; r.operand = std::move(v); return r;
    }
    static Rvalue ref(Place p, bool is_mut) {
        Rvalue r; r.kind = Kind::Ref; r.ref_place = std::move(p); r.ref_mut = is_mut; return r;
    }
    static Rvalue cast(Operand op, std::string type) {
        Rvalue r; r.kind = Kind::Cast; r.operand = std::move(op); r.cast_type = std::move(type); return r;
    }
    static Rvalue make_aggregate(Aggregate a) {
        Rvalue r; r.kind = Kind::Aggregate; r.aggregate = std::move(a); return r;
    }
};

// ---------- Statements ----------
struct Statement {
    enum class Kind { StorageLive, StorageDead, Assign, ReserveBorrow, Nop } kind = Kind::StorageLive;
    LocalId local = 0;
    std::optional<Place> place;
    std::optional<Rvalue> rvalue;
    bool reserve_mut = false;

    static Statement storage_live(LocalId l) {
        Statement s; s.kind = Kind::StorageLive; s.local = l; return s;
    }
    static Statement storage_dead(LocalId l) {
        Statement s; s.kind = Kind::StorageDead; s.local = l; return s;
    }
    static Statement assign(Place p, Rvalue r) {
        Statement s; s.kind = Kind::Assign;
        s.place = std::move(p); s.rvalue = std::move(r); return s;
    }
    static Statement reserve_borrow(Place p, bool is_mut) {
        Statement s; s.kind = Kind::ReserveBorrow; s.place = std::move(p); s.reserve_mut = is_mut; return s;
    }
    static Statement nop() { Statement s; s.kind = Kind::Nop; return s; }
};

// ---------- Terminators ----------
struct SwitchTarget { int64_t value = 0; BlockId target = 0; };

struct Terminator {
    enum class Kind { Goto, SwitchInt, Return, Call, Unreachable, Drop, Throw } kind = Kind::Goto;

    BlockId target = 0;
    std::optional<Operand> switch_on;
    std::vector<SwitchTarget> switch_targets;
    BlockId switch_default = 0;
    std::optional<Operand> return_value;

    std::string call_callee;
    std::string call_summary_key;
    std::vector<Operand> call_args;
    std::optional<Place> call_destination;
    std::optional<Place> call_receiver;
    bool call_receiver_is_mut = false;
    bool call_is_virtual = false;
    bool call_is_constructor = false;
    bool call_is_destructor = false;

    std::optional<Place> drop_place;
    std::optional<Operand> thrown_value;
    std::optional<Origin> receiver_reservation;

    static Terminator goto_(BlockId t) {
        Terminator x; x.kind = Kind::Goto; x.target = t; return x;
    }
    static Terminator ret(std::optional<Operand> v = std::nullopt) {
        Terminator x; x.kind = Kind::Return; x.return_value = std::move(v); return x;
    }
    static Terminator unreachable() { Terminator x; x.kind = Kind::Unreachable; return x; }
    static Terminator drop(Place p, BlockId t) {
        Terminator x; x.kind = Kind::Drop; x.drop_place = std::move(p); x.target = t; return x;
    }
    static Terminator throw_(std::optional<Operand> value, BlockId handler = INVALID_BLOCK) {
        Terminator x; x.kind = Kind::Throw; x.thrown_value = std::move(value); x.target = handler; return x;
    }
};

// ---------- Body ----------
struct BasicBlockData {
    std::vector<Statement> statements;
    Terminator terminator;
    bool terminated = false;
};

struct LocalDecl {
    std::string name;
    std::string type_name;
    Type type;
    bool is_arg = false;
    bool is_temp = false;
    bool is_mut = true;
    bool is_this = false;
    bool needs_drop = false;
    std::optional<Origin> origin;
};

struct Body {
    std::string name;
    std::string summary_key;
    std::string return_type;
    std::vector<LocalDecl> locals;
    std::vector<BasicBlockData> blocks;
    BlockId start_block = 0;
};

} // namespace mir
