#include "mir_builder.hpp"
#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/Expr.h>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/Stmt.h>
#include <clang/Basic/SourceManager.h>
#include <clang/Index/USRGeneration.h>
#include <llvm/Support/Casting.h>
#include <llvm/ADT/SmallString.h>

using namespace clang;

namespace mir {

static std::string summary_key_for(const Decl* decl) {
    if (!decl) return {};
    llvm::SmallString<128> usr;
    if (const auto* named = llvm::dyn_cast<NamedDecl>(decl)) {
        if (!index::generateUSRForDecl(named->getCanonicalDecl(), usr)) return std::string(usr.str());
        return named->getQualifiedNameAsString();
    }
    return {};
}

void MIRBuilder::mark_unsupported(SourceLocation location, std::string message) {
    unsupported_errors.push_back({location, std::move(message)});
}

bool MIRBuilder::VisitCXXNewExpr(CXXNewExpr* e) {
    mark_unsupported(e->getBeginLoc(), "manual allocation with 'new' is unsupported");
    return true;
}
bool MIRBuilder::VisitCXXDeleteExpr(CXXDeleteExpr* e) {
    mark_unsupported(e->getBeginLoc(), "manual deallocation with 'delete' is unsupported");
    return true;
}

// ---------- types ----------
std::string MIRBuilder::type_str(QualType qt) { return qt.getAsString(); }

Type MIRBuilder::build_type(QualType qt) {
    Type t;
    if (qt.isNull()) return t;
    if (qt->isVoidType())    { t.kind = Type::Kind::Void; return t; }
    if (qt->isBooleanType()) { t.kind = Type::Kind::Bool; return t; }
    if (qt->isIntegerType()) { t.kind = Type::Kind::Int; return t; }
    if (qt->isFloatingType()){ t.kind = Type::Kind::Float; return t; }
    if (qt->isReferenceType()) {
        t.kind = Type::Kind::Ref;
        t.is_mut = !qt->getPointeeType().isConstQualified();
        t.pointee = std::make_shared<Type>(build_type(qt->getPointeeType()));
        return t;
    }
    if (qt->isPointerType()) {
        t.kind = Type::Kind::RawPtr;
        t.pointee = std::make_shared<Type>(build_type(qt->getPointeeType()));
        return t;
    }
    if (qt->isArrayType()) {
        t.kind = Type::Kind::Array;
        t.element = std::make_shared<Type>(build_type(qt->getAsArrayTypeUnsafe()->getElementType()));
        return t;
    }
    if (const auto* rd = qt->getAsRecordDecl()) {
        t.kind = Type::Kind::Struct;
        t.name = rd->getNameAsString();
        return t;
    }
    return t;
}

BinOp MIRBuilder::map_binop(BinaryOperator::Opcode op) {
    switch (op) {
        case BO_Add: return BinOp::Add;
        case BO_Sub: return BinOp::Sub;
        case BO_Mul: return BinOp::Mul;
        case BO_Div: return BinOp::Div;
        case BO_Rem: return BinOp::Mod;
        case BO_EQ:  return BinOp::Eq;
        case BO_NE:  return BinOp::Ne;
        case BO_LT:  return BinOp::Lt;
        case BO_LE:  return BinOp::Le;
        case BO_GT:  return BinOp::Gt;
        case BO_GE:  return BinOp::Ge;
        default:     return BinOp::Unknown;
    }
}

// ---------- emit helpers ----------
LocalId MIRBuilder::declare_local(const std::string& name, const std::string& type,
                                  bool is_arg, bool is_temp, bool is_mut, bool is_this) {
    LocalId id = static_cast<LocalId>(body_->locals.size());
    LocalDecl ld;
    ld.name = name; ld.type_name = type;
    ld.is_arg = is_arg; ld.is_temp = is_temp;
    ld.is_mut = is_mut; ld.is_this = is_this;
    body_->locals.push_back(ld);
    if (!is_temp && !scopes_.empty() && !is_this)
        scopes_.back().locals.push_back(id);
    return id;
}

BlockId MIRBuilder::new_block() {
    BlockId id = static_cast<BlockId>(body_->blocks.size());
    body_->blocks.emplace_back();
    return id;
}

void MIRBuilder::emit(Statement s) {
    if (is_terminated()) return;
    body_->blocks[current_block_].statements.push_back(std::move(s));
}

void MIRBuilder::emit_assign(Place dest, Rvalue rv) {
    if (is_terminated()) return;

    LocalId dest_local = dest.local;
    BlockId blk = current_block_;
    uint32_t idx = static_cast<uint32_t>(body_->blocks[blk].statements.size());

    std::optional<Origin> new_origin;
    bool destination_can_carry_origin = dest_local < body_->locals.size()
        && (body_->locals[dest_local].type.kind == Type::Kind::Ref
            || body_->locals[dest_local].type.kind == Type::Kind::RawPtr
            || body_->locals[dest_local].type.kind == Type::Kind::Struct
            || body_->locals[dest_local].type.kind == Type::Kind::Container
            || body_->locals[dest_local].type.kind == Type::Kind::Unknown);
    if (rv.kind == Rvalue::Kind::Ref) {
        new_origin = Origin{blk, idx};
    } else if (destination_can_carry_origin && rv.kind == Rvalue::Kind::Use && rv.operand
               && rv.operand->kind != Operand::Kind::Constant) {
        LocalId src = rv.operand->place.local;
        if (src < body_->locals.size()) {
            new_origin = body_->locals[src].origin;
            if (rv.operand->kind == Operand::Kind::Move)
                body_->locals[src].origin.reset();
        }
    } else if (destination_can_carry_origin && rv.kind == Rvalue::Kind::Aggregate && rv.aggregate) {
        for (const auto& el : rv.aggregate->elements) {
            if (el.kind == Operand::Kind::Constant || el.place.local >= body_->locals.size()) continue;
            new_origin = body_->locals[el.place.local].origin;
            if (new_origin) break;
        }
    } else if (destination_can_carry_origin && rv.kind == Rvalue::Kind::Cast && rv.operand
               && rv.operand->kind != Operand::Kind::Constant
               && rv.operand->place.local < body_->locals.size()) {
        new_origin = body_->locals[rv.operand->place.local].origin;
    }
    if (dest_local < body_->locals.size())
        body_->locals[dest_local].origin = new_origin;

    emit(Statement::assign(dest, std::move(rv)));
}

void MIRBuilder::terminate(Terminator t) {
    auto& bb = body_->blocks[current_block_];
    if (bb.terminated) return;
    bb.terminator = std::move(t);
    bb.terminated = true;
}
bool MIRBuilder::is_terminated() const {
    return body_->blocks[current_block_].terminated;
}
void MIRBuilder::push_scope() { scopes_.emplace_back(); }
void MIRBuilder::pop_scope() {
    if (scopes_.empty()) return;
    auto& scope = scopes_.back();
    for (auto it = scope.locals.rbegin(); it != scope.locals.rend(); ++it) {
        if (body_->locals[*it].needs_drop && !is_terminated()) {
            BlockId next = new_block();
            terminate(Terminator::drop(Place{*it}, next));
            current_block_ = next;
        }
        if (!body_->locals[*it].is_temp) emit(Statement::storage_dead(*it));
    }
    scopes_.pop_back();
}

// ---------- function-level ----------
bool MIRBuilder::VisitFunctionDecl(FunctionDecl* fd) {
    if (!fd->hasBody()) return true;
    if (ctx_.getSourceManager().isInSystemHeader(fd->getLocation())) return true;

    Body body;
    body.name = fd->getQualifiedNameAsString();
    body.summary_key = summary_key_for(fd);
    body.return_type = type_str(fd->getReturnType());
    body_ = &body;
    var_to_local_.clear();
    scopes_.clear();
    loop_stack_.clear();
    exception_targets_.clear();
    switch_case_blocks_.clear();
    this_local_ = INVALID_BLOCK;

    body.start_block = 0;
    body.blocks.emplace_back();
    current_block_ = 0;

    push_scope();

    if (auto* md = llvm::dyn_cast<CXXMethodDecl>(fd)) {
        const auto* parent = md->getParent();
        bool is_const = md->isConst();
        std::string tname = parent->getNameAsString() + "*";
        this_local_ = declare_local("this", tname, true, false,
                                    /*is_mut=*/!is_const, /*is_this=*/true);
        body.locals[this_local_].type.kind = Type::Kind::RawPtr;
        emit(Statement::storage_live(this_local_));
    }

    for (auto* param : fd->parameters()) {
        LocalId lid = declare_local(param->getNameAsString(),
                                    type_str(param->getType()), true, false);
        body.locals[lid].type = build_type(param->getType());
        if (const auto* rd = param->getType()->getAsCXXRecordDecl())
            body.locals[lid].needs_drop = rd->hasNonTrivialDestructor();
        var_to_local_[param] = lid;
        emit(Statement::storage_live(lid));
    }

    lower_stmt(fd->getBody());
    pop_scope();
    if (!is_terminated()) terminate(Terminator::ret());

    bodies.push_back(std::move(body));
    body_ = nullptr;
    return true;
}

// ---------- statements ----------
void MIRBuilder::lower_decl_stmt(DeclStmt* ds) {
    for (auto* d : ds->decls()) {
        if (auto* vd = llvm::dyn_cast<VarDecl>(d)) {
            bool is_mut = !vd->getType().isConstQualified();
            LocalId lid = declare_local(vd->getNameAsString(), type_str(vd->getType()),
                                        false, false, is_mut);
            body_->locals[lid].type = build_type(vd->getType());
            if (const auto* rd = vd->getType()->getAsCXXRecordDecl())
                body_->locals[lid].needs_drop = rd->hasNonTrivialDestructor();
            var_to_local_[vd] = lid;
            emit(Statement::storage_live(lid));
            if (vd->hasInit()) {
                if (vd->getType()->isReferenceType()) {
                    Expr* init = vd->getInit()->IgnoreParenImpCasts();
                    Place referent = lower_expr(init);
                    bool mut = !vd->getType().getNonReferenceType().isConstQualified();
                    emit_assign(Place{lid}, Rvalue::ref(referent, mut));
                } else {
                    Operand val = lower_operand(vd->getInit());
                    emit_assign(Place{lid}, Rvalue::use(val));
                }
            }
        }
    }
}

void MIRBuilder::lower_return_stmt(ReturnStmt* rs) {
    std::optional<Operand> ret_val;
    if (auto* e = rs->getRetValue()) ret_val = lower_operand(e);
    std::vector<LocalId> drops;
    for (auto si = scopes_.rbegin(); si != scopes_.rend(); ++si)
        for (auto li = si->locals.rbegin(); li != si->locals.rend(); ++li)
            if (body_->locals[*li].needs_drop) drops.push_back(*li);
    if (drops.empty()) { terminate(Terminator::ret(std::move(ret_val))); return; }
    BlockId tail = new_block(), saved = current_block_;
    current_block_ = tail; terminate(Terminator::ret(std::move(ret_val)));
    for (auto it = drops.rbegin(); it != drops.rend(); ++it) {
        BlockId next = tail, drop_bb = new_block();
        current_block_ = drop_bb; terminate(Terminator::drop(Place{*it}, next)); tail = drop_bb;
    }
    current_block_ = saved; terminate(Terminator::goto_(tail));
}

void MIRBuilder::lower_if_stmt(IfStmt* is) {
    BlockId then_bb = new_block(), else_bb = new_block(), join_bb = new_block();
    Place cond = lower_expr(is->getCond());
    Terminator t;
    t.kind = Terminator::Kind::SwitchInt;
    t.switch_on = Operand::make_copy(cond, "bool");
    t.switch_targets.push_back({1, then_bb});
    t.switch_default = else_bb;
    terminate(t);

    current_block_ = then_bb;
    lower_stmt(is->getThen());
    if (!is_terminated()) terminate(Terminator::goto_(join_bb));

    current_block_ = else_bb;
    if (is->getElse()) lower_stmt(is->getElse());
    if (!is_terminated()) terminate(Terminator::goto_(join_bb));

    current_block_ = join_bb;
}

void MIRBuilder::lower_while_stmt(WhileStmt* ws) {
    BlockId header = new_block(), body_bb = new_block(), exit_bb = new_block();
    terminate(Terminator::goto_(header));

    current_block_ = header;
    Place cond = lower_expr(ws->getCond());
    Terminator t;
    t.kind = Terminator::Kind::SwitchInt;
    t.switch_on = Operand::make_copy(cond, "bool");
    t.switch_targets.push_back({1, body_bb});
    t.switch_default = exit_bb;
    terminate(t);

    loop_stack_.push_back({header, exit_bb});
    current_block_ = body_bb;
    lower_stmt(ws->getBody());
    if (!is_terminated()) terminate(Terminator::goto_(header));
    loop_stack_.pop_back();
    current_block_ = exit_bb;
}

void MIRBuilder::lower_for_stmt(ForStmt* fs) {
    push_scope();
    if (fs->getInit()) lower_stmt(fs->getInit());

    BlockId header = new_block(), body_bb = new_block();
    BlockId inc_bb = new_block(), exit_bb = new_block();
    terminate(Terminator::goto_(header));

    current_block_ = header;
    if (fs->getCond()) {
        Place cond = lower_expr(fs->getCond());
        Terminator t;
        t.kind = Terminator::Kind::SwitchInt;
        t.switch_on = Operand::make_copy(cond, "bool");
        t.switch_targets.push_back({1, body_bb});
        t.switch_default = exit_bb;
        terminate(t);
    } else {
        terminate(Terminator::goto_(body_bb));
    }

    loop_stack_.push_back({inc_bb, exit_bb});
    current_block_ = body_bb;
    lower_stmt(fs->getBody());
    if (!is_terminated()) terminate(Terminator::goto_(inc_bb));
    loop_stack_.pop_back();

    current_block_ = inc_bb;
    if (fs->getInc()) lower_stmt(fs->getInc());
    if (!is_terminated()) terminate(Terminator::goto_(header));

    current_block_ = exit_bb;
    pop_scope();
}

void MIRBuilder::lower_do_stmt(DoStmt* ds) {
    BlockId body_bb = new_block(), cond_bb = new_block(), exit_bb = new_block();
    terminate(Terminator::goto_(body_bb));

    loop_stack_.push_back({cond_bb, exit_bb});
    current_block_ = body_bb;
    lower_stmt(ds->getBody());
    if (!is_terminated()) terminate(Terminator::goto_(cond_bb));
    loop_stack_.pop_back();

    current_block_ = cond_bb;
    Place cond = lower_expr(ds->getCond());
    Terminator t;
    t.kind = Terminator::Kind::SwitchInt;
    t.switch_on = Operand::make_copy(cond, "bool");
    t.switch_targets.push_back({1, body_bb});
    t.switch_default = exit_bb;
    terminate(t);
    current_block_ = exit_bb;
}

void MIRBuilder::lower_range_for_stmt(CXXForRangeStmt* fs) {
    push_scope();
    lower_stmt(fs->getRangeStmt());
    lower_stmt(fs->getBeginStmt());
    lower_stmt(fs->getEndStmt());
    BlockId header = new_block(), body_bb = new_block(), inc_bb = new_block(), exit_bb = new_block();
    terminate(Terminator::goto_(header));
    current_block_ = header;
    (void)lower_expr_to_local(fs->getCond());
    Place cond = lower_expr(fs->getCond());
    Terminator branch;
    branch.kind = Terminator::Kind::SwitchInt;
    branch.switch_on = Operand::make_copy(cond, "bool");
    branch.switch_targets.push_back({1, body_bb}); branch.switch_default = exit_bb;
    terminate(std::move(branch));
    loop_stack_.push_back({inc_bb, exit_bb});
    current_block_ = body_bb;
    lower_stmt(fs->getLoopVarStmt());
    lower_stmt(fs->getBody());
    if (!is_terminated()) terminate(Terminator::goto_(inc_bb));
    current_block_ = inc_bb;
    lower_stmt(fs->getInc());
    if (!is_terminated()) terminate(Terminator::goto_(header));
    loop_stack_.pop_back();
    current_block_ = exit_bb;
    pop_scope();
}

void MIRBuilder::lower_try_stmt(CXXTryStmt* ts) {
    BlockId join = new_block();
    std::vector<BlockId> catches;
    for (unsigned i = 0; i < ts->getNumHandlers(); ++i) catches.push_back(new_block());
    BlockId dispatch = catches.empty() ? INVALID_BLOCK : catches.front();
    exception_targets_.push_back(dispatch);
    lower_stmt(ts->getTryBlock());
    exception_targets_.pop_back();
    if (!is_terminated()) terminate(Terminator::goto_(join));
    for (unsigned i = 0; i < ts->getNumHandlers(); ++i) {
        auto* handler = ts->getHandler(i);
        if (auto* exception = handler->getExceptionDecl()) {
            mark_unsupported(exception->getLocation(),
                "catch parameter values are not represented in MIR");
            LocalId lid = declare_local(exception->getNameAsString(),
                type_str(exception->getType()), false, false);
            var_to_local_[exception] = lid;
            emit(Statement::storage_live(lid));
        }
        current_block_ = catches[i];
        lower_stmt(handler->getHandlerBlock());
        if (!is_terminated()) terminate(Terminator::goto_(join));
    }
    current_block_ = join;
}

void MIRBuilder::lower_switch_stmt(SwitchStmt* ss) {
    Place value = lower_expr(ss->getCond());
    BlockId exit = new_block();
    std::vector<std::pair<const SwitchCase*, BlockId>> cases;
    for (SwitchCase* sc = ss->getSwitchCaseList(); sc; sc = sc->getNextSwitchCase())
        cases.push_back({sc, new_block()});
    BlockId default_block = exit;
    Terminator sw; sw.kind = Terminator::Kind::SwitchInt; sw.switch_on = Operand::make_copy(value, type_str(ss->getCond()->getType()));
    for (auto [sc, bb] : cases) {
        switch_case_blocks_[sc] = bb;
        if (auto* cs = llvm::dyn_cast<CaseStmt>(sc)) {
            Expr::EvalResult result;
            if (cs->getLHS()->EvaluateAsInt(result, ctx_))
                sw.switch_targets.push_back({result.Val.getInt().getSExtValue(), bb});
        } else if (llvm::isa<DefaultStmt>(sc)) default_block = bb;
    }
    sw.switch_default = default_block;
    terminate(std::move(sw));
    std::reverse(cases.begin(), cases.end());
    loop_stack_.push_back({exit, exit});
    for (size_t i = 0; i < cases.size(); ++i) {
        current_block_ = cases[i].second;
        lower_stmt(const_cast<Stmt*>(cases[i].first->getSubStmt()));
        if (!is_terminated()) terminate(Terminator::goto_(i + 1 < cases.size() ? cases[i + 1].second : exit));
    }
    loop_stack_.pop_back(); current_block_ = exit;
}

void MIRBuilder::lower_break_stmt(BreakStmt*) {
    if (loop_stack_.empty()) return;
    terminate(Terminator::goto_(loop_stack_.back().break_target));
}
void MIRBuilder::lower_continue_stmt(ContinueStmt*) {
    if (loop_stack_.empty()) return;
    terminate(Terminator::goto_(loop_stack_.back().continue_target));
}

void MIRBuilder::lower_assign_op(BinaryOperator* bo) {
    Place lhs = lower_expr(bo->getLHS());
    Operand rhs = lower_operand(bo->getRHS());
    if (bo->getOpcode() == BO_Assign) {
        emit_assign(lhs, Rvalue::use(rhs));
        return;
    }
    BinOp op = BinOp::Unknown;
    switch (bo->getOpcode()) {
        case BO_AddAssign: op = BinOp::Add; break;
        case BO_SubAssign: op = BinOp::Sub; break;
        case BO_MulAssign: op = BinOp::Mul; break;
        case BO_DivAssign: op = BinOp::Div; break;
        case BO_RemAssign: op = BinOp::Mod; break;
        default: break;
    }
    if (op == BinOp::Unknown) {
        mark_unsupported(bo->getOperatorLoc(), "compound assignment is not represented in MIR");
        return;
    }
    Operand lhs_copy = Operand::make_copy(lhs);
    emit_assign(lhs, Rvalue::binary(op, lhs_copy, rhs));
}

void MIRBuilder::lower_stmt(Stmt* s) {
    if (is_terminated()) return;

    if (llvm::isa<NullStmt>(s)) return;
    if (auto* cs = llvm::dyn_cast<CompoundStmt>(s)) {
        push_scope();
        for (auto* child : cs->body()) lower_stmt(child);
        pop_scope();
    } else if (auto* ds = llvm::dyn_cast<DeclStmt>(s))     lower_decl_stmt(ds);
    else if (auto* rs = llvm::dyn_cast<ReturnStmt>(s))     lower_return_stmt(rs);
    else if (auto* is = llvm::dyn_cast<IfStmt>(s))         lower_if_stmt(is);
    else if (auto* ws = llvm::dyn_cast<WhileStmt>(s))      lower_while_stmt(ws);
    else if (auto* fs = llvm::dyn_cast<ForStmt>(s))        lower_for_stmt(fs);
    else if (auto* dos = llvm::dyn_cast<DoStmt>(s))        lower_do_stmt(dos);
    else if (auto* range = llvm::dyn_cast<CXXForRangeStmt>(s)) lower_range_for_stmt(range);
    else if (auto* sw = llvm::dyn_cast<SwitchStmt>(s))     lower_switch_stmt(sw);
    else if (auto* ts = llvm::dyn_cast<CXXTryStmt>(s))     lower_try_stmt(ts);
    else if (auto* th = llvm::dyn_cast<CXXThrowExpr>(s)) {
        std::optional<Operand> val;
        if (th->getSubExpr()) val = lower_operand(th->getSubExpr());
        terminate(Terminator::throw_(std::move(val), exception_targets_.empty()
            ? INVALID_BLOCK : exception_targets_.back()));
    }
    else if (auto* bs = llvm::dyn_cast<BreakStmt>(s))      lower_break_stmt(bs);
    else if (auto* cs = llvm::dyn_cast<ContinueStmt>(s))   lower_continue_stmt(cs);
    else if (auto* cs = llvm::dyn_cast<CaseStmt>(s)) {
        auto it = switch_case_blocks_.find(cs);
        if (it != switch_case_blocks_.end()) {
            if (!is_terminated() && current_block_ != it->second) terminate(Terminator::goto_(it->second));
            current_block_ = it->second;
        }
        lower_stmt(cs->getSubStmt());
    }
    else if (auto* ds = llvm::dyn_cast<DefaultStmt>(s)) {
        auto it = switch_case_blocks_.find(ds);
        if (it != switch_case_blocks_.end()) {
            if (!is_terminated() && current_block_ != it->second) terminate(Terminator::goto_(it->second));
            current_block_ = it->second;
        }
        lower_stmt(ds->getSubStmt());
    }
    else if (auto* bo = llvm::dyn_cast<BinaryOperator>(s)) {
        switch (bo->getOpcode()) {
            case BO_Assign:
            case BO_AddAssign:
            case BO_SubAssign:
            case BO_MulAssign:
            case BO_DivAssign:
            case BO_RemAssign:
                lower_assign_op(bo);
                break;
            default:
                (void)lower_expr_to_local(bo);
                break;
        }
    }
    else if (auto* es = llvm::dyn_cast<Expr>(s))           (void)lower_expr_to_local(es);
    else mark_unsupported(s->getBeginLoc(), "statement kind is not represented in MIR");
}

// ---------- expressions ----------
Place MIRBuilder::lower_expr(Expr* e) {
    e = e->IgnoreParenImpCasts();

    if (auto* dre = llvm::dyn_cast<DeclRefExpr>(e)) {
        if (auto* vd = llvm::dyn_cast<VarDecl>(dre->getDecl())) {
            auto it = var_to_local_.find(vd);
            if (it != var_to_local_.end()) {
                Place p{it->second};
                if (vd->getType()->isReferenceType()) { Projection d; d.kind = ProjectionKind::Deref; p.projections.push_back(d); }
                return p;
            }
        }
    }

    if (llvm::isa<CXXThisExpr>(e)) {
        if (this_local_ != INVALID_BLOCK) return Place{this_local_};
        mark_unsupported(e->getExprLoc(), "'this' is not available in this MIR body");
        return Place{0};
    }

    if (auto* me = llvm::dyn_cast<MemberExpr>(e)) {
        if (auto* fd = llvm::dyn_cast<FieldDecl>(me->getMemberDecl())) {
            Place base;
            if (me->isImplicitAccess() || !me->getBase()) {
                base = Place{this_local_};
            } else {
                base = lower_expr(me->getBase());
            }
            if (me->isArrow()) {
                Projection d;
                d.kind = ProjectionKind::Deref;
                base.projections.push_back(d);
            }
            Projection p;
            p.kind = ProjectionKind::Field;
            p.field_idx = static_cast<uint32_t>(fd->getFieldIndex());
            base.projections.push_back(p);
            return base;
        }
    }

    if (auto* ase = llvm::dyn_cast<ArraySubscriptExpr>(e)) {
        Place base = lower_expr(ase->getBase());
        LocalId idx = lower_expr_to_local(ase->getIdx());
        Projection p;
        p.kind = ProjectionKind::Index;
        p.index_local = idx;
        base.projections.push_back(p);
        return base;
    }

    if (auto* uo = llvm::dyn_cast<UnaryOperator>(e)) {
        if (uo->getOpcode() == UO_Deref) {
            Place base = lower_expr(uo->getSubExpr());
            Projection p;
            p.kind = ProjectionKind::Deref;
            base.projections.push_back(p);
            return base;
        }
    }

    LocalId tmp = lower_rvalue_to_temp(e);
    return Place{tmp};
}

LocalId MIRBuilder::lower_expr_to_local(Expr* e) { return lower_expr(e).local; }

Operand MIRBuilder::lower_operand(Expr* e) {
    // std::move is an explicit ownership transfer. Preserve it before
    // stripping implicit casts and parentheses.
    Expr* original = e;
    if (auto* call = llvm::dyn_cast<CallExpr>(original->IgnoreParenImpCasts())) {
        if (auto* ref = llvm::dyn_cast<DeclRefExpr>(call->getCallee()->IgnoreParenImpCasts())) {
            if (ref->getDecl()->getName() == "move" && call->getNumArgs() == 1)
                return Operand::make_move(lower_expr(call->getArg(0)), type_str(e->getType()));
        }
    }
    e = e->IgnoreParenImpCasts();
    if (auto* il = llvm::dyn_cast<IntegerLiteral>(e))
        return Operand::make_const(il->getValue().getSExtValue(), type_str(e->getType()));
    if (auto* bl = llvm::dyn_cast<CXXBoolLiteralExpr>(e))
        return Operand::make_const(bl->getValue() ? 1 : 0, "bool");
    Place p = lower_expr(e);
    if (e->getType()->isRecordType())
        return Operand::make_move(p, type_str(e->getType()));
    return Operand::make_copy(p, type_str(e->getType()));
}

LocalId MIRBuilder::lower_binary_op(BinaryOperator* bo) {
    Operand l = lower_operand(bo->getLHS());
    Operand r = lower_operand(bo->getRHS());
    LocalId tmp = declare_local("", type_str(bo->getType()), false, true);
    emit(Statement::storage_live(tmp));
    emit_assign(Place{tmp}, Rvalue::binary(map_binop(bo->getOpcode()), l, r));
    return tmp;
}

LocalId MIRBuilder::lower_logical_and(BinaryOperator* bo) {
    LocalId result = declare_local("", "bool", false, true);
    emit(Statement::storage_live(result));
    emit_assign(Place{result}, Rvalue::use(Operand::make_const(0, "bool")));

    BlockId rhs_bb = new_block(), short_bb = new_block(), join_bb = new_block();
    Place lhs = lower_expr(bo->getLHS());
    Terminator t;
    t.kind = Terminator::Kind::SwitchInt;
    t.switch_on = Operand::make_copy(lhs, "bool");
    t.switch_targets.push_back({1, rhs_bb});
    t.switch_default = short_bb;
    terminate(t);

    current_block_ = short_bb;
    terminate(Terminator::goto_(join_bb));

    current_block_ = rhs_bb;
    Operand rhs = lower_operand(bo->getRHS());
    emit_assign(Place{result}, Rvalue::use(rhs));
    terminate(Terminator::goto_(join_bb));

    current_block_ = join_bb;
    return result;
}

LocalId MIRBuilder::lower_logical_or(BinaryOperator* bo) {
    LocalId result = declare_local("", "bool", false, true);
    emit(Statement::storage_live(result));
    emit_assign(Place{result}, Rvalue::use(Operand::make_const(1, "bool")));

    BlockId rhs_bb = new_block(), short_bb = new_block(), join_bb = new_block();
    Place lhs = lower_expr(bo->getLHS());
    Terminator t;
    t.kind = Terminator::Kind::SwitchInt;
    t.switch_on = Operand::make_copy(lhs, "bool");
    t.switch_targets.push_back({1, short_bb});
    t.switch_default = rhs_bb;
    terminate(t);

    current_block_ = short_bb;
    terminate(Terminator::goto_(join_bb));

    current_block_ = rhs_bb;
    Operand rhs = lower_operand(bo->getRHS());
    emit_assign(Place{result}, Rvalue::use(rhs));
    terminate(Terminator::goto_(join_bb));

    current_block_ = join_bb;
    return result;
}

LocalId MIRBuilder::lower_unary_op(UnaryOperator* uo) {
    switch (uo->getOpcode()) {
        case UO_PreInc: case UO_PostInc: case UO_PreDec: case UO_PostDec: {
            Place p = lower_expr(uo->getSubExpr());
            Operand old = Operand::make_copy(p, type_str(uo->getType()));
            Operand one = Operand::make_const(1, type_str(uo->getType()));
            BinOp op = (uo->getOpcode() == UO_PreInc || uo->getOpcode() == UO_PostInc) ? BinOp::Add : BinOp::Sub;
            emit_assign(p, Rvalue::binary(op, old, one));
            return p.local;
        }
        case UO_Minus:
        case UO_LNot: {
            Operand v = lower_operand(uo->getSubExpr());
            LocalId tmp = declare_local("", type_str(uo->getType()), false, true);
            emit(Statement::storage_live(tmp));
            emit_assign(Place{tmp},
                 Rvalue::unary(uo->getOpcode() == UO_Minus ? UnOp::Neg : UnOp::Not, v));
            return tmp;
        }
        case UO_AddrOf: {
            Place p = lower_expr(uo->getSubExpr());
            LocalId tmp = declare_local("", type_str(uo->getType()), false, true);
            emit(Statement::storage_live(tmp));
            bool is_mut = !uo->getType()->getPointeeType().isConstQualified();
            emit_assign(Place{tmp}, Rvalue::ref(p, is_mut));
            return tmp;
        }
        case UO_Deref: {
            Place p = lower_expr(uo->getSubExpr());
            Projection proj;
            proj.kind = ProjectionKind::Deref;
            p.projections.push_back(proj);
            LocalId tmp = declare_local("", type_str(uo->getType()), false, true);
            emit(Statement::storage_live(tmp));
            emit_assign(Place{tmp},
                 Rvalue::use(Operand::make_copy(p, type_str(uo->getType()))));
            return tmp;
        }
        default: {
            mark_unsupported(uo->getOperatorLoc(), "unary operator is not represented in MIR");
            LocalId tmp = declare_local("", type_str(uo->getType()), false, true);
            emit(Statement::storage_live(tmp));
            return tmp;
        }
    }
}

LocalId MIRBuilder::lower_conditional(ConditionalOperator* co) {
    LocalId result = declare_local("", type_str(co->getType()), false, true);
    emit(Statement::storage_live(result));

    BlockId then_bb = new_block(), else_bb = new_block(), join_bb = new_block();
    Place cond = lower_expr(co->getCond());
    Terminator t;
    t.kind = Terminator::Kind::SwitchInt;
    t.switch_on = Operand::make_copy(cond, "bool");
    t.switch_targets.push_back({1, then_bb});
    t.switch_default = else_bb;
    terminate(t);

    current_block_ = then_bb;
    Operand tv = lower_operand(co->getTrueExpr());
    emit_assign(Place{result}, Rvalue::use(tv));
    terminate(Terminator::goto_(join_bb));

    current_block_ = else_bb;
    Operand fv = lower_operand(co->getFalseExpr());
    emit_assign(Place{result}, Rvalue::use(fv));
    terminate(Terminator::goto_(join_bb));

    current_block_ = join_bb;
    return result;
}

LocalId MIRBuilder::lower_call(CallExpr* ce) {
    std::vector<Operand> args;
    for (auto* a : ce->arguments()) args.push_back(lower_operand(a));

    QualType ret_qt = ce->getCallReturnType(ctx_);
    LocalId dest = declare_local("", type_str(ret_qt), false, true);
    body_->locals[dest].type = build_type(ret_qt);
    emit(Statement::storage_live(dest));

    std::string callee_name;
    Expr* callee = ce->getCallee()->IgnoreParenImpCasts();
    if (auto* direct = ce->getDirectCallee()) callee_name = direct->getQualifiedNameAsString();
    else if (auto* dre = llvm::dyn_cast<DeclRefExpr>(callee)) callee_name = dre->getDecl()->getQualifiedNameAsString();
    else
        callee_name = "<indirect>";

    BlockId target = new_block();
    Terminator t;
    t.kind = Terminator::Kind::Call;
    t.call_callee = callee_name;
    t.call_summary_key = summary_key_for(ce->getDirectCallee());
    t.call_args = std::move(args);
    t.call_destination = Place{dest};
    t.target = target;
    terminate(t);
    current_block_ = target;
    return dest;
}

LocalId MIRBuilder::lower_member_call(CXXMemberCallExpr* mce) {
    const CXXMethodDecl* md = mce->getMethodDecl();

    Place receiver;
    if (mce->getImplicitObjectArgument()) {
        Expr* obj = mce->getImplicitObjectArgument()->IgnoreParenImpCasts();
        receiver = lower_expr(obj);
        // `p->method()` — Clang's implicit object argument is the pointer
        // itself, so insert the deref step that `->` implies.
        if (obj->getType()->isPointerType()) {
            Projection d;
            d.kind = ProjectionKind::Deref;
            receiver.projections.push_back(d);
        }
    } else {
        receiver = Place{this_local_};
    }

    bool receiver_is_mut = md ? !md->isConst() : true;
    std::optional<Origin> reservation;
    if (receiver_is_mut && !is_terminated()) {
        auto& statements = body_->blocks[current_block_].statements;
        reservation = Origin{current_block_, static_cast<uint32_t>(statements.size())};
        emit(Statement::reserve_borrow(receiver, true));
    }

    std::vector<Operand> args;
    for (auto* a : mce->arguments()) args.push_back(lower_operand(a));

    QualType ret_qt = mce->getCallReturnType(ctx_);
    LocalId dest = declare_local("", type_str(ret_qt), false, true);
    body_->locals[dest].type = build_type(ret_qt);
    emit(Statement::storage_live(dest));

    BlockId target = new_block();
    Terminator t;
    t.kind = Terminator::Kind::Call;
    t.call_callee = md ? md->getQualifiedNameAsString() : "<method>";
    t.call_summary_key = summary_key_for(md);
    t.call_args = std::move(args);
    t.call_destination = Place{dest};
    t.call_receiver = receiver;
    t.call_receiver_is_mut = receiver_is_mut;
    t.receiver_reservation = reservation;
    t.call_is_virtual = md ? md->isVirtual() : false;
    t.target = target;
    terminate(t);
    current_block_ = target;
    return dest;
}

LocalId MIRBuilder::lower_construct(CXXConstructExpr* cce) {
    std::vector<Operand> args;
    for (auto* a : cce->arguments()) args.push_back(lower_operand(a));

    QualType qt = cce->getType();
    LocalId dest = declare_local("", type_str(qt), false, true);
    body_->locals[dest].type = build_type(qt);
    emit(Statement::storage_live(dest));

    const CXXConstructorDecl* ctor = cce->getConstructor();
    std::string name = ctor ? ctor->getQualifiedNameAsString() : "<ctor>";

    BlockId target = new_block();
    Terminator t;
    t.kind = Terminator::Kind::Call;
    t.call_callee = name;
    t.call_summary_key = summary_key_for(ctor);
    t.call_args = std::move(args);
    t.call_destination = Place{dest};
    t.call_is_constructor = true;
    t.target = target;
    terminate(t);
    current_block_ = target;
    return dest;
}

LocalId MIRBuilder::lower_init_list(InitListExpr* ile) {
    QualType qt = ile->getType();
    std::vector<Operand> elems;
    for (auto* e : ile->inits()) elems.push_back(lower_operand(e));

    LocalId tmp = declare_local("", type_str(qt), false, true);
    emit(Statement::storage_live(tmp));

    Aggregate agg;
    agg.kind = qt->isArrayType() ? Aggregate::Kind::Array : Aggregate::Kind::Struct;
    if (agg.kind == Aggregate::Kind::Struct)
        if (const auto* rd = qt->getAsRecordDecl()) agg.struct_name = rd->getNameAsString();
    agg.elements = std::move(elems);

    emit_assign(Place{tmp}, Rvalue::make_aggregate(std::move(agg)));
    return tmp;
}

LocalId MIRBuilder::lower_rvalue_to_temp(Expr* e) {
    if (auto* cast = llvm::dyn_cast<ExplicitCastExpr>(e->IgnoreParenImpCasts())) {
        Operand src = lower_operand(cast->getSubExpr());
        LocalId tmp = declare_local("", type_str(cast->getType()), false, true);
        emit(Statement::storage_live(tmp));
        emit_assign(Place{tmp}, Rvalue::cast(std::move(src), type_str(cast->getType())));
        return tmp;
    }
    e = e->IgnoreParenImpCasts();

    if (auto* il = llvm::dyn_cast<IntegerLiteral>(e)) {
        LocalId tmp = declare_local("", type_str(e->getType()), false, true);
        emit(Statement::storage_live(tmp));
        emit_assign(Place{tmp}, Rvalue::use(Operand::make_const(
             il->getValue().getSExtValue(), type_str(e->getType()))));
        return tmp;
    }
    if (auto* bl = llvm::dyn_cast<CXXBoolLiteralExpr>(e)) {
        LocalId tmp = declare_local("", "bool", false, true);
        emit(Statement::storage_live(tmp));
        emit_assign(Place{tmp}, Rvalue::use(Operand::make_const(
             bl->getValue() ? 1 : 0, "bool")));
        return tmp;
    }
    if (llvm::isa<GNUNullExpr>(e) || llvm::isa<CXXNullPtrLiteralExpr>(e)) {
        LocalId tmp = declare_local("", type_str(e->getType()), false, true);
        emit(Statement::storage_live(tmp));
        emit_assign(Place{tmp}, Rvalue::use(Operand::make_const(0, type_str(e->getType()))));
        return tmp;
    }

    if (auto* bo = llvm::dyn_cast<BinaryOperator>(e)) {
        if (bo->getOpcode() == BO_LAnd) return lower_logical_and(bo);
        if (bo->getOpcode() == BO_LOr)  return lower_logical_or(bo);
        if (bo->getOpcode() == BO_Assign) {
            Place lhs = lower_expr(bo->getLHS());
            Operand rhs = lower_operand(bo->getRHS());
            emit_assign(lhs, Rvalue::use(rhs));
            return lhs.local;
        }
        if (map_binop(bo->getOpcode()) == BinOp::Unknown) {
            mark_unsupported(bo->getOperatorLoc(), "binary operator is not represented in MIR");
            LocalId tmp = declare_local("", type_str(e->getType()), false, true);
            emit(Statement::storage_live(tmp));
            return tmp;
        }
        return lower_binary_op(bo);
    }

    if (auto* uo = llvm::dyn_cast<UnaryOperator>(e))       return lower_unary_op(uo);
    if (auto* co = llvm::dyn_cast<ConditionalOperator>(e)) return lower_conditional(co);

    if (auto* mce = llvm::dyn_cast<CXXMemberCallExpr>(e)) return lower_member_call(mce);
    if (auto* ce = llvm::dyn_cast<CallExpr>(e))           return lower_call(ce);
    if (auto* cce = llvm::dyn_cast<CXXConstructExpr>(e))  return lower_construct(cce);
    if (auto* ile = llvm::dyn_cast<InitListExpr>(e))      return lower_init_list(ile);

    if (auto* ne = llvm::dyn_cast<CXXNewExpr>(e)) {
        std::vector<Operand> args;
        if (ne->getInitializer())
            if (auto* init = llvm::dyn_cast<InitListExpr>(ne->getInitializer()))
                for (Expr* a : init->inits()) args.push_back(lower_operand(a));
            else args.push_back(lower_operand(ne->getInitializer()));
        LocalId dest = declare_local("", type_str(e->getType()), false, true);
        emit(Statement::storage_live(dest));
        BlockId target = new_block(); Terminator t;
        t.kind = Terminator::Kind::Call; t.call_callee = "operator new";
        t.call_args = std::move(args); t.call_destination = Place{dest}; t.target = target;
        terminate(std::move(t)); current_block_ = target; return dest;
    }
    if (auto* de = llvm::dyn_cast<CXXDeleteExpr>(e)) {
        Operand ptr = lower_operand(de->getArgument());
        BlockId target = new_block(); Terminator t;
        t.kind = Terminator::Kind::Call; t.call_callee = "operator delete";
        t.call_args.push_back(std::move(ptr)); t.target = target;
        terminate(std::move(t)); current_block_ = target;
        LocalId tmp = declare_local("", "void", false, true); emit(Statement::storage_live(tmp)); return tmp;
    }

    mark_unsupported(e->getExprLoc(), "expression kind is not represented in MIR");
    LocalId tmp = declare_local("", type_str(e->getType()), false, true);
    emit(Statement::storage_live(tmp));
    return tmp;
}

} // namespace mir
