#pragma once
#include "mir.hpp"
#include <clang/AST/RecursiveASTVisitor.h>
#include <map>

namespace mir {

class MIRBuilder : public clang::RecursiveASTVisitor<MIRBuilder> {
public:
    explicit MIRBuilder(clang::ASTContext& ctx) : ctx_(ctx) {}
    bool VisitFunctionDecl(clang::FunctionDecl* fd);
    std::vector<Body> bodies;

private:
    clang::ASTContext& ctx_;
    Body* body_ = nullptr;
    BlockId current_block_ = 0;
    std::map<const clang::VarDecl*, LocalId> var_to_local_;
    LocalId this_local_ = INVALID_BLOCK;

    struct Scope { std::vector<LocalId> locals; };
    std::vector<Scope> scopes_;

    struct LoopCtx { BlockId continue_target; BlockId break_target; };
    std::vector<LoopCtx> loop_stack_;

    LocalId declare_local(const std::string& name, const std::string& type,
                          bool is_arg, bool is_temp, bool is_mut = true,
                          bool is_this = false);
    BlockId new_block();
    void emit(Statement s);
    void emit_assign(Place dest, Rvalue rv);
    void terminate(Terminator t);
    bool is_terminated() const;
    void push_scope();
    void pop_scope();

    void lower_stmt(clang::Stmt* s);
    void lower_decl_stmt(clang::DeclStmt* ds);
    void lower_return_stmt(clang::ReturnStmt* rs);
    void lower_if_stmt(clang::IfStmt* is);
    void lower_while_stmt(clang::WhileStmt* ws);
    void lower_for_stmt(clang::ForStmt* fs);
    void lower_do_stmt(clang::DoStmt* ds);
    void lower_break_stmt(clang::BreakStmt* bs);
    void lower_continue_stmt(clang::ContinueStmt* cs);
    void lower_assign_op(clang::BinaryOperator* bo);

    Place   lower_expr(clang::Expr* e);
    LocalId lower_expr_to_local(clang::Expr* e);
    LocalId lower_rvalue_to_temp(clang::Expr* e);
    Operand lower_operand(clang::Expr* e);

    LocalId lower_binary_op(clang::BinaryOperator* bo);
    LocalId lower_logical_and(clang::BinaryOperator* bo);
    LocalId lower_logical_or(clang::BinaryOperator* bo);
    LocalId lower_unary_op(clang::UnaryOperator* uo);
    LocalId lower_conditional(clang::ConditionalOperator* co);
    LocalId lower_call(clang::CallExpr* ce);
    LocalId lower_member_call(clang::CXXMemberCallExpr* mce);
    LocalId lower_construct(clang::CXXConstructExpr* cce);
    LocalId lower_init_list(clang::InitListExpr* ile);

    std::string type_str(clang::QualType qt);
    Type build_type(clang::QualType qt);
    BinOp map_binop(clang::BinaryOperator::Opcode op);
};

} // namespace mir
