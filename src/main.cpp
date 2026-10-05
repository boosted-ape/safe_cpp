#include "borrow.hpp"
#include "mir_builder.hpp"
#include "printer.hpp"
#include "verifier.hpp"
#include <clang/AST/ASTConsumer.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclTemplate.h>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/StmtCXX.h>
#include <clang/Index/USRGeneration.h>
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Frontend/FrontendActions.h>
#include <clang/Tooling/CommonOptionsParser.h>
#include <clang/Tooling/Tooling.h>
#include <iostream>
#include <llvm/Support/CommandLine.h>
#include <memory>
#include <map>
#include <set>
#include <llvm/ADT/SmallString.h>

using namespace clang;
using namespace clang::tooling;

static llvm::cl::OptionCategory ToolCategory("mir-builder options");
static std::string summary_key_for(const Decl* decl) {
    if (!decl) return {};
    llvm::SmallString<128> usr;
    if (const auto* named = dyn_cast<NamedDecl>(decl)) {
        if (!index::generateUSRForDecl(named->getCanonicalDecl(), usr)) return std::string(usr.str());
        return named->getQualifiedNameAsString();
    }
    return {};
}

struct WholeProgramCall {
    std::string caller;
    std::string callee;
    std::string callee_name;
    std::string location;
};

struct WholeProgramState {
    std::vector<mir::Body> bodies;
    std::vector<WholeProgramCall> calls;
    unsigned main_definitions = 0;
    unsigned policy_errors = 0;
    unsigned lowering_errors = 0;
};

class WholeProgramPolicy : public RecursiveASTVisitor<WholeProgramPolicy> {
public:
    WholeProgramPolicy(ASTContext& context, WholeProgramState& program)
        : context_(context), program_(program) {}

    bool TraverseFunctionDecl(FunctionDecl* fd) {
        const std::string previous = caller_;
        if (is_user_code(fd->getLocation())) caller_ = summary_key_for(fd);
        const bool result = RecursiveASTVisitor<WholeProgramPolicy>::TraverseFunctionDecl(fd);
        caller_ = previous;
        return result;
    }

    bool VisitFunctionDecl(FunctionDecl* fd) {
        if (!is_user_code(fd->getLocation())) return true;
        auto contains_unsafe_indirection = [](QualType type) {
            return !type.isNull() && (type->isPointerType() || type->isReferenceType()
                || type->isMemberPointerType() || type->isArrayType());
        };
        if (contains_unsafe_indirection(fd->getReturnType()))
            fail(fd->getLocation(), "whole-program profile forbids pointer, reference, array, or member-pointer returns");
        for (const ParmVarDecl* param : fd->parameters())
            if (contains_unsafe_indirection(param->getType()))
                fail(param->getLocation(), "whole-program profile forbids pointer, reference, array, or member-pointer parameters");
        if (fd->isVariadic())
            fail(fd->getLocation(), "whole-program profile forbids variadic functions");
        if (fd->getNameAsString() == "main" && fd->isGlobal() && fd->doesThisDeclarationHaveABody()) {
            ++program_.main_definitions;
            if (fd->getNumParams() != 0 || !fd->getReturnType().getCanonicalType()->isSpecificBuiltinType(BuiltinType::Int))
                fail(fd->getLocation(), "whole-program entry point must have signature int main()");
        }
        if (const auto* method = dyn_cast<CXXMethodDecl>(fd))
            if (method->isVirtual()) fail(fd->getLocation(), "whole-program profile forbids virtual methods");
        return true;
    }

    bool VisitVarDecl(VarDecl* vd) {
        if (!is_user_code(vd->getLocation()) || isa<ParmVarDecl>(vd)) return true;
        if (vd->isFileVarDecl() || vd->isStaticLocal())
            fail(vd->getLocation(), "whole-program profile forbids global and static storage");
        QualType type = vd->getType();
        if (!type.isNull() && (type->isPointerType() || type->isMemberPointerType() || type->isArrayType()))
            fail(vd->getLocation(), "whole-program profile forbids raw pointers, member pointers, and arrays");
        if (!type.isNull() && type.isVolatileQualified())
            fail(vd->getLocation(), "whole-program profile forbids volatile objects");
        return true;
    }

    bool VisitFieldDecl(FieldDecl* field) {
        if (!is_user_code(field->getLocation())) return true;
        QualType type = field->getType();
        if (type->isPointerType() || type->isReferenceType() || type->isMemberPointerType() || type->isArrayType())
            fail(field->getLocation(), "whole-program profile forbids pointer, reference, and array fields");
        if (field->isMutable()) fail(field->getLocation(), "whole-program profile forbids mutable fields");
        if (type.isVolatileQualified()) fail(field->getLocation(), "whole-program profile forbids volatile fields");
        return true;
    }

    bool VisitCXXRecordDecl(CXXRecordDecl* record) {
        if (!is_user_code(record->getLocation()) || !record->isThisDeclarationADefinition()) return true;
        if (record->isUnion()) fail(record->getLocation(), "whole-program profile forbids unions");
        if (const auto* dtor = record->getDestructor())
            if (!dtor->isTrivial()) fail(dtor->getLocation(), "whole-program profile forbids nontrivial destructors");
        return true;
    }

    bool VisitFunctionTemplateDecl(FunctionTemplateDecl* decl) {
        if (is_user_code(decl->getLocation()))
            fail(decl->getLocation(), "whole-program profile forbids function templates");
        return true;
    }
    bool VisitClassTemplateDecl(ClassTemplateDecl* decl) {
        if (is_user_code(decl->getLocation()))
            fail(decl->getLocation(), "whole-program profile forbids class templates");
        return true;
    }
    bool VisitLambdaExpr(LambdaExpr* expr) {
        if (is_user_code(expr->getBeginLoc()))
            fail(expr->getBeginLoc(), "whole-program profile forbids lambdas and captures");
        return true;
    }
    bool VisitArraySubscriptExpr(ArraySubscriptExpr* expr) {
        if (is_user_code(expr->getExprLoc()))
            fail(expr->getExprLoc(), "whole-program profile forbids array subscripting");
        return true;
    }
    bool VisitCXXForRangeStmt(CXXForRangeStmt* stmt) {
        if (is_user_code(stmt->getBeginLoc()))
            fail(stmt->getBeginLoc(), "whole-program profile forbids range-for until its iterator bounds are proven");
        return true;
    }
    bool VisitUnaryOperator(UnaryOperator* expr) {
        if (expr->getOpcode() == UO_AddrOf && is_user_code(expr->getOperatorLoc()))
            fail(expr->getOperatorLoc(), "whole-program profile forbids raw address-taking; bind a local reference instead");
        return true;
    }
    bool VisitCXXTryStmt(CXXTryStmt* stmt) {
        if (is_user_code(stmt->getBeginLoc()))
            fail(stmt->getBeginLoc(), "whole-program profile forbids exception handlers");
        return true;
    }
    bool VisitCXXThrowExpr(CXXThrowExpr* expr) {
        if (is_user_code(expr->getBeginLoc()))
            fail(expr->getBeginLoc(), "whole-program profile forbids throw expressions");
        return true;
    }
    bool VisitCXXConstCastExpr(CXXConstCastExpr* expr) {
        if (is_user_code(expr->getBeginLoc())) fail(expr->getBeginLoc(), "whole-program profile forbids const_cast");
        return true;
    }
    bool VisitCXXReinterpretCastExpr(CXXReinterpretCastExpr* expr) {
        if (is_user_code(expr->getBeginLoc())) fail(expr->getBeginLoc(), "whole-program profile forbids reinterpret_cast");
        return true;
    }
    bool VisitCXXDynamicCastExpr(CXXDynamicCastExpr* expr) {
        if (is_user_code(expr->getBeginLoc())) fail(expr->getBeginLoc(), "whole-program profile forbids dynamic_cast");
        return true;
    }
    bool VisitCStyleCastExpr(CStyleCastExpr* expr) {
        if (is_user_code(expr->getBeginLoc())) fail(expr->getBeginLoc(), "whole-program profile forbids C-style casts");
        return true;
    }
    bool VisitCallExpr(CallExpr* expr) {
        if (!is_user_code(expr->getExprLoc())) return true;
        const FunctionDecl* callee = expr->getDirectCallee();
        if (!callee) {
            fail(expr->getExprLoc(), "whole-program profile forbids indirect calls");
            return true;
        }
        record_call(callee, expr->getExprLoc());
        return true;
    }
    bool VisitCXXConstructExpr(CXXConstructExpr* expr) {
        const CXXConstructorDecl* ctor = expr->getConstructor();
        if (ctor && !ctor->isTrivial() && is_user_code(expr->getExprLoc())) record_call(ctor, expr->getExprLoc());
        return true;
    }

private:
    ASTContext& context_;
    WholeProgramState& program_;
    std::string caller_;

    bool is_user_code(SourceLocation loc) const {
        return loc.isValid() && !context_.getSourceManager().isInSystemHeader(loc);
    }
    void fail(SourceLocation loc, const char* message) {
        ++program_.policy_errors;
        auto id = context_.getDiagnostics().getCustomDiagID(DiagnosticsEngine::Error, "%0");
        context_.getDiagnostics().Report(loc, id) << message;
    }
    void record_call(const FunctionDecl* callee, SourceLocation loc) {
        const PresumedLoc presumed = context_.getSourceManager().getPresumedLoc(loc);
        std::string where = presumed.isValid()
            ? std::string(presumed.getFilename()) + ":" + std::to_string(presumed.getLine())
            : std::string("unknown source location");
        program_.calls.push_back({caller_, summary_key_for(callee),
            callee->getQualifiedNameAsString(), std::move(where)});
    }
};

class MIRConsumer : public ASTConsumer {
public:
    MIRConsumer(ASTContext& ctx, WholeProgramState& whole_program)
        : builder_(ctx), whole_program_(whole_program) {}

    void HandleTranslationUnit(ASTContext& ctx) override {
        builder_.TraverseDecl(ctx.getTranslationUnitDecl());

        for (const auto& e : builder_.unsupported_errors) {
            auto id = ctx.getDiagnostics().getCustomDiagID(DiagnosticsEngine::Error, "cannot analyze: %0");
            ctx.getDiagnostics().Report(e.location, id) << e.message;
            ++whole_program_.lowering_errors;
        }
        WholeProgramPolicy policy(ctx, whole_program_);
        policy.TraverseDecl(ctx.getTranslationUnitDecl());
        whole_program_.bodies.insert(whole_program_.bodies.end(), builder_.bodies.begin(), builder_.bodies.end());
    }
private:
    mir::MIRBuilder builder_;
    WholeProgramState& whole_program_;
};

class MIRAction : public ASTFrontendAction {
public:
    explicit MIRAction(WholeProgramState& state) : whole_program_(state) {}
    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance& ci, StringRef) override {
        return std::make_unique<MIRConsumer>(ci.getASTContext(), whole_program_);
    }
private:
    WholeProgramState& whole_program_;
};

class MIRActionFactory : public FrontendActionFactory {
public:
    explicit MIRActionFactory(WholeProgramState& state) : state_(state) {}
    std::unique_ptr<FrontendAction> create() override { return std::make_unique<MIRAction>(state_); }
private:
    WholeProgramState& state_;
};

static int finish_whole_program(WholeProgramState& state) {
    if (state.policy_errors || state.lowering_errors) return 1;
    if (state.main_definitions != 1) {
        llvm::errs() << "whole-program profile requires exactly one definition of int main() with no parameters\n";
        return 1;
    }
    std::map<std::string, size_t> definitions;
    for (size_t i = 0; i < state.bodies.size(); ++i)
        if (!state.bodies[i].summary_key.empty()) definitions.emplace(state.bodies[i].summary_key, i);
    for (const auto& call : state.calls) {
        if (call.callee.empty() || !definitions.count(call.callee)) {
            llvm::errs() << call.location << ": whole-program profile cannot verify call to '" << call.callee_name
                         << "': provide its definition in the analyzed source set\n";
            ++state.policy_errors;
        }
    }
    if (state.policy_errors) return 1;
    std::vector<mir::Body> bodies;
    std::set<std::string> seen;
    for (const auto& body : state.bodies)
        if (body.summary_key.empty() || seen.insert(body.summary_key).second) bodies.push_back(body);
    const auto summaries = mir::compute_return_borrow_summaries(bodies);
    unsigned errors = 0;
    for (const auto& body : bodies) {
        mir::print_body(body, std::cout);
        std::cout << "\n";
        const auto verified = mir::verify_body(body);
        if (!verified.ok) {
            ++errors;
            for (const auto& error : verified.errors) llvm::errs() << "MIR verification failed in " << body.name << ": " << error << "\n";
            continue;
        }
        for (const auto& diagnostic : mir::check_borrows(body, summaries)) {
            std::cout << "  // BORROW ERROR in " << body.name << " at bb" << diagnostic.block << ":" << diagnostic.stmt
                      << " — " << diagnostic.message << "\n";
            llvm::errs() << "borrow error in " << body.name << " at bb" << diagnostic.block << ":" << diagnostic.stmt
                         << ": " << diagnostic.message << "\n";
            ++errors;
        }
    }
    std::cout << "// whole-program profile: " << (errors ? "FAIL" : "OK") << " (" << errors << " errors, "
              << bodies.size() << " functions)\n";
    return errors ? 1 : 0;
}

int main(int argc, const char** argv) {
    auto expected = CommonOptionsParser::create(argc, argv, ToolCategory);
    if (!expected) {
        llvm::errs() << llvm::toString(expected.takeError());
        return 1;
    }
    ClangTool tool(expected->getCompilations(), expected->getSourcePathList());
    WholeProgramState program;
    MIRActionFactory factory(program);
    const int clang_status = tool.run(&factory);
    if (clang_status != 0) return clang_status;
    return finish_whole_program(program);
}
