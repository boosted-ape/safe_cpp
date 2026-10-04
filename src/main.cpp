#include "borrow.hpp"
#include "mir_builder.hpp"
#include "printer.hpp"
#include "verifier.hpp"
#include <clang/AST/ASTConsumer.h>
#include <clang/AST/ASTContext.h>
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Frontend/FrontendActions.h>
#include <clang/Tooling/CommonOptionsParser.h>
#include <clang/Tooling/Tooling.h>
#include <iostream>
#include <llvm/Support/CommandLine.h>
#include <memory>

using namespace clang;
using namespace clang::tooling;

static llvm::cl::OptionCategory ToolCategory("mir-builder options");

class MIRConsumer : public ASTConsumer {
public:
    explicit MIRConsumer(ASTContext& ctx) : builder_(ctx) {}

    void HandleTranslationUnit(ASTContext& ctx) override {
        builder_.TraverseDecl(ctx.getTranslationUnitDecl());

        int verify_errors = 0;
        int borrow_errors = 0;

        for (const auto& body : builder_.bodies) {
            mir::print_body(body, std::cout);
            std::cout << "\n";

            auto vr = mir::verify_body(body);
            if (!vr.ok) {
                std::cout << "  // VERIFY FAILED for " << body.name << "\n";
                for (const auto& e : vr.errors)
                    std::cout << "  //   " << e << "\n";
                verify_errors += static_cast<int>(vr.errors.size());
            }

            auto bd = mir::check_borrows(body);
            for (const auto& d : bd) {
                std::cout << "  // BORROW ERROR in " << body.name
                          << " at bb" << d.block << ":" << d.stmt
                          << " — " << d.message << "\n";
                ++borrow_errors;
            }
        }

        std::cout << "// verified: " << (verify_errors == 0 ? "OK" : "FAIL")
                  << ", borrow errors: " << borrow_errors << "\n";
    }
private:
    mir::MIRBuilder builder_;
};

class MIRAction : public ASTFrontendAction {
public:
    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance& ci, StringRef) override {
        return std::make_unique<MIRConsumer>(ci.getASTContext());
    }
};

int main(int argc, const char** argv) {
    auto expected = CommonOptionsParser::create(argc, argv, ToolCategory);
    if (!expected) {
        llvm::errs() << llvm::toString(expected.takeError());
        return 1;
    }
    ClangTool tool(expected->getCompilations(), expected->getSourcePathList());
    auto factory = newFrontendActionFactory<MIRAction>();
    return tool.run(factory.get());
}
