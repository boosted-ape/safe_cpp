#include "verifier.hpp"
#include <cassert>
#include <string>

int main() {
    {
        mir::Body body;
        assert(!mir::verify_body(body).ok);
    }
    {
        mir::Body body;
        body.blocks.emplace_back();
        body.start_block = 1;
        body.blocks[0].terminated = true;
        body.blocks[0].terminator = mir::Terminator::ret();
        assert(!mir::verify_body(body).ok);
    }
    {
        mir::Body body;
        body.blocks.emplace_back();
        assert(!mir::verify_body(body).ok); // unterminated block
    }
    {
        mir::Body body;
        body.blocks.emplace_back();
        auto& block = body.blocks[0];
        block.terminated = true;
        block.terminator.kind = mir::Terminator::Kind::SwitchInt;
        block.terminator.switch_default = 1;
        assert(!mir::verify_body(body).ok); // missing switch input and bad target
    }
    {
        mir::Body body;
        body.locals.emplace_back();
        body.blocks.emplace_back();
        auto& block = body.blocks[0];
        block.statements.push_back({});
        block.statements.back().kind = mir::Statement::Kind::Assign;
        block.terminated = true;
        block.terminator = mir::Terminator::ret();
        assert(!mir::verify_body(body).ok); // missing assignment destination and value
    }
    {
        mir::Body body;
        body.blocks.emplace_back();
        auto& block = body.blocks[0];
        block.terminated = true;
        block.terminator.kind = mir::Terminator::Kind::Call;
        assert(!mir::verify_body(body).ok); // invalid target and missing destination
    }
    {
        mir::Body body;
        body.locals.push_back({"value", "int"});
        body.blocks.emplace_back();
        auto& block = body.blocks[0];
        block.statements.push_back(mir::Statement::storage_live(0));
        block.terminated = true;
        block.terminator = mir::Terminator::ret(mir::Operand::make_copy({0}));
        const auto result = mir::verify_body(body);
        assert(!result.ok);
        assert(result.errors.size() == 1);
        assert(result.errors[0].find("before initialization") != std::string::npos);
    }
}
