#pragma once
#include "mir.hpp"
#include <string>
#include <vector>

namespace mir {

struct VerifyResult {
    bool ok = true;
    std::vector<std::string> errors;
};

VerifyResult verify_body(const Body& body);

} // namespace mir
