#pragma once
#include "mir.hpp"
#include <string>
#include <vector>

namespace mir {

struct BorrowDiagnostic {
    std::string message;
    BlockId block = 0;
    uint32_t stmt = 0;
};

std::vector<BorrowDiagnostic> check_borrows(const Body& body);

} // namespace mir
