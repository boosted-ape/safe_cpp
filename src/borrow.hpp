#pragma once
#include "mir.hpp"
#include <string>
#include <map>
#include <set>
#include <vector>

namespace mir {

struct BorrowDiagnostic {
    std::string message;
    BlockId block = 0;
    uint32_t stmt = 0;
    bool is_warning = false;
};

std::vector<BorrowDiagnostic> check_borrows(const Body& body);
using ReturnBorrowSummaries = std::map<std::string, std::set<size_t>>;
ReturnBorrowSummaries compute_return_borrow_summaries(const std::vector<Body>& bodies);
std::vector<BorrowDiagnostic> check_borrows(const Body& body, const ReturnBorrowSummaries& summaries);
bool load_return_borrow_summaries(const std::string& path, ReturnBorrowSummaries& summaries, std::string& error);
bool write_return_borrow_summaries(const std::string& path, const ReturnBorrowSummaries& summaries, std::string& error);

} // namespace mir
