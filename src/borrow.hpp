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
struct DropEffect {
    std::vector<Projection> projections;
    bool is_write = false;
    bool deep = true;
    // Index in the function's MIR argument order; destructors use 0 for this.
    size_t argument_index = 0;
};
using DropEffectSummaries = std::map<std::string, std::vector<DropEffect>>;
ReturnBorrowSummaries compute_return_borrow_summaries(const std::vector<Body>& bodies);
DropEffectSummaries compute_drop_effect_summaries(const std::vector<Body>& bodies);
std::vector<BorrowDiagnostic> check_borrows(const Body& body, const ReturnBorrowSummaries& summaries);
std::vector<BorrowDiagnostic> check_borrows(const Body& body,
    const ReturnBorrowSummaries& summaries, const DropEffectSummaries& drop_effects);
bool load_return_borrow_summaries(const std::string& path, ReturnBorrowSummaries& summaries, std::string& error);
bool write_return_borrow_summaries(const std::string& path, const ReturnBorrowSummaries& summaries, std::string& error);

} // namespace mir
