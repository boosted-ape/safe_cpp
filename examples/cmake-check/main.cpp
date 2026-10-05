#include "counter.hpp"

int main() {
    Counter counter{1};
    counter.push(counter.size());
    return counter.size() == 2 ? 0 : 1;
}
