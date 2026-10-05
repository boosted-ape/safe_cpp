// Historical summary-sidecar example. The current CLI has no sidecar mode;
// this file uses raw pointers, which strict whole-program mode rejects.
struct SummaryRecord { int value; };

int* library_first(int* first, int* second);
int* library_second(int* first, int* second);

int cross_tu_first_position(SummaryRecord& a, SummaryRecord& b) {
    int* result = library_first(&a.value, &b.value);
    b.value = 1; // accepted: library_first returns parameter 0
    return *result;
}

int cross_tu_second_position(SummaryRecord& a, SummaryRecord& b) {
    int* result = library_second(&a.value, &b.value);
    b.value = 2; // rejected: library_second returns parameter 1
    return *result;
}
