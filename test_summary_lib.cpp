// Historical summary-sidecar example. The current CLI has no sidecar mode;
// this file uses raw pointers, which strict whole-program mode rejects.
struct SummaryRecord { int value; };

int* library_first(int* first, int* second) { return first; }
int* library_second(int* first, int* second) { return second; }
