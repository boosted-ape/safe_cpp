// Strict whole-program borrow-checker negative test: loan is still used after
// the write, so the write conflicts with the live mutable loan.
int main() {
    int value = 1;
    int& loan = value;
    value = 2;
    return loan;
}
