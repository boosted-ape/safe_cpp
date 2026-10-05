// Coverage input for MIR lowering and CFG based NLL.
// Run with: ./build/mir-builder test_nll.cpp -- -std=c++17

struct Base {
    int value;
    virtual int get() const { return value; }
    virtual ~Base() {}
};

struct Derived : Base {
    int extra;
    int get() const override { return value + extra; }
};

struct Guard {
    int* ptr;
    ~Guard() { if (ptr) *ptr = 0; }
};

int nll_last_use_then_write(Base& b) {
    int& r = b.value;
    int observed = r; // last use of r
    b.value = observed + 1; // should be allowed by NLL
    return observed;
}

int branch_and_loop_liveness(Derived& d, int count) {
    int& r = d.value;
    int sum = 0;
    while (count > 0) {
        switch (count % 3) {
            case 0: sum += r; break;
            case 1: sum += d.get(); break; // virtual call
            default: sum += d.extra; break;
        }
        --count;
    }
    d.value = sum; // r is still live on loop paths above
    return r;
}

int range_for_and_cast(Derived& d) {
    int values[3] = {1, 2, 3};
    int total = 0;
    for (int x : values) total += static_cast<int>(x);
    Base* base = static_cast<Base*>(&d);
    return total + base->get();
}

int pointer_copy_keeps_loan_live() {
    int values[2] = {4, 9};
    int* first = &values[0];
    int* alias = first;
    values[0] = 12; // rejected: alias is used after this mutation
    return *alias;
}

int cast_copy_keeps_loan_live(Base& b) {
    int* original = &b.value;
    int* casted = reinterpret_cast<int*>(original);
    b.value = 21; // rejected while casted is used below
    return *casted;
}

int* identity_pointer(int* p) { return p; }
int* get_static();
int* pass_through(int* p) { return p; }
int* choose_second(int* a, int* b) { return b; }
int* return_first(int* a, int* b) { return a; }
int* return_second(int* a, int* b) { return b; }
int* annotated_first(int* a [[clang::lifetimebound]], int* b);
int* annotated_second(int* a, int* b [[clang::lifetimebound]]);

int false_positive_probe(Base& b) {
    int* r = &b.value;
    int* q = get_static(); // no argument origin can flow into this result
    b.value = 5;            // conflict only with r
    return *r + *q;
}

int sound_interproc_probe(Base& b) {
    int* r = &b.value;
    int* q = pass_through(r);
    b.value = 5; // conflict: q carries the loan through the call result
    return *q;
}

int no_conflict_probe(Base& a, Base& b) {
    int* r = &a.value;
    int* q = pass_through(r);
    b.value = 5; // disjoint base local; should be accepted
    return *q;
}

int disjoint_call_return_probe(Base& b, Base& other) {
    int* r = &b.value;
    int v = *r;
    int* q = choose_second(r, &other.value);
    b.value = 5; // should be allowed if result origin is argument-position-sensitive
    return *q + v;
}

int cross_arm_probe(Base& b, Base& other) {
    int* r = &b.value;
    int* q = return_first(&other.value, r);
    b.value = 6; // should be allowed: return_first returns its first argument
    return *q;
}

int return_first_tracks_first(Base& b, Base& other) {
    int* q = return_first(&b.value, &other.value);
    b.value = 7; // rejected: return_first returns the first argument
    return *q;
}

int choose_second_tracks_second(Base& b, Base& other) {
    int* q = choose_second(&b.value, &other.value);
    other.value = 8; // rejected: choose_second returns the second argument
    return *q;
}

int annotated_first_position(Base& b, Base& other) {
    int* q = annotated_first(&b.value, &other.value);
    b.value = 9; // annotation says the returned pointer may alias argument 0
    return *q;
}

int annotated_second_position(Base& b, Base& other) {
    int* r = &b.value;
    int v = *r;
    int* q = annotated_second(r, &other.value);
    b.value = 10; // annotation says argument 1 is returned; r is now dead
    return *q + v;
}

int returned_pointer_keeps_loan_live(Base& b) {
    int* p = identity_pointer(&b.value);
    b.value = 22; // rejected: the returned pointer still carries the loan
    return *p;
}

int branch_created_loan(bool take, Base& b) {
    int* p = nullptr;
    if (take) p = &b.value;
    b.value = 23; // conservatively rejected after the branch merge
    return p ? *p : 0;
}

int branch_loan_killed_on_other_arm(bool take, Base& b) {
    int* p = nullptr;
    if (take) p = &b.value;
    else p = nullptr; // must not erase the loan from the other incoming path
    b.value = 24;      // rejected on the path where p carries the loan
    return p ? *p : 0;
}

struct ReentrantBuffer {
    int count;
    int size() const { return count; }
    int bump() { return count++; }
    void push(int) { ++count; }
};

void nested_receiver_argument_call(ReentrantBuffer& buffer) {
    buffer.push(buffer.size()); // two-phase borrow case; should be accepted
}

void separate_receiver_calls(ReentrantBuffer& buffer) {
    int x = buffer.size();
    buffer.push(x);
}

void two_calls_same_expression(ReentrantBuffer& buffer) {
    buffer.push(buffer.size() + buffer.size());
}

void nested_mutating_argument_conflict(ReentrantBuffer& buffer) {
    buffer.push(buffer.bump()); // reserved mutable receiver conflicts with nested mutable access
}
