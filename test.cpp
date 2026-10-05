struct Entity {
    int hp;
    int rings[4];
};

// --- Should be rejected (Rust would reject) ---

// 1. Write to e->hp while a shared loan on e->hp is live.
int conflict_same_field(Entity* e) {
    int* hp = &e->hp;
    e->hp = 0;
    return *hp;
}

// 2. Two mutable loans on the same place.
int two_mut_loans(Entity* e) {
    int* a = &e->hp;
    int* b = &e->hp;
    *a = 1;
    *b = 2;
    return *a;
}

// 3. Mutable loan live across a read of the same place.
int read_while_mut(Entity* e) {
    int* hp = &e->hp;
    int  copy = e->hp;
    *hp = 5;
    return copy;
}

// 4. Loan on a subplace, mutation on an overlapping subplace.
int field_overlap(Entity* e) {
    int* first_ring = &e->rings[0];
    e->rings[0] = 5;
    return *first_ring;
}

// 5. Method call with mutable receiver while a loan on the receiver is live.
struct Counter {
    int count;
    void increment() { count = count + 1; }
    int  get() const { return count; }
};

int method_conflict(Counter* c) {
    int* p = &c->count;
    c->increment();
    return *p;
}

// --- Should be accepted (Rust would accept) ---

// 6. Two shared loans on the same place.
int two_shared(Entity* e) {
    const int& a = e->hp;
    const int& b = e->hp;
    return a + b;
}

// 7. Disjoint fields.
int disjoint_fields(Entity* e) {
    int* hp = &e->hp;
    int  v  = e->rings[1];
    return *hp + v;
}

// 8. Loan used, then mutation after its last use.
int mutate_after_use(Entity* e) {
    int v = *(&e->hp);
    e->hp = 0;
    return v;
}

// 9. Two different objects.
int different_objects(Entity* a, Entity* b) {
    int* hp = &a->hp;
    b->hp = 0;
    return *hp;
}

// 10. Method call on a different object while a loan exists on another.
int method_different_object(Counter* c, Entity* e) {
    int* hp = &e->hp;
    c->increment();
    return *hp;
}

// 11. Const method call while a loan on the receiver is live.
int const_method_ok(Counter* c) {
    const int& p = c->count;
    int  v = c->get();
    return p + v;
}
