int manual_allocation_is_unsupported() {
    int* p = new int(5);
    int value = *p;
    delete p;
    return value;
}

int unsupported_goto() {
    goto done;
done:
    return 0;
}

struct BaseForException {
    int value;
    int get() const { return value; }
};
struct GuardForException {
    int* ptr;
    ~GuardForException() { if (ptr) *ptr = 0; }
};

int unsupported_catch_parameter(BaseForException& b, bool fail) {
    GuardForException guard{&b.value};
    try {
        if (fail) throw 7;
        return b.get();
    } catch (int code) {
        return code;
    }
}
