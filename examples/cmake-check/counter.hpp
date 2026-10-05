#pragma once

struct Counter {
    int value;

    int size() const { return value; }
    void push(int amount) { value = value + amount; }
};
