cmake_minimum_required(VERSION 3.20)
project(safe_cpp C CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)

include_directories(${LLVM_INCLUDE_DIRS} ${CLANG_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS} ${CLANG_DEFINITIONS})

add_executable(mir-builder
    src/main.cpp
    src/printer.cpp
    src/verifier.cpp
    src/mir_builder.cpp
    src/borrow.cpp
)

target_link_libraries(mir-builder
    PRIVATE
    LLVMCore
    LLVMSupport
    clang-cpp
)
