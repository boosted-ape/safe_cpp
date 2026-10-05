cmake_minimum_required(VERSION 3.20)
project(safe_cpp_cmake_check LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(SAFE_CPP_CHECKER "" CACHE FILEPATH "Path to the built mir-builder executable")
if(NOT SAFE_CPP_CHECKER)
    message(FATAL_ERROR "Set SAFE_CPP_CHECKER to the path of mir-builder")
endif()

add_executable(sample main.cpp counter.cpp)

# mir-builder analyzes all translation units together. The regular C++
# compiler still produces the executable; mir-builder is not an LLVM backend.
add_custom_target(memory_safety_check ALL
    COMMAND "${SAFE_CPP_CHECKER}"
            "${CMAKE_CURRENT_SOURCE_DIR}/main.cpp"
            "${CMAKE_CURRENT_SOURCE_DIR}/counter.cpp"
            -- -std=c++17
    DEPENDS main.cpp counter.cpp
    COMMENT "Checking the sample with mir-builder"
    VERBATIM
)
add_dependencies(sample memory_safety_check)
