#ifndef EDITOR_TEST_FRAMEWORK_H
#define EDITOR_TEST_FRAMEWORK_H

#include <cstddef>
#include <exception>
#include <sstream>
#include <string>
#include <vector>

#include "editor/types.h"

// A deliberately tiny test harness. The point of moving the editor core to
// C++ was a dependency-free local loop, so the tests do not pull in a
// framework that would have to be fetched.

namespace testing {

struct Failure : public std::exception {
    std::string message;
    explicit Failure(std::string m) : message(std::move(m)) {}
    const char* what() const noexcept override { return message.c_str(); }
};

struct TestCase {
    std::string name;
    void (*fn)();
};

std::vector<TestCase>& registry();
int runAll(int argc, char** argv);

struct Registrar {
    Registrar(const char* name, void (*fn)());
};

// Wraps a UTF-16 literal so comparisons and failure messages both see a real
// ustring rather than a raw char16_t pointer.
inline editor::ustring U(const char16_t* s) { return editor::ustring(s); }

std::string show(bool v);
std::string show(const char* v);
std::string show(const char16_t* v);
std::string show(const std::string& v);
std::string show(const editor::ustring& v);
std::string show(const editor::Selection& v);
std::string show(const editor::Piece& v);

template <class T>
std::string show(const T& v) {
    std::ostringstream os;
    os << v;
    return os.str();
}

template <class T>
std::string show(const std::vector<T>& v) {
    std::string out = "[";
    for (std::size_t i = 0; i < v.size(); ++i) {
        if (i) out += ", ";
        out += show(v[i]);
    }
    out += "]";
    return out;
}

}  // namespace testing

#define TEST(NAME)                                                     \
    static void NAME();                                                \
    static ::testing::Registrar testing_registrar_##NAME(#NAME, NAME); \
    static void NAME()

#define EDITOR_FAIL(MSG) \
    throw ::testing::Failure(std::string(__FILE__ ":") + std::to_string(__LINE__) + "  " + (MSG))

#define CHECK(COND)                                                 \
    do {                                                            \
        if (!(COND)) EDITOR_FAIL(std::string("CHECK failed: " #COND)); \
    } while (false)

#define CHECK_FALSE(COND)                                                    \
    do {                                                                     \
        if ((COND)) EDITOR_FAIL(std::string("CHECK_FALSE failed: " #COND));  \
    } while (false)

#define CHECK_EQ(ACTUAL, EXPECTED)                                                  \
    do {                                                                            \
        const auto& actual_ = (ACTUAL);                                             \
        const auto& expected_ = (EXPECTED);                                         \
        if (!(actual_ == expected_)) {                                              \
            EDITOR_FAIL(std::string("CHECK_EQ failed: " #ACTUAL " == " #EXPECTED) + \
                        "\n      actual:   " + ::testing::show(actual_) +           \
                        "\n      expected: " + ::testing::show(expected_));         \
        }                                                                           \
    } while (false)

#define CHECK_THROWS(EXPR, EXCEPTION)                                            \
    do {                                                                         \
        bool threw_ = false;                                                     \
        try {                                                                    \
            (void)(EXPR);                                                        \
        } catch (const EXCEPTION&) {                                             \
            threw_ = true;                                                       \
        } catch (...) {                                                          \
        }                                                                        \
        if (!threw_) {                                                           \
            EDITOR_FAIL(std::string("expected " #EXCEPTION " from " #EXPR));     \
        }                                                                        \
    } while (false)

#endif  // EDITOR_TEST_FRAMEWORK_H
