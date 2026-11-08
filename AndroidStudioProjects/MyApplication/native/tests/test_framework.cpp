#include "test_framework.h"

#include <cstdio>
#include <cstring>
#include <string>

namespace testing {

std::vector<TestCase>& registry() {
    static std::vector<TestCase> cases;
    return cases;
}

Registrar::Registrar(const char* name, void (*fn)()) { registry().push_back(TestCase{name, fn}); }

std::string show(bool v) { return v ? "true" : "false"; }

std::string show(const char* v) { return v ? std::string(v) : std::string("(null)"); }

std::string show(const std::string& v) { return "\"" + v + "\""; }

std::string show(const char16_t* v) { return v ? show(editor::ustring(v)) : std::string("(null)"); }

std::string show(const editor::ustring& v) {
    // Readable for ASCII, explicit escapes for anything else, so a failing
    // assertion never prints mojibake.
    std::string out = "\"";
    char buf[8];
    for (editor::uchar c : v) {
        if (c == u'\n') {
            out += "\\n";
        } else if (c == u'\t') {
            out += "\\t";
        } else if (c == u'"') {
            out += "\\\"";
        } else if (c >= 0x20 && c < 0x7F) {
            out += static_cast<char>(c);
        } else {
            std::snprintf(buf, sizeof(buf), "\\u%04X", static_cast<unsigned>(c));
            out += buf;
        }
    }
    out += "\"";
    return out;
}

std::string show(const editor::Selection& v) {
    return "Selection(" + std::to_string(v.start) + ", " + std::to_string(v.end) + ")";
}

std::string show(const editor::Piece& v) {
    return std::string("Piece(") + (v.buffer == editor::BufferId::Original ? "orig" : "add") + ", " +
           std::to_string(v.offset) + ", " + std::to_string(v.length) + ")";
}

int runAll(int argc, char** argv) {
    const char* filter = nullptr;
    for (int i = 1; i < argc; ++i) {
        if (std::strncmp(argv[i], "--filter=", 9) == 0) filter = argv[i] + 9;
    }

    std::size_t passed = 0;
    std::vector<std::string> failures;

    for (const TestCase& tc : registry()) {
        if (filter && tc.name.find(filter) == std::string::npos) continue;

        try {
            tc.fn();
            ++passed;
            std::printf("[ PASS ] %s\n", tc.name.c_str());
        } catch (const Failure& f) {
            failures.push_back(tc.name + "\n    " + f.message);
            std::printf("[ FAIL ] %s\n    %s\n", tc.name.c_str(), f.message.c_str());
        } catch (const std::exception& e) {
            failures.push_back(tc.name + "\n    unexpected exception: " + e.what());
            std::printf("[ FAIL ] %s\n    unexpected exception: %s\n", tc.name.c_str(), e.what());
        } catch (...) {
            failures.push_back(tc.name + "\n    unexpected non-standard exception");
            std::printf("[ FAIL ] %s\n    unexpected non-standard exception\n", tc.name.c_str());
        }
    }

    std::printf("\n%zu passed, %zu failed\n", passed, failures.size());
    if (!failures.empty()) {
        std::printf("\nFailures:\n");
        for (const std::string& f : failures) std::printf("  - %s\n", f.c_str());
        return 1;
    }
    return 0;
}

}  // namespace testing

int main(int argc, char** argv) { return testing::runAll(argc, argv); }
