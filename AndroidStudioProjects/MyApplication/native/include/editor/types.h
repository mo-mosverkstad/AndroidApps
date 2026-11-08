#ifndef EDITOR_TYPES_H
#define EDITOR_TYPES_H

#include <cstdint>
#include <string>
#include <vector>

namespace editor {

// All text in the core is UTF-16.
//
// This is a deliberate choice: java.lang.String, Kotlin String and Compose's
// TextRange all index in UTF-16 code units, and char16_t is layout-compatible
// with jchar. Storing UTF-8 here would mean every offset crossing the JNI
// boundary needed a conversion, and any such conversion bug would silently
// corrupt documents containing non-ASCII text.
using ustring = std::u16string;
using uchar = char16_t;

enum class BufferId : int32_t {
    Original = 0,  // immutable text the document was opened with
    Added = 1      // append-only buffer holding everything typed since
};

// A run of characters inside one of the two buffers.
struct Piece {
    BufferId buffer = BufferId::Original;
    int32_t offset = 0;
    int32_t length = 0;
};

inline bool operator==(const Piece& a, const Piece& b) {
    return a.buffer == b.buffer && a.offset == b.offset && a.length == b.length;
}

inline bool operator!=(const Piece& a, const Piece& b) { return !(a == b); }

inline int32_t totalLength(const std::vector<Piece>& pieces) {
    int32_t sum = 0;
    for (const Piece& p : pieces) sum += p.length;
    return sum;
}

// A caret (start == end) or a selected range. Not normalised: start may be
// greater than end when the user dragged backwards, which Compose also allows.
struct Selection {
    int32_t start = 0;
    int32_t end = 0;

    Selection() = default;
    explicit Selection(int32_t caret) : start(caret), end(caret) {}
    Selection(int32_t s, int32_t e) : start(s), end(e) {}

    bool collapsed() const { return start == end; }
    int32_t min() const { return start < end ? start : end; }
    int32_t max() const { return start < end ? end : start; }
    int32_t length() const { return max() - min(); }
};

inline bool operator==(const Selection& a, const Selection& b) {
    return a.start == b.start && a.end == b.end;
}

inline bool operator!=(const Selection& a, const Selection& b) { return !(a == b); }

inline int32_t clampOffset(int32_t value, int32_t limit) {
    if (value < 0) return 0;
    if (value > limit) return limit;
    return value;
}

inline Selection clampSelection(Selection s, int32_t limit) {
    return Selection(clampOffset(s.start, limit), clampOffset(s.end, limit));
}

inline bool isHighSurrogate(uchar c) { return c >= 0xD800 && c <= 0xDBFF; }

inline bool isLowSurrogate(uchar c) { return c >= 0xDC00 && c <= 0xDFFF; }

}  // namespace editor

#endif  // EDITOR_TYPES_H
