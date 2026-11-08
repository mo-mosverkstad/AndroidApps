#ifndef EDITOR_TEXT_DIFF_H
#define EDITOR_TEXT_DIFF_H

#include <cstdint>

#include "editor/types.h"

namespace editor {

// A single splice: erase `removeLength` units at `pos`, then insert `insertText`.
struct TextEdit {
    int32_t pos = 0;
    int32_t removeLength = 0;
    ustring insertText;

    bool empty() const { return removeLength == 0 && insertText.empty(); }
};

// Recovers the minimal single splice that turns `oldText` into `newText` by
// matching the common prefix and suffix.
//
// This exists because Compose's BasicTextField reports a whole new string
// rather than the edit that produced it. Keeping the reconstruction here, in
// the core, means it is covered by the desktop tests instead of living in a
// Kotlin lambda that only runs on a device.
//
// Boundaries are nudged off the middle of a surrogate pair so a single edit
// never splits one astral character into two halves.
TextEdit diffTexts(const ustring& oldText, const ustring& newText);

}  // namespace editor

#endif  // EDITOR_TEXT_DIFF_H
