#include "editor/text_diff.h"

#include <algorithm>

namespace editor {

TextEdit diffTexts(const ustring& oldText, const ustring& newText) {
    const int32_t oldLen = static_cast<int32_t>(oldText.size());
    const int32_t newLen = static_cast<int32_t>(newText.size());

    TextEdit edit;
    if (oldText == newText) return edit;

    const int32_t limit = std::min(oldLen, newLen);

    int32_t prefix = 0;
    while (prefix < limit && oldText[static_cast<size_t>(prefix)] == newText[static_cast<size_t>(prefix)]) {
        ++prefix;
    }

    int32_t suffix = 0;
    while (suffix < oldLen - prefix && suffix < newLen - prefix &&
           oldText[static_cast<size_t>(oldLen - 1 - suffix)] ==
               newText[static_cast<size_t>(newLen - 1 - suffix)]) {
        ++suffix;
    }

    // Do not leave a boundary between the halves of a surrogate pair.
    if (prefix > 0 && prefix < oldLen && isHighSurrogate(oldText[static_cast<size_t>(prefix - 1)])) {
        --prefix;
    }
    if (suffix > 0 && oldLen - suffix < oldLen &&
        isLowSurrogate(oldText[static_cast<size_t>(oldLen - suffix)])) {
        --suffix;
    }

    const int32_t removeLength = oldLen - prefix - suffix;
    const int32_t insertLength = newLen - prefix - suffix;

    if (prefix < 0 || removeLength < 0 || insertLength < 0) {
        // Should be unreachable; fall back to replacing the whole document
        // rather than producing an invalid edit.
        edit.pos = 0;
        edit.removeLength = oldLen;
        edit.insertText = newText;
        return edit;
    }

    edit.pos = prefix;
    edit.removeLength = removeLength;
    if (insertLength > 0) {
        edit.insertText = newText.substr(static_cast<size_t>(prefix), static_cast<size_t>(insertLength));
    }
    return edit;
}

}  // namespace editor
