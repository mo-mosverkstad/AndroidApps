#include "editor/text_diff.h"
#include "test_framework.h"

using editor::diffTexts;
using editor::TextEdit;
using editor::ustring;
using testing::U;

namespace {

// Applies an edit the way the document would, so every case can be checked
// end to end rather than just on its fields.
ustring applyTo(const ustring& text, const TextEdit& edit) {
    ustring out = text;
    out.erase(static_cast<size_t>(edit.pos), static_cast<size_t>(edit.removeLength));
    out.insert(static_cast<size_t>(edit.pos), edit.insertText);
    return out;
}

}  // namespace

TEST(diff_reports_nothing_for_identical_text) {
    const TextEdit edit = diffTexts(U(u"hello"), U(u"hello"));
    CHECK(edit.empty());
}

TEST(diff_finds_a_single_typed_character) {
    const TextEdit edit = diffTexts(U(u"helo"), U(u"hello"));
    CHECK_EQ(edit.pos, 3);
    CHECK_EQ(edit.removeLength, 0);
    CHECK_EQ(edit.insertText, U(u"l"));
    CHECK_EQ(applyTo(U(u"helo"), edit), U(u"hello"));
}

TEST(diff_finds_an_append) {
    const TextEdit edit = diffTexts(U(u"ab"), U(u"abcd"));
    CHECK_EQ(edit.pos, 2);
    CHECK_EQ(edit.removeLength, 0);
    CHECK_EQ(edit.insertText, U(u"cd"));
}

TEST(diff_finds_a_prepend) {
    const TextEdit edit = diffTexts(U(u"cd"), U(u"abcd"));
    CHECK_EQ(edit.pos, 0);
    CHECK_EQ(edit.removeLength, 0);
    CHECK_EQ(edit.insertText, U(u"ab"));
}

TEST(diff_finds_a_backspace) {
    const TextEdit edit = diffTexts(U(u"hello"), U(u"hell"));
    CHECK_EQ(edit.pos, 4);
    CHECK_EQ(edit.removeLength, 1);
    CHECK(edit.insertText.empty());
}

TEST(diff_finds_a_deletion_in_the_middle) {
    const TextEdit edit = diffTexts(U(u"abcdef"), U(u"abef"));
    CHECK_EQ(edit.pos, 2);
    CHECK_EQ(edit.removeLength, 2);
    CHECK(edit.insertText.empty());
}

TEST(diff_finds_a_replacement) {
    const TextEdit edit = diffTexts(U(u"hello world"), U(u"hi world"));
    CHECK_EQ(edit.pos, 1);
    CHECK_EQ(edit.removeLength, 4);
    CHECK_EQ(edit.insertText, U(u"i"));
    CHECK_EQ(applyTo(U(u"hello world"), edit), U(u"hi world"));
}

TEST(diff_handles_clearing_the_document) {
    const TextEdit edit = diffTexts(U(u"hello"), U(u""));
    CHECK_EQ(edit.pos, 0);
    CHECK_EQ(edit.removeLength, 5);
    CHECK(edit.insertText.empty());
}

TEST(diff_handles_filling_an_empty_document) {
    const TextEdit edit = diffTexts(U(u""), U(u"hello"));
    CHECK_EQ(edit.pos, 0);
    CHECK_EQ(edit.removeLength, 0);
    CHECK_EQ(edit.insertText, U(u"hello"));
}

TEST(diff_handles_repeated_characters) {
    // "aaa" -> "aaaa": any single-character insert is correct, the result is
    // what matters.
    const TextEdit edit = diffTexts(U(u"aaa"), U(u"aaaa"));
    CHECK_EQ(edit.removeLength, 0);
    CHECK_EQ(static_cast<int32_t>(edit.insertText.size()), 1);
    CHECK_EQ(applyTo(U(u"aaa"), edit), U(u"aaaa"));
}

TEST(diff_does_not_split_a_surrogate_pair) {
    const ustring grinning = U(u"\U0001F600");  // D83D DE00
    const ustring heart = U(u"\U0001F496");     // D83D DC96

    // Both start with the same high surrogate, so a naive prefix match would
    // stop between the halves of the pair.
    const TextEdit edit = diffTexts(grinning, heart);
    CHECK_EQ(edit.pos, 0);
    CHECK_EQ(applyTo(grinning, edit), heart);

    // The boundary must not land inside the pair.
    CHECK_FALSE(editor::isLowSurrogate(grinning[static_cast<size_t>(edit.pos)]));
}

TEST(diff_handles_typing_after_an_emoji) {
    const ustring before = U(u"hi \U0001F600");
    const ustring after = U(u"hi \U0001F600!");
    const TextEdit edit = diffTexts(before, after);
    CHECK_EQ(edit.removeLength, 0);
    CHECK_EQ(edit.insertText, U(u"!"));
    CHECK_EQ(applyTo(before, edit), after);
}

TEST(diff_handles_deleting_an_emoji) {
    const ustring before = U(u"a\U0001F600b");
    const ustring after = U(u"ab");
    const TextEdit edit = diffTexts(before, after);
    CHECK_EQ(edit.pos, 1);
    CHECK_EQ(edit.removeLength, 2);
    CHECK_EQ(applyTo(before, edit), after);
}
