#include "editor/editor_model.h"
#include "test_framework.h"

using editor::EditorModel;
using editor::Selection;
using editor::ustring;
using testing::U;

namespace {

// Types one character at a time through the public API, the way the Compose
// text field feeds whole-document updates in.
void typeAt(EditorModel& model, int32_t start, const ustring& text) {
    int32_t caret = start;
    for (editor::uchar c : text) {
        ustring body = model.snapshot().text;
        body.insert(static_cast<size_t>(caret), ustring(1, c));
        model.setText(body, Selection(caret + 1));
        ++caret;
    }
}

int64_t activeTabId(const EditorModel& model) {
    const editor::EditorSnapshot& s = model.snapshot();
    if (s.selectedIndex < 0) return 0;
    return s.tabs[static_cast<size_t>(s.selectedIndex)].id;
}

bool activeTabDirty(const EditorModel& model) {
    const editor::EditorSnapshot& s = model.snapshot();
    if (s.selectedIndex < 0) return false;
    return s.tabs[static_cast<size_t>(s.selectedIndex)].dirty;
}

}  // namespace

// ---------------------------------------------------------------------------
// baseline
// ---------------------------------------------------------------------------

TEST(model_starts_with_no_tabs) {
    EditorModel model;
    CHECK_EQ(model.tabCount(), 0);
    CHECK_EQ(model.snapshot().selectedIndex, -1);
    CHECK_EQ(model.snapshot().text, U(u""));
    CHECK_FALSE(model.snapshot().canUndo);
    CHECK_FALSE(model.snapshot().canRedo);
}

TEST(model_creates_and_selects_tabs) {
    EditorModel model;
    const int64_t first = model.createTab(U(u"one"), U(u"one.txt"));
    const int64_t second = model.createTab(U(u"two"), U(u"two.txt"));

    CHECK_EQ(model.tabCount(), 2);
    CHECK_EQ(model.snapshot().selectedIndex, 1);
    CHECK_EQ(model.snapshot().text, U(u"two"));

    CHECK(model.selectTab(first));
    CHECK_EQ(model.snapshot().selectedIndex, 0);
    CHECK_EQ(model.snapshot().text, U(u"one"));

    CHECK_FALSE(model.selectTab(99999));
    CHECK_EQ(model.snapshot().selectedIndex, 0);
    CHECK(second != first);
}

// A newly opened file puts the caret at the start, not at the end of the file.
TEST(model_opens_a_file_with_the_caret_at_the_start) {
    EditorModel model;
    model.createTab(U(u"hello world"), U(u"a.txt"));
    CHECK_EQ(model.snapshot().selection, Selection(0));
}

// ---------------------------------------------------------------------------
// BUG: typing over a selection used to need two presses of Undo
// ---------------------------------------------------------------------------

TEST(model_replacing_a_selection_is_a_single_undo_step) {
    EditorModel model;
    model.createTab(U(u"hello world"), U(u"a.txt"));
    model.markTabSaved(activeTabId(model));

    // Select "hello" and type "hi" over it.
    model.setSelection(Selection(0, 5));
    model.setText(U(u"hi world"), Selection(2));
    CHECK_EQ(model.snapshot().text, U(u"hi world"));
    CHECK_EQ(model.undoDepth(), 1u);

    CHECK(model.undo());
    CHECK_EQ(model.snapshot().text, U(u"hello world"));
    CHECK_FALSE(model.snapshot().canUndo);

    // And the selection comes back, not just the text.
    CHECK_EQ(model.snapshot().selection, Selection(0, 5));

    CHECK(model.redo());
    CHECK_EQ(model.snapshot().text, U(u"hi world"));
    CHECK_EQ(model.snapshot().selection, Selection(2));
}

TEST(model_replacing_the_whole_document_is_a_single_undo_step) {
    EditorModel model;
    model.createTab(U(u"aaaa"), U(u"a.txt"));

    model.setSelection(Selection(0, 4));
    model.setText(U(u"bbbb"), Selection(4));
    CHECK_EQ(model.undoDepth(), 1u);

    CHECK(model.undo());
    CHECK_EQ(model.snapshot().text, U(u"aaaa"));
}

// ---------------------------------------------------------------------------
// BUG: the caret jumped to the end of the document after undo/redo
// ---------------------------------------------------------------------------

TEST(model_undo_puts_the_caret_where_the_edit_happened) {
    EditorModel model;
    model.createTab(U(u"hello world"), U(u"a.txt"));

    // Type " there" after "hello".
    model.setSelection(Selection(5));
    typeAt(model, 5, U(u" there"));
    CHECK_EQ(model.snapshot().text, U(u"hello there world"));
    CHECK_EQ(model.snapshot().selection, Selection(11));

    CHECK(model.undo());
    CHECK_EQ(model.snapshot().text, U(u"hello world"));
    // Caret returns to the start of the typing run, not to offset 11.
    CHECK_EQ(model.snapshot().selection, Selection(5));

    CHECK(model.redo());
    CHECK_EQ(model.snapshot().text, U(u"hello there world"));
    CHECK_EQ(model.snapshot().selection, Selection(11));
}

TEST(model_undo_of_a_deletion_restores_the_caret) {
    EditorModel model;
    model.createTab(U(u"abcdef"), U(u"a.txt"));

    model.setSelection(Selection(2, 4));
    model.applyEdit(2, 2, U(u""), Selection(2));
    CHECK_EQ(model.snapshot().text, U(u"abef"));
    CHECK_EQ(model.snapshot().selection, Selection(2));

    CHECK(model.undo());
    CHECK_EQ(model.snapshot().text, U(u"abcdef"));
    CHECK_EQ(model.snapshot().selection, Selection(2, 4));
}

// ---------------------------------------------------------------------------
// BUG: switching tabs reset the caret to the end of the document
// ---------------------------------------------------------------------------

TEST(model_remembers_the_caret_per_tab) {
    EditorModel model;
    const int64_t a = model.createTab(U(u"aaaaaaaa"), U(u"a.txt"));
    const int64_t b = model.createTab(U(u"bbbbbbbb"), U(u"b.txt"));

    model.selectTab(a);
    model.setSelection(Selection(3));
    model.selectTab(b);
    model.setSelection(Selection(6, 7));

    model.selectTab(a);
    CHECK_EQ(model.snapshot().text, U(u"aaaaaaaa"));
    CHECK_EQ(model.snapshot().selection, Selection(3));

    model.selectTab(b);
    CHECK_EQ(model.snapshot().text, U(u"bbbbbbbb"));
    CHECK_EQ(model.snapshot().selection, Selection(6, 7));
}

TEST(model_keeps_each_tab_undo_history_separate) {
    EditorModel model;
    const int64_t a = model.createTab(U(u"a"), U(u"a.txt"));
    const int64_t b = model.createTab(U(u"b"), U(u"b.txt"));

    model.selectTab(a);
    typeAt(model, 1, U(u"XYZ"));
    CHECK_EQ(model.snapshot().text, U(u"aXYZ"));

    model.selectTab(b);
    CHECK_EQ(model.snapshot().text, U(u"b"));
    CHECK_FALSE(model.snapshot().canUndo);

    model.selectTab(a);
    CHECK(model.snapshot().canUndo);
    CHECK(model.undo());
    CHECK_EQ(model.snapshot().text, U(u"a"));
}

// ---------------------------------------------------------------------------
// BUG: undoing back to the saved state left the tab marked dirty
// ---------------------------------------------------------------------------

TEST(model_tab_is_clean_again_after_undoing_back_to_the_saved_state) {
    EditorModel model;
    const int64_t tab = model.createTab(U(u"hello"), U(u"a.txt"), U(u"content://a.txt"));
    CHECK_FALSE(activeTabDirty(model));

    typeAt(model, 5, U(u"!"));
    CHECK(activeTabDirty(model));

    model.markTabSaved(tab);
    CHECK_FALSE(activeTabDirty(model));

    typeAt(model, 6, U(u"?"));
    CHECK(activeTabDirty(model));

    CHECK(model.undo());
    CHECK_EQ(model.snapshot().text, U(u"hello!"));
    CHECK_FALSE(activeTabDirty(model));

    // Redoing moves away from the saved state again.
    CHECK(model.redo());
    CHECK(activeTabDirty(model));
}

TEST(model_undoing_past_the_saved_state_is_dirty_again) {
    EditorModel model;
    const int64_t tab = model.createTab(U(u"hello"), U(u"a.txt"));

    typeAt(model, 5, U(u" one"));
    model.finalizeEdits();
    typeAt(model, 9, U(u" two"));
    model.markTabSaved(tab);
    CHECK_FALSE(activeTabDirty(model));

    CHECK(model.undo());
    CHECK_EQ(model.snapshot().text, U(u"hello one"));
    CHECK(activeTabDirty(model));
}

// ---------------------------------------------------------------------------
// BUG: closing a tab leaked its document and undo history
// ---------------------------------------------------------------------------

TEST(model_closing_a_tab_frees_its_document) {
    EditorModel model;
    const int64_t a = model.createTab(U(u"one"), U(u"one.txt"));
    const int64_t b = model.createTab(U(u"two"), U(u"two.txt"));
    CHECK_EQ(model.documentCount(), 2u);

    CHECK(model.closeTab(a));
    CHECK_EQ(model.documentCount(), 1u);
    CHECK_EQ(model.tabCount(), 1);

    CHECK(model.closeTab(b));
    CHECK_EQ(model.documentCount(), 0u);
    CHECK_EQ(model.tabCount(), 0);
    CHECK_EQ(model.snapshot().selectedIndex, -1);
    CHECK_EQ(model.snapshot().text, U(u""));
}

TEST(model_closing_an_unknown_tab_changes_nothing) {
    EditorModel model;
    model.createTab(U(u"one"), U(u"one.txt"));
    CHECK_FALSE(model.closeTab(4242));
    CHECK_EQ(model.tabCount(), 1);
}

TEST(model_close_keeps_a_sensible_tab_selected) {
    EditorModel model;
    const int64_t a = model.createTab(U(u"a"), U(u"a.txt"));
    model.createTab(U(u"b"), U(u"b.txt"));
    const int64_t c = model.createTab(U(u"c"), U(u"c.txt"));

    model.selectTab(c);
    CHECK_EQ(model.snapshot().selectedIndex, 2);

    // Closing a tab before the active one shifts the selection with it.
    CHECK(model.closeTab(a));
    CHECK_EQ(model.snapshot().selectedIndex, 1);
    CHECK_EQ(model.snapshot().text, U(u"c"));

    // Closing the active last tab falls back to the new last tab.
    CHECK(model.closeTab(c));
    CHECK_EQ(model.snapshot().selectedIndex, 0);
    CHECK_EQ(model.snapshot().text, U(u"b"));
}

// ---------------------------------------------------------------------------
// BUG: editing with no tabs open threw instead of being a no-op
// ---------------------------------------------------------------------------

TEST(model_edit_operations_are_safe_with_no_tabs) {
    EditorModel model;

    CHECK_FALSE(model.undo());
    CHECK_FALSE(model.redo());
    CHECK_FALSE(model.setText(U(u"anything")));
    CHECK_FALSE(model.setSelection(Selection(5)));
    CHECK_FALSE(model.applyEdit(0, 0, U(u"x")));
    CHECK_FALSE(model.markTabSaved(1));
    CHECK_FALSE(model.setTabFile(1, U(u"x"), U(u"y")));
    model.finalizeEdits();  // must not throw

    CHECK_EQ(model.activeText(), U(u""));
    CHECK_EQ(model.tabCount(), 0);
}

TEST(model_rejects_out_of_range_edits) {
    EditorModel model;
    model.createTab(U(u"abc"), U(u"a.txt"));

    CHECK_FALSE(model.applyEdit(4, 0, U(u"x")));
    CHECK_FALSE(model.applyEdit(-1, 0, U(u"x")));
    CHECK_FALSE(model.applyEdit(0, 4, U(u"")));
    CHECK_FALSE(model.applyEdit(2, 2, U(u"")));
    CHECK_FALSE(model.applyEdit(0, 0, U(u"")));  // nothing to do

    CHECK_EQ(model.snapshot().text, U(u"abc"));
    CHECK_FALSE(model.snapshot().canUndo);
}

// ---------------------------------------------------------------------------
// undo grouping
// ---------------------------------------------------------------------------

TEST(model_groups_a_continuous_typing_run) {
    EditorModel model;
    model.createTab(U(u""), U(u"a.txt"));

    typeAt(model, 0, U(u"hello"));
    CHECK_EQ(model.snapshot().text, U(u"hello"));
    CHECK_EQ(model.undoDepth(), 1u);

    CHECK(model.undo());
    CHECK_EQ(model.snapshot().text, U(u""));
}

TEST(model_starts_a_new_undo_group_after_the_caret_jumps) {
    EditorModel model;
    model.createTab(U(u"....."), U(u"a.txt"));

    model.setSelection(Selection(0));
    typeAt(model, 0, U(u"ab"));
    CHECK_EQ(model.snapshot().text, U(u"ab....."));

    // Click elsewhere, then keep typing.
    model.setSelection(Selection(7));
    typeAt(model, 7, U(u"cd"));
    CHECK_EQ(model.snapshot().text, U(u"ab.....cd"));

    CHECK_EQ(model.undoDepth(), 2u);
    CHECK(model.undo());
    CHECK_EQ(model.snapshot().text, U(u"ab....."));
    CHECK(model.undo());
    CHECK_EQ(model.snapshot().text, U(u"....."));
}

TEST(model_groups_a_run_of_backspaces) {
    EditorModel model;
    model.createTab(U(u"abcdef"), U(u"a.txt"));
    model.setSelection(Selection(6));

    // Backspace three times.
    model.applyEdit(5, 1, U(u""), Selection(5));
    model.applyEdit(4, 1, U(u""), Selection(4));
    model.applyEdit(3, 1, U(u""), Selection(3));
    CHECK_EQ(model.snapshot().text, U(u"abc"));
    CHECK_EQ(model.undoDepth(), 1u);

    CHECK(model.undo());
    CHECK_EQ(model.snapshot().text, U(u"abcdef"));
    CHECK_EQ(model.snapshot().selection, Selection(6));
}

TEST(model_splits_the_group_when_typing_turns_into_deleting) {
    EditorModel model;
    model.createTab(U(u""), U(u"a.txt"));

    typeAt(model, 0, U(u"abc"));
    model.applyEdit(2, 1, U(u""), Selection(2));
    CHECK_EQ(model.snapshot().text, U(u"ab"));
    CHECK_EQ(model.undoDepth(), 2u);

    CHECK(model.undo());
    CHECK_EQ(model.snapshot().text, U(u"abc"));
    CHECK(model.undo());
    CHECK_EQ(model.snapshot().text, U(u""));
}

TEST(model_finalize_closes_the_current_undo_group) {
    EditorModel model;
    model.createTab(U(u""), U(u"a.txt"));

    typeAt(model, 0, U(u"ab"));
    model.finalizeEdits();
    typeAt(model, 2, U(u"cd"));
    CHECK_EQ(model.undoDepth(), 2u);
}

// ---------------------------------------------------------------------------
// files and text handling
// ---------------------------------------------------------------------------

TEST(model_tracks_the_file_a_tab_points_at) {
    EditorModel model;
    const int64_t tab = model.createTab(U(u"x"), U(u"untitled.txt"));

    CHECK_FALSE(model.snapshot().tabs[0].hasPath);

    CHECK(model.setTabFile(tab, U(u"notes.txt"), U(u"content://docs/1")));
    CHECK(model.snapshot().tabs[0].hasPath);
    CHECK_EQ(model.snapshot().tabs[0].fileName, U(u"notes.txt"));
    CHECK_EQ(model.snapshot().tabs[0].filePath, U(u"content://docs/1"));
}

TEST(model_reports_unsaved_changes_across_tabs) {
    EditorModel model;
    model.createTab(U(u"a"), U(u"a.txt"));
    const int64_t b = model.createTab(U(u"b"), U(u"b.txt"));
    CHECK_FALSE(model.hasUnsavedChanges());

    typeAt(model, 1, U(u"!"));
    CHECK(model.hasUnsavedChanges());

    model.markTabSaved(b);
    CHECK_FALSE(model.hasUnsavedChanges());
}

TEST(model_set_text_with_unchanged_body_only_moves_the_caret) {
    EditorModel model;
    model.createTab(U(u"hello"), U(u"a.txt"));

    CHECK(model.setText(U(u"hello"), Selection(3)));
    CHECK_EQ(model.snapshot().selection, Selection(3));
    CHECK_FALSE(model.snapshot().canUndo);

    CHECK_FALSE(model.setText(U(u"hello"), Selection(3)));
}

TEST(model_handles_astral_characters_without_shifting_offsets) {
    EditorModel model;
    model.createTab(U(u"a\U0001F600b"), U(u"a.txt"));
    CHECK_EQ(model.snapshot().text, U(u"a\U0001F600b"));

    // The emoji occupies offsets 1..3, exactly as Kotlin would index it.
    model.setSelection(Selection(1, 3));
    model.setText(U(u"aXb"), Selection(2));
    CHECK_EQ(model.snapshot().text, U(u"aXb"));
    CHECK_EQ(model.undoDepth(), 1u);

    CHECK(model.undo());
    CHECK_EQ(model.snapshot().text, U(u"a\U0001F600b"));
    CHECK_EQ(model.snapshot().selection, Selection(1, 3));
}

TEST(model_survives_a_long_editing_session) {
    EditorModel model;
    model.createTab(U(u""), U(u"a.txt"));

    for (int32_t i = 0; i < 500; ++i) {
        ustring body = model.snapshot().text;
        body.append(U(u"line\n"));
        model.setText(body, Selection(static_cast<int32_t>(body.size())));
    }
    CHECK_EQ(static_cast<int32_t>(model.snapshot().text.size()), 2500);

    int undos = 0;
    while (model.snapshot().canUndo) {
        model.undo();
        ++undos;
    }
    CHECK(undos > 0);
    CHECK_EQ(model.snapshot().text, U(u""));

    while (model.snapshot().canRedo) model.redo();
    CHECK_EQ(static_cast<int32_t>(model.snapshot().text.size()), 2500);
}
