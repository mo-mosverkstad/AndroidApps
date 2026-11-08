#include <utility>

#include "editor/document.h"
#include "editor/history.h"
#include "test_framework.h"

using editor::EditType;
using editor::Memento;
using editor::PieceTableDocument;
using editor::Selection;
using testing::U;

namespace {

using History = editor::HistoryManager<PieceTableDocument, Memento>;

// Types `text` one character at a time, the way a real keyboard would.
void type(PieceTableDocument& doc, History& history, const editor::ustring& text, int32_t at) {
    int32_t caret = at;
    for (editor::uchar c : text) {
        const Selection before(caret);
        const Selection after(caret + 1);
        history.push(doc.insert(caret, editor::ustring(1, c)), EditType::Inserting, before, after);
        ++caret;
    }
}

}  // namespace

TEST(history_starts_empty) {
    History history;
    CHECK_FALSE(history.canUndo());
    CHECK_FALSE(history.canRedo());
    CHECK_EQ(history.revision(), 0u);
}

TEST(history_groups_a_run_of_typing_into_one_undo_step) {
    PieceTableDocument doc;
    History history;

    type(doc, history, U(u"hello"), 0);
    CHECK_EQ(doc.text(), U(u"hello"));
    CHECK_EQ(history.undoDepth(), 1u);

    Selection restored;
    CHECK(history.undo(doc, &restored));
    CHECK_EQ(doc.text(), U(u""));
    CHECK_FALSE(history.canUndo());

    // The caret goes back to where the run began, not to the end of the text.
    CHECK_EQ(restored, Selection(0));
}

TEST(history_splits_the_group_when_the_edit_direction_changes) {
    PieceTableDocument doc;
    History history;

    type(doc, history, U(u"abc"), 0);
    history.push(doc.erase(2, 1), EditType::Deleting, Selection(3), Selection(2));
    CHECK_EQ(doc.text(), U(u"ab"));
    CHECK_EQ(history.undoDepth(), 2u);

    Selection restored;
    CHECK(history.undo(doc, &restored));
    CHECK_EQ(doc.text(), U(u"abc"));

    CHECK(history.undo(doc, &restored));
    CHECK_EQ(doc.text(), U(u""));
}

TEST(history_finalize_closes_the_current_group) {
    PieceTableDocument doc;
    History history;

    type(doc, history, U(u"ab"), 0);
    history.finalize();
    type(doc, history, U(u"cd"), 2);
    CHECK_EQ(doc.text(), U(u"abcd"));
    CHECK_EQ(history.undoDepth(), 2u);

    Selection restored;
    history.undo(doc, &restored);
    CHECK_EQ(doc.text(), U(u"ab"));
}

// A transaction is what makes "type over a selection" a single undo step.
TEST(history_transaction_groups_a_delete_and_insert_into_one_step) {
    PieceTableDocument doc(U(u"hello world"));
    History history;

    const Selection before(0, 5);  // "hello" selected
    const Selection after(2);      // caret after typing "hi"

    history.beginTransaction();
    history.push(doc.erase(0, 5), EditType::Deleting, before, after);
    history.push(doc.insert(0, U(u"hi")), EditType::Inserting, before, after);
    history.commitTransaction();

    CHECK_EQ(doc.text(), U(u"hi world"));
    CHECK_EQ(history.undoDepth(), 1u);

    Selection restored;
    CHECK(history.undo(doc, &restored));
    CHECK_EQ(doc.text(), U(u"hello world"));
    CHECK_EQ(restored, before);
    CHECK_FALSE(history.canUndo());
}

TEST(history_redo_replays_a_transaction_in_order) {
    PieceTableDocument doc(U(u"hello world"));
    History history;

    history.beginTransaction();
    history.push(doc.erase(0, 5), EditType::Deleting, Selection(0, 5), Selection(2));
    history.push(doc.insert(0, U(u"hi")), EditType::Inserting, Selection(0, 5), Selection(2));
    history.commitTransaction();

    Selection restored;
    history.undo(doc, &restored);
    CHECK_EQ(doc.text(), U(u"hello world"));

    CHECK(history.redo(doc, &restored));
    CHECK_EQ(doc.text(), U(u"hi world"));
    CHECK_EQ(restored, Selection(2));

    // And it is undoable again, still as one step.
    CHECK(history.undo(doc, &restored));
    CHECK_EQ(doc.text(), U(u"hello world"));
}

TEST(history_undo_redo_round_trips_a_long_sequence) {
    PieceTableDocument doc;
    History history;

    type(doc, history, U(u"one"), 0);
    history.finalize();
    type(doc, history, U(u" two"), 3);
    history.finalize();
    type(doc, history, U(u" three"), 7);
    history.finalize();
    CHECK_EQ(doc.text(), U(u"one two three"));

    Selection sel;
    while (history.canUndo()) history.undo(doc, &sel);
    CHECK_EQ(doc.text(), U(u""));

    while (history.canRedo()) history.redo(doc, &sel);
    CHECK_EQ(doc.text(), U(u"one two three"));
}

TEST(history_a_new_edit_discards_the_redo_stack) {
    PieceTableDocument doc;
    History history;

    type(doc, history, U(u"abc"), 0);
    Selection sel;
    history.undo(doc, &sel);
    CHECK(history.canRedo());

    type(doc, history, U(u"z"), 0);
    CHECK_FALSE(history.canRedo());
    CHECK_EQ(doc.text(), U(u"z"));
}

// The revision number is what the dirty flag is built on: it names the current
// document state and is restored exactly when an edit is undone.
TEST(history_revision_identifies_the_document_state) {
    PieceTableDocument doc;
    History history;

    const uint64_t pristine = history.revision();

    type(doc, history, U(u"abc"), 0);
    history.finalize();
    const uint64_t afterFirst = history.revision();
    CHECK(afterFirst != pristine);

    type(doc, history, U(u"def"), 3);
    history.finalize();
    const uint64_t afterSecond = history.revision();
    CHECK(afterSecond != afterFirst);

    Selection sel;
    history.undo(doc, &sel);
    CHECK_EQ(history.revision(), afterFirst);

    history.undo(doc, &sel);
    CHECK_EQ(history.revision(), pristine);

    history.redo(doc, &sel);
    CHECK_EQ(history.revision(), afterFirst);

    history.redo(doc, &sel);
    CHECK_EQ(history.revision(), afterSecond);
}

TEST(history_revision_is_stable_across_finalize) {
    PieceTableDocument doc;
    History history;

    type(doc, history, U(u"ab"), 0);
    const uint64_t openRevision = history.revision();
    history.finalize();
    CHECK_EQ(history.revision(), openRevision);
}

TEST(history_undo_on_an_empty_stack_reports_failure) {
    PieceTableDocument doc(U(u"abc"));
    History history;

    Selection sel;
    CHECK_FALSE(history.undo(doc, &sel));
    CHECK_FALSE(history.redo(doc, &sel));
    CHECK_EQ(doc.text(), U(u"abc"));
}

TEST(history_respects_its_entry_cap) {
    PieceTableDocument doc;
    History history(8);

    for (int i = 0; i < 40; ++i) {
        const int32_t at = doc.length();
        Memento m = doc.insert(at, U(u"x"));
        history.push(std::move(m), EditType::Inserting, Selection(at), Selection(at + 1));
        history.finalize();
    }
    CHECK_EQ(doc.length(), 40);
    CHECK_EQ(history.undoDepth(), 8u);
}
