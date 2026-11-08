#include "editor/document.h"
#include "test_framework.h"

using editor::Memento;
using editor::PieceTableDocument;
using testing::U;

TEST(document_insert_produces_a_memento_that_undoes_it) {
    PieceTableDocument doc(U(u"hello"));
    const Memento m = doc.insert(5, U(u" world"));
    CHECK_EQ(doc.text(), U(u"hello world"));

    CHECK_EQ(m.pos, 5);
    CHECK_EQ(m.insertedLength, 6);
    CHECK(m.removed.empty());

    doc.apply(m);
    CHECK_EQ(doc.text(), U(u"hello"));
}

TEST(document_erase_produces_a_memento_that_undoes_it) {
    PieceTableDocument doc(U(u"hello world"));
    const Memento m = doc.erase(5, 6);
    CHECK_EQ(doc.text(), U(u"hello"));

    CHECK_EQ(m.pos, 5);
    CHECK_EQ(m.insertedLength, 0);
    CHECK_EQ(editor::totalLength(m.removed), 6);

    doc.apply(m);
    CHECK_EQ(doc.text(), U(u"hello world"));
}

TEST(document_apply_returns_a_working_inverse) {
    PieceTableDocument doc(U(u"abcdef"));
    const Memento edit = doc.erase(2, 2);
    CHECK_EQ(doc.text(), U(u"abef"));

    const Memento undoIt = doc.apply(edit);  // back to abcdef
    CHECK_EQ(doc.text(), U(u"abcdef"));

    const Memento redoIt = doc.apply(undoIt);  // forward again
    CHECK_EQ(doc.text(), U(u"abef"));

    doc.apply(redoIt);
    CHECK_EQ(doc.text(), U(u"abcdef"));
}

TEST(document_apply_round_trips_many_times) {
    PieceTableDocument doc(U(u"0123456789"));
    Memento m = doc.insert(5, U(u"xyz"));
    CHECK_EQ(doc.text(), U(u"01234xyz56789"));

    for (int i = 0; i < 25; ++i) {
        m = doc.apply(m);
        const bool shouldBeOriginal = (i % 2) == 0;
        CHECK_EQ(doc.text(), shouldBeOriginal ? U(u"0123456789") : U(u"01234xyz56789"));
    }
}

TEST(document_substr_and_length_track_the_text) {
    PieceTableDocument doc(U(u"the quick brown fox"));
    CHECK_EQ(doc.length(), 19);
    CHECK_EQ(doc.substr(4, 5), U(u"quick"));

    doc.erase(0, 4);
    CHECK_EQ(doc.length(), 15);
    CHECK_EQ(doc.substr(0, 5), U(u"quick"));
}
