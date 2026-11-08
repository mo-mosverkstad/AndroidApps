#include <stdexcept>
#include <string>
#include <vector>

#include "editor/piece_table.h"
#include "test_framework.h"

using editor::Piece;
using editor::PieceTable;
using editor::ustring;
using testing::U;

namespace {

// Deterministic PRNG so a fuzz failure is always reproducible.
struct Rng {
    uint32_t state = 12345u;
    uint32_t next() {
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        return state;
    }
    int32_t below(int32_t n) { return n <= 0 ? 0 : static_cast<int32_t>(next() % static_cast<uint32_t>(n)); }
};

}  // namespace

TEST(piece_table_starts_empty) {
    PieceTable pt;
    CHECK_EQ(pt.length(), 0);
    CHECK_EQ(pt.text(), U(u""));
    CHECK_EQ(pt.pieceCount(), 0);
}

TEST(piece_table_holds_initial_text) {
    PieceTable pt(U(u"hello"));
    CHECK_EQ(pt.length(), 5);
    CHECK_EQ(pt.text(), U(u"hello"));
    CHECK_EQ(pt.originalBufferSize(), 5);
    CHECK_EQ(pt.addedBufferSize(), 0);
}

TEST(piece_table_inserts_at_start_middle_and_end) {
    PieceTable pt(U(u"bcd"));
    pt.insert(0, U(u"a"));
    CHECK_EQ(pt.text(), U(u"abcd"));
    pt.insert(4, U(u"e"));
    CHECK_EQ(pt.text(), U(u"abcde"));
    pt.insert(2, U(u"XY"));
    CHECK_EQ(pt.text(), U(u"abXYcde"));
    CHECK_EQ(pt.length(), 7);
}

TEST(piece_table_inserting_empty_text_is_a_noop) {
    PieceTable pt(U(u"abc"));
    pt.insert(1, U(u""));
    CHECK_EQ(pt.text(), U(u"abc"));
    CHECK_EQ(pt.addedBufferSize(), 0);
}

TEST(piece_table_erases_a_range) {
    PieceTable pt(U(u"hello world"));
    const std::vector<Piece> removed = pt.erase(5, 6);
    CHECK_EQ(pt.text(), U(u"hello"));
    CHECK_EQ(editor::totalLength(removed), 6);
}

TEST(piece_table_erase_spanning_many_pieces_returns_them_in_order) {
    PieceTable pt(U(u"AF"));
    pt.insert(1, U(u"E"));
    pt.insert(1, U(u"D"));
    pt.insert(1, U(u"C"));
    pt.insert(1, U(u"B"));
    CHECK_EQ(pt.text(), U(u"ABCDEF"));

    const std::vector<Piece> removed = pt.erase(1, 4);
    CHECK_EQ(pt.text(), U(u"AF"));
    CHECK_EQ(editor::totalLength(removed), 4);

    // Splicing them back in the order they were returned must reproduce the
    // original text, which is what undo relies on.
    pt.insertPieces(1, removed);
    CHECK_EQ(pt.text(), U(u"ABCDEF"));
}

// This is the behaviour that stops the added buffer growing without bound.
// The Kotlin implementation copied every deleted range back into the added
// buffer so that undo could re-insert it, which meant memory grew on deletes
// as well as inserts.
TEST(piece_table_erase_does_not_copy_text_into_the_added_buffer) {
    PieceTable pt(U(u"hello world"));
    CHECK_EQ(pt.addedBufferSize(), 0);

    const std::vector<Piece> removed = pt.erase(0, 6);
    CHECK_EQ(pt.text(), U(u"world"));
    CHECK_EQ(pt.addedBufferSize(), 0);

    pt.insertPieces(0, removed);
    CHECK_EQ(pt.text(), U(u"hello world"));
    CHECK_EQ(pt.addedBufferSize(), 0);
}

TEST(piece_table_insert_pieces_restores_exact_text) {
    PieceTable pt(U(u"one two three"));
    const std::vector<Piece> removed = pt.erase(4, 4);
    CHECK_EQ(pt.text(), U(u"one three"));
    pt.insertPieces(4, removed);
    CHECK_EQ(pt.text(), U(u"one two three"));
}

TEST(piece_table_substr_reads_across_piece_boundaries) {
    PieceTable pt(U(u"ad"));
    pt.insert(1, U(u"c"));
    pt.insert(1, U(u"b"));
    CHECK_EQ(pt.text(), U(u"abcd"));

    CHECK_EQ(pt.substr(0, 4), U(u"abcd"));
    CHECK_EQ(pt.substr(1, 2), U(u"bc"));
    CHECK_EQ(pt.substr(0, 0), U(u""));
    CHECK_EQ(pt.substr(4, 0), U(u""));
    CHECK_EQ(pt.substr(3, 1), U(u"d"));
}

// The Kotlin version silently clamped out-of-range positions, so an
// off-by-one in a caller corrupted the document instead of failing.
TEST(piece_table_rejects_out_of_range_positions) {
    PieceTable pt(U(u"abc"));

    CHECK_THROWS(pt.insert(4, U(u"x")), std::out_of_range);
    CHECK_THROWS(pt.insert(-1, U(u"x")), std::out_of_range);
    CHECK_THROWS(pt.erase(0, 4), std::out_of_range);
    CHECK_THROWS(pt.erase(3, 1), std::out_of_range);
    CHECK_THROWS(pt.erase(-1, 1), std::out_of_range);
    CHECK_THROWS(pt.erase(1, -1), std::out_of_range);
    CHECK_THROWS(pt.substr(2, 2), std::out_of_range);
    CHECK_THROWS(pt.insertPieces(9, std::vector<Piece>{}), std::out_of_range);

    // Nothing above should have modified the document.
    CHECK_EQ(pt.text(), U(u"abc"));
}

TEST(piece_table_handles_astral_characters_as_surrogate_pairs) {
    // U+1F600 GRINNING FACE is two UTF-16 units, matching how Kotlin and
    // Compose count offsets.
    const ustring emoji = U(u"\U0001F600");
    CHECK_EQ(static_cast<int32_t>(emoji.size()), 2);

    PieceTable pt(U(u"ab"));
    pt.insert(1, emoji);
    CHECK_EQ(pt.length(), 4);
    CHECK_EQ(pt.substr(1, 2), emoji);
    CHECK_EQ(pt.text(), U(u"a\U0001F600b"));
}

TEST(piece_table_stays_balanced_after_many_mid_piece_splits) {
    // Repeatedly inserting into the middle forces the mid-piece split path.
    // With the Kotlin version's fresh random priorities this could violate the
    // heap property and let the tree degenerate.
    PieceTable pt;
    for (int32_t i = 0; i < 2000; ++i) {
        pt.insert(pt.length() / 2, U(u"x"));
    }
    CHECK_EQ(pt.length(), 2000);

    const int32_t height = pt.treeHeight();
    CHECK(height > 0);
    CHECK(height < 80);  // a degenerate tree would be in the thousands
}

TEST(piece_table_matches_a_reference_string_under_random_edits) {
    PieceTable pt;
    ustring reference;
    Rng rng;

    for (int step = 0; step < 4000; ++step) {
        const int32_t len = static_cast<int32_t>(reference.size());
        const bool doInsert = len == 0 || (rng.next() % 3u) != 0u;

        if (doInsert) {
            const int32_t pos = rng.below(len + 1);
            const int32_t count = 1 + rng.below(6);
            ustring chunk;
            for (int32_t i = 0; i < count; ++i) {
                chunk.push_back(static_cast<editor::uchar>(u'a' + rng.below(26)));
            }
            pt.insert(pos, chunk);
            reference.insert(static_cast<size_t>(pos), chunk);
        } else {
            const int32_t pos = rng.below(len);
            const int32_t count = 1 + rng.below(len - pos);
            pt.erase(pos, count);
            reference.erase(static_cast<size_t>(pos), static_cast<size_t>(count));
        }

        CHECK_EQ(pt.length(), static_cast<int32_t>(reference.size()));
    }

    CHECK_EQ(pt.text(), reference);

    // Spot-check substr against the reference too.
    if (!reference.empty()) {
        const int32_t pos = rng.below(static_cast<int32_t>(reference.size()));
        const int32_t count = rng.below(static_cast<int32_t>(reference.size()) - pos);
        CHECK_EQ(pt.substr(pos, count),
                 reference.substr(static_cast<size_t>(pos), static_cast<size_t>(count)));
    }
}

TEST(piece_table_survives_a_large_document) {
    // Guards against the recursive traversals the Kotlin version used, which
    // could overflow the stack on a big or lopsided tree.
    ustring big(200000, u'z');
    PieceTable pt(big);
    CHECK_EQ(pt.length(), 200000);

    for (int32_t i = 0; i < 5000; ++i) {
        pt.insert(i * 2, U(u"q"));
    }
    CHECK_EQ(pt.length(), 205000);
    CHECK_EQ(static_cast<int32_t>(pt.text().size()), 205000);
}
