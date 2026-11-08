#ifndef EDITOR_PIECE_TABLE_H
#define EDITOR_PIECE_TABLE_H

#include <cstdint>
#include <vector>

#include "editor/types.h"

namespace editor {

// A piece table whose piece sequence is held in an implicit treap keyed by
// cumulative character length, giving expected O(log n) insert/erase.
//
// Two buffers: `original` (the opened text, immutable) and `added`
// (append-only, holds everything inserted since).
//
// Unlike the Kotlin version this was ported from, erase() does NOT copy the
// removed text back into the added buffer. It returns the exact Piece list it
// detached, which insertPieces() can splice back verbatim. That keeps undo
// zero-copy and stops the added buffer from growing on every deletion.
class PieceTable {
public:
    explicit PieceTable(ustring initial = ustring());
    ~PieceTable();

    PieceTable(const PieceTable&) = delete;
    PieceTable& operator=(const PieceTable&) = delete;
    PieceTable(PieceTable&& other) noexcept;
    PieceTable& operator=(PieceTable&& other) noexcept;

    int32_t length() const;

    // Materialises the whole document. O(n).
    ustring text() const;

    // Materialises [pos, pos + len). Throws std::out_of_range when out of bounds.
    ustring substr(int32_t pos, int32_t len) const;

    // Appends `text` to the added buffer and splices it in at `pos`.
    // Throws std::out_of_range when pos is outside [0, length()].
    void insert(int32_t pos, const ustring& text);

    // Detaches [pos, pos + len) and returns the pieces that covered it, in
    // document order. Throws std::out_of_range when the range is invalid.
    std::vector<Piece> erase(int32_t pos, int32_t len);

    // Splices previously detached pieces back in at `pos`, in order. No text
    // is copied: the pieces still point into the existing buffers.
    void insertPieces(int32_t pos, const std::vector<Piece>& pieces);

    // --- diagnostics, used by the tests ---------------------------------
    std::vector<Piece> pieces() const;
    int32_t pieceCount() const;
    int32_t originalBufferSize() const;
    int32_t addedBufferSize() const;
    int32_t treeHeight() const;

private:
    struct Node;

    static int32_t subtreeLength(Node* n);
    static void recalc(Node* n);
    static Node* merge(Node* a, Node* b);
    static void split(Node* node, int32_t index, Node** outLeft, Node** outRight);
    static void destroy(Node* n);
    static void collect(Node* n, std::vector<Piece>& out);
    static int32_t heightOf(Node* n);

    Node* makeNode(const Piece& p);
    uint32_t nextPriority();
    void appendPieceText(const Piece& p, ustring& out) const;
    void checkPosition(int32_t pos) const;
    void checkRange(int32_t pos, int32_t len) const;

    ustring original_;
    ustring added_;
    Node* root_ = nullptr;

    // Deterministic PRNG so that a failing test is reproducible. The treap
    // only needs priorities that are uncorrelated with insertion order.
    uint32_t rngState_ = 0x9E3779B9u;
};

}  // namespace editor

#endif  // EDITOR_PIECE_TABLE_H
