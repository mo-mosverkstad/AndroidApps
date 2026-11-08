#ifndef EDITOR_DOCUMENT_H
#define EDITOR_DOCUMENT_H

#include <cstdint>
#include <vector>

#include "editor/piece_table.h"
#include "editor/types.h"

namespace editor {

// One reversible change to a document.
//
// Reading it as an instruction: "erase `insertedLength` characters at `pos`,
// then splice `removed` back in at `pos`". Applying a Memento therefore undoes
// the edit that produced it, and apply() hands back the Memento that undoes
// the undo. One operation serves both directions.
//
// `removed` holds Pieces rather than text, so undoing a deletion re-splices
// characters that are already in the buffers instead of copying them again.
struct Memento {
    int32_t pos = 0;
    std::vector<Piece> removed;
    int32_t insertedLength = 0;

    bool empty() const { return insertedLength == 0 && removed.empty(); }
};

class PieceTableDocument {
public:
    explicit PieceTableDocument(ustring initial = ustring());

    PieceTableDocument(const PieceTableDocument&) = delete;
    PieceTableDocument& operator=(const PieceTableDocument&) = delete;

    int32_t length() const;
    ustring text() const;
    ustring substr(int32_t pos, int32_t len) const;

    Memento insert(int32_t pos, const ustring& text);
    Memento erase(int32_t pos, int32_t len);

    // Applies `m` and returns its inverse.
    Memento apply(const Memento& m);

    const PieceTable& table() const { return table_; }

private:
    PieceTable table_;
};

}  // namespace editor

#endif  // EDITOR_DOCUMENT_H
