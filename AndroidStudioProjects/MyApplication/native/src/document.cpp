#include "editor/document.h"

#include <utility>

namespace editor {

PieceTableDocument::PieceTableDocument(ustring initial) : table_(std::move(initial)) {}

int32_t PieceTableDocument::length() const { return table_.length(); }

ustring PieceTableDocument::text() const { return table_.text(); }

ustring PieceTableDocument::substr(int32_t pos, int32_t len) const {
    return table_.substr(pos, len);
}

Memento PieceTableDocument::insert(int32_t pos, const ustring& text) {
    table_.insert(pos, text);

    Memento m;
    m.pos = pos;
    m.insertedLength = static_cast<int32_t>(text.size());
    return m;  // undo = erase what we just inserted
}

Memento PieceTableDocument::erase(int32_t pos, int32_t len) {
    Memento m;
    m.pos = pos;
    m.removed = table_.erase(pos, len);
    m.insertedLength = 0;
    return m;  // undo = splice the removed pieces back
}

Memento PieceTableDocument::apply(const Memento& m) {
    std::vector<Piece> justRemoved;

    if (m.insertedLength > 0) {
        justRemoved = table_.erase(m.pos, m.insertedLength);
    }
    if (!m.removed.empty()) {
        table_.insertPieces(m.pos, m.removed);
    }

    Memento inverse;
    inverse.pos = m.pos;
    inverse.removed = std::move(justRemoved);
    inverse.insertedLength = totalLength(m.removed);
    return inverse;
}

}  // namespace editor
