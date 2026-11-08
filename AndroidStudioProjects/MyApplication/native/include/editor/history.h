#ifndef EDITOR_HISTORY_H
#define EDITOR_HISTORY_H

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <utility>
#include <vector>

#include "editor/types.h"

namespace editor {

enum class EditType {
    Inserting,
    Deleting,
    Other
};

// Undo/redo over any document exposing `Memento apply(const Memento&)` that
// returns the inverse of what it applied (see PieceTableDocument).
//
// Three things it does that the Kotlin original did not:
//
//  * Transactions. beginTransaction()/commitTransaction() force everything
//    pushed between them into a single undo entry regardless of edit type.
//    That is what makes "type over a selection" one undo step instead of two.
//
//  * Selection tracking. Each entry records where the caret was before and
//    after, so undo can put the caret back where the edit happened rather
//    than leaving the caller to guess.
//
//  * Stable entry identity. Every entry carries an id that survives being
//    moved between the undo and redo stacks, so revision() names the current
//    document state. Comparing it against the revision captured at save time
//    gives a dirty flag that correctly becomes clean again when the user
//    undoes back to the saved state.
template <class Doc, class MementoT>
class HistoryManager {
public:
    struct Batch {
        uint64_t id = 0;
        std::vector<MementoT> items;
        Selection before;
        Selection after;
    };

    explicit HistoryManager(std::size_t maxEntries = 4096) : maxEntries_(maxEntries) {}

    bool canUndo() const { return !undo_.empty() || !open_.items.empty(); }
    bool canRedo() const { return !redo_.empty(); }

    std::size_t undoDepth() const { return undo_.size() + (open_.items.empty() ? 0u : 1u); }
    std::size_t redoDepth() const { return redo_.size(); }

    // Identifies the current document state for dirty tracking. 0 means
    // "as it was created". Stable across finalize(), and restored exactly
    // when an edit is undone.
    uint64_t revision() const {
        if (!open_.items.empty()) return open_.id;
        return undo_.empty() ? 0u : undo_.back().id;
    }

    bool inTransaction() const { return inTransaction_; }

    void beginTransaction() {
        finalize();
        inTransaction_ = true;
    }

    void commitTransaction() {
        inTransaction_ = false;
        finalize();
    }

    void push(MementoT m, EditType type, Selection before, Selection after) {
        if (!inTransaction_ && !shouldMerge(type)) finalize();

        if (open_.items.empty()) {
            open_.id = ++nextId_;
            open_.before = before;
        }
        open_.items.push_back(std::move(m));
        open_.after = after;

        lastType_ = type;
        hasLastType_ = true;
        redo_.clear();
    }

    // Seals the open batch so that the next edit starts a new undo step.
    void finalize() {
        if (!open_.items.empty()) {
            undo_.push_back(std::move(open_));
            trim();
        }
        open_ = Batch();
        hasLastType_ = false;
        lastType_ = EditType::Other;
    }

    bool undo(Doc& doc, Selection* outSelection) {
        finalize();
        if (undo_.empty()) return false;

        Batch batch = std::move(undo_.back());
        undo_.pop_back();

        Batch inverse;
        inverse.id = batch.id;
        inverse.before = batch.before;
        inverse.after = batch.after;
        inverse.items.reserve(batch.items.size());

        // Undo in reverse order, then store the inverses in forward order so
        // redo() can replay them chronologically.
        for (auto it = batch.items.rbegin(); it != batch.items.rend(); ++it) {
            inverse.items.push_back(doc.apply(*it));
        }
        std::reverse(inverse.items.begin(), inverse.items.end());

        redo_.push_back(std::move(inverse));
        if (outSelection) *outSelection = batch.before;
        return true;
    }

    bool redo(Doc& doc, Selection* outSelection) {
        if (redo_.empty()) return false;

        Batch batch = std::move(redo_.back());
        redo_.pop_back();

        Batch inverse;
        inverse.id = batch.id;
        inverse.before = batch.before;
        inverse.after = batch.after;
        inverse.items.reserve(batch.items.size());

        for (const MementoT& m : batch.items) {
            inverse.items.push_back(doc.apply(m));
        }

        undo_.push_back(std::move(inverse));
        if (outSelection) *outSelection = batch.after;
        return true;
    }

    void clear() {
        undo_.clear();
        redo_.clear();
        open_ = Batch();
        hasLastType_ = false;
        lastType_ = EditType::Other;
        inTransaction_ = false;
    }

private:
    bool shouldMerge(EditType type) const {
        if (open_.items.empty()) return true;
        if (type == EditType::Other) return false;
        return hasLastType_ && lastType_ == type;
    }

    void trim() {
        while (maxEntries_ > 0 && undo_.size() > maxEntries_) undo_.pop_front();
    }

    std::deque<Batch> undo_;
    std::deque<Batch> redo_;
    Batch open_;

    EditType lastType_ = EditType::Other;
    bool hasLastType_ = false;
    bool inTransaction_ = false;
    uint64_t nextId_ = 0;
    std::size_t maxEntries_;
};

}  // namespace editor

#endif  // EDITOR_HISTORY_H
