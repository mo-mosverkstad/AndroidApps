#ifndef EDITOR_EDITOR_MODEL_H
#define EDITOR_EDITOR_MODEL_H

#include <cstdint>
#include <memory>
#include <optional>
#include <unordered_map>
#include <vector>

#include "editor/document.h"
#include "editor/history.h"
#include "editor/text_diff.h"
#include "editor/types.h"

namespace editor {

struct TabInfo {
    int64_t id = 0;
    ustring fileName;
    ustring filePath;     // meaningful only when hasPath is true
    bool hasPath = false;
    bool dirty = false;
};

// Immutable view of everything the UI needs to draw a frame.
struct EditorSnapshot {
    std::vector<TabInfo> tabs;
    int32_t selectedIndex = -1;  // -1 when no tab is open
    ustring text;
    Selection selection;
    bool canUndo = false;
    bool canRedo = false;
};

// The whole editor: open tabs, their documents and their undo histories.
//
// Not thread-safe by design. Confine it to one thread (on Android, the main
// thread) and do file I/O outside it.
class EditorModel {
public:
    using History = HistoryManager<PieceTableDocument, Memento>;

    EditorModel();
    ~EditorModel();

    EditorModel(const EditorModel&) = delete;
    EditorModel& operator=(const EditorModel&) = delete;

    const EditorSnapshot& snapshot() const { return snapshot_; }

    // --- tabs ------------------------------------------------------------
    // Returns the new tab's id. The caret starts at offset 0, as it would in
    // any editor that has just opened a file.
    int64_t createTab(ustring initialText,
                      ustring fileName,
                      std::optional<ustring> filePath = std::nullopt);

    bool closeTab(int64_t tabId);
    bool selectTab(int64_t tabId);

    // Renames a tab and/or points it at a different file.
    bool setTabFile(int64_t tabId, ustring fileName, std::optional<ustring> filePath);

    // Records that the tab's current content is what is on disk. The tab stays
    // clean until the content moves away from this state again, in either
    // direction.
    bool markTabSaved(int64_t tabId);

    int32_t tabCount() const { return static_cast<int32_t>(tabs_.size()); }
    bool isTabDirty(int64_t tabId) const;
    bool hasUnsavedChanges() const;

    // --- editing ---------------------------------------------------------
    // Reports the caret/selection the user moved to. Breaks undo grouping so
    // that typing after a caret jump starts a new undo step.
    bool setSelection(Selection s);

    // Precise splice. `selAfter` defaults to a caret just past the inserted
    // text. Returns false and changes nothing when the range is invalid.
    bool applyEdit(int32_t pos,
                   int32_t removeLength,
                   const ustring& insertText,
                   std::optional<Selection> selAfter = std::nullopt);

    // Accepts a whole new document body, recovers the edit that produced it
    // and applies that. This is what the Compose text field feeds.
    bool setText(const ustring& newText, std::optional<Selection> selAfter = std::nullopt);

    bool undo();
    bool redo();

    // Seals the open undo group. Call before saving or switching away.
    void finalizeEdits();

    ustring activeText() const;

    // --- diagnostics, used by the tests ---------------------------------
    std::size_t documentCount() const { return docs_.size(); }
    std::size_t undoDepth() const;
    std::size_t redoDepth() const;
    const PieceTableDocument* activeDocument() const;

private:
    struct DocEntry {
        PieceTableDocument doc;
        History history;
        uint64_t cleanRevision = 0;

        // Caret position produced by the previous edit, or -1 when unknown.
        // Used to decide whether the next edit continues the same typing run.
        int32_t lastCaret = -1;

        explicit DocEntry(ustring initial) : doc(std::move(initial)) {}
    };

    struct Tab {
        int64_t id = 0;
        int64_t docId = 0;
        ustring fileName;
        std::optional<ustring> filePath;
        Selection selection;
    };

    Tab* activeTab();
    const Tab* activeTab() const;
    Tab* findTab(int64_t tabId, int32_t* indexOut);
    const Tab* findTab(int64_t tabId) const;
    DocEntry* docFor(const Tab& tab);
    const DocEntry* docFor(const Tab& tab) const;
    void releaseDocIfUnused(int64_t docId);
    void refreshSnapshot();

    std::vector<Tab> tabs_;
    std::unordered_map<int64_t, std::unique_ptr<DocEntry>> docs_;
    int32_t selectedIndex_ = -1;
    int64_t nextTabId_ = 0;
    int64_t nextDocId_ = 0;
    EditorSnapshot snapshot_;
};

}  // namespace editor

#endif  // EDITOR_EDITOR_MODEL_H
