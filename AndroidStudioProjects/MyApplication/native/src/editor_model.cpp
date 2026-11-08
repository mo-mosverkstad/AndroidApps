#include "editor/editor_model.h"

#include <algorithm>
#include <utility>

namespace editor {

EditorModel::EditorModel() { refreshSnapshot(); }

EditorModel::~EditorModel() = default;

// ---------------------------------------------------------------------------
// lookup helpers
// ---------------------------------------------------------------------------

EditorModel::Tab* EditorModel::activeTab() {
    if (selectedIndex_ < 0 || selectedIndex_ >= static_cast<int32_t>(tabs_.size())) return nullptr;
    return &tabs_[static_cast<size_t>(selectedIndex_)];
}

const EditorModel::Tab* EditorModel::activeTab() const {
    if (selectedIndex_ < 0 || selectedIndex_ >= static_cast<int32_t>(tabs_.size())) return nullptr;
    return &tabs_[static_cast<size_t>(selectedIndex_)];
}

EditorModel::Tab* EditorModel::findTab(int64_t tabId, int32_t* indexOut) {
    for (size_t i = 0; i < tabs_.size(); ++i) {
        if (tabs_[i].id == tabId) {
            if (indexOut) *indexOut = static_cast<int32_t>(i);
            return &tabs_[i];
        }
    }
    return nullptr;
}

const EditorModel::Tab* EditorModel::findTab(int64_t tabId) const {
    for (const Tab& t : tabs_) {
        if (t.id == tabId) return &t;
    }
    return nullptr;
}

EditorModel::DocEntry* EditorModel::docFor(const Tab& tab) {
    auto it = docs_.find(tab.docId);
    return it == docs_.end() ? nullptr : it->second.get();
}

const EditorModel::DocEntry* EditorModel::docFor(const Tab& tab) const {
    auto it = docs_.find(tab.docId);
    return it == docs_.end() ? nullptr : it->second.get();
}

void EditorModel::releaseDocIfUnused(int64_t docId) {
    for (const Tab& t : tabs_) {
        if (t.docId == docId) return;
    }
    docs_.erase(docId);
}

// ---------------------------------------------------------------------------
// snapshot
// ---------------------------------------------------------------------------

void EditorModel::refreshSnapshot() {
    if (tabs_.empty()) {
        selectedIndex_ = -1;
    } else if (selectedIndex_ < 0 || selectedIndex_ >= static_cast<int32_t>(tabs_.size())) {
        selectedIndex_ = static_cast<int32_t>(tabs_.size()) - 1;
    }

    snapshot_.tabs.clear();
    snapshot_.tabs.reserve(tabs_.size());

    for (const Tab& t : tabs_) {
        TabInfo info;
        info.id = t.id;
        info.fileName = t.fileName;
        info.hasPath = t.filePath.has_value();
        if (info.hasPath) info.filePath = *t.filePath;

        const DocEntry* entry = docFor(t);
        info.dirty = entry != nullptr && entry->history.revision() != entry->cleanRevision;

        snapshot_.tabs.push_back(std::move(info));
    }

    snapshot_.selectedIndex = selectedIndex_;

    Tab* active = activeTab();
    DocEntry* entry = active ? docFor(*active) : nullptr;

    if (!active || !entry) {
        snapshot_.text.clear();
        snapshot_.selection = Selection(0);
        snapshot_.canUndo = false;
        snapshot_.canRedo = false;
        return;
    }

    snapshot_.text = entry->doc.text();
    active->selection = clampSelection(active->selection, entry->doc.length());
    snapshot_.selection = active->selection;
    snapshot_.canUndo = entry->history.canUndo();
    snapshot_.canRedo = entry->history.canRedo();
}

// ---------------------------------------------------------------------------
// tabs
// ---------------------------------------------------------------------------

int64_t EditorModel::createTab(ustring initialText,
                               ustring fileName,
                               std::optional<ustring> filePath) {
    const int64_t docId = ++nextDocId_;
    docs_.emplace(docId, std::unique_ptr<DocEntry>(new DocEntry(std::move(initialText))));

    Tab tab;
    tab.id = ++nextTabId_;
    tab.docId = docId;
    tab.fileName = std::move(fileName);
    tab.filePath = std::move(filePath);
    tab.selection = Selection(0);

    tabs_.push_back(std::move(tab));
    selectedIndex_ = static_cast<int32_t>(tabs_.size()) - 1;

    // A freshly opened document matches what is on disk.
    DocEntry& entry = *docs_.at(docId);
    entry.cleanRevision = entry.history.revision();
    entry.lastCaret = 0;

    refreshSnapshot();
    return tabs_.back().id;
}

bool EditorModel::closeTab(int64_t tabId) {
    int32_t index = -1;
    if (!findTab(tabId, &index)) return false;

    const int64_t docId = tabs_[static_cast<size_t>(index)].docId;
    tabs_.erase(tabs_.begin() + index);

    // Drop the document and its history, which the Kotlin version leaked for
    // the lifetime of the ViewModel.
    releaseDocIfUnused(docId);

    if (tabs_.empty()) {
        selectedIndex_ = -1;
    } else if (selectedIndex_ > index) {
        --selectedIndex_;
    } else if (selectedIndex_ == index) {
        selectedIndex_ = std::min(index, static_cast<int32_t>(tabs_.size()) - 1);
    }

    refreshSnapshot();
    return true;
}

bool EditorModel::selectTab(int64_t tabId) {
    int32_t index = -1;
    if (!findTab(tabId, &index)) return false;

    // Seal the outgoing tab's undo group before leaving it.
    finalizeEdits();

    selectedIndex_ = index;
    refreshSnapshot();
    return true;
}

bool EditorModel::setTabFile(int64_t tabId, ustring fileName, std::optional<ustring> filePath) {
    Tab* tab = findTab(tabId, nullptr);
    if (!tab) return false;

    tab->fileName = std::move(fileName);
    tab->filePath = std::move(filePath);
    refreshSnapshot();
    return true;
}

bool EditorModel::markTabSaved(int64_t tabId) {
    Tab* tab = findTab(tabId, nullptr);
    if (!tab) return false;

    DocEntry* entry = docFor(*tab);
    if (!entry) return false;

    entry->history.finalize();
    entry->cleanRevision = entry->history.revision();
    refreshSnapshot();
    return true;
}

bool EditorModel::isTabDirty(int64_t tabId) const {
    const Tab* tab = findTab(tabId);
    if (!tab) return false;
    const DocEntry* entry = docFor(*tab);
    return entry != nullptr && entry->history.revision() != entry->cleanRevision;
}

bool EditorModel::hasUnsavedChanges() const {
    for (const Tab& t : tabs_) {
        const DocEntry* entry = docFor(t);
        if (entry && entry->history.revision() != entry->cleanRevision) return true;
    }
    return false;
}

// ---------------------------------------------------------------------------
// editing
// ---------------------------------------------------------------------------

bool EditorModel::setSelection(Selection s) {
    Tab* tab = activeTab();
    if (!tab) return false;
    DocEntry* entry = docFor(*tab);
    if (!entry) return false;

    const Selection clamped = clampSelection(s, entry->doc.length());
    if (clamped == tab->selection) return false;

    // Moving the caret away from where the last edit left it ends the current
    // typing run, so the next keystroke starts a fresh undo step.
    const bool movedAway = entry->lastCaret < 0 || !clamped.collapsed() ||
                           clamped.start != entry->lastCaret;
    if (movedAway) entry->history.finalize();

    tab->selection = clamped;
    entry->lastCaret = clamped.collapsed() ? clamped.start : -1;
    refreshSnapshot();
    return true;
}

bool EditorModel::applyEdit(int32_t pos,
                            int32_t removeLength,
                            const ustring& insertText,
                            std::optional<Selection> selAfter) {
    Tab* tab = activeTab();
    if (!tab) return false;
    DocEntry* entry = docFor(*tab);
    if (!entry) return false;

    const int32_t docLength = entry->doc.length();
    if (pos < 0 || removeLength < 0 || pos > docLength || removeLength > docLength - pos) {
        return false;
    }
    if (removeLength == 0 && insertText.empty()) return false;

    const Selection before = clampSelection(tab->selection, docLength);
    const Selection after =
        selAfter.has_value() ? *selAfter
                             : Selection(pos + static_cast<int32_t>(insertText.size()));

    const bool isInsert = removeLength == 0 && !insertText.empty();
    const bool isErase = removeLength > 0 && insertText.empty();
    const bool isReplace = !isInsert && !isErase;

    // Typing is only grouped while it stays contiguous. Insert continues a run
    // when it lands exactly where the previous edit left the caret; backspace
    // and forward-delete both touch the caret position too.
    bool contiguous = false;
    if (entry->lastCaret >= 0) {
        if (isInsert) {
            contiguous = pos == entry->lastCaret;
        } else if (isErase) {
            contiguous = pos + removeLength == entry->lastCaret || pos == entry->lastCaret;
        }
    }
    if (!contiguous) entry->history.finalize();

    // A replace is one logical edit, so its delete and insert go into a single
    // undo entry. The Kotlin version pushed them as two, which is why typing
    // over a selection needed two presses of Undo.
    if (isReplace) entry->history.beginTransaction();

    if (removeLength > 0) {
        entry->history.push(entry->doc.erase(pos, removeLength), EditType::Deleting, before, after);
    }
    if (!insertText.empty()) {
        entry->history.push(entry->doc.insert(pos, insertText), EditType::Inserting, before, after);
    }

    if (isReplace) entry->history.commitTransaction();

    tab->selection = clampSelection(after, entry->doc.length());
    entry->lastCaret = tab->selection.collapsed() ? tab->selection.start : -1;

    refreshSnapshot();
    return true;
}

bool EditorModel::setText(const ustring& newText, std::optional<Selection> selAfter) {
    Tab* tab = activeTab();
    if (!tab) return false;
    DocEntry* entry = docFor(*tab);
    if (!entry) return false;

    const ustring current = entry->doc.text();
    if (current == newText) {
        if (selAfter.has_value()) return setSelection(*selAfter);
        return false;
    }

    const TextEdit edit = diffTexts(current, newText);
    if (edit.empty()) return false;

    return applyEdit(edit.pos, edit.removeLength, edit.insertText, selAfter);
}

bool EditorModel::undo() {
    Tab* tab = activeTab();
    if (!tab) return false;
    DocEntry* entry = docFor(*tab);
    if (!entry) return false;

    Selection restored;
    if (!entry->history.undo(entry->doc, &restored)) return false;

    tab->selection = clampSelection(restored, entry->doc.length());
    entry->lastCaret = tab->selection.collapsed() ? tab->selection.start : -1;

    refreshSnapshot();
    return true;
}

bool EditorModel::redo() {
    Tab* tab = activeTab();
    if (!tab) return false;
    DocEntry* entry = docFor(*tab);
    if (!entry) return false;

    Selection restored;
    if (!entry->history.redo(entry->doc, &restored)) return false;

    tab->selection = clampSelection(restored, entry->doc.length());
    entry->lastCaret = tab->selection.collapsed() ? tab->selection.start : -1;

    refreshSnapshot();
    return true;
}

void EditorModel::finalizeEdits() {
    Tab* tab = activeTab();
    if (!tab) return;
    DocEntry* entry = docFor(*tab);
    if (!entry) return;

    entry->history.finalize();
    refreshSnapshot();
}

ustring EditorModel::activeText() const {
    const Tab* tab = activeTab();
    if (!tab) return ustring();
    const DocEntry* entry = docFor(*tab);
    if (!entry) return ustring();
    return entry->doc.text();
}

std::size_t EditorModel::undoDepth() const {
    const Tab* tab = activeTab();
    if (!tab) return 0;
    const DocEntry* entry = docFor(*tab);
    return entry ? entry->history.undoDepth() : 0;
}

std::size_t EditorModel::redoDepth() const {
    const Tab* tab = activeTab();
    if (!tab) return 0;
    const DocEntry* entry = docFor(*tab);
    return entry ? entry->history.redoDepth() : 0;
}

const PieceTableDocument* EditorModel::activeDocument() const {
    const Tab* tab = activeTab();
    if (!tab) return nullptr;
    const DocEntry* entry = docFor(*tab);
    return entry ? &entry->doc : nullptr;
}

}  // namespace editor
