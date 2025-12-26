package com.example.myapplication.core

// -------------------- PieceTable / Treap --------------------
import com.example.myapplication.core.PieceTableDocument
import com.example.myapplication.core.PieceTableMemento
import com.example.myapplication.lib.PieceTable

// -------------------- HistoryManager --------------------

import com.example.myapplication.lib.HistoryManager
import java.util.UUID

// -------------------- Editor model --------------------

data class SelectionRange(val start: Int, val end: Int = start) {
    init {
        require(start >= 0 && end >= 0)
        require(start <= end)
    }
}

data class TabMeta(
    val id: String = UUID.randomUUID().toString(),
    val docId: String,
    val fileName: String,
    val filePath: String? = null,
    val isDirty: Boolean = false
)

data class EditorState(
    val tabs: List<TabMeta> = emptyList(),
    val selectedIndex: Int = 0,
    val visibleText: String = "",
    val selection: SelectionRange = SelectionRange(0),
    val canUndo: Boolean = false,
    val canRedo: Boolean = false
)

class EditorModel {

    private val docs = mutableMapOf<String, PieceTableDocument>()
    private val histories = mutableMapOf<String, HistoryManager<PieceTableDocument, PieceTableMemento>>()

    private var state = EditorState()
    fun getState(): EditorState = state

    private fun clampIndex(tabs: List<TabMeta>, idx: Int): Int =
        when {
            tabs.isEmpty() -> 0
            idx < 0 -> 0
            idx > tabs.lastIndex -> tabs.lastIndex
            else -> idx
        }

    // -----------------------------------------------------
    // TAB CREATION
    // -----------------------------------------------------
    fun createTab(
        initialText: String,
        fileName: String,
        filePath: String? = null
    ): EditorState {

        val docId = UUID.randomUUID().toString()
        val doc = PieceTableDocument(PieceTable(initialText))

        docs[docId] = doc
        histories[docId] = HistoryManager()

        val tabs = state.tabs + TabMeta(
            docId = docId,
            fileName = fileName,
            filePath = filePath
        )

        state = state.copy(
            tabs = tabs,
            selectedIndex = tabs.lastIndex,
            visibleText = doc.toString(),
            selection = SelectionRange(doc.length),
            canUndo = false,
            canRedo = false
        )
        return state
    }

    // -----------------------------------------------------
    // TAB CLOSING
    // -----------------------------------------------------
    fun closeTab(tabId: String): EditorState {
        val idx = state.tabs.indexOfFirst { it.id == tabId }
        if (idx < 0) return state

        val newTabs = state.tabs.toMutableList().also { it.removeAt(idx) }
        val newIdx = clampIndex(newTabs, idx)

        val newText =
            newTabs.getOrNull(newIdx)?.let { docs[it.docId]?.toString() } ?: ""

        val hist = newTabs.getOrNull(newIdx)?.let { histories[it.docId] }

        state = state.copy(
            tabs = newTabs,
            selectedIndex = newIdx,
            visibleText = newText,
            selection = SelectionRange(newText.length),
            canUndo = hist?.canUndo ?: false,
            canRedo = hist?.canRedo ?: false
        )
        return state
    }

    fun markTabClean(tabId: String) {
        val tabs = state.tabs.toMutableList()
        val idx = tabs.indexOfFirst { it.id == tabId }
        if (idx >= 0) {
            tabs[idx] = tabs[idx].copy(isDirty = false)
            state = state.copy(tabs = tabs)
        }
    }

    fun updateTabFileInfo(tabId: String, newName: String, newPath: String) {
        val tabs = state.tabs.toMutableList()
        val idx = tabs.indexOfFirst { it.id == tabId }
        if (idx >= 0) {
            tabs[idx] = tabs[idx].copy(fileName = newName, filePath = newPath)
            state = state.copy(tabs = tabs)
        }
    }

    // -----------------------------------------------------
    // TAB SELECTION
    // -----------------------------------------------------
    fun selectTab(tabId: String): EditorState {
        val idx = state.tabs.indexOfFirst { it.id == tabId }
        if (idx < 0) return state

        val tab = state.tabs[idx]
        val hist = histories[tab.docId]!!
        val doc = docs[tab.docId]!!

        hist.finalizeExternal()

        state = state.copy(
            selectedIndex = idx,
            visibleText = doc.toString(),
            selection = SelectionRange(doc.length),
            canUndo = hist.canUndo,
            canRedo = hist.canRedo
        )
        return state
    }

    // -----------------------------------------------------
    // UNDO / REDO
    // -----------------------------------------------------
    fun undo(): EditorState {
        val tab = state.tabs[state.selectedIndex]
        val doc = docs[tab.docId]!!
        val hist = histories[tab.docId]!!

        hist.undo(doc)
        return rebuildAfterHistory(doc, hist)
    }

    fun redo(): EditorState {
        val tab = state.tabs[state.selectedIndex]
        val doc = docs[tab.docId]!!
        val hist = histories[tab.docId]!!

        hist.redo(doc)
        return rebuildAfterHistory(doc, hist)
    }

    private fun rebuildAfterHistory(
        doc: PieceTableDocument,
        hist: HistoryManager<PieceTableDocument, PieceTableMemento>
    ): EditorState {

        val text = doc.toString()
        val tabs = state.tabs.toMutableList()
        tabs[state.selectedIndex] =
            tabs[state.selectedIndex].copy(isDirty = true)

        state = state.copy(
            tabs = tabs,
            visibleText = text,
            selection = SelectionRange(text.length),
            canUndo = hist.canUndo,
            canRedo = hist.canRedo
        )
        return state
    }

    // -----------------------------------------------------
    // TEXT DIFF FROM UI
    // -----------------------------------------------------
    fun applyTextChange(
        removeStart: Int,
        removeLen: Int,
        addText: String
    ): EditorState {

        val tab = state.tabs[state.selectedIndex]
        val doc = docs[tab.docId]!!
        val hist = histories[tab.docId]!!

        val type = when {
            removeLen > 0 && addText.isEmpty() -> HistoryManager.EditType.DELETING
            removeLen == 0 && addText.isNotEmpty() -> HistoryManager.EditType.INSERTING
            else -> HistoryManager.EditType.OTHER
        }

        if (type == HistoryManager.EditType.OTHER)
            hist.finalizeExternal()

        if (removeLen > 0)
            hist.push(doc.delete(removeStart, removeLen), HistoryManager.EditType.DELETING)

        if (addText.isNotEmpty())
            hist.push(doc.insert(removeStart, addText), HistoryManager.EditType.INSERTING)

        val text = doc.toString()
        val tabs = state.tabs.toMutableList()
        tabs[state.selectedIndex] =
            tabs[state.selectedIndex].copy(isDirty = true)

        state = state.copy(
            tabs = tabs,
            visibleText = text,
            selection = SelectionRange(removeStart + addText.length),
            canUndo = hist.canUndo,
            canRedo = hist.canRedo
        )
        return state
    }

    fun getActiveDocumentText(): String {
        val tab = state.tabs.getOrNull(state.selectedIndex) ?: return ""
        val doc = docs[tab.docId] ?: return ""
        return doc.toString()
    }

    /**
     * Finalizes any pending, grouped edits (like continuous typing) for the
     * currently active tab. This should be called before saving or switching tabs.
     */
    fun finalizeActiveEdits() {
        val tab = state.tabs.getOrNull(state.selectedIndex) ?: return
        histories[tab.docId]?.finalizeExternal()
    }


}