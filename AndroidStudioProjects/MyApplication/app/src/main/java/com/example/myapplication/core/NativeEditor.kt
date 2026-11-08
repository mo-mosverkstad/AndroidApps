package com.example.myapplication.core

/**
 * A caret (when [start] == [end]) or a selected range, in UTF-16 offsets —
 * the same units Kotlin's String and Compose's TextRange use.
 */
data class SelectionRange(val start: Int, val end: Int = start)

data class TabMeta(
    val id: Long,
    val fileName: String,
    val filePath: String?,
    val isDirty: Boolean
)

/**
 * Everything the UI needs to draw one frame. Produced by the native core;
 * never modified in Kotlin.
 */
data class EditorState(
    val tabs: List<TabMeta> = emptyList(),
    val selectedIndex: Int = -1,
    val visibleText: String = "",
    val selection: SelectionRange = SelectionRange(0),
    val canUndo: Boolean = false,
    val canRedo: Boolean = false
) {
    val activeTab: TabMeta?
        get() = tabs.getOrNull(selectedIndex)
}

/**
 * Kotlin face of the C++ editor core.
 *
 * The piece table, undo history, caret tracking and dirty-state logic all live
 * in `native/` and are covered by the desktop test suite there. This class
 * only marshals calls and turns the native snapshot into an [EditorState].
 *
 * Not thread-safe: use it from a single thread (the main thread) and keep file
 * I/O outside it.
 */
class NativeEditor : AutoCloseable {

    private var handle: Long = nativeCreate()

    private fun requireHandle(): Long {
        check(handle != 0L) { "NativeEditor has already been closed" }
        return handle
    }

    override fun close() {
        if (handle != 0L) {
            nativeDestroy(handle)
            handle = 0L
        }
    }

    // --- tabs --------------------------------------------------------------

    /** Returns the id of the new tab, which becomes the selected one. */
    fun createTab(text: String, fileName: String, filePath: String? = null): Long =
        nativeCreateTab(requireHandle(), text, fileName, filePath)

    fun closeTab(tabId: Long): Boolean = nativeCloseTab(requireHandle(), tabId)

    fun selectTab(tabId: Long): Boolean = nativeSelectTab(requireHandle(), tabId)

    fun setTabFile(tabId: Long, fileName: String, filePath: String?): Boolean =
        nativeSetTabFile(requireHandle(), tabId, fileName, filePath)

    /**
     * Records that the tab's current contents are what sits on disk. The tab
     * stays clean until the contents move away from this state, in either
     * direction — so undoing back to a saved state clears the dirty marker.
     */
    fun markTabSaved(tabId: Long): Boolean = nativeMarkTabSaved(requireHandle(), tabId)

    fun hasUnsavedChanges(): Boolean = nativeHasUnsavedChanges(requireHandle())

    // --- editing -----------------------------------------------------------

    /**
     * Hands the core a whole new document body plus the caret that produced
     * it. The core recovers the actual edit, so a replacement stays a single
     * undo step.
     */
    fun setText(text: String, selection: SelectionRange): Boolean =
        nativeSetText(requireHandle(), text, selection.start, selection.end)

    fun applyEdit(
        pos: Int,
        removeLength: Int,
        insertText: String,
        selection: SelectionRange
    ): Boolean = nativeApplyEdit(
        requireHandle(), pos, removeLength, insertText, selection.start, selection.end
    )

    fun setSelection(selection: SelectionRange): Boolean =
        nativeSetSelection(requireHandle(), selection.start, selection.end)

    fun undo(): Boolean = nativeUndo(requireHandle())

    fun redo(): Boolean = nativeRedo(requireHandle())

    /** Seals the open undo group. Call before saving or switching away. */
    fun finalizeEdits() = nativeFinalizeEdits(requireHandle())

    /** The active document's full text, straight from the piece table. */
    fun activeText(): String = nativeActiveText(requireHandle())

    // --- snapshot ----------------------------------------------------------

    fun state(): EditorState {
        val h = requireHandle()
        val ints = nativeSnapshotInts(h)
        val flat = nativeSnapshotTabs(h)

        val tabs = ArrayList<TabMeta>(flat.size / FIELDS_PER_TAB)
        var i = 0
        while (i + FIELDS_PER_TAB <= flat.size) {
            tabs.add(
                TabMeta(
                    id = flat[i]?.toLongOrNull() ?: 0L,
                    fileName = flat[i + 1] ?: "",
                    filePath = flat[i + 2],
                    isDirty = flat[i + 3] == "1"
                )
            )
            i += FIELDS_PER_TAB
        }

        return EditorState(
            tabs = tabs,
            selectedIndex = ints[0],
            visibleText = nativeVisibleText(h),
            selection = SelectionRange(ints[1], ints[2]),
            canUndo = ints[3] != 0,
            canRedo = ints[4] != 0
        )
    }

    // --- JNI ---------------------------------------------------------------
    // Declared as instance methods so the symbol names stay the plain
    // Java_<package>_NativeEditor_<name> form.

    private external fun nativeCreate(): Long
    private external fun nativeDestroy(handle: Long)

    private external fun nativeCreateTab(
        handle: Long,
        text: String,
        fileName: String,
        filePath: String?
    ): Long

    private external fun nativeCloseTab(handle: Long, tabId: Long): Boolean
    private external fun nativeSelectTab(handle: Long, tabId: Long): Boolean

    private external fun nativeSetTabFile(
        handle: Long,
        tabId: Long,
        fileName: String,
        filePath: String?
    ): Boolean

    private external fun nativeMarkTabSaved(handle: Long, tabId: Long): Boolean
    private external fun nativeHasUnsavedChanges(handle: Long): Boolean

    private external fun nativeSetText(
        handle: Long,
        text: String,
        selectionStart: Int,
        selectionEnd: Int
    ): Boolean

    private external fun nativeApplyEdit(
        handle: Long,
        pos: Int,
        removeLength: Int,
        insertText: String,
        selectionStart: Int,
        selectionEnd: Int
    ): Boolean

    private external fun nativeSetSelection(
        handle: Long,
        selectionStart: Int,
        selectionEnd: Int
    ): Boolean

    private external fun nativeUndo(handle: Long): Boolean
    private external fun nativeRedo(handle: Long): Boolean
    private external fun nativeFinalizeEdits(handle: Long)

    private external fun nativeVisibleText(handle: Long): String
    private external fun nativeActiveText(handle: Long): String
    private external fun nativeSnapshotInts(handle: Long): IntArray
    private external fun nativeSnapshotTabs(handle: Long): Array<String?>

    private companion object {
        const val FIELDS_PER_TAB = 4

        init {
            System.loadLibrary("editorcore")
        }
    }
}
