// MainActivity.kt
package com.example.myapplication

import android.content.Context
import android.database.Cursor
import android.net.Uri
import android.os.Bundle
import android.provider.OpenableColumns
import android.widget.Toast
import androidx.activity.ComponentActivity
import androidx.activity.compose.rememberLauncherForActivityResult
import androidx.activity.compose.setContent
import androidx.activity.enableEdgeToEdge
import androidx.activity.result.contract.ActivityResultContracts
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.text.BasicTextField
import androidx.compose.foundation.verticalScroll
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Add
import androidx.compose.material.icons.filled.Close
import androidx.compose.material3.*
import androidx.compose.runtime.*
import androidx.compose.runtime.key
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.text.TextRange
import androidx.compose.ui.text.input.TextFieldValue
import androidx.compose.ui.unit.dp
import androidx.lifecycle.ViewModel
import androidx.lifecycle.viewModelScope
import androidx.lifecycle.viewmodel.compose.viewModel
import com.example.myapplication.ui.theme.MyApplicationTheme
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.StateFlow
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.OutputStreamWriter
import java.util.concurrent.Executors
import kotlin.random.Random
import java.util.UUID
import java.util.ArrayDeque

// -------------------- PieceTable / Treap --------------------
import com.example.myapplication.lib.PieceTable

// -------------------- HistoryManager --------------------

/**
 * Simplified and robust HistoryManager that stores *original* ops (not inverses).
 * Behavior:
 * - pushOp(op, type) to add an operation (op is the operation that WAS applied to the document)
 * - batching of consecutive INSERTING or DELETING ops into one undo entry
 * - finalizeExternal() to finalize current batch (e.g. on Enter, selection change)
 * - undo(doc) applies inverses in reverse order
 * - redo(doc) reapplies original ops in original order
 */
class HistoryManager {

    enum class EditType {
        INSERTING,
        DELETING,
        OTHER
    }

    private val undo = ArrayDeque<List<PieceTable.Op>>()
    private val redo = ArrayDeque<List<PieceTable.Op>>()

    private var currentBatch: MutableList<PieceTable.Op> = mutableListOf()
    private var lastEditType: EditType? = null

    val canUndo: Boolean get() = undo.isNotEmpty() || currentBatch.isNotEmpty()
    val canRedo: Boolean get() = redo.isNotEmpty()

    private fun shouldMerge(type: EditType): Boolean {
        if (currentBatch.isEmpty()) return true
        return (lastEditType == type) && (type == EditType.INSERTING || type == EditType.DELETING)
    }

    @Synchronized
    fun pushOp(op: PieceTable.Op, type: EditType) {
        if (type == EditType.OTHER) {
            finalizeBatchLocked()
            undo.addLast(listOf(op))
            redo.clear()
            lastEditType = null
            return
        }

        if (!shouldMerge(type)) {
            finalizeBatchLocked()
        }

        currentBatch.add(op)
        lastEditType = type
        redo.clear()
    }

    @Synchronized
    fun finalizeExternal() {
        finalizeBatchLocked()
    }

    @Synchronized
    private fun finalizeBatchLocked() {
        if (currentBatch.isNotEmpty()) {
            undo.addLast(currentBatch.toList())
            currentBatch.clear()
        }
        lastEditType = null
    }

    @Synchronized
    fun undo(doc: PieceTable): Boolean {
        finalizeBatchLocked()
        val batch = if (undo.isEmpty()) null else undo.removeLast() ?: return false
        val redoBatch = mutableListOf<PieceTable.Op>()

        // Apply inverses in reverse order
        if (batch != null) {
            for (op in batch.asReversed()) {
                val inv = doc.invert(op)
                doc.apply(inv)
                redoBatch.add(op) // for redo we will reapply original ops
            }
        }

        // push original ops for redo in their original order
        redo.addLast(redoBatch.asReversed().toMutableList())
        lastEditType = null
        return true
    }

    @Synchronized
    fun redo(doc: PieceTable): Boolean {
        val batch = if (redo.isEmpty()) null else redo.removeLast() ?: return false
        val undoBatch = mutableListOf<PieceTable.Op>()

        if (batch != null) {
            for (op in batch) {
                doc.apply(op)
                undoBatch.add(op)
            }
        }

        undo.addLast(undoBatch.toList())
        lastEditType = null
        return true
    }

    override fun toString(): String {
        return "HistoryManager(undo=${undo.size}, redo=${redo.size}, pending=${currentBatch.size})"
    }
}

// -------------------- Editor model --------------------

// A platform-independent way to represent a text selection range.
// It replaces androidx.compose.ui.text.TextRange.
data class SelectionRange(val start: Int, val end: Int = start) {
    init {
        require(start >= 0 && end >= 0) { "Selection must be non-negative" }
        require(start <= end) { "Selection start must be <= end" }
    }
}


data class TabMeta(
    val id: String = UUID.randomUUID().toString(),
    val docId: String,
    val fileName: String,
    // Replaced Android's Uri with a platform-agnostic String path.
    val filePath: String? = null,
    val isDirty: Boolean = false
)

data class EditorState(
    val tabs: List<TabMeta> = emptyList(),
    val selectedIndex: Int = 0,
    val visibleText: String = "",
    // Use the new platform-independent SelectionRange.
    val selection: SelectionRange = SelectionRange(0),
    val canUndo: Boolean = false,
    val canRedo: Boolean = false
)

class EditorModel {

    private val docs = mutableMapOf<String, PieceTable>()
    private val histories = mutableMapOf<String, HistoryManager>()

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
    // The signature now accepts a String 'filePath' instead of an Android 'Uri'.
    fun createTab(initialText: String, fileName: String, filePath: String? = null): EditorState {
        val docId = UUID.randomUUID().toString()

        docs[docId] = PieceTable(initialText)
        histories[docId] = HistoryManager()

        val newTab = TabMeta(docId = docId, fileName = fileName, filePath = filePath, isDirty = false)
        val tabs = state.tabs + newTab
        val idx = tabs.lastIndex

        val doc = docs[docId]!!

        state = state.copy(
            tabs = tabs,
            selectedIndex = idx,
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
        if (idx == -1) return state

        val newTabs = state.tabs.toMutableList().also { it.removeAt(idx) }
        val newIdx = clampIndex(newTabs, idx)

        val newVisible =
            if (newTabs.isEmpty()) ""
            else {
                val docId = newTabs[newIdx].docId
                docs[docId]?.toString() ?: ""
            }

        val hist = newTabs.getOrNull(newIdx)?.let { histories[it.docId] }

        state = state.copy(
            tabs = newTabs,
            selectedIndex = newIdx,
            visibleText = newVisible,
            selection = SelectionRange(newVisible.length),
            canUndo = hist?.canUndo ?: false,
            canRedo = hist?.canRedo ?: false
        )
        return state
    }

    fun markTabClean(tabId: String) {
        val updatedTabs = state.tabs.toMutableList()
        val idx = updatedTabs.indexOfFirst { it.id == tabId }
        if (idx >= 0) {
            updatedTabs[idx] = updatedTabs[idx].copy(isDirty = false)
            state = state.copy(tabs = updatedTabs)
        }
    }

    // The signature now accepts a String 'newPath' instead of an Android 'Uri'.
    fun updateTabFileInfo(tabId: String, newFileName: String, newPath: String) {
        val updatedTabs = state.tabs.toMutableList()
        val idx = updatedTabs.indexOfFirst { it.id == tabId }
        if (idx >= 0) {
            updatedTabs[idx] = updatedTabs[idx].copy(fileName = newFileName, filePath = newPath)
            state = state.copy(tabs = updatedTabs)
        }
    }

    // -----------------------------------------------------
    // TAB SELECTION
    // -----------------------------------------------------
    fun selectTab(tabId: String): EditorState {
        val idx = state.tabs.indexOfFirst { it.id == tabId }
        if (idx == -1) return state

        val tab = state.tabs[idx]
        histories[tab.docId]?.finalizeExternal()

        val doc = docs[tab.docId]!!

        state = state.copy(
            selectedIndex = idx,
            visibleText = doc.toString(),
            selection = SelectionRange(doc.length),
            canUndo = histories[tab.docId]!!.canUndo,
            canRedo = histories[tab.docId]!!.canRedo
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

        hist.finalizeExternal()
        hist.undo(doc)

        return rebuildStateAfterHistory(doc, hist)
    }

    fun redo(): EditorState {
        val tab = state.tabs[state.selectedIndex]
        val doc = docs[tab.docId]!!
        val hist = histories[tab.docId]!!

        hist.finalizeExternal()
        hist.redo(doc)

        return rebuildStateAfterHistory(doc, hist)
    }

    private fun rebuildStateAfterHistory(doc: PieceTable, hist: HistoryManager): EditorState {
        val newText = doc.toString()
        val newSel = SelectionRange(newText.length)

        val updatedTabs = state.tabs.toMutableList()
        updatedTabs[state.selectedIndex] = updatedTabs[state.selectedIndex].copy(isDirty = true)

        state = state.copy(
            tabs = updatedTabs,
            visibleText = newText,
            selection = newSel,
            canUndo = hist.canUndo,
            canRedo = hist.canRedo
        )
        return state
    }

    // -----------------------------------------------------
    // UI TEXT DIFF APPLIED TO MODEL
    // -----------------------------------------------------
    fun applyTextChange(removeStart: Int, removeLen: Int, addText: String): EditorState {
        val tab = state.tabs[state.selectedIndex]
        val doc = docs[tab.docId]!!
        val hist = histories[tab.docId]!!

        val editType = when {
            removeLen > 0 && addText.isEmpty() -> HistoryManager.EditType.DELETING
            removeLen == 0 && addText.isNotEmpty() -> HistoryManager.EditType.INSERTING
            else -> HistoryManager.EditType.OTHER
        }

        if (editType == HistoryManager.EditType.OTHER)
            hist.finalizeExternal()

        if (removeLen > 0)
            hist.pushOp(doc.deleteWithOp(removeStart, removeLen), HistoryManager.EditType.DELETING)

        if (addText.isNotEmpty())
            hist.pushOp(doc.insertWithOp(removeStart, addText), HistoryManager.EditType.INSERTING)

        // This part was cut off in the original file, but it would likely rebuild
        // the state similar to how rebuildStateAfterHistory does.
        // For completeness, it would look something like this:

        val newText = doc.toString()
        // Here you would also update selection based on the change,
        // but for now we'll just move it to the end of the change.
        val newSelection = SelectionRange(removeStart + addText.length)

        val updatedTabs = state.tabs.toMutableList()
        updatedTabs[state.selectedIndex] = updatedTabs[state.selectedIndex].copy(isDirty = true)

        state = state.copy(
            tabs = updatedTabs,
            visibleText = newText,
            selection = newSelection,
            canUndo = hist.canUndo,
            canRedo = hist.canRedo
        )
        return state
    }
}


class EditorViewModel : ViewModel() {

    private val model = EditorModel()

    private val _uiState = MutableStateFlow(EditorState())
    val uiState: StateFlow<EditorState> = _uiState

    @Volatile
    var applyingModelUpdate = false

    private val singleThread = Executors.newSingleThreadExecutor { r ->
        Thread(r, "editor-dispatcher").apply { isDaemon = true }
    }
    private val editorDispatcher = singleThread.asCoroutineDispatcher()
    private var diffJob: Job? = null

    private fun pushState() {
        _uiState.value = model.getState()
    }

    // ---------------------------------------------------------
    // TABS
    // ---------------------------------------------------------
    fun newTab() {
        model.createTab("", "New File")
        pushState()
    }

    fun closeTabById(id: String) {
        model.closeTab(id)
        pushState()
    }

    fun selectTabById(id: String) {
        model.selectTab(id)
        pushState()
    }

    fun markTabClean(tabId: String) {
        model.markTabClean(tabId)
        pushState()
    }

    fun updateTabFileInfo(tabId: String, newFileName: String, newUri: Uri) {
        model.updateTabFileInfo(tabId, newFileName, newUri.toString()) // Convert Uri to String
        pushState()
    }


    // ---------------------------------------------------------
    // UNDO / REDO
    // ---------------------------------------------------------
    fun undo() {
        viewModelScope.launch(editorDispatcher) {
            model.undo()
            withContext(Dispatchers.Main) { pushState() }
        }
    }

    fun redo() {
        viewModelScope.launch(editorDispatcher) {
            model.redo()
            withContext(Dispatchers.Main) { pushState() }
        }
    }

    // ---------------------------------------------------------
    // TEXT CHANGE FROM UI
    // ---------------------------------------------------------
    fun applyTextChangeFromUi(newValue: TextFieldValue) {
        diffJob?.cancel()
        diffJob = viewModelScope.launch {
            delay(8)

            withContext(editorDispatcher) {
                val cur = model.getState()
                val old = cur.visibleText
                val fresh = newValue.text
                if (old == fresh) {
                    return@withContext
                }

                // compute prefix
                val min = minOf(old.length, fresh.length)
                var prefix = 0
                while (prefix < min && old[prefix] == fresh[prefix]) prefix++

                // compute suffix
                var suffix = 0
                val oldRemaining = old.length - prefix
                val newRemaining = fresh.length - prefix
                while (suffix < oldRemaining && suffix < newRemaining &&
                    old[old.length - 1 - suffix] == fresh[fresh.length - 1 - suffix]) suffix++

                val removeStart = prefix
                val removeLen = old.length - prefix - suffix
                val addText = if (fresh.length - prefix - suffix > 0)
                    fresh.substring(prefix, fresh.length - suffix)
                else ""

                model.applyTextChange(removeStart, removeLen, addText)

                withContext(Dispatchers.Main) {
                    applyingModelUpdate = true
                    pushState()
                    applyingModelUpdate = false
                }
            }
        }
    }

    // ---------------------------------------------------------
    // FILE I/O (ANDROID)
    // ---------------------------------------------------------
    fun openFile(context: Context, uri: Uri) {
        viewModelScope.launch(Dispatchers.IO) {
            val text = readFile(context, uri)
            val name = getFileName(context, uri) ?: "Untitled"

            model.createTab(text, name, uri.toString()) // Convert Uri to String

            withContext(Dispatchers.Main) { pushState() }
        }
    }


    fun saveToUri(context: Context, uri: Uri) {
        val text = model.getState().visibleText
        viewModelScope.launch(Dispatchers.IO) {
            writeFile(context, uri, text)
        }
    }

    // ---------------------------------------------------------
    // HELPERS
    // ---------------------------------------------------------
    private fun readFile(context: Context, uri: Uri): String {
        return context.contentResolver.openInputStream(uri)?.use { stream ->
            BufferedReader(InputStreamReader(stream)).use { it.readText() }
        } ?: ""
    }

    private fun writeFile(context: Context, uri: Uri, text: String) {
        context.contentResolver.openOutputStream(uri)?.use { stream ->
            OutputStreamWriter(stream).use { it.write(text) }
        }
    }

    private fun getFileName(context: Context, uri: Uri): String? {
        var name: String? = null
        context.contentResolver.query(uri, null, null, null, null)?.use { cursor: Cursor ->
            val index = cursor.getColumnIndex(OpenableColumns.DISPLAY_NAME)
            if (cursor.moveToFirst() && index >= 0) {
                name = cursor.getString(index)
            }
        }
        return name
    }

    override fun onCleared() {
        super.onCleared()
        singleThread.shutdownNow()
    }
}


// -------------------- MainActivity + Compose --------------------
class MainActivity : ComponentActivity() {
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        enableEdgeToEdge()
        setContent {
            MyApplicationTheme {
                Surface(modifier = Modifier.fillMaxSize()) {
                    TextEditorHost()
                }
            }
        }
    }
}


@Composable
fun TextEditorHost(vm: EditorViewModel = viewModel()) {
    val context = LocalContext.current
    val state by vm.uiState.collectAsState()

    // Open file launcher
    val openLauncher = rememberLauncherForActivityResult(ActivityResultContracts.OpenDocument()) { uri ->
        if (uri != null) vm.openFile(context, uri)
    }

    // Save As launcher with updated logic
    val saveAsLauncher = rememberLauncherForActivityResult(ActivityResultContracts.CreateDocument("*/*")) { uri ->
        if (uri != null) {
            val idx = state.selectedIndex.coerceIn(0, maxOf(0, state.tabs.lastIndex))
            if (idx in state.tabs.indices) {
                val tab = state.tabs[idx]
                vm.saveToUri(context, uri)
                vm.updateTabFileInfo(tab.id, tab.fileName, uri) // ✅ Update file info
                vm.markTabClean(tab.id) // ✅ Reset dirty flag
            }
            Toast.makeText(context, "File saved!", Toast.LENGTH_SHORT).show()
        }
    }

    Column(modifier = Modifier.fillMaxSize()) {
        // Toolbar Row
        Row(
            modifier = Modifier.fillMaxWidth().padding(8.dp),
            horizontalArrangement = Arrangement.SpaceEvenly,
            verticalAlignment = Alignment.CenterVertically
        ) {
            Button(onClick = { openLauncher.launch(arrayOf("*/*")) }, enabled = true) {
                Text("Load")
            }

            // ✅ Save button: mark tab clean after saving
            Button(onClick = {
                val idx = state.selectedIndex.coerceIn(0, maxOf(0, state.tabs.lastIndex))
                if (idx in state.tabs.indices) {
                    // val tab = state.tabs[idx]
                    // In the "Save" button's onClick lambda
                    val tab = state.tabs[idx]
                    if (tab.filePath != null) {
                        // Convert the filePath String back to a Uri for Android file operations
                        vm.saveToUri(context, Uri.parse(tab.filePath))
                        vm.markTabClean(tab.id)
                    } else {
                        // If there's no path, trigger "Save As"
                        saveAsLauncher.launch(tab.fileName)
                    }

                }
            }, enabled = state.tabs.isNotEmpty()) {
                Text("Save")
            }

            // ✅ Save As button: triggers launcher
            Button(onClick = {
                val idx = state.selectedIndex.coerceIn(0, maxOf(0, state.tabs.lastIndex))
                if (idx in state.tabs.indices) {
                    val tab = state.tabs[idx]
                    saveAsLauncher.launch(tab.fileName)
                }
            }, enabled = state.tabs.isNotEmpty()) {
                Text("Save As")
            }

            Button(onClick = { vm.undo() }, enabled = state.canUndo) { Text("Undo") }
            Button(onClick = { vm.redo() }, enabled = state.canRedo) { Text("Redo") }
        }

        // Tabs Row
        Row(verticalAlignment = Alignment.CenterVertically) {
            val tabsSnapshot = state.tabs
            val selectedIndexForRow = tabsSnapshot.let { tabs ->
                if (tabs.isEmpty()) 0 else state.selectedIndex.coerceIn(0, tabs.lastIndex)
            }

            key(tabsSnapshot.size, tabsSnapshot.map { it.id }.hashCode()) {
                if (tabsSnapshot.isNotEmpty()) {
                    ScrollableTabRow(
                        selectedTabIndex = selectedIndexForRow,
                        modifier = Modifier.weight(1f),
                        edgePadding = 0.dp
                    ) {
                        tabsSnapshot.forEachIndexed { idx, tab ->
                            key(tab.id) {
                                Tab(
                                    selected = idx == selectedIndexForRow,
                                    onClick = { vm.selectTabById(tab.id) },
                                    text = {
                                        Row(verticalAlignment = Alignment.CenterVertically) {
                                            Text(tab.fileName + if (tab.isDirty) "*" else "", maxLines = 1)
                                            Spacer(Modifier.width(4.dp))
                                            IconButton(onClick = { vm.closeTabById(tab.id) }, modifier = Modifier.size(22.dp)) {
                                                Icon(Icons.Default.Close, contentDescription = "Close Tab", modifier = Modifier.size(16.dp))
                                            }
                                        }
                                    }
                                )
                            }
                        }
                    }
                } else {
                    Box(modifier = Modifier.weight(1f).padding(start = 12.dp)) { Text("No files open") }
                }
            }

            IconButton(onClick = { vm.newTab() }) { Icon(Icons.Default.Add, contentDescription = "New Tab") }
        }

        // Editor Area
        Box(modifier = Modifier.fillMaxSize().padding(8.dp)) {
            // In the editor area Box
            Box(modifier = Modifier.fillMaxSize().padding(8.dp)) {
                var textState by remember(state.tabs, state.visibleText) {
                    // Convert your custom SelectionRange to Compose's TextRange
                    mutableStateOf(
                        TextFieldValue(
                            text = state.visibleText,
                            selection = TextRange(state.selection.start, state.selection.end)
                        )
                    )
                }

                LaunchedEffect(state.visibleText, state.selection) {
                    // Also convert here when the state from the ViewModel changes
                    if (state.visibleText != textState.text ||
                        TextRange(state.selection.start, state.selection.end) != textState.selection) {
                        textState = TextFieldValue(
                            text = state.visibleText,
                            selection = TextRange(state.selection.start, state.selection.end)
                        )
                    }
                }

                if (state.tabs.isEmpty()) {
                Box(modifier = Modifier.fillMaxSize(), contentAlignment = Alignment.Center) {
                    Text("Open or create a file to start editing")
                }
            } else {
                BasicTextField(
                    value = textState,
                    onValueChange = { newValue ->
                        if (vm.applyingModelUpdate) {
                            textState = newValue
                            return@BasicTextField
                        }
                        if (newValue.text == textState.text) {
                            textState = newValue
                            vm.applyTextChangeFromUi(newValue)
                            return@BasicTextField
                        }
                        textState = newValue
                        vm.applyTextChangeFromUi(newValue)
                    },
                    modifier = Modifier.fillMaxSize().verticalScroll(rememberScrollState())
                )
            }
        }
    }
}}

