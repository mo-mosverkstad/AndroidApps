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
import java.util.*
import java.util.concurrent.Executors
import kotlin.random.Random

// -------------------- PieceTable / Treap --------------------
private const val BUF_ORIG = 0
private const val BUF_ADD = 1

data class PieceRef(val bufferId: Int, val offset: Int, val length: Int)
data class Piece(val bufferId: Int, val offset: Int, val length: Int)

private class Node(
    var piece: Piece,
    var priority: Int = Random.nextInt(),
    var left: Node? = null,
    var right: Node? = null
) {
    var subtreeLen: Int = piece.length
    fun recalc() {
        subtreeLen = piece.length + (left?.subtreeLen ?: 0) + (right?.subtreeLen ?: 0)
    }
}

private fun split(node: Node?, index: Int): Pair<Node?, Node?> {
    if (node == null) return Pair(null, null)
    val leftLen = node.left?.subtreeLen ?: 0
    return when {
        index < leftLen -> {
            val (l, r) = split(node.left, index)
            node.left = r
            node.recalc()
            Pair(l, node)
        }
        index > leftLen + node.piece.length -> {
            val (l, r) = split(node.right, index - leftLen - node.piece.length)
            node.right = l
            node.recalc()
            Pair(node, r)
        }
        else -> {
            val cutInPiece = index - leftLen
            if (cutInPiece == 0) {
                val right = node
                val left = node.left
                right.left = null
                right.recalc()
                Pair(left, right)
            } else if (cutInPiece == node.piece.length) {
                val left = node
                val right = node.right
                left.right = null
                left.recalc()
                Pair(left, right)
            } else {
                val p = node.piece
                val leftPiece = Piece(p.bufferId, p.offset, cutInPiece)
                val rightPiece = Piece(p.bufferId, p.offset + cutInPiece, p.length - cutInPiece)
                val leftNode = Node(leftPiece, Random.nextInt(), node.left, null)
                leftNode.recalc()
                val rightNode = Node(rightPiece, Random.nextInt(), null, node.right)
                rightNode.recalc()
                Pair(leftNode, rightNode)
            }
        }
    }
}

private fun merge(a: Node?, b: Node?): Node? {
    if (a == null) return b
    if (b == null) return a
    return if (a.priority > b.priority) {
        a.right = merge(a.right, b)
        a.recalc()
        a
    } else {
        b.left = merge(a, b.left)
        b.recalc()
        b
    }
}

class PieceTable(originalText: String = "") {
    private val original = StringBuilder(originalText)
    private val addBuffer = StringBuilder()
    private var root: Node? = if (originalText.isNotEmpty()) Node(Piece(BUF_ORIG, 0, originalText.length)) else null
    val length: Int get() = root?.subtreeLen ?: 0

    private fun appendFromPiece(sb: StringBuilder, piece: Piece, localStart: Int, localLen: Int) {
        val src = if (piece.bufferId == BUF_ORIG) original else addBuffer
        sb.append(src.substring(piece.offset + localStart, piece.offset + localStart + localLen))
    }

    fun getSubstring(start: Int, len: Int): String {
        require(start >= 0 && len >= 0 && start + len <= length)
        val sb = StringBuilder(len)
        fun walk(node: Node?, leftIndex: Int) {
            if (node == null) return
            val leftLen = node.left?.subtreeLen ?: 0
            val nodeStartIndex = leftIndex + leftLen
            if (start < nodeStartIndex) walk(node.left, leftIndex)
            val piece = node.piece
            val pieceGlobalEnd = nodeStartIndex + piece.length
            val overlapStart = maxOf(start, nodeStartIndex)
            val overlapEnd = minOf(start + len, pieceGlobalEnd)
            if (overlapStart < overlapEnd) {
                appendFromPiece(sb, piece, overlapStart - nodeStartIndex, overlapEnd - overlapStart)
            }
            if (start + len > pieceGlobalEnd) walk(node.right, pieceGlobalEnd)
        }
        walk(root, 0)
        return sb.toString()
    }

    override fun toString(): String {
        val sb = StringBuilder(length)
        fun inorder(n: Node?) {
            if (n == null) return
            inorder(n.left)
            appendFromPiece(sb, n.piece, 0, n.piece.length)
            inorder(n.right)
        }
        inorder(root)
        return sb.toString()
    }

    private fun insertPieceAt(pos: Int, piece: Piece) {
        val (left, right) = split(root, pos)
        val node = Node(piece)
        root = merge(merge(left, node), right)
    }

    private fun deleteRange(pos: Int, len: Int) {
        val (left, rest) = split(root, pos)
        val (_, right) = split(rest, len)
        root = merge(left, right)
    }

    private fun deleteAndReturnPiece(pos: Int, len: Int): PieceRef {
        if (len == 0) return PieceRef(BUF_ADD, addBuffer.length, 0)
        val (left, rest) = split(root, pos)
        val (middle, right) = split(rest, len)
        val sb = StringBuilder()
        fun collect(n: Node?) {
            if (n == null) return
            collect(n.left)
            appendFromPiece(sb, n.piece, 0, n.piece.length)
            collect(n.right)
        }
        collect(middle)
        val offset = addBuffer.length
        addBuffer.append(sb)
        root = merge(left, right)
        return PieceRef(BUF_ADD, offset, len)
    }

    sealed class Op {
        data class Insert(val pos: Int, val pieceRef: PieceRef) : Op()
        data class Delete(val pos: Int, val length: Int, val deletedRef: PieceRef) : Op()
    }

    fun insertWithOp(pos: Int, text: String): Op {
        if (text.isEmpty()) return Op.Insert(pos, PieceRef(BUF_ADD, addBuffer.length, 0))
        val offset = addBuffer.length
        addBuffer.append(text)
        insertPieceAt(pos, Piece(BUF_ADD, offset, text.length))
        return Op.Insert(pos, PieceRef(BUF_ADD, offset, text.length))
    }

    fun deleteWithOp(pos: Int, len: Int): Op {
        val delRef = deleteAndReturnPiece(pos, len)
        return Op.Delete(pos, len, delRef)
    }

    fun apply(op: Op) {
        when (op) {
            is Op.Insert -> insertPieceAt(op.pos, Piece(op.pieceRef.bufferId, op.pieceRef.offset, op.pieceRef.length))
            is Op.Delete -> deleteRange(op.pos, op.length)
        }
    }

    fun invert(op: Op): Op {
        return when (op) {
            is Op.Insert -> Op.Delete(op.pos, op.pieceRef.length, PieceRef(op.pieceRef.bufferId, op.pieceRef.offset, op.pieceRef.length))
            is Op.Delete -> Op.Insert(op.pos, PieceRef(op.deletedRef.bufferId, op.deletedRef.offset, op.deletedRef.length))
        }
    }
}

// -------------------- HistoryManager --------------------
class HistoryManager {
    private val undo = ArrayDeque<PieceTable.Op>()
    private val redo = ArrayDeque<PieceTable.Op>()
    val canUndo: Boolean get() = undo.isNotEmpty()
    val canRedo: Boolean get() = redo.isNotEmpty()

    fun pushInverse(op: PieceTable.Op) {
        undo.addLast(op)
        redo.clear()
    }

    fun undo(doc: PieceTable): PieceTable.Op? {
        if (undo.isEmpty()) return null
        val op = undo.removeLast()
        val redoOp = doc.invert(op)
        doc.apply(op)
        redo.addLast(redoOp)
        return op
    }

    fun redo(doc: PieceTable): PieceTable.Op? {
        if (redo.isEmpty()) return null
        val op = redo.removeLast()
        val inv = doc.invert(op)
        doc.apply(op)
        undo.addLast(inv)
        return op
    }
}

// -------------------- EditorViewModel --------------------

data class TabMeta(
    val id: String = UUID.randomUUID().toString(),
    val docId: String,
    val fileName: String,
    val fileUri: Uri? = null,
    val isDirty: Boolean = false
)

data class EditorUiState(
    val tabs: List<TabMeta> = emptyList(),
    val selectedIndex: Int = 0,
    val visibleText: String = "",
    val selection: TextRange = TextRange(0),
    val canUndo: Boolean = false,
    val canRedo: Boolean = false
)

class EditorViewModel : ViewModel() {
    private val docs = mutableMapOf<String, PieceTable>()
    private val histories = mutableMapOf<String, HistoryManager>()
    private val _uiState = MutableStateFlow(EditorUiState())
    val uiState: StateFlow<EditorUiState> = _uiState
    @Volatile var applyingModelUpdate = false
    private val editorExecutor = Executors.newSingleThreadExecutor { r -> Thread(r, "editor-dispatcher").apply { isDaemon = true } }
    private val editorDispatcher = editorExecutor.asCoroutineDispatcher()
    private var diffJob: Job? = null

    // helper to clamp selected index safely for a given tabs list
    private fun clampIndexFor(tabs: List<TabMeta>, idx: Int): Int = when {
        tabs.isEmpty() -> 0
        idx < 0 -> 0
        idx > tabs.lastIndex -> tabs.lastIndex
        else -> idx
    }

    fun createTab(initialText: String = "", fileName: String = "New File"): String {
        val docId = UUID.randomUUID().toString()
        docs[docId] = PieceTable(initialText)
        histories[docId] = HistoryManager()
        val meta = TabMeta(docId = docId, fileName = fileName)
        val tabs = _uiState.value.tabs + meta
        val newIndex = tabs.lastIndex
        val safeIndex = clampIndexFor(tabs, newIndex)
        _uiState.value = _uiState.value.copy(
            tabs = tabs,
            selectedIndex = safeIndex,
            visibleText = docs[docId]!!.toString(),
            selection = TextRange(docs[docId]!!.length),
            canUndo = false,
            canRedo = false
        )
        return docId
    }

    fun newTab() = createTab(initialText = "", fileName = "New File ${_uiState.value.tabs.size + 1}")

    fun closeTabById(id: String) {
        val cur = _uiState.value
        val idx = cur.tabs.indexOfFirst { it.id == id }
        if (idx == -1) return

        val remaining = cur.tabs.toMutableList().also { it.removeAt(idx) }
        val newSelected = clampIndexFor(remaining, idx)

        if (remaining.isEmpty()) {
            _uiState.value = cur.copy(
                tabs = remaining,
                selectedIndex = newSelected,
                visibleText = "",
                selection = TextRange(0),
                canUndo = false,
                canRedo = false
            )
        } else {
            val selTab = remaining[newSelected]
            val doc = docs[selTab.docId]
            val hist = histories[selTab.docId]
            _uiState.value = cur.copy(
                tabs = remaining,
                selectedIndex = newSelected,
                visibleText = doc?.toString() ?: "",
                selection = TextRange((doc?.length ?: 0).coerceAtLeast(0)),
                canUndo = hist?.canUndo == true,
                canRedo = hist?.canRedo == true
            )
        }
    }

    fun selectTabById(id: String) {
        val idx = _uiState.value.tabs.indexOfFirst { it.id == id }
        if (idx != -1) {
            val tab = _uiState.value.tabs[idx]
            val doc = docs[tab.docId] ?: PieceTable("")
            _uiState.value = _uiState.value.copy(
                selectedIndex = idx,
                visibleText = doc.toString(),
                selection = TextRange(doc.length),
                canUndo = histories[tab.docId]?.canUndo == true,
                canRedo = histories[tab.docId]?.canRedo == true
            )
        }
    }

    fun applyTextChangeFromUi(newValue: androidx.compose.ui.text.input.TextFieldValue) {
        diffJob?.cancel()
        diffJob = viewModelScope.launch {
            delay(8)
            withContext(editorDispatcher) {
                val cur = _uiState.value
                val safeIdx = clampIndexFor(cur.tabs, cur.selectedIndex)
                if (safeIdx !in cur.tabs.indices) return@withContext
                val tab = cur.tabs[safeIdx]
                val doc = docs[tab.docId] ?: return@withContext
                val history = histories[tab.docId] ?: return@withContext
                val old = cur.visibleText
                val fresh = newValue.text
                if (old == fresh) {
                    withContext(Dispatchers.Main) { _uiState.value = _uiState.value.copy(selection = newValue.selection) }
                    return@withContext
                }

                val prefix = sequence {
                    val min = minOf(old.length, fresh.length)
                    var i = 0
                    while (i < min && old[i] == fresh[i]) { yield(i); i++ }
                }.count()

                var oldSuffixLen = old.length - prefix
                var newSuffixLen = fresh.length - prefix
                var suffix = 0
                while (suffix < oldSuffixLen && suffix < newSuffixLen &&
                    old[old.length - 1 - suffix] == fresh[fresh.length - 1 - suffix]) suffix++

                val removeStart = prefix
                val removeLen = old.length - prefix - suffix
                val addText = if (fresh.length - prefix - suffix > 0) fresh.substring(prefix, fresh.length - suffix) else ""

                if (removeLen > 0) {
                    val op = doc.deleteWithOp(removeStart, removeLen)
                    val inv = doc.invert(op)
                    history.pushInverse(inv)
                }
                if (addText.isNotEmpty()) {
                    val op = doc.insertWithOp(removeStart, addText)
                    val inv = doc.invert(op)
                    history.pushInverse(inv)
                }

                withContext(Dispatchers.Main) {
                    applyingModelUpdate = true
                    try {
                        val newFull = doc.toString()
                        val caret = removeStart + addText.length
                        val newSelection = TextRange(caret.coerceIn(0, newFull.length))
                        val updatedTabs = _uiState.value.tabs.toMutableList()
                        val safeIdxMain = clampIndexFor(updatedTabs, _uiState.value.selectedIndex)
                        if (safeIdxMain in updatedTabs.indices) updatedTabs[safeIdxMain] = updatedTabs[safeIdxMain].copy(isDirty = true)

                        _uiState.value = _uiState.value.copy(
                            tabs = updatedTabs,
                            visibleText = newFull,
                            selection = newSelection,
                            canUndo = history.canUndo,
                            canRedo = history.canRedo
                        )
                    } finally { applyingModelUpdate = false }
                }
            }
        }
    }

    fun undo() = runUndoRedo(true)
    fun redo() = runUndoRedo(false)

    private fun runUndoRedo(isUndo: Boolean) {
        viewModelScope.launch {
            withContext(editorDispatcher) {
                val cur = _uiState.value
                val safeIdx = clampIndexFor(cur.tabs, cur.selectedIndex)
                if (safeIdx !in cur.tabs.indices) return@withContext
                val tab = cur.tabs[safeIdx]
                val doc = docs[tab.docId] ?: return@withContext
                val history = histories[tab.docId] ?: return@withContext
                if (isUndo) history.undo(doc) else history.redo(doc)
                withContext(Dispatchers.Main) {
                    applyingModelUpdate = true
                    try {
                        val newFull = doc.toString()
                        val newSel = TextRange(newFull.length)
                        val updatedTabs = _uiState.value.tabs.toMutableList()
                        val safeIdxMain = clampIndexFor(updatedTabs, _uiState.value.selectedIndex)
                        if (safeIdxMain in updatedTabs.indices) updatedTabs[safeIdxMain] = updatedTabs[safeIdxMain].copy(isDirty = true)

                        _uiState.value = _uiState.value.copy(
                            tabs = updatedTabs,
                            visibleText = newFull,
                            selection = newSel,
                            canUndo = history.canUndo,
                            canRedo = history.canRedo
                        )
                    } finally { applyingModelUpdate = false }
                }
            }
        }
    }

    fun openFile(context: Context, uri: Uri) {
        viewModelScope.launch(Dispatchers.IO) {
            val content = readFile(context, uri)
            val docId = UUID.randomUUID().toString()
            docs[docId] = PieceTable(content)
            histories[docId] = HistoryManager()
            val name = getFileName(context, uri) ?: "Untitled"
            val meta = TabMeta(docId = docId, fileName = name, fileUri = uri, isDirty = false)
            withContext(Dispatchers.Main) {
                val tabs = _uiState.value.tabs + meta
                val newIndex = tabs.lastIndex
                val safeIndex = clampIndexFor(tabs, newIndex)
                _uiState.value = _uiState.value.copy(
                    tabs = tabs,
                    selectedIndex = safeIndex,
                    visibleText = docs[docId]!!.toString(),
                    selection = TextRange(docs[docId]!!.length),
                    canUndo = false,
                    canRedo = false
                )
            }
        }
    }

    fun saveToUri(context: Context, uri: Uri) {
        val cur = _uiState.value
        val safeIdx = clampIndexFor(cur.tabs, cur.selectedIndex)
        if (safeIdx !in cur.tabs.indices) return
        val tab = cur.tabs[safeIdx]
        val doc = docs[tab.docId] ?: return
        viewModelScope.launch(Dispatchers.IO) {
            writeFile(context, uri, doc.toString())
            val name = getFileName(context, uri) ?: tab.fileName
            withContext(Dispatchers.Main) {
                val updatedTabs = _uiState.value.tabs.toMutableList()
                val safeIdxMain = clampIndexFor(updatedTabs, _uiState.value.selectedIndex)
                if (safeIdxMain in updatedTabs.indices) updatedTabs[safeIdxMain] = updatedTabs[safeIdxMain].copy(isDirty = false, fileName = name, fileUri = uri)
                _uiState.value = _uiState.value.copy(tabs = updatedTabs)
            }
        }
    }

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
            val idx = cursor.getColumnIndex(OpenableColumns.DISPLAY_NAME)
            if (cursor.moveToFirst() && idx >= 0) {
                name = cursor.getString(idx)
            }
        }
        return name
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

    val openLauncher = rememberLauncherForActivityResult(ActivityResultContracts.OpenDocument()) { uri ->
        if (uri != null) vm.openFile(context, uri)
    }
    val saveAsLauncher = rememberLauncherForActivityResult(ActivityResultContracts.CreateDocument("text/plain")) { uri ->
        if (uri != null) vm.saveToUri(context, uri)
        if (uri != null) Toast.makeText(context, "File saved!", Toast.LENGTH_SHORT).show()
    }

    Column(modifier = Modifier.fillMaxSize()) {
        Row(modifier = Modifier.fillMaxWidth().padding(8.dp), horizontalArrangement = Arrangement.SpaceEvenly, verticalAlignment = Alignment.CenterVertically) {
            Button(onClick = { openLauncher.launch(arrayOf("text/plain")) }, enabled = true) { Text("Load") }
            Button(onClick = {
                val idx = state.selectedIndex.coerceIn(0, maxOf(0, state.tabs.lastIndex))
                if (idx in state.tabs.indices) {
                    val tab = state.tabs[idx]
                    if (tab.fileUri != null) vm.saveToUri(context, tab.fileUri)
                    else saveAsLauncher.launch("${tab.fileName}.txt")
                }
            }, enabled = state.tabs.isNotEmpty()) { Text("Save") }
            Button(onClick = {
                val idx = state.selectedIndex.coerceIn(0, maxOf(0, state.tabs.lastIndex))
                if (idx in state.tabs.indices) {
                    val tab = state.tabs[idx]
                    saveAsLauncher.launch("${tab.fileName}.txt")
                }
            }, enabled = state.tabs.isNotEmpty()) { Text("Save As") }
            Button(onClick = { vm.undo() }, enabled = state.canUndo) { Text("Undo") }
            Button(onClick = { vm.redo() }, enabled = state.canRedo) { Text("Redo") }
        }

        Row(verticalAlignment = Alignment.CenterVertically) {
            val tabsSnapshot = state.tabs      // snapshot once
            // clamp using the same snapshot
            val selectedIndexForRow = tabsSnapshot
                .let { tabs ->
                    if (tabs.isEmpty()) 0
                    else state.selectedIndex.coerceIn(0, tabs.lastIndex)
                }

            // Key by tabs size (or tabs IDs) to ensure children and selected index are from same snapshot
            key(tabsSnapshot.size, tabsSnapshot.map { it.id }.hashCode()) {
                if (tabsSnapshot.isNotEmpty()) {
                    ScrollableTabRow(
                        selectedTabIndex = selectedIndexForRow,
                        modifier = Modifier.weight(1f),
                        edgePadding = 0.dp
                    ) {
                        tabsSnapshot.forEachIndexed { idx, tab ->
                            key(tab.id) {
                                Tab(selected = idx == selectedIndexForRow, onClick = { vm.selectTabById(tab.id) }, text = {
                                    Row(verticalAlignment = Alignment.CenterVertically) {
                                        Text(tab.fileName + if (tab.isDirty) "*" else "", maxLines = 1)
                                        Spacer(Modifier.width(4.dp))
                                        IconButton(onClick = { vm.closeTabById(tab.id) }, modifier = Modifier.size(22.dp)) {
                                            Icon(Icons.Default.Close, contentDescription = "Close Tab", modifier = Modifier.size(16.dp))
                                        }
                                    }
                                })
                            }
                        }
                    }
                } else {
                    Box(modifier = Modifier.weight(1f).padding(start = 12.dp)) { Text("No files open") }
                }
            }

            IconButton(onClick = { vm.newTab() }) { Icon(Icons.Default.Add, contentDescription = "New Tab") }
        }


        Box(modifier = Modifier.fillMaxSize().padding(8.dp)) {
            var textState by remember(state.tabs, state.visibleText) { mutableStateOf(TextFieldValue(state.visibleText, state.selection)) }

            LaunchedEffect(state.visibleText, state.selection) { textState = TextFieldValue(state.visibleText, state.selection) }

            if (state.tabs.isEmpty()) {
                Box(modifier = Modifier.fillMaxSize(), contentAlignment = Alignment.Center) { Text("Open or create a file to start editing") }
            } else {
                BasicTextField(value = textState, onValueChange = { newValue ->
                    if (vm.applyingModelUpdate) { textState = newValue; return@BasicTextField }
                    if (newValue.text == textState.text) { textState = newValue; vm.applyTextChangeFromUi(newValue); return@BasicTextField }
                    textState = newValue
                    vm.applyTextChangeFromUi(newValue)
                }, modifier = Modifier.fillMaxSize().verticalScroll(rememberScrollState()))
            }
        }
    }
}
