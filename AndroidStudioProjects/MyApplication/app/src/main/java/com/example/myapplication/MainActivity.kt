package com.example.myapplication

import android.content.Context
import android.content.Intent
import android.net.Uri
import android.os.Bundle
import android.provider.OpenableColumns
import android.widget.Toast
import androidx.activity.ComponentActivity
import androidx.activity.compose.rememberLauncherForActivityResult
import androidx.activity.compose.setContent
import androidx.activity.enableEdgeToEdge
import androidx.activity.result.contract.ActivityResultContracts
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.layout.width
import androidx.compose.foundation.text.BasicTextField
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Add
import androidx.compose.material.icons.filled.Close
import androidx.compose.material3.AlertDialog
import androidx.compose.material3.Button
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.ScrollableTabRow
import androidx.compose.material3.Surface
import androidx.compose.material3.Tab
import androidx.compose.material3.Text
import androidx.compose.material3.TextButton
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.collectAsState
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.SolidColor
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.text.TextRange
import androidx.compose.ui.text.TextStyle
import androidx.compose.ui.text.font.FontFamily
import androidx.compose.ui.text.input.TextFieldValue
import androidx.compose.ui.unit.dp
import androidx.core.net.toUri
import androidx.lifecycle.ViewModel
import androidx.lifecycle.viewModelScope
import androidx.lifecycle.viewmodel.compose.viewModel
import com.example.myapplication.core.EditorState
import com.example.myapplication.core.NativeEditor
import com.example.myapplication.core.SelectionRange
import com.example.myapplication.core.TabMeta
import com.example.myapplication.ui.theme.MyApplicationTheme
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.flow.MutableSharedFlow
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.SharedFlow
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.flow.asSharedFlow
import kotlinx.coroutines.flow.asStateFlow
import kotlinx.coroutines.launch
import kotlinx.coroutines.withContext
import java.io.IOException
import java.io.InputStreamReader
import java.io.OutputStreamWriter
import java.nio.charset.StandardCharsets

private const val DEFAULT_FILE_NAME = "untitled.txt"

/**
 * Holds the native editor and the Android-side concerns around it: file I/O
 * through the Storage Access Framework, and one-shot user messages.
 *
 * All editor state lives in the C++ core. This class never second-guesses it;
 * it forwards an event and republishes the resulting snapshot.
 */
class EditorViewModel : ViewModel() {

    private val editor = NativeEditor()

    private val _uiState = MutableStateFlow(editor.state())
    val uiState: StateFlow<EditorState> = _uiState.asStateFlow()

    private val _messages = MutableSharedFlow<String>(extraBufferCapacity = 8)
    val messages: SharedFlow<String> = _messages.asSharedFlow()

    override fun onCleared() {
        editor.close()
        super.onCleared()
    }

    private fun publish() {
        _uiState.value = editor.state()
    }

    // --- tabs --------------------------------------------------------------

    fun newTab() {
        editor.createTab(text = "", fileName = DEFAULT_FILE_NAME)
        publish()
    }

    fun closeTab(tabId: Long) {
        editor.closeTab(tabId)
        publish()
    }

    fun selectTab(tabId: Long) {
        editor.selectTab(tabId)
        publish()
    }

    // --- editing -----------------------------------------------------------

    /**
     * Feeds a whole new [TextFieldValue] to the core, which works out what the
     * actual edit was. Both the text and the caret are forwarded, so the core
     * can group typing correctly and restore the caret on undo.
     */
    fun onEditorInput(value: TextFieldValue) {
        val changed = editor.setText(
            text = value.text,
            selection = SelectionRange(value.selection.start, value.selection.end)
        )
        if (changed) publish()
    }

    fun undo() {
        if (editor.undo()) publish()
    }

    fun redo() {
        if (editor.redo()) publish()
    }

    // --- file I/O ----------------------------------------------------------

    fun openFile(context: Context, uri: Uri) {
        viewModelScope.launch {
            val loaded = runCatching {
                withContext(Dispatchers.IO) {
                    persistPermission(context, uri)
                    readText(context, uri) to queryDisplayName(context, uri)
                }
            }
            loaded
                .onSuccess { (text, name) ->
                    editor.createTab(
                        text = text,
                        fileName = name ?: uri.lastPathSegment ?: DEFAULT_FILE_NAME,
                        filePath = uri.toString()
                    )
                    publish()
                }
                .onFailure { error ->
                    _messages.tryEmit("Couldn't open file: ${error.describe()}")
                }
        }
    }

    /** Saves the active tab to a path it already knows about. */
    fun saveActiveTab(context: Context, uri: Uri) {
        viewModelScope.launch { performSave(context, uri, renameTo = null) }
    }

    /** Saves the active tab to a newly chosen location and adopts its name. */
    fun saveActiveTabAs(context: Context, uri: Uri) {
        viewModelScope.launch {
            val name = runCatching {
                withContext(Dispatchers.IO) { queryDisplayName(context, uri) }
            }.getOrNull()
            performSave(context, uri, renameTo = name)
        }
    }

    /**
     * The tab is only marked clean once the bytes are actually on disk, and
     * only if the document has not moved on in the meantime. The previous
     * implementation marked it clean and showed "File saved!" before the write
     * had even started, so a failed write looked like a success.
     */
    private suspend fun performSave(context: Context, uri: Uri, renameTo: String?) {
        val tab = editor.state().activeTab ?: return

        editor.finalizeEdits()
        val snapshot = editor.activeText()

        val outcome = runCatching {
            withContext(Dispatchers.IO) {
                persistPermission(context, uri)
                writeText(context, uri, snapshot)
            }
        }

        outcome
            .onSuccess {
                val name = renameTo ?: tab.fileName
                editor.setTabFile(tab.id, name, uri.toString())

                val stillCurrent = editor.state().activeTab?.id == tab.id &&
                    editor.activeText() == snapshot
                if (stillCurrent) editor.markTabSaved(tab.id)

                publish()
                _messages.tryEmit(
                    if (stillCurrent) "Saved $name" else "Saved $name (document changed since)"
                )
            }
            .onFailure { error ->
                _messages.tryEmit("Couldn't save: ${error.describe()}")
            }
    }

    // --- helpers -----------------------------------------------------------

    private fun Throwable.describe(): String = message ?: this::class.java.simpleName

    /**
     * Keeps the grant alive across process death. Without this, saving back to
     * a file opened in an earlier session fails with a SecurityException.
     */
    private fun persistPermission(context: Context, uri: Uri) {
        try {
            context.contentResolver.takePersistableUriPermission(
                uri,
                Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION
            )
        } catch (_: SecurityException) {
            // Some providers do not offer a persistable grant. The one-shot
            // grant for this session still works, so carry on.
        }
    }

    private fun readText(context: Context, uri: Uri): String {
        val stream = context.contentResolver.openInputStream(uri)
            ?: throw IOException("No input stream for $uri")
        return stream.use { input ->
            InputStreamReader(input, StandardCharsets.UTF_8).use { it.readText() }
        }
    }

    private fun writeText(context: Context, uri: Uri, text: String) {
        val resolver = context.contentResolver

        // "wt" truncates first. With a plain "w" the provider may keep the
        // tail of the previous, longer file.
        val stream = try {
            resolver.openOutputStream(uri, "wt")
        } catch (_: Exception) {
            resolver.openOutputStream(uri)
        } ?: throw IOException("No output stream for $uri")

        stream.use { output ->
            OutputStreamWriter(output, StandardCharsets.UTF_8).use { it.write(text) }
        }
    }

    private fun queryDisplayName(context: Context, uri: Uri): String? {
        if (uri.scheme == "content") {
            context.contentResolver.query(uri, null, null, null, null)?.use { cursor ->
                val index = cursor.getColumnIndex(OpenableColumns.DISPLAY_NAME)
                if (index >= 0 && cursor.moveToFirst()) {
                    cursor.getString(index)?.let { return it }
                }
            }
        }
        return uri.path?.substringAfterLast('/')?.takeIf { it.isNotBlank() }
    }
}

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

    var pendingClose by remember { mutableStateOf<TabMeta?>(null) }

    LaunchedEffect(vm) {
        vm.messages.collect { message ->
            Toast.makeText(context, message, Toast.LENGTH_SHORT).show()
        }
    }

    val openLauncher = rememberLauncherForActivityResult(
        ActivityResultContracts.OpenDocument()
    ) { uri -> if (uri != null) vm.openFile(context, uri) }

    val saveAsLauncher = rememberLauncherForActivityResult(
        ActivityResultContracts.CreateDocument("text/plain")
    ) { uri -> if (uri != null) vm.saveActiveTabAs(context, uri) }

    val activeTab = state.activeTab

    Column(modifier = Modifier.fillMaxSize()) {

        Row(
            modifier = Modifier
                .fillMaxWidth()
                .padding(8.dp),
            horizontalArrangement = Arrangement.SpaceEvenly,
            verticalAlignment = Alignment.CenterVertically
        ) {
            Button(onClick = { openLauncher.launch(arrayOf("*/*")) }) {
                Text("Load")
            }

            Button(
                onClick = {
                    val tab = activeTab ?: return@Button
                    val path = tab.filePath
                    if (path != null) {
                        vm.saveActiveTab(context, path.toUri())
                    } else {
                        saveAsLauncher.launch(tab.fileName)
                    }
                },
                enabled = activeTab != null
            ) {
                Text("Save")
            }

            Button(
                onClick = { activeTab?.let { saveAsLauncher.launch(it.fileName) } },
                enabled = activeTab != null
            ) {
                Text("Save As")
            }

            Button(onClick = { vm.undo() }, enabled = state.canUndo) { Text("Undo") }
            Button(onClick = { vm.redo() }, enabled = state.canRedo) { Text("Redo") }
        }

        Row(verticalAlignment = Alignment.CenterVertically) {
            if (state.tabs.isEmpty()) {
                Box(
                    modifier = Modifier
                        .weight(1f)
                        .padding(start = 12.dp)
                ) {
                    Text("No files open")
                }
            } else {
                ScrollableTabRow(
                    selectedTabIndex = state.selectedIndex.coerceIn(0, state.tabs.lastIndex),
                    modifier = Modifier.weight(1f),
                    edgePadding = 0.dp
                ) {
                    state.tabs.forEachIndexed { index, tab ->
                        key(tab.id) {
                            Tab(
                                selected = index == state.selectedIndex,
                                onClick = { vm.selectTab(tab.id) },
                                text = {
                                    Row(verticalAlignment = Alignment.CenterVertically) {
                                        Text(
                                            text = tab.fileName + if (tab.isDirty) "*" else "",
                                            maxLines = 1
                                        )
                                        Spacer(Modifier.width(4.dp))
                                        IconButton(
                                            onClick = {
                                                if (tab.isDirty) {
                                                    pendingClose = tab
                                                } else {
                                                    vm.closeTab(tab.id)
                                                }
                                            },
                                            modifier = Modifier.size(22.dp)
                                        ) {
                                            Icon(
                                                imageVector = Icons.Default.Close,
                                                contentDescription = "Close ${tab.fileName}",
                                                modifier = Modifier.size(16.dp)
                                            )
                                        }
                                    }
                                }
                            )
                        }
                    }
                }
            }

            IconButton(onClick = { vm.newTab() }) {
                Icon(Icons.Default.Add, contentDescription = "New tab")
            }
        }

        Box(
            modifier = Modifier
                .fillMaxSize()
                .padding(8.dp)
        ) {
            if (activeTab == null) {
                Box(modifier = Modifier.fillMaxSize(), contentAlignment = Alignment.Center) {
                    Text("Open or create a file to start editing")
                }
            } else {
                EditorTextField(
                    tabId = activeTab.id,
                    text = state.visibleText,
                    selection = state.selection,
                    onValueChange = vm::onEditorInput
                )
            }
        }
    }

    pendingClose?.let { tab ->
        AlertDialog(
            onDismissRequest = { pendingClose = null },
            title = { Text("Discard changes?") },
            text = { Text("${tab.fileName} has unsaved changes. Closing it will lose them.") },
            confirmButton = {
                TextButton(onClick = {
                    vm.closeTab(tab.id)
                    pendingClose = null
                }) {
                    Text("Discard")
                }
            },
            dismissButton = {
                TextButton(onClick = { pendingClose = null }) { Text("Keep editing") }
            }
        )
    }
}

/**
 * Mirrors the core's text and caret into a [TextFieldValue].
 *
 * The local copy is keyed on the tab id alone. Keying it on the text, as the
 * previous version did, re-created the state on every keystroke and fought
 * IME composition.
 */
@Composable
private fun EditorTextField(
    tabId: Long,
    text: String,
    selection: SelectionRange,
    onValueChange: (TextFieldValue) -> Unit
) {
    var field by remember(tabId) {
        mutableStateOf(TextFieldValue(text, TextRange(selection.start, selection.end)))
    }

    val fromCore = toTextFieldValue(text, selection)
    LaunchedEffect(tabId, text, selection) {
        if (field.text != fromCore.text || field.selection != fromCore.selection) {
            field = fromCore
        }
    }

    BasicTextField(
        value = field,
        onValueChange = { updated ->
            field = updated
            onValueChange(updated)
        },
        textStyle = TextStyle(
            fontFamily = FontFamily.Monospace,
            color = MaterialTheme.colorScheme.onSurface
        ),
        cursorBrush = SolidColor(MaterialTheme.colorScheme.primary),
        modifier = Modifier.fillMaxSize()
    )
}

private fun toTextFieldValue(text: String, selection: SelectionRange): TextFieldValue {
    val limit = text.length
    return TextFieldValue(
        text = text,
        selection = TextRange(
            selection.start.coerceIn(0, limit),
            selection.end.coerceIn(0, limit)
        )
    )
}
