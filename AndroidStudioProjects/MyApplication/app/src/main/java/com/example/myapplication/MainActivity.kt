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
import androidx.core.net.toUri
import android.util.Log
import androidx.compose.ui.graphics.vector.path

import com.example.myapplication.core.EditorModel
import com.example.myapplication.core.EditorState


class EditorViewModel : ViewModel() {

    private val model = EditorModel()

    private val _uiState = MutableStateFlow(EditorState())
    val uiState: StateFlow<EditorState> = _uiState

    @Volatile
    var applyingModelUpdate = false

    // NO MORE THREADING CODE HERE. It's all gone.

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
        model.updateTabFileInfo(tabId, newFileName, newUri.toString())
        pushState()
    }


    // ---------------------------------------------------------
    // UNDO / REDO
    // ---------------------------------------------------------
    fun undo() {
        model.undo()
        pushState()
    }

    fun redo() {
        model.redo()
        pushState()
    }

    // ---------------------------------------------------------
    // TEXT CHANGE FROM UI - SIMPLE & DIRECT
    // ---------------------------------------------------------
    fun applyTextChangeFromUi(newValue: TextFieldValue) {
        // No more jobs, no more delays. Process the change immediately.
        val old = model.getState().visibleText
        val fresh = newValue.text
        if (old == fresh) {
            return
        }

        val min = minOf(old.length, fresh.length)
        var prefix = 0
        while (prefix < min && old[prefix] == fresh[prefix]) prefix++

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

        applyingModelUpdate = true
        pushState()
        applyingModelUpdate = false
    }

    // ---------------------------------------------------------
    // FILE I/O (ANDROID) - SIMPLE & DIRECT
    // ---------------------------------------------------------
    fun openFile(context: Context, uri: Uri) {
        // Use a background thread ONLY for reading the file from disk.
        viewModelScope.launch(Dispatchers.IO) {
            val text = readFile(context, uri)
            val name = getFileName(context, uri) ?: "Untitled"

            // Switch back to the main thread to update the model and UI.
            withContext(Dispatchers.Main) {
                model.createTab(text, name, uri.toString())
                pushState()
            }
        }
    }

    fun saveToUri(context: Context, uri: Uri) {
        // The model is ALWAYS up-to-date now. No waiting is needed.

        // 1. Finalize the undo group.
        model.finalizeActiveEdits()

        // 2. Get the fresh, correct text.
        val text = model.getActiveDocumentText()

        Log.d("SAVE_DEBUG", "Text being saved: '$text'")

        // 3. Launch a simple background job ONLY for writing to disk.
        viewModelScope.launch(Dispatchers.IO) {
            try {
                writeFile(context, uri, text)
            } catch (e: Exception) {
                Log.e("SAVE_DEBUG", "Error saving file", e)
            }
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
        if (uri.scheme == "content") {
            context.contentResolver.query(uri, null, null, null, null)?.use { cursor ->
                val index = cursor.getColumnIndex(OpenableColumns.DISPLAY_NAME)
                if (cursor.moveToFirst() && index >= 0) {
                    name = cursor.getString(index)
                }
            }
        }
        return name ?: uri.path?.substringAfterLast('/')
    }

    // onCleared is no longer needed.
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
                        vm.saveToUri(context, tab.filePath.toUri())
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

