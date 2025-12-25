package com.example.myapplication.lib

import com.example.myapplication.core.PieceTableMemento

// T as the memento of the document
interface DocumentHistory<T>{
    fun apply(m: T): T
}

// T as the document itself, U as the memento delta
class HistoryManager<T: DocumentHistory<U>, U>{

    enum class EditType {
        INSERTING,
        DELETING,
        OTHER
    }

    private val undo = ArrayDeque<List<U>>()
    private val redo = ArrayDeque<List<U>>()

    private var currentBatch = mutableListOf<U>()
    private var lastType: EditType? = null

    val canUndo: Boolean
        get() = undo.isNotEmpty() || currentBatch.isNotEmpty()

    val canRedo: Boolean
        get() = redo.isNotEmpty()

    private fun shouldMerge(type: EditType): Boolean {
        if (currentBatch.isEmpty()) return true
        return lastType == type &&
                (type == EditType.INSERTING || type == EditType.DELETING)
    }

    @Synchronized
    fun push(m: U, type: EditType) {
        if (type == EditType.OTHER) {
            finalizeBatchLocked()
            undo.addLast(listOf(m))
            redo.clear()
            lastType = null
            return
        }

        if (!shouldMerge(type)) {
            finalizeBatchLocked()
        }

        currentBatch.add(m)
        lastType = type
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
        lastType = null
    }

    @Synchronized
    fun undo(doc: T): Boolean {
        finalizeBatchLocked()
        if (undo.isEmpty()) return false

        val batch = undo.removeLast()
        val redoBatch = mutableListOf<U>()

        for (m in batch.asReversed()) {
            val inverse = doc.apply(m)
            redoBatch.add(inverse)
        }

        redo.addLast(redoBatch.asReversed())
        return true
    }

    @Synchronized
    fun redo(doc: T): Boolean {
        if (redo.isEmpty()) return false

        val batch = redo.removeLast()
        val undoBatch = mutableListOf<U>()

        for (m in batch) {
            val inverse = doc.apply(m)
            undoBatch.add(inverse)
        }

        undo.addLast(undoBatch)
        return true
    }
}
