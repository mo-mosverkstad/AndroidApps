package com.example.myapplication.core

import com.example.myapplication.lib.PieceRef
import com.example.myapplication.lib.PieceTable

data class PieceTableMemento(
    val pos: Int,
    val deleted: PieceRef,
    val inserted: PieceRef
)

class PieceTableDocument(
    private val table: PieceTable
) {

    val length: Int get() = table.length
    override fun toString(): String = table.toString()

    fun insert(pos: Int, text: String): PieceTableMemento {
        val ins = table.insert(pos, text)
        return PieceTableMemento(
            pos = pos,
            deleted = PieceRef(ins.bufferId, ins.offset, 0),
            inserted = ins
        )
    }

    fun delete(pos: Int, len: Int): PieceTableMemento {
        val del = table.delete(pos, len)
        return PieceTableMemento(
            pos = pos,
            deleted = del,
            inserted = PieceRef(del.bufferId, del.offset, 0)
        )
    }

    fun apply(m: PieceTableMemento): PieceTableMemento {
        if (m.inserted.length > 0)
            table.deleteRange(m.pos, m.inserted.length)

        if (m.deleted.length > 0)
            table.insertPiece(m.pos, m.deleted)

        return PieceTableMemento(
            pos = m.pos,
            deleted = m.inserted,
            inserted = m.deleted
        )
    }
}
