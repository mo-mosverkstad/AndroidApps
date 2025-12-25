package com.example.myapplication.lib

import kotlin.random.Random

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