package com.example.myapplication.lib

import kotlin.random.Random

private const val BUF_ORIG = 0
private const val BUF_ADD = 1

data class PieceRef(val bufferId: Int, val offset: Int, val length: Int)
data class Piece(val bufferId: Int, val offset: Int, val length: Int)

/* ===================== TREAP ===================== */

private class Node(
    var piece: Piece,
    var priority: Int = Random.nextInt(),
    var left: Node? = null,
    var right: Node? = null
) {
    var subtreeLen: Int = piece.length
    fun recalc() {
        subtreeLen =
            piece.length +
                    (left?.subtreeLen ?: 0) +
                    (right?.subtreeLen ?: 0)
    }
}

private fun merge(a: Node?, b: Node?): Node? =
    when {
        a == null -> b
        b == null -> a
        a.priority > b.priority -> {
            a.right = merge(a.right, b)
            a.recalc()
            a
        }
        else -> {
            b.left = merge(a, b.left)
            b.recalc()
            b
        }
    }

private fun split(node: Node?, index: Int): Pair<Node?, Node?> {
    if (node == null) return null to null
    val leftLen = node.left?.subtreeLen ?: 0

    return when {
        index < leftLen -> {
            val (l, r) = split(node.left, index)
            node.left = r
            node.recalc()
            l to node
        }

        index > leftLen + node.piece.length -> {
            val (l, r) =
                split(node.right, index - leftLen - node.piece.length)
            node.right = l
            node.recalc()
            node to r
        }

        else -> {
            val cut = index - leftLen
            when (cut) {
                0 -> node.left to run {
                    node.left = null
                    node.recalc()
                    node
                }
                node.piece.length -> run {
                    val r = node.right
                    node.right = null
                    node.recalc()
                    node to r
                }
                else -> {
                    val p = node.piece
                    val left = Node(
                        Piece(p.bufferId, p.offset, cut),
                        Random.nextInt(),
                        node.left,
                        null
                    )
                    val right = Node(
                        Piece(p.bufferId, p.offset + cut, p.length - cut),
                        Random.nextInt(),
                        null,
                        node.right
                    )
                    left.recalc()
                    right.recalc()
                    left to right
                }
            }
        }
    }
}

/* ===================== PIECE TABLE ===================== */

class PieceTable(initialText: String = "") {

    private val original = StringBuilder(initialText)
    private val add = StringBuilder()

    private var root: Node? =
        if (initialText.isNotEmpty())
            Node(Piece(BUF_ORIG, 0, initialText.length))
        else null

    val length: Int
        get() = root?.subtreeLen ?: 0

    override fun toString(): String {
        val sb = StringBuilder(length)
        fun walk(n: Node?) {
            if (n == null) return
            walk(n.left)
            val src = if (n.piece.bufferId == BUF_ORIG) original else add
            sb.append(
                src,
                n.piece.offset,
                n.piece.offset + n.piece.length
            )
            walk(n.right)
        }
        walk(root)
        return sb.toString()
    }

    /* ---------- primitive ops ---------- */

    fun insert(pos: Int, text: String): PieceRef {
        if (text.isEmpty()) return PieceRef(BUF_ADD, add.length, 0)

        val offset = add.length
        add.append(text)

        val (l, r) = split(root, pos)
        root = merge(
            merge(l, Node(Piece(BUF_ADD, offset, text.length))),
            r
        )
        return PieceRef(BUF_ADD, offset, text.length)
    }

    fun delete(pos: Int, len: Int): PieceRef {
        if (len == 0) return PieceRef(BUF_ADD, add.length, 0)

        val (l, rest) = split(root, pos)
        val (mid, r) = split(rest, len)

        val sb = StringBuilder(len)
        fun collect(n: Node?) {
            if (n == null) return
            collect(n.left)
            val src =
                if (n.piece.bufferId == BUF_ORIG) original else add
            sb.append(
                src,
                n.piece.offset,
                n.piece.offset + n.piece.length
            )
            collect(n.right)
        }
        collect(mid)

        val offset = add.length
        add.append(sb)
        root = merge(l, r)

        return PieceRef(BUF_ADD, offset, len)
    }

    fun insertPiece(pos: Int, ref: PieceRef) {
        if (ref.length == 0) return
        val (l, r) = split(root, pos)
        root = merge(
            merge(l, Node(Piece(ref.bufferId, ref.offset, ref.length))),
            r
        )
    }

    fun deleteRange(pos: Int, len: Int) {
        if (len == 0) return
        val (l, rest) = split(root, pos)
        val (_, r) = split(rest, len)
        root = merge(l, r)
    }
}
