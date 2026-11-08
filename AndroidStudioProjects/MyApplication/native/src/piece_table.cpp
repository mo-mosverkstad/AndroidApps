#include "editor/piece_table.h"

#include <algorithm>
#include <stdexcept>
#include <string>
#include <utility>

namespace editor {

struct PieceTable::Node {
    Piece piece;
    uint32_t priority = 0;
    Node* left = nullptr;
    Node* right = nullptr;
    int32_t subtreeLength = 0;
};

// ---------------------------------------------------------------------------
// construction
// ---------------------------------------------------------------------------

PieceTable::PieceTable(ustring initial) : original_(std::move(initial)) {
    if (!original_.empty()) {
        root_ = makeNode(Piece{BufferId::Original, 0, static_cast<int32_t>(original_.size())});
    }
}

PieceTable::~PieceTable() { destroy(root_); }

PieceTable::PieceTable(PieceTable&& other) noexcept
    : original_(std::move(other.original_)),
      added_(std::move(other.added_)),
      root_(other.root_),
      rngState_(other.rngState_) {
    other.root_ = nullptr;
}

PieceTable& PieceTable::operator=(PieceTable&& other) noexcept {
    if (this != &other) {
        destroy(root_);
        original_ = std::move(other.original_);
        added_ = std::move(other.added_);
        root_ = other.root_;
        rngState_ = other.rngState_;
        other.root_ = nullptr;
    }
    return *this;
}

uint32_t PieceTable::nextPriority() {
    // xorshift32
    uint32_t x = rngState_;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    rngState_ = x;
    return x;
}

PieceTable::Node* PieceTable::makeNode(const Piece& p) {
    Node* n = new Node();
    n->piece = p;
    n->priority = nextPriority();
    n->subtreeLength = p.length;
    return n;
}

// ---------------------------------------------------------------------------
// treap primitives
// ---------------------------------------------------------------------------

int32_t PieceTable::subtreeLength(Node* n) { return n ? n->subtreeLength : 0; }

void PieceTable::recalc(Node* n) {
    if (!n) return;
    n->subtreeLength = n->piece.length + subtreeLength(n->left) + subtreeLength(n->right);
}

PieceTable::Node* PieceTable::merge(Node* a, Node* b) {
    if (!a) return b;
    if (!b) return a;
    if (a->priority > b->priority) {
        a->right = merge(a->right, b);
        recalc(a);
        return a;
    }
    b->left = merge(a, b->left);
    recalc(b);
    return b;
}

// Splits the sequence so that *outLeft holds the first `index` characters.
//
// When `index` falls inside a piece, the piece is cut in two. Both halves
// inherit the ORIGINAL node's priority. The Kotlin version this replaces gave
// each half a fresh random priority while letting them adopt the original
// node's children, which could violate the treap's heap property and let the
// tree degenerate. Reusing the priority keeps the invariant intact: the old
// node's priority already dominated both of its children, and each half keeps
// only one of them.
void PieceTable::split(Node* node, int32_t index, Node** outLeft, Node** outRight) {
    if (!node) {
        *outLeft = nullptr;
        *outRight = nullptr;
        return;
    }

    const int32_t leftLen = subtreeLength(node->left);

    if (index <= leftLen) {
        Node* l = nullptr;
        Node* r = nullptr;
        split(node->left, index, &l, &r);
        node->left = r;
        recalc(node);
        *outLeft = l;
        *outRight = node;
        return;
    }

    if (index >= leftLen + node->piece.length) {
        Node* l = nullptr;
        Node* r = nullptr;
        split(node->right, index - leftLen - node->piece.length, &l, &r);
        node->right = l;
        recalc(node);
        *outLeft = node;
        *outRight = r;
        return;
    }

    // 0 < cut < node->piece.length
    const int32_t cut = index - leftLen;

    Node* rightHalf = new Node();
    rightHalf->piece = Piece{node->piece.buffer, node->piece.offset + cut, node->piece.length - cut};
    rightHalf->priority = node->priority;
    rightHalf->left = nullptr;
    rightHalf->right = node->right;
    recalc(rightHalf);

    node->piece.length = cut;
    node->right = nullptr;
    recalc(node);

    *outLeft = node;
    *outRight = rightHalf;
}

// Iterative so that a pathological tree cannot blow the stack.
void PieceTable::destroy(Node* n) {
    if (!n) return;
    std::vector<Node*> stack;
    stack.push_back(n);
    while (!stack.empty()) {
        Node* cur = stack.back();
        stack.pop_back();
        if (cur->left) stack.push_back(cur->left);
        if (cur->right) stack.push_back(cur->right);
        delete cur;
    }
}

void PieceTable::collect(Node* n, std::vector<Piece>& out) {
    std::vector<Node*> stack;
    Node* cur = n;
    while (cur || !stack.empty()) {
        while (cur) {
            stack.push_back(cur);
            cur = cur->left;
        }
        cur = stack.back();
        stack.pop_back();
        if (cur->piece.length > 0) out.push_back(cur->piece);
        cur = cur->right;
    }
}

int32_t PieceTable::heightOf(Node* n) {
    if (!n) return 0;
    std::vector<std::pair<Node*, int32_t>> stack;
    stack.emplace_back(n, 1);
    int32_t best = 0;
    while (!stack.empty()) {
        const std::pair<Node*, int32_t> top = stack.back();
        stack.pop_back();
        best = std::max(best, top.second);
        if (top.first->left) stack.emplace_back(top.first->left, top.second + 1);
        if (top.first->right) stack.emplace_back(top.first->right, top.second + 1);
    }
    return best;
}

// ---------------------------------------------------------------------------
// bounds checking
// ---------------------------------------------------------------------------

void PieceTable::checkPosition(int32_t pos) const {
    const int32_t len = length();
    if (pos < 0 || pos > len) {
        throw std::out_of_range("PieceTable: position " + std::to_string(pos) +
                                " outside [0, " + std::to_string(len) + "]");
    }
}

void PieceTable::checkRange(int32_t pos, int32_t len) const {
    const int32_t total = length();
    if (pos < 0 || len < 0 || pos > total || len > total - pos) {
        throw std::out_of_range("PieceTable: range [" + std::to_string(pos) + ", " +
                                std::to_string(static_cast<int64_t>(pos) + len) +
                                ") outside [0, " + std::to_string(total) + ")");
    }
}

// ---------------------------------------------------------------------------
// reading
// ---------------------------------------------------------------------------

int32_t PieceTable::length() const { return subtreeLength(root_); }

void PieceTable::appendPieceText(const Piece& p, ustring& out) const {
    const ustring& src = (p.buffer == BufferId::Original) ? original_ : added_;
    out.append(src, static_cast<size_t>(p.offset), static_cast<size_t>(p.length));
}

ustring PieceTable::text() const {
    ustring out;
    out.reserve(static_cast<size_t>(length()));

    std::vector<Node*> stack;
    Node* cur = root_;
    while (cur || !stack.empty()) {
        while (cur) {
            stack.push_back(cur);
            cur = cur->left;
        }
        cur = stack.back();
        stack.pop_back();
        appendPieceText(cur->piece, out);
        cur = cur->right;
    }
    return out;
}

ustring PieceTable::substr(int32_t pos, int32_t len) const {
    checkRange(pos, len);

    ustring out;
    if (len == 0) return out;
    out.reserve(static_cast<size_t>(len));

    const int32_t rangeEnd = pos + len;
    int32_t seen = 0;
    bool done = false;

    std::vector<Node*> stack;
    Node* cur = root_;
    while (!done && (cur || !stack.empty())) {
        while (cur) {
            stack.push_back(cur);
            cur = cur->left;
        }
        cur = stack.back();
        stack.pop_back();

        const int32_t pieceStart = seen;
        const int32_t pieceEnd = seen + cur->piece.length;
        seen = pieceEnd;

        if (pieceEnd > pos && pieceStart < rangeEnd) {
            const int32_t from = std::max(pos, pieceStart) - pieceStart;
            const int32_t to = std::min(rangeEnd, pieceEnd) - pieceStart;
            appendPieceText(Piece{cur->piece.buffer, cur->piece.offset + from, to - from}, out);
        }

        if (pieceEnd >= rangeEnd) {
            done = true;
        } else {
            cur = cur->right;
        }
    }
    return out;
}

std::vector<Piece> PieceTable::pieces() const {
    std::vector<Piece> out;
    collect(root_, out);
    return out;
}

int32_t PieceTable::pieceCount() const { return static_cast<int32_t>(pieces().size()); }

int32_t PieceTable::originalBufferSize() const { return static_cast<int32_t>(original_.size()); }

int32_t PieceTable::addedBufferSize() const { return static_cast<int32_t>(added_.size()); }

int32_t PieceTable::treeHeight() const { return heightOf(root_); }

// ---------------------------------------------------------------------------
// writing
// ---------------------------------------------------------------------------

void PieceTable::insert(int32_t pos, const ustring& text) {
    checkPosition(pos);
    if (text.empty()) return;

    const int32_t offset = static_cast<int32_t>(added_.size());
    added_ += text;

    Node* inserted = makeNode(Piece{BufferId::Added, offset, static_cast<int32_t>(text.size())});

    Node* l = nullptr;
    Node* r = nullptr;
    split(root_, pos, &l, &r);
    root_ = merge(merge(l, inserted), r);
}

std::vector<Piece> PieceTable::erase(int32_t pos, int32_t len) {
    checkRange(pos, len);

    std::vector<Piece> removed;
    if (len == 0) return removed;

    Node* left = nullptr;
    Node* rest = nullptr;
    split(root_, pos, &left, &rest);

    Node* mid = nullptr;
    Node* right = nullptr;
    split(rest, len, &mid, &right);

    collect(mid, removed);
    destroy(mid);

    root_ = merge(left, right);
    return removed;
}

void PieceTable::insertPieces(int32_t pos, const std::vector<Piece>& pieces) {
    checkPosition(pos);
    if (pieces.empty()) return;

    Node* chain = nullptr;
    for (const Piece& p : pieces) {
        if (p.length <= 0) continue;
        chain = merge(chain, makeNode(p));
    }
    if (!chain) return;

    Node* l = nullptr;
    Node* r = nullptr;
    split(root_, pos, &l, &r);
    root_ = merge(merge(l, chain), r);
}

}  // namespace editor
