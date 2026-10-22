# A high-score board keeps its scores in an AVL tree: a binary search
# tree whose insert rotates a node when one side grows two levels
# taller than the other. Scores may repeat; build folds a list of
# scores into a tree and to_list reads them back in order. LAWS: insert
# keeps the search order and adds exactly one score, so build yields an
# ordered tree with the same scores, multiplicities and size as its
# list, and to_list of an ordered tree is sorted and keeps every count.

import Base

type Tree is Data:
  Leaf{}
  Node{l: Tree, k: Nat, r: Tree}

def max(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n b:
      b
    case 1n+a 0n:
      1n+a
    case 1n+a 1n+b:
      1n+max(a, b)

def height(t: Tree) -> Nat:
  match t:
    case Leaf{}:
      0n
    case Node{l, k, r}:
      1n+max(height(l), height(r))

# LE(a, b): a <= b, as a type: Unit when it holds, Empty when it fails
def LE(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n b:
      Unit
    case 1n+a 0n:
      Empty
    case 1n+a 1n+b:
      LE(a, b)

# the verdict of a comparison, with its evidence
def le_case(x: Nat, k: Nat) -> Or(LE(x, k), LE(k, x)):
  match x k:
    case 0n b:
      Inl{Unit{}}
    case 1n+a 0n:
      Inr{Unit{}}
    case 1n+a 1n+b:
      le_case(a, b)

# the left child becomes the root
def rot_r(l: Tree, k: Nat, r: Tree) -> Tree:
  match l:
    case Leaf{}:
      Node{Leaf{}, k, r}
    case Node{ll, lk, lr}:
      Node{ll, lk, Node{lr, k, r}}

# the right child becomes the root
def rot_l(l: Tree, k: Nat, r: Tree) -> Tree:
  match r:
    case Leaf{}:
      Node{l, k, Leaf{}}
    case Node{rl, rk, rr}:
      Node{Node{l, k, rl}, rk, rr}

# the left child is two levels taller; c compares its own two sides,
# and a taller inner side is rotated out first
def fix_l(ll: Tree, lk: Nat, lr: Tree, k: Nat, r: Tree, c: Cmp) -> Tree:
  match c:
    case LT{}:
      rot_r(rot_l(ll, lk, lr), k, r)
    case c:
      rot_r(Node{ll, lk, lr}, k, r)

def fix_r(l: Tree, k: Nat, rl: Tree, rk: Nat, rr: Tree, c: Cmp) -> Tree:
  match c:
    case GT{}:
      rot_l(l, k, rot_r(rl, rk, rr))
    case c:
      rot_l(l, k, Node{rl, rk, rr})

# c compares height(l) with 1n+height(r): GT means l is two levels taller
def bal_l(l: Tree, k: Nat, r: Tree, c: Cmp) -> Tree:
  match l c:
    case Node{+ll, lk, +lr} GT{}:
      fix_l(ll, lk, lr, k, r, Nat.cmp(height(ll), height(lr)))
    case l c:
      Node{l, k, r}

def bal_r(l: Tree, k: Nat, r: Tree, c: Cmp) -> Tree:
  match r c:
    case Node{+rl, rk, +rr} GT{}:
      fix_r(l, k, rl, rk, rr, Nat.cmp(height(rl), height(rr)))
    case r c:
      Node{l, k, r}

# x goes left when x <= k, else right; il and ir insert it there
def ins.go(-x: Nat, +l: Tree, k: Nat, +r: Tree, c: Or(LE(x, k), LE(k, x)), il: Unit -> Tree, ir: Unit -> Tree) -> Tree:
  match c:
    case Inl{e}:
      +l2 = il(Unit{})
      bal_l(l2, k, r, Nat.cmp(height(l2), 1n+height(r)))
    case Inr{e}:
      +r2 = ir(Unit{})
      bal_r(l, k, r2, Nat.cmp(height(r2), 1n+height(l)))

def insert(+x: Nat, +t: Tree) -> Tree:
  match t:
    case Leaf{}:
      Node{Leaf{}, x, Leaf{}}
    case Node{+l, +k, +r}:
      ins.go(x, l, k, r, le_case(x, k), u => insert(x, l), u => insert(x, r))

def build(xs: List<&2, Nat>) -> Tree:
  match xs:
    case Nil{}:
      Leaf{}
    case h <> t:
      insert(h, build(t))

# Bst(lo, hi, t): every score of t lies in lo..hi and the tree is ordered
def Bst(lo: Nat, hi: Nat, t: Tree) -> Type:
  match t:
    case Leaf{}:
      Unit
    case Node{l, k, r}:
      (LE(lo, k) & LE(k, hi) & Bst(lo, k, l) & Bst(k, hi, r))

# every score of the list is at most top
def InRange(top: Nat, xs: List<&2, Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      (LE(h, top) & InRange(top, t))

def bump(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

# how many times y occurs in the tree
def count(+y: Nat, t: Tree) -> Nat:
  match t:
    case Leaf{}:
      0n
    case Node{l, k, r}:
      Nat.add(count(y, l), bump(Cmp.is_eq(Nat.cmp(y, k)), count(y, r)))

# how many times y occurs in the list
def tally(+y: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      bump(Cmp.is_eq(Nat.cmp(y, h)), tally(y, t))

# the scores in order, in front of acc
def to_list(t: Tree, acc: List<&2, Nat>) -> List<&2, Nat>:
  match t:
    case Leaf{}:
      acc
    case Node{l, k, r}:
      to_list(l, k <> to_list(r, acc))

# Sorted.from(lo, xs): every element is at least lo and the list ascends
def Sorted.from(lo: Nat, xs: List<&2, Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      (LE(lo, h) & Sorted.from(h, t))

def size(t: Tree) -> Nat:
  match t:
    case Leaf{}:
      0n
    case Node{l, k, r}:
      Nat.add(size(l), 1n+size(r))

def len(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      1n+len(t)

# LAW: insert keeps the tree ordered within its bounds
law insert_ord:
  for +x: Nat
  for +t: Tree
  for +lo: Nat
  for +hi: Nat
  Bst(lo, hi, t) -> LE(lo, x) -> LE(x, hi) -> Bst(lo, hi, insert(x, t))

# LAW: insert adds one occurrence of x and keeps every other count
law insert_count:
  for +y: Nat
  for +x: Nat
  for +t: Tree
  {bump(Cmp.is_eq(Nat.cmp(y, x)), count(y, t)) == count(y, insert(x, t)) : Nat}

# LAW: a board built from scores at most top is ordered within 0..top
law build_ord:
  for +top: Nat
  for +xs: List<&2, Nat>
  for ok: InRange(top, xs)
  Bst(0n, top, build(xs))

# LAW: the board holds each score as many times as the list does
law build_count:
  for +y: Nat
  for +xs: List<&2, Nat>
  {count(y, build(xs)) == tally(y, xs) : Nat}

# LAW: the board lists its scores in ascending order
law to_list_sorted:
  for +top: Nat
  for +t: Tree
  for b: Bst(0n, top, t)
  Sorted.from(0n, to_list(t, Nil{}))

# LAW: the listing holds each score as many times as the tree does
law to_list_count:
  for +y: Nat
  for +t: Tree
  for +acc: List<&2, Nat>
  {Nat.add(count(y, t), tally(y, acc)) == tally(y, to_list(t, acc)) : Nat}

# LAW: the board holds as many scores as its list
law build_size:
  for +xs: List<&2, Nat>
  {size(build(xs)) == len(xs) : Nat}

