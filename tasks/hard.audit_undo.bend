# An access-control service keeps an audit log of Grant and Revoke
# actions. The log is a rope: a leaf holds one action, a node holds two
# halves and caches the number of actions under them, so the count is
# O(1) and the halves replay in parallel. undo(log, k) drops the last k
# actions: the right half first, what is left of k off the left half.
# LAW: two undos are one undo of the summed count, and undo keeps the
# cached counts true.

import Base

type Act is Data:
  Grant{p: Nat}
  Revoke{p: Nat}

type Log is Data:
  Emp{}
  One{e: Act}
  Cat{n: Nat, l: Log, r: Log}

# the cached count of actions
def size(t: Log) -> Nat:
  match t:
    case Emp{}:
      0n
    case One{e}:
      1n
    case Cat{n, l, r}:
      n

# joins two logs; an empty half is dropped
def cat.go(+l: Log, +r: Log) -> Log:
  match r:
    case Emp{}:
      l
    case r:
      Cat{Nat.add(size(l), size(r)), l, r}

def cat(+l: Log, +r: Log) -> Log:
  match l:
    case Emp{}:
      r
    case l:
      cat.go(l, r)

# drops the last k actions
def undo(t: Log, +k: Nat) -> Log:
  match t:
    case Emp{}:
      Emp{}
    case One{e}:
      match k:
        case 0n:
          One{e}
        case 1n+p:
          Emp{}
    case Cat{n, l, +r}:
      cat(undo(l, Nat.sub(k, size(r))), undo(r, k))

# every node caches the count of its halves
def WF(t: Log) -> Type:
  match t:
    case Emp{}:
      Unit
    case One{e}:
      Unit
    case Cat{n, l, r}:
      {Nat.add(size(l), size(r)) == n : Nat} & WF(l) & WF(r)

# LAW: undoing b actions, then a more, is undoing a+b actions
law undo_undo:
  for +t: Log
  for +a: Nat
  for +b: Nat
  for w: WF(t)
  {undo(undo(t, b), a) == undo(t, Nat.add(a, b)) : Log}

# LAW: undo keeps the cached counts true
law undo_wf:
  for +t: Log
  for +k: Nat
  for w: WF(t)
  WF(undo(t, k))

