# A game's quiver draws its arrows as stacks of at most 1n+m arrows each:
# the UI pours the count into stacks, and draws the open stack even when
# it is empty. Saving sums the stacks back into the count. LAWS: the
# count survives the round trip, so no arrow is lost or made, and no
# drawn stack holds more than 1n+m arrows.

import Base

def sum(xs: List<Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      Nat.add(x, sum(rest))

# pours n more arrows into stacks of at most 1n+m arrows; the open
# stack holds c arrows and has room for r more
def pour(+m: Nat, n: Nat, r: Nat, c: Nat) -> List<Nat>:
  match n:
    case 0n:
      [c]
    case 1n+p:
      match r:
        case 0n:
          c <> pour(m, p, m, 1n)
        case 1n+q:
          pour(m, p, q, 1n+c)

# the stacks that draw n arrows
def split(+m: Nat, n: Nat) -> List<Nat>:
  pour(m, n, 1n+m, 0n)

# LE(a, b): a proof that a <= b
def LE(a: Nat, b: Nat) -> Type:
  match a b:
    case 0n b0:
      Unit
    case 1n+a1 0n:
      Empty
    case 1n+a1 1n+b1:
      LE(a1, b1)

# every stack holds at most 1n+m arrows
def Bounded(m: Nat, xs: List<Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case x <> rest:
      (LE(x, 1n+m) & Bounded(m, rest))

# LAW: the arrows survive the round trip
law split_sum:
  for +m: Nat
  for n: Nat
  {sum(split(m, n)) == n : Nat}

# LAW: no drawn stack overflows
law split_bounded:
  for +m: Nat
  for n: Nat
  Bounded(m, split(m, n))

