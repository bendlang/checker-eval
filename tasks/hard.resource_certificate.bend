# A workshop assigns natural-number certificates to binary resource trees.
# Triangular diagonals pack both child certificates into one number.
# Prove that equal certificates identify exactly the same tree.
import Base

type Resource is Data:
  Leaf{}
  Fork{left: Resource, right: Resource}

def triangle(+n: Nat) -> Nat:
  match n:
    case 0n: 0n
    case 1n+p: 1n+Nat.add(p, triangle(p))

def diagonal(+a: Nat, +b: Nat) -> Nat:
  Nat.add(b, triangle(Nat.add(a, b)))

def certificate(t: Resource) -> Nat:
  match t:
    case Leaf{}: 0n
    case Fork{l, r}: 1n+diagonal(certificate(l), certificate(r))

law certificate_unique:
  for t: Resource
  for u: Resource
  for e: {certificate(t) == certificate(u) : Nat}
  {t == u : Resource}

