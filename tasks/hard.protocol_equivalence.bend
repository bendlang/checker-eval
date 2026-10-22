# Compare finite nondeterministic protocols that take and return channel credits.
# need(p,k) is the least initial credit ensuring every branch stays nonnegative
# and finishes with at least k credits; sequencing runs its left side first.
# Return universal agreement or a concrete final-credit request separating them.
import Base

type Protocol is Data:
  Skip{}
  Take{}
  Put{}
  Seq{left: Protocol, right: Protocol}
  Choice{left: Protocol, right: Protocol}

type Summary is Data:
  Summary{need: Nat, left: Nat}

type Verdict<-f: Nat -> Nat, -g: Nat -> Nat> is Type:
  Same{proof: @k: Nat -> {f(k) == g(k) : Nat}}
  Different{request: Nat, proof: {f(request) == g(request) : Nat} -> Empty}

def pred(n: Nat) -> Nat:
  match n:
    case 0n: 0n
    case 1n+p: p

def maximum(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n b: b
    case 1n+a 0n: 1n+a
    case 1n+a 1n+b: 1n+maximum(a,b)

def need(p: Protocol, +k: Nat) -> Nat:
  match p:
    case Skip{}: k
    case Take{}: 1n+k
    case Put{}: pred(k)
    case Seq{p,q}: need(p,need(q,k))
    case Choice{p,q}: maximum(need(p,k),need(q,k))

law compare:
  for +p: Protocol
  for +q: Protocol
  Verdict<(k => need(p,k)), (k => need(q,k))>

