# A street musician's live looper records toggle cues at natural timestamps.
# Adjacent copies of the same cue cancel; different cues do not commute.
# Return a reduced cue sequence with exactly the same action on every reduced
# suffix, and prove that this canonical representative is unique.
import Base

def same(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+q:
      False{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      same(p, q)

def choose(x: Nat, h: Nat, t: +List<Nat>, b: Bool) -> +List<Nat>:
  match b:
    case True{}:
      t
    case False{}:
      x <> h <> t

def toggle(+x: Nat, xs: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      [x]
    case Con{+h, t}:
      choose(x, h, t, same(x, h))

def action(xs: +List<Nat>, s: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      s
    case Con{h, t}:
      toggle(h, action(t, s))

def Fresh(x: Nat, xs: +List<Nat>) -> Data:
  match xs:
    case Nil{}:
      Unit
    case Con{h, t}:
      {same(x, h) == False{} : Bool}

def Reduced(xs: +List<Nat>) -> Data:
  match xs:
    case Nil{}:
      Unit
    case Con{+h, +t}:
      Sigma<&2, &2, Fresh(h, t), u => Reduced(t)>

def Equivalent(+xs: +List<Nat>, +ys: +List<Nat>) -> Type:
  @+s: +List<Nat> -> Reduced(s) -> {action(xs, s) == action(ys, s) : +List<Nat>}

law canonical:
  for +xs: +List<Nat>
  exs ys: +List<Nat>
  Reduced(ys) & Equivalent(xs, ys)

law unique:
  for +xs: +List<Nat>
  for +ys: +List<Nat>
  for rx: Reduced(xs)
  for ry: Reduced(ys)
  for e: Equivalent(xs, ys)
  {xs == ys : +List<Nat>}

