# Certify an optimizer for open SK combinator terms.
# A step contracts K x y to x or S x y z to (x z) (y z), anywhere.
# Construct a common reduct for any two finite reduction histories.
import Base

type Term is Data:
  Atom{name: +List<Bool>}
  K{}
  S{}
  Ap{fun: Term, arg: Term}

type Step is Data:
  Drop{x: Term, y: Term}
  Copy{x: Term, y: Term, z: Term}
  Left{step: Step, arg: Term}
  Right{fun: Term, step: Step}

type Parallel is Data:
  PAtom{name: +List<Bool>}
  PK{}
  PS{}
  PApp{fun: Parallel, arg: Parallel}
  PDrop{x: Parallel, y: Parallel}
  PCopy{x: Parallel, y: Parallel, z: Parallel}

type Certificate<-A: Data, -s: A -> Term, -t: A -> Term,
  -a: Term, -b: Term> is Data:
  Cert{proof: A, src: {a == s(proof) : Term}, dst: {b == t(proof) : Term}}

type Walk<-R: @-a: Term -> @-b: Term -> Data, -a: Term, -b: Term> is Data:
  Stop{eq: {a == b : Term}}
  More{mid: Term, step: R(a, mid), rest: Walk<R, mid, b>}

type Join<-R: @-a: Term -> @-b: Term -> Data, -a: Term, -b: Term> is Data:
  Joined{term: Term, left: Walk<R, a, term>, right: Walk<R, b, term>}

def source(step: Step) -> Term:
  match step:
    case Drop{x, y}: Ap{Ap{K{}, x}, y}
    case Copy{x, y, z}: Ap{Ap{Ap{S{}, x}, y}, z}
    case Left{step, arg}: Ap{source(step), arg}
    case Right{fun, step}: Ap{fun, source(step)}

def target(step: Step) -> Term:
  match step:
    case Drop{x, y}: x
    case Copy{x, y, +z}: Ap{Ap{x, z}, Ap{y, z}}
    case Left{step, arg}: Ap{target(step), arg}
    case Right{fun, step}: Ap{fun, target(step)}

def single(-a: Term, -b: Term) -> Data:
  Certificate<Step, source, target, a, b>

law confluence:
  for a: Term
  for b: Term
  for c: Term
  for left: Walk<single, a, b>
  for right: Walk<single, a, c>
  exs d: Term
  Walk<single, b, d> & Walk<single, c, d>

