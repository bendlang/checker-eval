# A robot planner uses regular plans with unit-cost actions and free control flow.
# Remove empty loop iterations while preserving every exact feasible budget.
# Fail, done, action, choice, sequence, and repetition are the regular operations.
import Base

type Plan is Data:
  Dead{}
  Rest{}
  Act{}
  Pick{left: Plan, right: Plan}
  Seq{left: Plan, right: Plan}
  Loop{body: Plan}

type Trace is Data:
  Quiet{}
  Moved{}
  TakeL{run: Trace}
  TakeR{run: Trace}
  Join{first: Trace, second: Trace}
  Finish{}
  Again{first: Trace, rest: Trace}

def cost(d: Trace) -> Nat:
  match d:
    case Quiet{}: 0n
    case Moved{}: 1n
    case TakeL{x}: cost(x)
    case TakeR{x}: cost(x)
    case Join{x, y}: Nat.add(cost(x), cost(y))
    case Finish{}: 0n
    case Again{x, y}: Nat.add(cost(x), cost(y))

def Valid(p: Plan, +d: Trace) -> Type:
  match p, d:
    case Rest{}, Quiet{}: Unit
    case Act{}, Moved{}: Unit
    case Pick{a, b}, TakeL{x}: Valid(a, x)
    case Pick{a, b}, TakeR{x}: Valid(b, x)
    case Seq{a, b}, Join{x, y}: Valid(a, x) & Valid(b, y)
    case Loop{a}, Finish{}: Unit
    case Loop{a}, Again{x, y}: Valid(a, x) & Valid(Loop{a}, y)
    case _, _: Empty

def Runs(+p: Plan, +n: Nat) -> Type:
  &d: Trace -> Valid(p, d) & {cost(d) == n : Nat}

def nullable(p: Plan) -> Bool:
  match p:
    case Dead{}: False{}
    case Rest{}: True{}
    case Act{}: False{}
    case Pick{a, b}: Bool.or(nullable(a), nullable(b))
    case Seq{a, b}: Bool.and(nullable(a), nullable(b))
    case Loop{a}: True{}

def optional(b: Bool, p: Plan) -> Plan:
  match b:
    case False{}: Dead{}
    case True{}: p

# clean(p, False) preserves p; clean(p, True) additionally removes its empty run.
def clean(+p: Plan, +positive: Bool) -> Plan:
  match p:
    case Dead{}: Dead{}
    case Rest{}:
      match positive:
        case False{}: Rest{}
        case True{}: Dead{}
    case Act{}: Act{}
    case Pick{a, b}: Pick{clean(a, positive), clean(b, positive)}
    case Seq{+a, b}:
      match positive:
        case False{}: Seq{clean(a, False{}), clean(b, False{})}
        case True{}: Pick{Seq{clean(a, True{}), clean(b, False{})}, optional(nullable(a), clean(b, True{}))}
    case Loop{+a}:
      match positive:
        case False{}: Loop{clean(a, True{})}
        case True{}: Seq{clean(a, True{}), Loop{clean(a, True{})}}

def Proper(p: Plan) -> Type:
  match p:
    case Dead{}: Unit
    case Rest{}: Unit
    case Act{}: Unit
    case Pick{a, b}: Proper(a) & Proper(b)
    case Seq{a, b}: Proper(a) & Proper(b)
    case Loop{+a}: Proper(a) & {nullable(a) == False{} : Bool}

law normalize:
  for +p: Plan
  Proper(clean(p, False{})) & (@n: Nat -> (Runs(clean(p, False{}), n) -> Runs(p, n)) & (Runs(p, n) -> Runs(clean(p, False{}), n)))

