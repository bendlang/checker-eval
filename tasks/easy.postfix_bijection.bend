# A language scientist needs a streaming codec for symbolic binary trees.
# Emit postfix bytecode into a supplied continuation. Join pops right, then left;
# stack underflow rejects. Prove execution and the exact converse: every program
# accepted from an empty stack with one tree is precisely that tree's encoding.
import Base

type Tree is Data:
  Leaf{symbol: Nat}
  Fork{left: Tree, right: Tree}

type Token is Data:
  Push{symbol: Nat}
  Join{}

def run(p: List<&2, Token>, s: List<&2, Tree>) -> Maybe<&2, List<&2, Tree>>:
  match p:
    case Nil{}:
      Some{s}
    case Con{h, t}:
      match h:
        case Push{n}:
          run(t, Con{Leaf{n}, s})
        case Join{}:
          match s:
            case Nil{}:
              None{}
            case Con{r, rest}:
              match rest:
                case Nil{}:
                  None{}
                case Con{l, tail}:
                  run(t, Con{Fork{l, r}, tail})

law emit:
  for t: Tree
  for k: List<&2, Token>
  List<&2, Token>

law emit_leaf:
  for n: Nat
  for k: List<&2, Token>
  {emit(Leaf{n}, k) == Con{Push{n}, k} : List<&2, Token>}

law emit_fork:
  for l: Tree
  for r: Tree
  for k: List<&2, Token>
  {emit(Fork{l, r}, k) == emit(l, emit(r, Con{Join{}, k})) : List<&2, Token>}

law execution:
  for t: Tree
  for +s: List<&2, Tree>
  for +k: List<&2, Token>
  {run(emit(t, k), s) == run(k, Con{t, s}) : Maybe<&2, List<&2, Tree>>}

law complete:
  for +p: List<&2, Token>
  for +t: Tree
  for e: {run(p, Nil{}) == Some{Con{t, Nil{}}} : Maybe<&2, List<&2, Tree>>}
  {emit(t, Nil{}) == p : List<&2, Token>}

