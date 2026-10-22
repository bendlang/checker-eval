# An inventory tracker merges warehouse shelf trees from left to right.
# Empty shelves are pruned and unary branches collapsed. Prove this
# cleanup preserves the order of every item in the merged inventory.
import Base

type Shelf is Data:
  Vacant{}
  Stock{item: Nat}
  Aisle{left: Shelf, right: Shelf}

def cat(xs: List<Nat>, ys: List<Nat>) -> List<Nat>:
  match xs:
    case Nil{}: ys
    case Con{h, t}: Con{h, cat(t, ys)}

def items(s: Shelf) -> List<Nat>:
  match s:
    case Vacant{}: Nil{}
    case Stock{item}: [item]
    case Aisle{left, right}: cat(items(left), items(right))

def join(a: Shelf, b: Shelf) -> Shelf:
  match a:
    case Vacant{}: b
    case Stock{item}:
      match b:
        case Vacant{}: Stock{item}
        case Stock{other}: Aisle{Stock{item}, Stock{other}}
        case Aisle{left, right}: Aisle{Stock{item}, Aisle{left, right}}
    case Aisle{left, right}:
      match b:
        case Vacant{}: Aisle{left, right}
        case Stock{item}: Aisle{Aisle{left, right}, Stock{item}}
        case Aisle{x, y}: Aisle{Aisle{left, right}, Aisle{x, y}}

def prune(s: Shelf) -> Shelf:
  match s:
    case Vacant{}: Vacant{}
    case Stock{item}: Stock{item}
    case Aisle{left, right}: join(prune(left), prune(right))

law merged_inventory:
  for a: Shelf
  for b: Shelf
  {items(prune(Aisle{a, b})) == cat(items(a), items(b)) : List<Nat>}

