# A back-end serves a table of orders through a paged API. A request
# names a page size n and a cursor, how many table rows were scanned so
# far, and gets the next n open orders plus the cursor of the page after
# them, or none when no open order is left. A client asks for page after
# page until one has no cursor. LAW: every page of that walk but the last
# holds exactly n rows, so a client that stops at a short page is safe.

import Base

# an order: its key, and whether it is still open
type Row is Data:
  Row{key: Nat, open: Bool}

# a page: its rows, and the cursor of the page after it
type Page is Data:
  Page{rows: +List<Row>, next: +Maybe<Nat>}

def length(xs: +List<Row>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case r <> rs:
      1n+length(rs)

def drop(k: Nat, xs: +List<Row>) -> +List<Row>:
  match k:
    case 0n:
      xs
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case r <> rs:
          drop(p, rs)

def push(r: Row, pg: Page) -> Page:
  Page{rs, next} = pg
  Page{r <> rs, next}

# scans rows, of which at were scanned before, for m more open orders:
# a closed order is skipped; an open one fills the page, or ends it
# with the cursor when the page is full
def scan(rows: +List<Row>, m: Nat, at: Nat) -> Page:
  match rows:
    case Nil{}:
      Page{Nil{}, None{}}
    case Row{key, False{}} <> rs:
      scan(rs, m, 1n+at)
    case Row{key, True{}} <> rs:
      match m:
        case 0n:
          Page{Nil{}, Some{at}}
        case 1n+p:
          push(Row{key, True{}}, scan(rs, p, 1n+at))

# the page of n open orders after the cursor at
def page(+rows: +List<Row>, +n: Nat, +at: Nat) -> Page:
  scan(drop(at, rows), n, at)

# the client's walk from a page: it keeps the page's rows and asks for
# the page after its cursor; fuel bounds how many pages it asks for
def walk(fuel: Nat, pg: Page, +rows: +List<Row>, +n: Nat) -> +List<+List<Row>>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      Page{rs, next} = pg
      match next:
        case None{}:
          [rs]
        case Some{at}:
          rs <> walk(f, page(rows, n, at), rows, n)

def pages(fuel: Nat, +rows: +List<Row>, +n: Nat) -> +List<+List<Row>>:
  walk(fuel, page(rows, n, 0n), rows, n)

# every page but the last holds exactly n rows
def Full(n: Nat, ps: +List<+List<Row>>) -> Type:
  match ps:
    case Nil{}:
      Unit
    case p <> rest:
      match rest:
        case Nil{}:
          Unit
        case q <> more:
          ({length(p) == n : Nat} & Full(n, q <> more))

# LAW: a client that stops at a short page misses nothing: every page
# of a walk but the last holds exactly n rows
law pages_full:
  for  fuel: Nat
  for +rows: +List<Row>
  for +n: Nat
  Full(n, pages(fuel, rows, n))

