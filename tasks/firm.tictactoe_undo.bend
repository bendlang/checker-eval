# A tic-tac-toe app keeps its move log as a stack, newest move on top,
# and replays it from the empty board: a move takes a free cell for the
# player whose turn it is; an illegal move is skipped. Undo has two ways:
# the honest way drops moves from the log and replays it; the cheap way
# frees their cells and hands the turn back. LAWS: on a legal log, k cheap
# undos give the honest board, and redoing the k dropped moves restores it.

import Base

type Player is Data:
  X{}
  O{}

type Cell is Data:
  Free{}
  Mark{p: Player}

# whose turn it is, and the rows of the board
type Game is Data:
  Game{turn: Player, rows: +List<+List<Cell>>}

# a move names a position on the board
type Move is Data:
  Pos{row: Nat, col: Nat}

def other(p: Player) -> Player:
  match p:
    case X{}:
      O{}
    case O{}:
      X{}

def is_free(c: Cell) -> Bool:
  match c:
    case Free{}:
      True{}
    case Mark{p}:
      False{}

# the cell at column c of a row; Free past the end
def get_cell(row: +List<Cell>, c: Nat) -> Cell:
  match row:
    case Nil{}:
      Free{}
    case h <> t:
      match c:
        case 0n:
          h
        case 1n+p:
          get_cell(t, p)

def set_cell(row: +List<Cell>, c: Nat, v: Cell) -> +List<Cell>:
  match row:
    case Nil{}:
      Nil{}
    case h <> t:
      match c:
        case 0n:
          v <> t
        case 1n+p:
          h <> set_cell(t, p, v)

def get(rows: +List<+List<Cell>>, r: Nat, c: Nat) -> Cell:
  match rows:
    case Nil{}:
      Free{}
    case row <> rest:
      match r:
        case 0n:
          get_cell(row, c)
        case 1n+p:
          get(rest, p, c)

def set(rows: +List<+List<Cell>>, r: Nat, c: Nat, v: Cell) -> +List<+List<Cell>>:
  match rows:
    case Nil{}:
      Nil{}
    case row <> rest:
      match r:
        case 0n:
          set_cell(row, c, v) <> rest
        case 1n+p:
          row <> set(rest, p, c, v)

# the cell a move names
def at(g: Game, m: Move) -> Cell:
  Game{turn, rows} = g
  Pos{r, c} = m
  get(rows, r, c)

# marks the cell when ok says it is free; else skips the move
def place(g: Game, m: Move, ok: Bool) -> Game:
  Game{+turn, rows} = g
  Pos{r, c} = m
  match ok:
    case True{}:
      Game{other(turn), set(rows, r, c, Mark{turn})}
    case False{}:
      Game{turn, rows}

def play(+g: Game, +m: Move) -> Game:
  place(g, m, is_free(at(g, m)))

# the cheap undo of one move: frees its cell and hands the turn back
def unplay(g: Game, m: Move) -> Game:
  Game{turn, rows} = g
  Pos{r, c} = m
  Game{other(turn), set(rows, r, c, Free{})}

def start() -> Game:
  Game{X{}, [[Free{}, Free{}, Free{}], [Free{}, Free{}, Free{}], [Free{}, Free{}, Free{}]]}

# plays a log onto g, oldest move first
def play_all(log: +List<Move>, g: Game) -> Game:
  match log:
    case Nil{}:
      g
    case m <> older:
      play(play_all(older, g), m)

def replay(log: +List<Move>) -> Game:
  play_all(log, start())

# the k newest moves
def take(k: Nat, log: +List<Move>) -> +List<Move>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      match log:
        case Nil{}:
          Nil{}
        case m <> older:
          m <> take(p, older)

# the log without its k newest moves
def drop(k: Nat, log: +List<Move>) -> +List<Move>:
  match k:
    case 0n:
      log
    case 1n+p:
      match log:
        case Nil{}:
          Nil{}
        case m <> older:
          drop(p, older)

# k cheap undos: pops k moves from the log and unplays them on g
def undo(k: Nat, log: +List<Move>, g: Game) -> Game:
  match k:
    case 0n:
      g
    case 1n+p:
      match log:
        case Nil{}:
          g
        case m <> older:
          undo(p, older, unplay(g, m))

# a log is legal when every move found its cell free
def Legal(log: +List<Move>) -> Type:
  match log:
    case Nil{}:
      Unit
    case m <> older:
      ({Free{} == at(replay(older), m) : Cell} & Legal(older))

# LAW: k cheap undos give the board of the log without its k newest moves
law undo_ok:
  for +k: Nat
  for +log: +List<Move>
  for  e: Legal(log)
  {replay(drop(k, log)) == undo(k, log, replay(log)) : Game}

# LAW: replaying the k dropped moves onto the undone board restores it
law redo_ok:
  for +k: Nat
  for +log: +List<Move>
  for  e: Legal(log)
  {replay(log) == play_all(take(k, log), undo(k, log, replay(log))) : Game}

