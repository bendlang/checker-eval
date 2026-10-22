# A pomodoro timer logs each day's intervals: Work, Rest and Pause, with
# their minutes. A Work interval of 25 minutes or more is a completed
# pomodoro; a shorter one was interrupted. A log is one day or two logs
# side by side, so the weekly tally runs in parallel and merges the
# halves. LAW: the tally's pomodoro count is the number of completed
# pomodoros the filter lists.

import Base

type Interval is Data:
  Work{mins: Nat}
  Rest{mins: Nat}
  Pause{mins: Nat}

type Stats is Data:
  Stats{done: Nat, focus: Nat, rest: Nat}

type Log is Data:
  Day{items: +List<Interval>}
  Split{l: Log, r: Log}

def Stats.done(s: Stats) -> Nat:
  Stats{done, focus, rest} = s
  done

# a short (interrupted) work interval adds focus minutes but no pomodoro
def tally.work(m: Nat, s: Stats, short: Bool) -> Stats:
  Stats{done, focus, rest} = s
  match short:
    case True{}:
      Stats{done, Nat.add(m, focus), rest}
    case False{}:
      Stats{1n+done, Nat.add(m, focus), rest}

def tally.rest(m: Nat, s: Stats) -> Stats:
  Stats{done, focus, rest} = s
  Stats{done, focus, Nat.add(m, rest)}

# folds a day's intervals into the stats s
def tally.day(items: +List<Interval>, s: Stats) -> Stats:
  match items:
    case Nil{}:
      s
    case Work{+m} <> t:
      tally.day(t, tally.work(m, s, (m < 25n : Nat)))
    case Rest{m} <> t:
      tally.day(t, tally.rest(m, s))
    case Pause{m} <> t:
      tally.day(t, s)

def merge(a: Stats, b: Stats) -> Stats:
  Stats{d1, f1, r1} = a
  Stats{d2, f2, r2} = b
  Stats{Nat.add(d1, d2), Nat.add(f1, f2), Nat.add(r1, r2)}

def tally(log: Log) -> Stats:
  match log:
    case Day{items}:
      tally.day(items, Stats{0n, 0n, 0n})
    case Split{l, r}:
      a b = tally(l) tally(r)
      merge(a, b)

# the minutes of every completed pomodoro, in order
def keep(m: Nat, rest: +List<Nat>, short: Bool) -> +List<Nat>:
  match short:
    case True{}:
      rest
    case False{}:
      m <> rest

def pomodoros.day(items: +List<Interval>) -> +List<Nat>:
  match items:
    case Nil{}:
      Nil{}
    case Work{+m} <> t:
      keep(m, pomodoros.day(t), (m < 25n : Nat))
    case Rest{m} <> t:
      pomodoros.day(t)
    case Pause{m} <> t:
      pomodoros.day(t)

def append(xs: +List<Nat>, ys: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      ys
    case h <> t:
      h <> append(t, ys)

def pomodoros(log: Log) -> +List<Nat>:
  match log:
    case Day{items}:
      pomodoros.day(items)
    case Split{l, r}:
      append(pomodoros(l), pomodoros(r))

def length(xs: +List<Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      1n+length(t)

# LAW: the tally counts exactly the completed pomodoros
law done_counts:
  for log: Log
  {Stats.done(tally(log)) == length(pomodoros(log)) : Nat}

