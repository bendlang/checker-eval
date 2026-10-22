# A museum conservator records labeled phases and their durations in ticks.
# Produce each phase's completion time, measured from the start of the work.
# Prove that appending phases splices their timeline after the first total duration.
import Base

type Phases is Data:
  EndPhases{}
  Phase{label: Nat, ticks: Nat, rest: Phases}

def join(xs: Phases, ys: Phases) -> Phases:
  match xs:
    case EndPhases{}:
      ys
    case Phase{label, ticks, rest}:
      Phase{label, ticks, join(rest, ys)}

def elapsed(xs: Phases) -> Nat:
  match xs:
    case EndPhases{}:
      0n
    case Phase{label, ticks, rest}:
      Nat.add(ticks, elapsed(rest))

def delay(+ticks: Nat, xs: Phases) -> Phases:
  match xs:
    case EndPhases{}:
      EndPhases{}
    case Phase{label, time, rest}:
      Phase{label, Nat.add(ticks, time), delay(ticks, rest)}

law timeline:
  for xs: Phases
  Phases

law timeline_empty:
  {timeline(EndPhases{}) == EndPhases{} : Phases}

law timeline_phase:
  for label: Nat
  for ticks: Nat
  for rest: Phases
  {timeline(Phase{label, ticks, rest}) ==
    Phase{label, ticks, delay(ticks, timeline(rest))} : Phases}

law timeline_splice:
  for xs: Phases
  for +ys: Phases
  {timeline(join(xs, ys)) ==
    join(timeline(xs), delay(elapsed(xs), timeline(ys))) : Phases}

