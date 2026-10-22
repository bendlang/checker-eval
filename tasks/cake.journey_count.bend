# A regional field-science planner audits chronological station visits.
# Replaying a journey increments a saved visit count once per station identifier.
# Prove that replay adds exactly the journey's length to every saved count.
import Base

def visits(stations: +List<Nat>) -> Nat:
  match stations:
    case Nil{}:
      0n
    case Con{station, rest}:
      1n+visits(rest)

def replay(stations: +List<Nat>, saved: Nat) -> Nat:
  match stations:
    case Nil{}:
      saved
    case Con{station, rest}:
      replay(rest, 1n+saved)

law replay_count:
  for stations: +List<Nat>
  for +saved: Nat
  {replay(stations, saved) == Nat.add(visits(stations), saved) : Nat}

