# A unit converter stores each conversion factor as a fraction of
# naturals (1 inch is 254/100 cm). The factor for an area or a volume
# is the linear factor raised to a power. A result whose denominator
# divides its numerator is shown as a whole number (300/100 m is 3 m).
# LAW: for a factor with a positive denominator, reducing its power and
# raising its reduced form to that power name the same number.

import Base

type Frac is Data:
  Frac{num: Nat, den: Nat}

def Frac.num(q: Frac) -> Nat:
  Frac{num, den} = q
  num

def Frac.den(q: Frac) -> Nat:
  Frac{num, den} = q
  den

def Frac.pow(+q: Frac, +n: Nat) -> Frac:
  Frac{Nat.pow(Frac.num(q), n), Nat.pow(Frac.den(q), n)}

# the whole number d when the remainder r is 0n, else the fraction unchanged
def Frac.reduce.fin(q: Frac, dr: Nat & Nat) -> Frac:
  (d, r) = dr
  match r:
    case 0n:
      Frac{d, 1n}
    case 1n+rp:
      q

def Frac.reduce(+q: Frac) -> Frac:
  Frac.reduce.fin(q, Nat.divmod(Frac.num(q), Frac.den(q)))

# two fractions name the same number when they cross-multiply equal
def Frac.eq(+p: Frac, +q: Frac) -> Type:
  {Nat.mul(Frac.num(p), Frac.den(q)) == Nat.mul(Frac.num(q), Frac.den(p)) : Nat}

# LAW: reduce commutes with pow, as numbers, for a factor a/(1+b)
law reduce_pow:
  for +a: Nat
  for +b: Nat
  for +n: Nat
  Frac.eq(Frac.reduce(Frac.pow(Frac{a, 1n+b}, n)), Frac.pow(Frac.reduce(Frac{a, 1n+b}), n))

