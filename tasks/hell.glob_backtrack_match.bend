# A URL router matches a path (a list of Nat codes) against a glob:
# One{k} takes one code of class k, Many{k} takes any run of codes of
# class k. bt is the backtracking matcher; nfa runs the glob as an NFA,
# stepping a deduplicated set of live states; norm squashes a run of a
# run. Match is the spec, a type: the path fits the glob. LAWS: bt is
# sound and complete for Match, nfa and norm agree with bt, the live
# set is a set, and fitting a glob is decidable.

import Base

# a class of codes: any code, or the codes from lo to hi
type Cls is Data:
  Any{}
  Rng{lo: Nat, hi: Nat}

type Pat is Data:
  Fin{}
  One{k: Cls, p: Pat}
  Many{k: Cls, p: Pat}

def app(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      ys
    case h <> t:
      h <> app(A, t, ys)

def hit(k: Cls, +c: Nat) -> Bool:
  match k:
    case Any{}:
      True{}
    case Rng{lo, hi}:
      Bool.and(Cmp.is_le(Nat.cmp(lo, c)), Cmp.is_le(Nat.cmp(c, hi)))

# the backtracking matcher
def bt(+p: Pat, +s: List<&2, Nat>) -> Bool:
  match p s:
    case Fin{} Nil{}:
      True{}
    case Fin{} c <> t:
      False{}
    case One{k, q} Nil{}:
      False{}
    case One{k, q} c <> t:
      Bool.and(hit(k, c), bt(q, t))
    case Many{k, q} Nil{}:
      bt(q, Nil{})
    case Many{k, q} c <> t:
      Bool.or(bt(q, c <> t), Bool.and(hit(k, c), bt(Many{k, q}, t)))

# the NFA: a state is a glob suffix; step moves one state on a code
def keep(b: Bool, p: Pat) -> List<&2, Pat>:
  match b:
    case True{}:
      [p]
    case False{}:
      Nil{}

def step(+p: Pat, +c: Nat) -> List<&2, Pat>:
  match p:
    case Fin{}:
      Nil{}
    case One{k, q}:
      keep(hit(k, c), q)
    case Many{k, q}:
      app(Pat, keep(hit(k, c), Many{k, q}), step(q, c))

def Cls.eq(a: Cls, b: Cls) -> Bool:
  match a b:
    case Any{} Any{}:
      True{}
    case Any{} Rng{c, d}:
      False{}
    case Rng{a, b} Any{}:
      False{}
    case Rng{a, b} Rng{c, d}:
      Bool.and(Cmp.is_eq(Nat.cmp(a, c)), Cmp.is_eq(Nat.cmp(b, d)))

def Pat.eq(a: Pat, b: Pat) -> Bool:
  match a b:
    case Fin{} Fin{}:
      True{}
    case Fin{} One{k, q}:
      False{}
    case Fin{} Many{k, q}:
      False{}
    case One{k, q} Fin{}:
      False{}
    case One{k, q} One{k2, q2}:
      Bool.and(Cls.eq(k, k2), Pat.eq(q, q2))
    case One{k, q} Many{k2, q2}:
      False{}
    case Many{k, q} Fin{}:
      False{}
    case Many{k, q} One{k2, q2}:
      False{}
    case Many{k, q} Many{k2, q2}:
      Bool.and(Cls.eq(k, k2), Pat.eq(q, q2))

def mem(+p: Pat, ps: List<&2, Pat>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(Pat.eq(p, h), mem(p, t))

def pick(b: Bool, p: Pat, ps: List<&2, Pat>) -> List<&2, Pat>:
  match b:
    case True{}:
      ps
    case False{}:
      p <> ps

# the live set is a set: a state already present is dropped
def dedup(ps: List<&2, Pat>) -> List<&2, Pat>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> +r:
      pick(mem(p, r), p, dedup(r))

def nullable(p: Pat) -> Bool:
  match p:
    case Fin{}:
      True{}
    case One{k, q}:
      False{}
    case Many{k, q}:
      nullable(q)

def nulls(ps: List<&2, Pat>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> r:
      Bool.or(nullable(p), nulls(r))

def moves(ps: List<&2, Pat>, +c: Nat) -> List<&2, Pat>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> r:
      app(Pat, step(p, c), moves(r, c))

def sim(s: List<&2, Nat>, ps: List<&2, Pat>) -> Bool:
  match s:
    case Nil{}:
      nulls(ps)
    case c <> t:
      sim(t, dedup(moves(ps, c)))

def nfa(p: Pat, s: List<&2, Nat>) -> Bool:
  sim(s, [p])

# LE(a, b): a <= b, as a type
def LE(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n b:
      Unit
    case 1n+a 0n:
      Empty
    case 1n+a 1n+b:
      LE(a, b)

# In(k, c): the code c belongs to the class k
def In(k: Cls, c: Nat) -> Type:
  match k:
    case Any{}:
      Unit
    case Rng{lo, hi}:
      LE(lo, c) & LE(c, hi)

# All(k, u): every code of u belongs to k
def All(k: Cls, u: List<&2, Nat>) -> Type:
  match u:
    case Nil{}:
      Unit
    case c <> t:
      In(k, c) & All(k, t)

# Match(p, s): the path s fits the glob p; Many{k, q} takes a run u of
# class k, then q takes the rest v
def Match(+p: Pat, +s: List<&2, Nat>) -> Type:
  match p s:
    case Fin{} Nil{}:
      Unit
    case Fin{} c <> t:
      Empty
    case One{k, q} Nil{}:
      Empty
    case One{k, q} c <> t:
      In(k, c) & Match(q, t)
    case Many{k, q} s:
      Exists(List<&2, Nat>, u => Exists(List<&2, Nat>, v => {s == app(Nat, u, v) : List<&2, Nat>} & All(k, u) & Match(q, v)))

# LAW: when bt says True, the path fits the glob
law bt_sound:
  for +p: Pat
  for +s: List<&2, Nat>
  for e: {True{} == bt(p, s) : Bool}
  Match(p, s)

# LAW: when the path fits the glob, bt says True
law bt_complete:
  for +p: Pat
  for +s: List<&2, Nat>
  for m: Match(p, s)
  {True{} == bt(p, s) : Bool}

# LAW: the NFA simulation agrees with the backtracking matcher
law nfa_bt:
  for +p: Pat
  for +s: List<&2, Nat>
  {nfa(p, s) == bt(p, s) : Bool}

# the normalizer: two runs of one class in a row are one run
def merge(b: Bool, k: Cls, k2: Cls, q: Pat) -> Pat:
  match b:
    case True{}:
      Many{k2, q}
    case False{}:
      Many{k, Many{k2, q}}

def squash(+k: Cls, +p: Pat) -> Pat:
  match p:
    case Fin{}:
      Many{k, Fin{}}
    case One{k2, q}:
      Many{k, One{k2, q}}
    case Many{k2, q}:
      merge(Cls.eq(k, k2), k, k2, q)

def norm(p: Pat) -> Pat:
  match p:
    case Fin{}:
      Fin{}
    case One{k, q}:
      One{k, norm(q)}
    case Many{k, q}:
      squash(k, norm(q))

# LAW: the normalizer keeps the language
law norm_bt:
  for +p: Pat
  for +s: List<&2, Nat>
  {bt(norm(p), s) == bt(p, s) : Bool}

# Nodup(ps): no state appears twice
def Nodup(ps: List<&2, Pat>) -> Type:
  match ps:
    case Nil{}:
      Unit
    case +p <> +r:
      {False{} == mem(p, r) : Bool} & Nodup(r)

# LAW: the live set is a set: dedup drops every repeated state
law dedup_nodup:
  for +ps: List<&2, Pat>
  Nodup(dedup(ps))

# LAW: dedup is idempotent
law dedup_idem:
  for +ps: List<&2, Pat>
  {dedup(dedup(ps)) == dedup(ps) : List<&2, Pat>}

# LAW: fitting a glob is decidable
law match_dec:
  for +p: Pat
  for +s: List<&2, Nat>
  Or(Match(p, s), Match(p, s) -> Empty)

# LAW: a state finds itself in a set that holds it
law mem_self:
  for +p: Pat
  for +ps: List<&2, Pat>
  {True{} == mem(p, p <> ps) : Bool}

# LAW: a live set accepts what any of its states accepts
law sim_mem:
  for +ps: List<&2, Pat>
  for +p: Pat
  for +s: List<&2, Nat>
  for e: {True{} == mem(p, ps) : Bool}
  for b: {True{} == bt(p, s) : Bool}
  {True{} == sim(s, ps) : Bool}

# LAW: so the NFA is sound and complete for the spec too
law nfa_sound:
  for +p: Pat
  for +s: List<&2, Nat>
  for e: {True{} == nfa(p, s) : Bool}
  Match(p, s)

law nfa_complete:
  for +p: Pat
  for +s: List<&2, Nat>
  for m: Match(p, s)
  {True{} == nfa(p, s) : Bool}

