/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Tactic.Linarith.Datatypes

/-!
# Parsing input expressions into linear form

`linarith` computes the linear form of its input expressions,
assuming (without justification) that the type of these expressions
is a commutative semiring.
It identifies atoms up to ring-equivalence: that is, `(y*3)*x` will be identified `3*(x*y)`,
where the monomial `x*y` is the linear atom.

* Variables are represented by natural numbers.
* Monomials are represented by `Monom := TreeMap ℕ ℕ`.
  The monomial `1` is represented by the empty map.
* Linear combinations of monomials are represented by `Sum := TreeMap Monom ℤ`.

All input expressions are converted to `Sum`s, preserving the map from expressions to variables.
We then discard the monomial information, mapping each distinct monomial to a natural number.
The resulting `TreeMap ℕ ℤ` represents the ring-normalized linear form of the expression.
This is ultimately converted into a `Linexp` in the obvious way.

`linearFormsAndMaxVar` is the main entry point into this file. Everything else is contained.
-/

open Std (TreeMap)

namespace Std.TreeMap

-- This will be replaced by a `BEq` instance implemented in the standard library,
-- likely in Q4 2025.

/-- Returns true if the two maps have the same size and the same keys and values
(with keys compared using the ordering, and values compared using `BEq`). -/
def beq {α β : Type*} [BEq β] {c : α → α → Ordering} (m₁ m₂ : TreeMap α β c) : Bool :=
  m₁.size == m₂.size && Id.run do
    -- This could be made more efficient by simultaneously traversing both maps.
    for (k, v) in m₁ do
      if let some v' := m₂[k]? then
        if v != v' then
          return false
      else
        return false
    return true

instance {α β : Type*} [BEq β] {c : α → α → Ordering} : BEq (TreeMap α β c) := ⟨beq⟩

end Std.TreeMap


section
open Lean Elab Tactic Meta

/--
`findDefeq red m e` looks for a key in `m` that is defeq to `e` (up to transparency `red`),
and returns the value associated with this key if it exists.
Otherwise, it fails.
-/
def List.findDefeq {v : Type} (red : TransparencyMode) (m : List (Expr × v)) (e : Expr) :
    MetaM v := do
  if let some (_, n) ← m.findM? fun ⟨e', _⟩ => withTransparency red (isDefEq e e') then
    return n
  else
    failure
end

/--
We introduce a local instance allowing addition of `TreeMap`s,
removing any keys with value zero.
We don't need to prove anything about this addition, as it is only used in meta code.
-/
local instance {α β : Type*} {c : α → α → Ordering} [Add β] [Zero β] [DecidableEq β] :
    Add (TreeMap α β c) where
  add := fun f g => (f.mergeWith (fun _ b b' => b + b') g).filter (fun _ b => b ≠ 0)

namespace Mathlib.Tactic.Linarith

/-- A local abbreviation for `TreeMap` so we don't need to write `Ord.compare` each time. -/
abbrev Map (α β) [Ord α] := TreeMap α β Ord.compare

/-! ### Parsing datatypes -/

/-- Variables (represented by natural numbers) map to their power. -/
abbrev Monom : Type := Map ℕ ℕ

/-- `1` is represented by the empty monomial, the product of no variables. -/
def Monom.one : Monom := TreeMap.empty

/-- Compare monomials by first comparing their keys and then their powers. -/
def Monom.lt : Monom → Monom → Bool :=
  fun a b =>
    ((a.keys : List ℕ) < b.keys) ||
      (((a.keys : List ℕ) = b.keys) && ((a.values : List ℕ) < b.values))

instance : Ord Monom where
  compare x y := if x.lt y then .lt else if x == y then .eq else .gt

/-- Linear combinations of monomials are represented by mapping monomials to coefficients. -/
abbrev Sum : Type := Map Monom ℤ

/-- `1` is represented as the singleton sum of the monomial `Monom.one` with coefficient 1. -/
def Sum.one : Sum := TreeMap.empty.insert Monom.one 1

/-- `Sum.scaleByMonom s m` multiplies every monomial in `s` by `m`. -/
def Sum.scaleByMonom (s : Sum) (m : Monom) : Sum :=
  s.foldr (fun m' coeff sm => sm.insert (m + m') coeff) TreeMap.empty

/-- `sum.mul s1 s2` distributes the multiplication of two sums. -/
def Sum.mul (s1 s2 : Sum) : Sum :=
  s1.foldr (fun mn coeff sm => sm + ((s2.scaleByMonom mn).map (fun _ v => v * coeff)))
    TreeMap.empty

/-- The `n`th power of `s : Sum` is the `n`-fold product of `s`, with `s.pow 0 = Sum.one`. -/
partial def Sum.pow (s : Sum) : ℕ → Sum
  | 0 => Sum.one
  | 1 => s
  | n =>
    let m := n >>> 1
    let a := s.pow m
    if n &&& 1 = 0 then
      a.mul a
    else
      a.mul a |>.mul s

/-- `SumOfMonom m` lifts `m` to a sum with coefficient `1`. -/
def SumOfMonom (m : Monom) : Sum :=
  TreeMap.empty.insert m 1

/-- The unit monomial `one` is represented by the empty TreeMap. -/
def one : Monom := TreeMap.empty

/-- A scalar `z` is represented by a `Sum` with coefficient `z` and monomial `one` -/
def scalar (z : ℤ) : Sum :=
  TreeMap.empty.insert one z

/-- A single variable `n` is represented by a sum with coefficient `1` and monomial `n`. -/
def var (n : ℕ) : Sum :=
  TreeMap.empty.insert (TreeMap.empty.insert n 1) 1


/-! ### Parsing algorithms -/

open Lean Elab Tactic Meta

/--
`ExprMap` is used to record atomic expressions which have been seen while processing inequality
expressions.
-/
-- The natural number is just the index in the list,
-- and we could reimplement to just use `List Expr` if desired.
abbrev ExprMap := List (Expr × ℕ)

/--
`linearFormOfAtom red map e` is the atomic case for `linear_form_of_expr`.
If `e` appears with index `k` in `map`, it returns the singleton sum `var k`.
Otherwise it updates `map`, adding `e` with index `n`, and returns the singleton sum `var n`.
-/
def linearFormOfAtom (red : TransparencyMode) (m : ExprMap) (e : Expr) : MetaM (ExprMap × Sum) := do
  try
    let k ← m.findDefeq red e
    return (m, var k)
  catch _ =>
    let n := m.length + 1
    return ((e, n)::m, var n)

/--
`linearFormOfExpr red map e` computes the linear form of `e`.

`map` is a lookup map from atomic expressions to variable numbers.
If a new atomic expression is encountered, it is added to the map with a new number.
It matches atomic expressions up to reducibility given by `red`.

Because it matches up to definitional equality, this function must be in the `MetaM` monad,
and forces some functions that call it into `MetaM` as well.
-/

partial def linearFormOfExpr (red : TransparencyMode) (m : ExprMap) (e : Expr) :
    MetaM (ExprMap × Sum) := do
  let e ← whnfR e
  match e.numeral? with
  | some 0 => return ⟨m, TreeMap.empty⟩
  | some (n + 1) => return ⟨m, scalar (n + 1)⟩
  | none =>
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, e1, e2]) => do
    let (m1, comp1) ← linearFormOfExpr red m e1
    let (m2, comp2) ← linearFormOfExpr red m1 e2
    return (m2, comp1.mul comp2)
  | (``HAdd.hAdd, #[_, _, _, _, e1, e2]) => do
    let (m1, comp1) ← linearFormOfExpr red m e1
    let (m2, comp2) ← linearFormOfExpr red m1 e2
    return (m2, comp1 + comp2)
  | (``HSub.hSub, #[_, _, _, _, e1, e2]) => do
    let (m1, comp1) ← linearFormOfExpr red m e1
    let (m2, comp2) ← linearFormOfExpr red m1 e2
    return (m2, comp1 + comp2.map (fun _ v => -v))
  | (``Neg.neg, #[_, _, e]) => do
    let (m1, comp) ← linearFormOfExpr red m e
    return (m1, comp.map (fun _ v => -v))
  | (``HPow.hPow, #[_, _, _, _, a, n]) => do
    match n.numeral? with
    | some n => do
      let (m1, comp) ← linearFormOfExpr red m a
      return (m1, comp.pow n)
    | none => linearFormOfAtom red m e
  | _ => linearFormOfAtom red m e

/--
`elimMonom s map` eliminates the monomial level of the `Sum` `s`.

`map` is a lookup map from monomials to variable numbers.
The output `TreeMap ℕ ℤ` has the same structure as `s : Sum`,
but each monomial key is replaced with its index according to `map`.
If any new monomials are encountered, they are assigned variable numbers and `map` is updated.
-/
def elimMonom (s : Sum) (m : Map Monom ℕ) : Map Monom ℕ × Map ℕ ℤ :=
  s.foldr (fun mn coeff ⟨map, out⟩ ↦
    match map[mn]? with
    | some n => ⟨map, out.insert n coeff⟩
    | none =>
      let n := map.size
      ⟨map.insert mn n, out.insert n coeff⟩)
    (m, TreeMap.empty)

/--
`toComp red e e_map monom_map` converts an expression of the form `t < 0`, `t ≤ 0`, or `t = 0`
into a `comp` object.

`e_map` maps atomic expressions to indices; `monom_map` maps monomials to indices.
Both of these are updated during processing and returned.
-/
def toComp (red : TransparencyMode) (e : Expr) (e_map : ExprMap) (monom_map : Map Monom ℕ) :
    MetaM (Comp × ExprMap × Map Monom ℕ) := do
  let (iq, e) ← parseCompAndExpr e
  let (m', comp') ← linearFormOfExpr red e_map e
  let ⟨nm, mm'⟩ := elimMonom comp' monom_map
  -- Note: we use `.reverse` as `Linexp.get` assumes the monomial are in descending order
  return ⟨⟨iq, mm'.toList.reverse⟩, m', nm⟩

/--
`toCompFold red e_map exprs monom_map` folds `toComp` over `exprs`,
updating `e_map` and `monom_map` as it goes.
-/
def toCompFold (red : TransparencyMode) : ExprMap → List Expr → Map Monom ℕ →
    MetaM (List Comp × ExprMap × Map Monom ℕ)
| m, [],     mm => return ([], m, mm)
| m, (h::t), mm => do
    let (c, m', mm') ← toComp red h m mm
    let (l, mp, mm') ← toCompFold red m' t mm'
    return (c::l, mp, mm')

/--
`linearFormsAndMaxVar red pfs` is the main interface for computing the linear forms of a list
of expressions. Given a list `pfs` of proofs of comparisons, it produces a list `c` of `Comp`s of
the same length, such that `c[i]` represents the linear form of the type of `pfs[i]`.

It also returns the largest variable index that appears in comparisons in `c`.
-/
def linearFormsAndMaxVar (red : TransparencyMode) (pfs : List Expr) :
    MetaM (List Comp × ℕ) := do
  let pftps ← (pfs.mapM inferType)
  let (l, _, map) ← toCompFold red [] pftps TreeMap.empty
  trace[linarith.detail] "monomial map: {map.toList.map fun ⟨k,v⟩ => (k.toList, v)}"
  return (l, map.size - 1)

end Mathlib.Tactic.Linarith
