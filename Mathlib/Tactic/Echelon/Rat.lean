/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Algebra.CharP.Defs  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Echelon.Core
public import Mathlib.Tactic.NormNum.Basic

/-!
# The rational model for the Bareiss elimination

The computable model of ℚ. Entries evaluate to rational numerals via `norm_num`, reported
as integer numerators with their denominators, so that the elimination runs on integer values.
It is the fallback model the tactic uses when no ring-specific model matches the ring.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Echelon

/-- Data-only evaluation of a matrix entry to its rational value via `norm_num`.
Fraction values are accepted only in characteristic zero. -/
def evalRatEntry (charZero : Bool) (e : Expr) : MetaM Rat := do
  let ⟨_, _, eQ⟩ ← inferTypeQ' e
  let r ← try some <$> Mathlib.Meta.NormNum.derive eQ catch _ => pure none
  if let some v := r.bind (·.toRat) then
    if v.den == 1 || charZero then
      return v
  throwError "the following entry cannot be simplified to a numeral{indentExpr e}"

/-- Build the numeral of an integer in `α`: `mkNumeral` on the absolute value, negated if
`i` is negative. -/
def mkIntNumeral {u : Level} (α : Q(Type u)) (i : Int) : MetaM Q($α) := do
  let n : Q($α) ← mkNumeral α i.natAbs
  if i < 0 then
    let _ ← synthInstanceQ q(Neg $α)
    return q(-$n)
  else
    return n

/-- The rational model. -/
def ratModel {u : Level} (α : Q(Type u)) (_cr : Q(CommRing $α)) :
    MetaM ((c : Carrier) × Model c.type) := do
  -- the characteristic determines the zero test
  let pQ : Q(ℕ) ← mkFreshExprMVarQ q(ℕ)
  let .some _ ← trySynthInstanceQ q(CharP $α $pQ)
    | throwError "could not determine the characteristic of the element type{indentExpr α}"
  -- `whnfD`: the ambient transparency inside `simp` is `reducible`, which does not reduce
  -- the numeral to a literal
  let some p := (← whnfD (← instantiateMVars pQ)).rawNatLit?
    | throwError "the characteristic of the element type is not a literal{indentExpr α}"
  let ops : RingOps Int := {
    zero := 0
    one := 1
    mul x y := x * y
    sub x y := x - y
    divExact x y := x / y
    isZero x := if p == 0 then x == 0 else x % p == 0 }
  return ⟨.int, {
    ops
    evalEntry := fun e => do
      let v ← evalRatEntry (p == 0) e
      return (v.num, if v.den == 1 then none else some (v.den : Int))
    commonMultiple := fun a b => (Int.lcm a b : Int)
    mkEntry := mkIntNumeral α }⟩

end Mathlib.Tactic.Echelon
