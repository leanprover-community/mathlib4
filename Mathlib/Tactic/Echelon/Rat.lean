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

The computable model of literals expressible in ℚ. It is the fallback model the tactic uses when no
other model matches the ring.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Echelon

/-- Data-only evaluation of a matrix entry to its rational value via `norm_num`.
Fraction values are accepted only in characteristic zero. -/
def evalRatEntry (charZero : Bool) (e : Expr) : MetaM Rat := do
  let ⟨_, _, eQ⟩ ← inferTypeQ' e
  let r ← try some <$> Meta.NormNum.derive eQ catch _ => pure none
  if let some v := r.bind (·.toRat) then
    if v.den == 1 || charZero then
      return v
  throwError "the following entry cannot be simplified to a numeral{indentExpr e}"

/-- Build the numeral of an integer in `α`: `mkNumeral` on the absolute value, negated if
`i` is negative. -/
def mkIntNumeral {u : Level} (α : Q(Type u)) (i : Int) : MetaM Q($α) := do
  let n ← mkNumeral α i.natAbs
  have n : Q($α) := n
  if i < 0 then
    let _ ← synthInstanceQ q(Neg $α)
    return q(-$n)
  else
    return n

/-- Check whether `decide` reduces the nonzero-ness of a numeral of `α` to a verdict, the shape
of the entry conditions the certificate closes by `decide`. ℝ has a classical `DecidableEq`
instance, so instance synthesis alone does not settle this.
The probe checks 2 instead of 1 against 0 because some rings might have decidable equality
facts between 0 and 1, but not for general entries against 0. -/
def checkDecideEq {u : Level} (α : Q(Type u)) (rα : Q(CommRing $α)) : MetaM Bool := do
  let two : Q($α) ← mkIntNumeral α 2
  -- `Decidable` of the single disequality rather than `DecidableEq`: a ring where equality
  -- is only decidable against zero should pass
  let some _inst ← synthInstanceQ? q(Decidable ($two ≠ 0)) | return false
  let dec := q(decide ($two ≠ 0))
  return (Kernel.whnf (← getEnv) (← getLCtx) dec).toOption.any fun r =>
    r.isConstOf ``Bool.true || r.isConstOf ``Bool.false

/-- `norm_num`'s core as an entry certifier. -/
def normNumCertifier : EntryCertifier := fun p => do
  let ⟨b, prf⟩ ← Mathlib.Meta.NormNum.deriveBool p
  unless b do throwError "norm_num refutes{indentExpr p}"
  return prf

/-- The rational model. -/
def ratModel {u : Level} (α : Q(Type u)) (rα : Q(CommRing $α)) :
    MetaM (Model Int) := do
  let entryCertifier? ← do
    if ← checkDecideEq α rα then pure none
    else
      trace[Tactic.evalRank] "`decide` cannot settle equality in the element type; \
        using the `norm_num` entry certifier{indentExpr α}"
      pure (some normNumCertifier)
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
    mul := (· * ·)
    sub := (· - ·)
    divExact := (· / ·)
    isZero := if p == 0 then (· == 0) else fun v => v % p == 0 }
  return {
    ops
    evalEntry := fun e => do
      let v ← evalRatEntry (p == 0) e
      return (v.num, if v.den == 1 then none else some (v.den : Int))
    commonMultiple := fun a b => (Int.lcm a b : Int)
    mkEntry := mkIntNumeral α
    entryCertifier? }

end Mathlib.Tactic.Echelon
