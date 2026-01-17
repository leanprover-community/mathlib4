/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Real.Basic

/-!
# Comparing real numbers

In this file we implement the procedure of comparing real numbers.

## Main definitions

* `compareReal`: compares a real number with zero.
* `checkZero`: checks if a real number is zero.
* `checkLtZero`: checks if a real number is less than zero.
* `compareTwoReals`: compares two real numbers.
-/

public meta section

namespace ComputeAsymptotics

open Qq Lean Elab Meta Tactic

namespace CompareReal

/-- Result of comparing a real number with zero. -/
inductive CompareResult (x : Q(Real))
| pos (pf : Q(0 < $x))
| neg (pf : Q($x < 0))
| zero (pf : Q($x = 0))

open Mathlib.Meta.NormNum in
/-- Normalize a real number using `norm_num` and `PreMS_const` simp lemmas. -/
def normalizeReal (x : Q(ℝ)) : TacticM <| (x' : Q(ℝ)) × Q($x = $x') := do
  let simpCtx ← Elab.Tactic.mkSimpContext (← `(tactic| simp -failIfUnchanged [PreMS_const])) false
  let simpCtx := simpCtx.ctx
  let ⟨⟨(x1 : Q(ℝ)), pf1?, _⟩, _⟩ := ← simp x simpCtx
  let pf1 : Q($x = $x1) := pf1?.getD (← mkEqRefl x)
  let ⟨(x2 : Q(ℝ)), pf2?, _⟩ ← deriveSimp simpCtx true x1
  let pf2 : Q($x1 = $x2) := pf2?.getD (← mkEqRefl x1)
  let pf : Q($x = $x2) := q(($pf1).trans $pf2)
  return ⟨x2, pf⟩

/-- Compare a real number `x` with zero assuming that `x` is normalized. -/
def compareRealCore (x : Q(ℝ)) : TacticM (CompareResult x) := do
  let e ← mkFreshExprMVar q(0 < $x)
  let res ← evalTacticAt (← `(tactic| norm_num; (try linarith); (try positivity))) e.mvarId!
  if res.isEmpty then
    return .pos e

  let e ← mkFreshExprMVar q($x < 0)
  let res ← evalTacticAt (← `(tactic| norm_num; (try linarith); (try positivity))) e.mvarId!
  if res.isEmpty then
    return .neg e

  let e ← mkFreshExprMVar q($x = 0)
  let res ← evalTacticAt (← `(tactic|
    norm_num <;> try field_simp <;> (try linarith) <;> (try positivity) <;> ring_nf)) e.mvarId!
  if res.isEmpty then
    return .zero e
  throwError f!"Cannot compare real number {← ppExpr x} with zero. You can use a `have` " ++
    "statement to provide the sign of the expression."

/-- Compare a real number `x` with zero. -/
def compareReal (x : Q(ℝ)) : TacticM (CompareResult x) := do
  dbg_trace "compareReal: {← ppExpr x}"
  let ⟨x', pf⟩ ← normalizeReal x
  dbg_trace "x': {x'}"
  let r ← compareRealCore x'
  return match r with
  | .pos e => .pos q(Eq.subst (motive := fun x ↦ 0 < x) (Eq.symm $pf) $e)
  | .neg e => .neg q(Eq.subst (motive := fun x ↦ x < 0) (Eq.symm $pf) $e)
  | .zero e => .zero q(Eq.subst (motive := fun x ↦ x = 0) (Eq.symm $pf) $e)

/-- Result of checking if a real number is zero. -/
inductive CheckZeroResult (x : Q(ℝ))
| eq (h : Q($x = 0))
| neq (h : Q($x ≠ 0))

/-- Check if a real number is zero. -/
def checkZero (x : Q(ℝ)) : TacticM (CheckZeroResult x) := do
  return match ← compareReal x with
  | .pos h => .neq q((ne_of_lt $h).symm)
  | .neg h => .neq q((ne_of_gt $h).symm)
  | .zero h => .eq q($h)

/-- Prove that a real number is not zero. -/
def proveNeZero (x : Q(ℝ)) : TacticM (Q($x ≠ 0)) := do
  let .neq h ← checkZero x | panic! "proveNeZero: unexpected zero"
  return h

/-- Result of checking if a real number is less than zero. -/
inductive CheckLtZeroResult (x : Q(ℝ))
| lt (h : Q($x < 0))
| not_lt (h : Q(¬$x < 0))

/-- Check if a real number is less than zero. -/
def checkLtZero (x : Q(ℝ)) : TacticM (CheckLtZeroResult x) := do
  return match ← compareReal x with
  | .pos h => .not_lt q(not_lt_of_gt $h)
  | .neg h => .lt q($h)
  | .zero h => .not_lt q(($h).symm.not_gt)

/-- Result of comparing two real numbers. -/
inductive CompareTwoRealsResult (x y : Q(ℝ))
| lt (h : Q($x < $y))
| eq (h : Q($x = $y))
| gt (h : Q($y < $x))

lemma eq_of_sub_eq_zero {x y : ℝ} (h : y - x = 0) : x = y := by linarith

/-- Compare two real numbers. -/
def compareTwoReals (x y : Q(ℝ)) : TacticM (CompareTwoRealsResult x y) := do
  return match ← compareReal q($y - $x) with
  | .pos h => .lt q(lt_add_neg_iff_lt.mp $h)
  | .zero h => .eq q(eq_of_sub_eq_zero $h)
  | .neg h => .gt q(sub_neg.mp $h)

end CompareReal

export CompareReal (normalizeReal compareReal checkLtZero compareTwoReals)

end ComputeAsymptotics
