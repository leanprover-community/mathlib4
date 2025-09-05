/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

/-!
# TODO
-/

open Qq Lean Elab Meta Tactic

namespace CompareReal

inductive CompareResult (x : Q(Real))
| pos (pf : Q(0 < $x))
| neg (pf : Q($x < 0))
| zero (pf : Q($x = 0))

open Mathlib.Meta.NormNum in
def normalizeReal (x : Q(ℝ)) : TacticM <| (x' : Q(ℝ)) × Q($x = $x') := do
  let simpCtx ← Elab.Tactic.mkSimpContext (← `(tactic| simp [PreMS_const])) false
  let simpCtx := {simpCtx.ctx with config := {simpCtx.ctx.config with failIfUnchanged := false}}
  let ⟨⟨(x1 : Q(ℝ)), pf1?, _⟩, _⟩ := ← simp x simpCtx
  let pf1 : Q($x = $x1) := pf1?.getD (← mkEqRefl x)
  let ⟨(x2 : Q(ℝ)), pf2?, _⟩ ← deriveSimp simpCtx true x1
  let pf2 : Q($x1 = $x2) := pf2?.getD (← mkEqRefl x1)
  let pf : Q($x = $x2) := q(Eq.trans $pf1 $pf2)
  return ⟨x2, pf⟩

syntax "compare_real" : tactic
macro_rules
| `(tactic| compare_real) => `(tactic| norm_num; try linarith)

def compareRealCore (x : Q(ℝ)) : TacticM (CompareResult x) := do
  let e ← mkFreshExprMVar q(0 < $x)
  let res ← evalTacticAt (← `(tactic| compare_real)) e.mvarId!
  if res.isEmpty then
    return .pos e

  let e ← mkFreshExprMVar q($x < 0)
  let res ← evalTacticAt (← `(tactic| compare_real)) e.mvarId!
  if res.isEmpty then
    return .neg e

  let e ← mkFreshExprMVar q($x = 0)
  let res ← evalTacticAt (← `(tactic| compare_real)) e.mvarId!
  if res.isEmpty then
    return .zero e
  throwError f!"Cannot compare real number {← ppExpr x} with zero"

def compareReal (x : Q(ℝ)) : TacticM (CompareResult x) := do
  let ⟨x', pf⟩ ← normalizeReal x
  -- dbg_trace f!"normalizeReal: {← ppExpr x} --> {← ppExpr x'}"
  let r ← compareRealCore x'
  return match r with
  | .pos e => .pos q(Eq.subst (motive := fun x ↦ 0 < x) (Eq.symm $pf) $e)
  | .neg e => .neg q(Eq.subst (motive := fun x ↦ x < 0) (Eq.symm $pf) $e)
  | .zero e => .zero q(Eq.subst (motive := fun x ↦ x = 0) (Eq.symm $pf) $e)

inductive CheckZeroResult (x : Q(ℝ))
| eq (h : Q($x = 0))
| neq (h : Q($x ≠ 0))

def checkZero (x : Q(ℝ)) : TacticM (CheckZeroResult x) := do
  return match ← compareReal x with
  | .pos h => .neq q((ne_of_lt $h).symm)
  | .neg h => .neq q((ne_of_gt $h).symm)
  | .zero h => .eq q($h)

def proveNeZero (x : Q(ℝ)) : TacticM (Q($x ≠ 0)) := do
  let .neq h ← checkZero x | panic! "proveNeZero: unexpected zero"
  return h

inductive CheckLtZeroResult (x : Q(ℝ))
| lt (h : Q($x < 0))
| not_lt (h : Q(¬$x < 0))

def checkLtZero (x : Q(ℝ)) : TacticM (CheckLtZeroResult x) := do
  return match ← compareReal x with
  | .pos h => .not_lt q(not_lt_of_gt $h)
  | .neg h => .lt q($h)
  | .zero h => .not_lt q(($h).symm.not_gt)

inductive CompareTwoRealsResult (x y : Q(ℝ))
| lt (h : Q($x < $y))
| eq (h : Q($x = $y))
| gt (h : Q($y < $x))

lemma eq_of_sub_eq_zero {x y : ℝ} (h : y - x = 0) : x = y := by linarith

def compareTwoReals (x y : Q(ℝ)) : TacticM (CompareTwoRealsResult x y) := do
  return match ← compareReal q($y - $x) with
  | .pos h => .lt q(lt_add_neg_iff_lt.mp $h)
  | .zero h => .eq q(eq_of_sub_eq_zero $h)
  | .neg h => .gt q(sub_neg.mp $h)

end CompareReal

export CompareReal (normalizeReal compareReal checkZero checkLtZero compareTwoReals)
