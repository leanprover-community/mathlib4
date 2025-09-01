/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Tendsto.Meta.ConstSimp

/-!
# TODO
-/

open Qq Lean Elab Meta Tactic

namespace CompareReal

inductive CompareResult (x : Q(Real))
| pos (pf : Q(0 < $x))
| neg (pf : Q($x < 0))
| zero (pf : Q($x = 0))

open Mathlib.Meta.NormNum Parser Tactic

-- #check simpArgs

def preproces (x : Q(ℝ)) : TacticM <| (x' : Q(ℝ)) × (Option Q($x = $x')) := do
  let simpCtx : Simp.Context := ← getSimpContext (← `(config | (config := { })) ) (← `(simpArgs | [PreMS_const])) -- now to pass no config?
  let ⟨x', pf?, _⟩ ← deriveSimp simpCtx true x
  return ⟨x', pf?⟩

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
  let ⟨x', pf?⟩ ← preproces x
  haveI' : $x =Q $x' := ⟨⟩
  let pf : Q($x = $x') := pf?.getD q(rfl)
  let r ← compareRealCore x'
  return match r with
  | .pos e => .pos q(Eq.subst (motive := fun x ↦ 0 < x) (Eq.symm $pf) $e)
  | .neg e => .neg q(Eq.subst (motive := fun x ↦ x < 0) (Eq.symm $pf) $e)
  | .zero e => .zero q(Eq.subst (motive := fun x ↦ x = 0) (Eq.symm $pf) $e)

def proveNeZero (x : Q(ℝ)) : TacticM (Q($x ≠ 0)) := do
  match ← compareReal x with
  | .pos h => return q((ne_of_lt $h).symm)
  | .neg h => return q((ne_of_gt $h).symm)
  | .zero _ => panic! "proveNeZero: unexpected zero"

end CompareReal

export CompareReal (compareReal)
