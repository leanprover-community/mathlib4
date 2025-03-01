/-
Copyright (c) 2024 Vasilii Nesterov. All rights reserved.
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

open Mathlib.Meta.NormNum

def preproces (x : Q(ℝ)) : MetaM <| Option ((x' : Q(ℝ)) × Q($x = $x')) := do
  let simpCtx : Simp.Context := {
    congrTheorems := (← getSimpCongrTheorems)
    config        := Simp.neutralConfig
  }
  let ⟨x', pf?, _⟩ ← deriveSimp simpCtx true x
  return pf?.map fun pf =>
    ⟨x', pf⟩

def compareRealCore (x : Q(ℝ)) : TacticM (CompareResult x) := do
  let e ← mkFreshExprMVar q(0 < $x)
  let res ← evalTacticAt (← `(tactic| norm_num; try linarith)) e.mvarId!
  if res.isEmpty then
    return .pos e

  let e ← mkFreshExprMVar q($x < 0)
  let res ← evalTacticAt (← `(tactic| norm_num; try linarith)) e.mvarId!
  if res.isEmpty then
    return .neg e

  let e ← mkFreshExprMVar q($x = 0)
  let res ← evalTacticAt (← `(tactic| norm_num; try linarith)) e.mvarId!
  if res.isEmpty then
    return .zero e
  throwError f!"Cannot compare real number {← ppExpr x} with zero"

def compareReal (x : Q(ℝ)) : TacticM (CompareResult x) := do
  match ← preproces x with
  | none => return ← compareRealCore x
  | some ⟨x', pf⟩ =>
    -- dbg_trace f!"preprocessed : {← ppExpr x'}" -- TODO: the whole thing does not work
    let r ← compareRealCore x'
    return match r with
    | .pos e => .pos q(Eq.subst (motive := fun x ↦ 0 < x) (Eq.symm $pf) $e)
    | .neg e => .neg q(Eq.subst (motive := fun x ↦ x < 0) (Eq.symm $pf) $e)
    | .zero e => .zero q(Eq.subst (motive := fun x ↦ x = 0) (Eq.symm $pf) $e)

end CompareReal

export CompareReal (compareReal)
