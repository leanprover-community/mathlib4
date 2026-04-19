/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Morphisms to `⦋1⦌`

We define a bijective map `SimplexCategory.toMk₁ : Fin (n + 2) → `⦋n⦌ ⟶ ⦋1⦌`.
This is used in the file `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne`
in the study of simplices in the simplicial set `Δ[1]`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SimplexCategory

/-- Given `i : Fin (n + 2)`, this is the morphism `⦋n⦌ ⟶ ⦋1⦌` in the simplex
category which corresponds to the monotone map `Fin (n + 1) → Fin 2` which
takes `i` times the value `0`. -/
def toMk₁ {n : ℕ} (i : Fin (n + 2)) : ⦋n⦌ ⟶ ⦋1⦌ :=
  Hom.mk
    { toFun j := if j.castSucc < i then 0 else 1
      monotone' j₁ j₂ h := by
        dsimp
        split_ifs <;> grind }

@[local grind =]
lemma toMk₁_apply {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
  dsimp% toMk₁ i j = if j.castSucc < i then 0 else 1 := rfl

#guard_msgs in
open Lean Elab Command Term Meta in
elab "#elab_if " cond:term " in " cmd:command : command => do
  if (← liftTermElabM do
    let e ← elabTerm cond none
    synthesizeSyntheticMVarsNoPostponing
    let e ← if (← isDefEq (← inferType e) (mkConst ``Bool)) then pure e else mkDecide e
    unsafe evalExpr Bool (mkConst ``Bool) e
  ) then elabCommand cmd

#elab_if Lean.versionString == "4.30.0-rc2" in
/--
  [issue] failed to convert to ring expression
        1
-/
#guard_msgs (substring := true) in
lemma toMk₁_apply_eq_zero_iff {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    dsimp% toMk₁ i j = 0 ↔ j.castSucc < i := by
  grind

#elab_if Lean.versionString == "4.29.0" in
#guard_msgs in
lemma toMk₁_apply_eq_zero_iff {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    dsimp% toMk₁ i j = 0 ↔ j.castSucc < i := by
  grind
