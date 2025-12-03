/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public meta import Mathlib.Tactic.CategoryTheory.Coherence.Normalize
public meta import Mathlib.Tactic.CategoryTheory.Coherence.PureCoherence
public meta import Aesop
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Tactic.CategoryTheory.Coherence.Normalize
public import Mathlib.Tactic.CategoryTheory.Coherence.PureCoherence

/-!
# The Core function for `monoidal` and `bicategory` tactics

This file provides the function `BicategoryLike.main` for proving equalities in monoidal categories
and bicategories. Using `main`, we will define the following tactics:
- `monoidal` at `Mathlib/Tactic/CategoryTheory/Monoidal/Basic.lean`
- `bicategory` at `Mathlib/Tactic/CategoryTheory/Bicategory/Basic.lean`

The `main` first normalizes the both sides using `eval`, then compares the corresponding components.
It closes the goal at non-structural parts with `rfl` and the goal at structural parts by
`pureCoherence`.

-/

public meta section

open Lean Meta Elab
open CategoryTheory Mathlib.Tactic.BicategoryLike

namespace Mathlib.Tactic.BicategoryLike

theorem mk_eq {α : Type _} (a b a' b' : α) (ha : a = a') (hb : b = b') (h : a' = b') : a = b := by
  simp [h, ha, hb]

/-- Transform an equality between 2-morphisms into the equality between their normalizations. -/
def normalForm (ρ : Type) [Context ρ]
    [MonadMor₁ (CoherenceM ρ)]
    [MonadMor₂Iso (CoherenceM ρ)]
    [MonadNormalExpr (CoherenceM ρ)] [MkEval (CoherenceM ρ)]
    [MkMor₂ (CoherenceM ρ)]
    [MonadMor₂ (CoherenceM ρ)]
    (nm : Name) (mvarId : MVarId) : MetaM (List MVarId) := do
  mvarId.withContext do
    let e ← instantiateMVars <| ← mvarId.getType
    withTraceNode nm (fun _ => return m!"normalize: {e}") do
      let some (_, e₁, e₂) := (← whnfR <| ← instantiateMVars <| e).eq?
        | throwError "{nm}_nf requires an equality goal"
      let ctx : ρ ← mkContext e₁
      CoherenceM.run (ctx := ctx) do
        let e₁' ← MkMor₂.ofExpr e₁
        let e₂' ← MkMor₂.ofExpr e₂
        let e₁'' ← eval nm e₁'
        let e₂'' ← eval nm e₂'
        let H ← mkAppM ``mk_eq #[e₁, e₂, e₁''.expr.e.e, e₂''.expr.e.e, e₁''.proof, e₂''.proof]
        mvarId.apply H

universe v u

theorem mk_eq_of_cons {C : Type u} [CategoryStruct.{v} C]
    {f₁ f₂ f₃ f₄ : C}
    (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs ηs' : f₃ ⟶ f₄)
    (e_α : α = α') (e_η : η = η') (e_ηs : ηs = ηs') :
    α ≫ η ≫ ηs = α' ≫ η' ≫ ηs' := by
  simp [e_α, e_η, e_ηs]

/-- Split the goal `α ≫ η ≫ ηs = α' ≫ η' ≫ ηs'` into `α = α'`, `η = η'`, and `ηs = ηs'`. -/
def ofNormalizedEq (mvarId : MVarId) : MetaM (List MVarId) := do
  mvarId.withContext do
    let e ← instantiateMVars <| ← mvarId.getType
    let some (_, e₁, e₂) := (← whnfR e).eq? | throwError "requires an equality goal"
    match (← whnfR e₁).getAppFnArgs, (← whnfR e₂).getAppFnArgs with
    | (``CategoryStruct.comp, #[_, _, _, _, _, α, η]),
      (``CategoryStruct.comp, #[_, _, _, _, _, α', η']) =>
      match (← whnfR η).getAppFnArgs, (← whnfR η').getAppFnArgs with
      | (``CategoryStruct.comp, #[_, _, _, _, _, η, ηs]),
        (``CategoryStruct.comp, #[_, _, _, _, _, η', ηs']) =>
        let e_α ← mkFreshExprMVar (← Meta.mkEq α α')
        let e_η  ← mkFreshExprMVar (← Meta.mkEq η η')
        let e_ηs ← mkFreshExprMVar (← Meta.mkEq ηs ηs')
        let x ← mvarId.apply (← mkAppM ``mk_eq_of_cons #[α, α', η, η', ηs, ηs', e_α, e_η, e_ηs])
        return x
      | _, _ => throwError "failed to make a normalized equality for {e}"
    | _, _ => throwError "failed to make a normalized equality for {e}"

/-- List.splitEvenOdd [0, 1, 2, 3, 4] = ([0, 2, 4], [1, 3]) -/
def List.splitEvenOdd {α : Type u} : List α → List α × List α
  | [] => ([], [])
  | [a] => ([a], [])
  | a::b::xs =>
    let (as, bs) := List.splitEvenOdd xs
    (a::as, b::bs)

/-- The core function for `monoidal` and `bicategory` tactics. -/
def main (ρ : Type) [Context ρ] [MonadMor₁ (CoherenceM ρ)] [MonadMor₂Iso (CoherenceM ρ)]
    [MonadNormalExpr (CoherenceM ρ)] [MkEval (CoherenceM ρ)] [MkMor₂ (CoherenceM ρ)]
    [MonadMor₂ (CoherenceM ρ)] [MonadCoherehnceHom (CoherenceM ρ)]
    [MonadNormalizeNaturality (CoherenceM ρ)] [MkEqOfNaturality (CoherenceM ρ)]
    (nm : Name) (mvarId : MVarId) : MetaM (List MVarId) :=
  mvarId.withContext do
    let mvarIds ← normalForm ρ nm mvarId
    let (mvarIdsCoherence, mvarIdsRefl) := List.splitEvenOdd (← repeat' ofNormalizedEq mvarIds)
    for mvarId in mvarIdsRefl do mvarId.refl
    let mvarIds'' ← mvarIdsCoherence.mapM fun mvarId => do
      withTraceNode nm (fun _ => do return m!"goal: {← mvarId.getType}") do
        try
          pureCoherence ρ nm mvarId
        catch _ => return [mvarId]
    return mvarIds''.flatten

end Mathlib.Tactic.BicategoryLike
