/-
Copyright (c) 2026 Cody Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cody Mitchell
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# Extension of `reassoc` to linear maps.

We extend `reassoc` and `reassoc_of%` for equality of linear maps.
Adding `@[reassoc]` to a lemma named `F` of shape `∀ .., f = g`,
where `f g : M →ₗ[R] N`, will create a new lemma named `F_assoc` of shape
`∀ .. {M'} (h : M' →ₗ[R] M), f ∘ₗ h = g ∘ₗ h`
but with compositions fully right associated and identities removed using
`LinearMap.comp_id`, `LinearMap.id_comp`, and `LinearMap.comp_assoc`.

This is useful for generating lemmas which the simplifier can use even on expressions
that are already right associated.
-/

public meta section

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.Reassoc

universe u₁ u₂ u₃

theorem LinearMap.eq_whisker {R : Type u₁} [Semiring R]
    {M₂ : Type u₂} [AddCommMonoid M₂] [Module R M₂]
    {M₃ : Type u₃} [AddCommMonoid M₃] [Module R M₃]
    {f g : M₂ →ₗ[R] M₃} (w : f = g)
    {M₁ : Type u₂} [AddCommMonoid M₁] [Module R M₁] (h : M₁ →ₗ[R] M₂) :
    f ∘ₗ h = g ∘ₗ h := by
  rw [w]

/-- Simplify an expression using only linear map composition identities. -/
def linearMapSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``LinearMap.comp_id, ``LinearMap.id_comp, ``LinearMap.comp_assoc] e
    (config := { decide := false })

/--
Given an equation `f = g` between linear maps `M₂ →ₗ[R] M₃`,
produce the equation `∀ {M₁} (h : M₁ →ₗ[R] M₂), f ∘ₗ h = g ∘ₗ h`,
but with compositions fully right associated and identities removed.
-/
def reassocExprLinearMap (e : Expr) : MetaM (Expr × Array MVarId) := do
  let lem₀ ← mkConstWithFreshMVarLevels ``LinearMap.eq_whisker
  let (args, _, _) ← forallMetaBoundedTelescope (← inferType lem₀) 11
  let inst := args[1]!
  inst.mvarId!.setKind .synthetic
  let w := args[10]!
  w.mvarId!.assignIfDefEq e
  withEnsuringLocalInstance inst.mvarId! do
    return (← simpType linearMapSimp (mkAppN lem₀ args), #[inst.mvarId!])

initialize registerReassocExpr reassocExprLinearMap

end Mathlib.Tactic.Reassoc
