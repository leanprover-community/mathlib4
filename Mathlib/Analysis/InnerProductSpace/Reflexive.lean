/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Hilbert spaces are reflexive

We prove that a Hilbert space `H` is reflexive: the canonical map from `H` to its
double dual is surjective. This is a consequence of the Riesz representation theorem
`InnerProductSpace.toDual`.
-/

public section

open scoped ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A Hilbert space is reflexive. -/
instance InnerProductSpace.isReflexive {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] : TopologicalSpace.IsReflexive 𝕜 H := by
  rw [NormedSpace.isReflexive_iff_surjective_inclusionInDoubleDual]
  intro Λ
  let T := InnerProductSpace.toDual 𝕜 H
  -- `y ↦ conj (Λ ⟪y, ·⟫)` is a continuous linear form, represented by a vector by the Riesz theorem
  let ψ : StrongDual 𝕜 H := LinearMap.mkContinuous
    { toFun := fun y ↦ conj (Λ (T y))
      map_add' := fun y z ↦ by simp
      map_smul' := fun c y ↦ by simp [map_smulₛₗ] } ‖Λ‖
    fun y ↦ by simpa [T] using Λ.le_opNorm (T y)
  refine ⟨T.symm ψ, ContinuousLinearMap.ext fun φ ↦ ?_⟩
  obtain ⟨z, rfl⟩ := T.surjective φ
  rw [NormedSpace.dual_def, InnerProductSpace.toDual_apply_apply, ← inner_conj_symm,
    InnerProductSpace.toDual_symm_apply]
  simp [ψ]
