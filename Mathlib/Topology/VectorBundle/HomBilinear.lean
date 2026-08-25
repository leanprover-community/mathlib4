/-
Copyright (c) 2025 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dominic Steinitz
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.Hom

/-!
# Coordinate expressions for the bundle of bilinear forms

Coordinate-level identities for `ContinuousLinearMap.inCoordinates` and the inverse
trivialization on the bundle of scalar-valued bilinear forms `fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ`,
used when transporting a fibrewise bilinear form (e.g. a Riemannian metric) through a
trivialization.
-/

open Set Bundle Trivialization

/-
`E` is a vector bundle over `B` with model fiber `F`.
-/
variable {B : Type*} {F : Type*} {E : B → Type*}
  [TopologicalSpace B]
  [NormedAddCommGroup F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [FiberBundle F E] [NormedSpace ℝ F] [VectorBundle ℝ F E]

public section

/-- Coordinate form on coordinate inputs = intrinsic form on transported inputs, for
`inCoordinates` on the bundle of bilinear forms `fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ`.
Specialisation of `inCoordinates_apply_eq₂` to a scalar codomain. -/
lemma inCoordinates_apply_eq₂_bilin
    {x₀ x : B} {ϕ : E x →L[ℝ] E x →L[ℝ] ℝ} {v w : F}
    (h₁x : x ∈ (trivializationAt F E x₀).baseSet) :
    ContinuousLinearMap.inCoordinates F E (F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] ℝ) x₀ x x₀ x ϕ v w =
    ϕ ((trivializationAt F E x₀).symm x v) ((trivializationAt F E x₀).symm x w) := by
  rw [inCoordinates_apply_eq₂ h₁x h₁x (by simp [Trivial.fiberBundle_trivializationAt'])]
  simp [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization]

/-- Intrinsic form on transported inputs = coordinate form's evaluation, for the inverse
trivialization of the bundle of bilinear forms `fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ`. The
pulled-back form `symm ϕ` applied to fibre vectors `u v : E x` equals `ϕ` applied to their
images `continuousLinearMapAt ℝ x u` and `continuousLinearMapAt ℝ x v` in `F`. -/
lemma trivializationAt_symm_apply_bilin
    (x₀ x : B) (hb : x ∈ (trivializationAt F E x₀).baseSet)
    (ϕ : F →L[ℝ] F →L[ℝ] ℝ) (u v : E x) :
    (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) x₀).symm x ϕ u v =
    ϕ (trivializationAt F E x₀ |>.continuousLinearMapAt ℝ x u)
      (trivializationAt F E x₀ |>.continuousLinearMapAt ℝ x v) := by
  let ψ := FiberBundle.trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
      (fun (x : B) ↦ E x →L[ℝ] E x →L[ℝ] ℝ) x₀
  let χ := trivializationAt F E x₀
  let w := ψ.symm x ϕ
  have hc : x ∈ ψ.baseSet := by
    rw [hom_trivializationAt_baseSet]
    simp only [hom_trivializationAt_baseSet, Trivial.fiberBundle_trivializationAt',
      Trivial.trivialization_baseSet, inter_univ, inter_self]
    exact hb
  have h1 : ∀ u v,
      (((continuousLinearMapAt ℝ ψ x) (ψ.symmL ℝ x ϕ)) u) v = ϕ u v :=
    fun u v => by rw [continuousLinearMapAt_symmL ψ hc]
  have h2 : ∀ u v, ϕ u v = w (χ.symm x u) (χ.symm x v) := fun u v => by
    rw [← h1, continuousLinearMapAt_apply, linearMapAt_apply, hom_trivializationAt_apply,
      if_pos hc, ← inCoordinates_apply_eq₂_bilin hb]
    rw [symmL_apply]
    exact hc
  have h3 := symmL_continuousLinearMapAt (R := ℝ) (trivializationAt F E x₀) hb u
  rw [symmL_apply] at h3
  · have h4 := symmL_continuousLinearMapAt (R := ℝ) (trivializationAt F E x₀) hb v
    rw [symmL_apply] at h4
    · rw [show w u v = ϕ (χ.continuousLinearMapAt ℝ x u) (χ.continuousLinearMapAt ℝ x v) from by
        rw [h2 (χ.continuousLinearMapAt ℝ x u) (χ.continuousLinearMapAt ℝ x v), h3, h4]]
    · exact hb
  · exact hb

end
