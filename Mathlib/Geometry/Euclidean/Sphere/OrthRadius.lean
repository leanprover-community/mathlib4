/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Geometry.Euclidean.Sphere.Basic

/-!
# Spaces orthogonal to the radius vector in spheres.

This file defines the affine subspace orthogonal to the radius vector at a point.

## Main definitions

* `EuclideanGeometry.Sphere.orthRadius`: the affine subspace orthogonal to the radius vector at
  a point (the tangent space, if that point lies in the sphere; more generally, the polar of the
  inversion of that point in the sphere).

-/

@[expose] public section


namespace EuclideanGeometry

namespace Sphere

open AffineSubspace RealInnerProductSpace
open scoped Affine

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- The affine subspace orthogonal to the radius vector of the sphere `s` at the point `p` (if
`p` lies in `s`, this is the tangent space; generally, this is the polar of the inversion of `p`
in `s`). -/
noncomputable def orthRadius (s : Sphere P) (p : P) : AffineSubspace ℝ P :=
  .mk' p (ℝ ∙ (p -ᵥ s.center))ᗮ

lemma self_mem_orthRadius (s : Sphere P) (p : P) : p ∈ s.orthRadius p :=
  self_mem_mk' _ _

lemma mem_orthRadius_iff_inner_left {s : Sphere P} {p x : P} :
    x ∈ s.orthRadius p ↔ ⟪x -ᵥ p, p -ᵥ s.center⟫ = 0 := by
  rw [orthRadius, mem_mk', Submodule.mem_orthogonal_singleton_iff_inner_left]

lemma mem_orthRadius_iff_inner_right {s : Sphere P} {p x : P} :
    x ∈ s.orthRadius p ↔ ⟪p -ᵥ s.center, x -ᵥ p⟫ = 0 := by
  rw [mem_orthRadius_iff_inner_left, inner_eq_zero_symm]

@[simp] lemma direction_orthRadius (s : Sphere P) (p : P) :
    (s.orthRadius p).direction = (ℝ ∙ (p -ᵥ s.center))ᗮ := by
  rw [orthRadius, direction_mk']

@[simp] lemma orthRadius_center (s : Sphere P) : s.orthRadius s.center = ⊤ := by
  simp [orthRadius]

@[simp] lemma center_mem_orthRadius_iff {s : Sphere P} {p : P} :
    s.center ∈ s.orthRadius p ↔ p = s.center := by
  rw [mem_orthRadius_iff_inner_left, ← neg_vsub_eq_vsub_rev, inner_neg_left]
  simp

lemma orthRadius_le_orthRadius_iff {s : Sphere P} {p q : P} :
    s.orthRadius p ≤ s.orthRadius q ↔ p = q ∨ q = s.center := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := direction_le h
    simp only [direction_orthRadius] at h'
    have h'' := Submodule.orthogonal_le h'
    simp only [Submodule.orthogonal_orthogonal, Submodule.span_singleton_le_iff_mem,
      Submodule.mem_span_singleton] at h''
    rcases h'' with ⟨r, hr⟩
    have hp : p ∈ s.orthRadius q := h (s.self_mem_orthRadius p)
    rw [mem_orthRadius_iff_inner_left, ← vsub_sub_vsub_cancel_right p q s.center, ← hr,
      inner_sub_left, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← sub_mul,
      mul_eq_zero] at hp
    rcases hp with hp | hp
    · nth_rw 1 [← one_mul r] at hp
      rw [← sub_mul, mul_eq_zero] at hp
      rcases hp with hp | rfl
      · rw [sub_eq_zero] at hp
        rw [← hp, one_smul, vsub_left_cancel_iff] at hr
        exact .inl hr
      · rw [zero_smul, eq_comm, vsub_eq_zero_iff_eq] at hr
        exact .inr hr
    · simp only [inner_self_eq_zero, vsub_eq_zero_iff_eq] at hp
      rw [hp, vsub_self, smul_zero, eq_comm, vsub_eq_zero_iff_eq] at hr
      exact .inr hr
  · rcases h with rfl | rfl <;> simp

@[simp] lemma orthRadius_eq_orthRadius_iff {s : Sphere P} {p q : P} :
    s.orthRadius p = s.orthRadius q ↔ p = q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hpq := orthRadius_le_orthRadius_iff.1 h.le
  have hqp := orthRadius_le_orthRadius_iff.1 h.symm.le
  grind

lemma finrank_orthRadius [FiniteDimensional ℝ V] {s : Sphere P} {p : P} (hp : p ≠ s.center) :
    Module.finrank ℝ (s.orthRadius p).direction + 1 = Module.finrank ℝ V := by
  rw [orthRadius, add_comm, direction_mk']
  convert (ℝ ∙ (p -ᵥ s.center)).finrank_add_finrank_orthogonal
  exact (finrank_span_singleton (vsub_ne_zero.2 hp)).symm

lemma orthRadius_map {s : Sphere P} (p : P) {f : P ≃ᵃⁱ[ℝ] P} (h : f s.center = s.center) :
    (s.orthRadius p).map f.toAffineMap = s.orthRadius (f p) := by
  rw [orthRadius, map_mk', orthRadius]
  convert rfl using 2
  convert (Submodule.map_orthogonal_equiv (ℝ ∙ (p -ᵥ s.center)) f.linearIsometryEquiv).symm
  simp [Submodule.map_span, Set.image_singleton, h]

lemma direction_orthRadius_le_iff {s : Sphere P} {p q : P} :
    (s.orthRadius p).direction ≤ (s.orthRadius q).direction ↔
      ∃ r : ℝ, q -ᵥ s.center = r • (p -ᵥ s.center) := by
  simp [Submodule.orthogonal_le_orthogonal_iff, Submodule.mem_span_singleton, eq_comm]

lemma orthRadius_parallel_orthRadius_iff {s : Sphere P} {p q : P} :
    s.orthRadius p ∥ s.orthRadius q ↔ ∃ r : ℝ, r ≠ 0 ∧ q -ᵥ s.center = r • (p -ᵥ s.center) := by
  simp_rw [orthRadius, parallel_iff_direction_eq_and_eq_bot_iff_eq_bot, direction_mk',
    Submodule.orthogonalComplement_eq_orthogonalComplement,
    Submodule.span_singleton_eq_span_singleton, ← coe_eq_bot_iff,
    ← Set.not_nonempty_iff_eq_empty, mk'_nonempty, and_true, ← Units.exists_iff_ne_zero, eq_comm,
    Units.smul_def]

end Sphere

end EuclideanGeometry
