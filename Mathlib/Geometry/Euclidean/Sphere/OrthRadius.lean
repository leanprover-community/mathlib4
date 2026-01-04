/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Geometry.Euclidean.Projection
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

open AffineSubspace Function RealInnerProductSpace
open scoped Affine

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- The affine subspace orthogonal to the radius vector of the sphere `s` at the point `p` (if
`p` lies in `s`, this is the tangent space; generally, this is the polar of the inversion of `p`
in `s`). -/
def orthRadius (s : Sphere P) (p : P) : AffineSubspace ℝ P := .mk' p (ℝ ∙ (p -ᵥ s.center))ᗮ

instance (s : Sphere P) (p : P) : Nonempty (s.orthRadius p) := by
  rw [orthRadius]
  infer_instance

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

instance (s : Sphere P) (p : P) : (s.orthRadius p).direction.HasOrthogonalProjection := by
  rw [direction_orthRadius]
  infer_instance

@[simp] lemma orthRadius_center (s : Sphere P) : s.orthRadius s.center = ⊤ := by
  simp [orthRadius]

@[simp] lemma center_mem_orthRadius_iff {s : Sphere P} {p : P} :
    s.center ∈ s.orthRadius p ↔ p = s.center := by
  rw [mem_orthRadius_iff_inner_left, ← neg_vsub_eq_vsub_rev, inner_neg_left]
  simp

@[simp] lemma orthogonalProjection_orthRadius_center (s : Sphere P) (p : P) :
    orthogonalProjection (s.orthRadius p) s.center = p := by
  simp_rw [orthRadius, coe_orthogonalProjection_eq_iff_mem]
  rw [← Submodule.neg_mem_iff]
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

lemma orthRadius_injective (s : Sphere P) : Injective s.orthRadius :=
  fun _ _ ↦ orthRadius_eq_orthRadius_iff.1

lemma finrank_orthRadius [FiniteDimensional ℝ V] {s : Sphere P} {p : P} (hp : p ≠ s.center) :
    Module.finrank ℝ (s.orthRadius p).direction + 1 = Module.finrank ℝ V := by
  rw [orthRadius, add_comm, direction_mk']
  convert (ℝ ∙ (p -ᵥ s.center)).finrank_add_finrank_orthogonal
  exact (finrank_span_singleton (vsub_ne_zero.2 hp)).symm

lemma orthRadius_map {s : Sphere P} (p : P) {f : P ≃ᵃⁱ[ℝ] P} (h : f s.center = s.center) :
    (s.orthRadius p).map f.toAffineMap = s.orthRadius (f p) := by
  rw [orthRadius, map_mk', orthRadius]
  convert rfl using 2
  convert (Submodule.map_orthogonal (ℝ ∙ (p -ᵥ s.center)) f.linearIsometryEquiv).symm
  simp [Submodule.map_span, Set.image_singleton, h]

lemma direction_orthRadius_le_iff {s : Sphere P} {p q : P} :
    (s.orthRadius p).direction ≤ (s.orthRadius q).direction ↔
      ∃ r : ℝ, q -ᵥ s.center = r • (p -ᵥ s.center) := by
  simp [Submodule.orthogonal_le_orthogonal_iff, Submodule.mem_span_singleton, eq_comm]

lemma orthRadius_parallel_orthRadius_iff {s : Sphere P} {p q : P} :
    s.orthRadius p ∥ s.orthRadius q ↔ ∃ r : ℝ, r ≠ 0 ∧ q -ᵥ s.center = r • (p -ᵥ s.center) := by
  simp only [orthRadius, parallel_iff_direction_eq_and_eq_bot_iff_eq_bot, direction_mk',
    Submodule.orthogonalComplement_eq_orthogonalComplement,
    Submodule.span_singleton_eq_span_singleton, ← coe_eq_bot_iff,
    ← Set.not_nonempty_iff_eq_empty, mk'_nonempty, not_true_eq_false, and_true]
  exact ⟨fun ⟨r, h⟩ ↦ ⟨r, r.ne_zero, h.symm⟩, fun ⟨r, hr, h⟩ ↦ ⟨.mk0 r hr, h.symm⟩⟩

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

lemma ncard_inter_orthRadius_eq_two_of_dist_lt_radius [hf2 : Fact (Module.finrank ℝ V = 2)]
    {s : Sphere P} {p : P} (hp : dist p s.center < s.radius) (hpc : p ≠ s.center) :
    (s ∩ s.orthRadius p : Set P).ncard = 2 := by
  rw [Set.ncard_eq_two]
  have hf := finrank_orthRadius hpc
  simp only [hf2.out, Nat.reduceEqDiff, finrank_eq_one_iff'] at hf
  obtain ⟨v, hv0, hv⟩ := hf
  let v' : V := (√(s.radius ^ 2 - (dist p s.center) ^ 2) / ‖v‖) • v
  have hvp : 0 < √(s.radius ^ 2 - (dist p s.center) ^ 2) := by
    rw [Real.sqrt_pos, sub_pos, sq_lt_sq, abs_of_nonneg dist_nonneg]
    exact lt_abs.2 (.inl hp)
  have hv' : ∀ p' ∈ s.orthRadius p, ∃ c : ℝ, c • v' +ᵥ p = p' := by
    intro p' hp'
    rw [orthRadius, mem_mk', ← direction_orthRadius] at hp'
    obtain ⟨c, hc⟩ := hv ⟨_, hp'⟩
    have hc' : c • (v : V) = p' -ᵥ p := by
      norm_cast
      simp [hc]
    refine ⟨‖v‖ / √(s.radius ^ 2 - (dist p s.center) ^ 2) * c, ?_⟩
    simp_rw [v', smul_smul]
    rw [eq_comm, eq_vadd_iff_vsub_eq, ← hc']
    congr
    field
  have hvn : ‖v'‖ ^ 2 = s.radius ^ 2 - (dist p s.center) ^ 2 := by
    simp only [AddSubgroupClass.coe_norm, norm_smul, norm_div, Real.norm_eq_abs, v', abs_norm,
      mul_pow, div_pow, sq_abs]
    rw [Real.sq_sqrt (Real.sqrt_pos.1 hvp).le]
    have hv0 : ‖(v : V)‖ ≠ 0 := by simp [hv0]
    field
  have hvd : (v : V) ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ := by
    rw [← direction_orthRadius]
    exact v.property
  have hvn' (c : ℝ) : (dist (c • v' +ᵥ p) s.center) ^ 2 =
      (dist p s.center) ^ 2 + c ^ 2 * (s.radius ^ 2 - (dist p s.center) ^ 2) := by
    rw [dist_eq_norm_vsub, vadd_vsub_assoc, norm_add_sq_real, ← dist_eq_norm_vsub, norm_smul,
      mul_pow, hvn, Real.norm_eq_abs, sq_abs, real_inner_smul_left]
    simp_rw [v', real_inner_smul_left]
    rw [Submodule.inner_right_of_mem_orthogonal hvd (by simp)]
    ring
  have hvn'' (c : ℝ) : dist (c • v' +ᵥ p) s.center = s.radius ↔ |c| = 1 := by
    rw [← abs_of_nonneg dist_nonneg, ← abs_of_nonneg (dist_nonneg.trans hp.le),
      ← sq_eq_sq_iff_abs_eq_abs, hvn', eq_comm, ← sub_eq_iff_eq_add',
      right_eq_mul₀ (Real.sqrt_pos.1 hvp).ne', sq_eq_one_iff]
    refine ⟨fun h ↦ ?_, eq_or_eq_neg_of_abs_eq⟩
    obtain rfl | rfl := h <;> norm_num
  refine ⟨(1 : ℝ) • v' +ᵥ p, (-1 : ℝ) • v' +ᵥ p, ?_, ?_⟩
  · simp only [one_smul, neg_smul, ne_eq, vadd_right_cancel_iff, ← add_eq_zero_iff_eq_neg,
      ← two_smul ℝ, smul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    rw [← norm_eq_zero]
    intro h
    simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hvn
    rw [← hvn] at hvp
    simp at hvp
  · ext p'
    refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
    · rw [Set.mem_inter_iff, Metric.mem_sphere, SetLike.mem_coe] at h
      obtain ⟨hc, ho⟩ := h
      obtain ⟨c, rfl⟩ := hv' _ ho
      rw [hvn''] at hc
      obtain rfl | rfl := eq_or_eq_neg_of_abs_eq hc <;> grind
    · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl <;> rw [Metric.mem_sphere, hvn''] <;> norm_num
    · rcases h with rfl | rfl <;>
        simp only [SetLike.mem_coe, mem_orthRadius_iff_inner_left, vadd_vsub, v',
          real_inner_smul_left] <;>
        rw [Submodule.inner_right_of_mem_orthogonal hvd (by simp)] <;> simp

end Sphere

end EuclideanGeometry
