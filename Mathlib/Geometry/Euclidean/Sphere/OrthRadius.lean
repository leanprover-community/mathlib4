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

@[simp] lemma self_mem_orthRadius (s : Sphere P) (p : P) : p ∈ s.orthRadius p :=
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
  simp_rw [orthRadius, parallel_iff_direction_eq_and_eq_bot_iff_eq_bot, direction_mk',
    Submodule.orthogonalComplement_eq_orthogonalComplement,
    Submodule.span_singleton_eq_span_singleton, ← coe_eq_bot_iff,
    ← Set.not_nonempty_iff_eq_empty, mk'_nonempty, and_true, ← Units.exists_iff_ne_zero, eq_comm,
    Units.smul_def]

lemma dist_sq_eq_iff_mem_orthRadius {s : Sphere P} {p q : P} :
    (dist q s.center) ^ 2 = (dist p s.center) ^ 2 + (dist q p) ^ 2 ↔ q ∈ s.orthRadius p := by
  simp_rw [dist_eq_norm_vsub, pow_two]
  rw [← vsub_add_vsub_cancel q p s.center]
  nth_rw 3 [add_comm]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, ← mem_orthRadius_iff_inner_left]

alias ⟨_, dist_sq_eq_of_mem_orthRadius⟩ := dist_sq_eq_iff_mem_orthRadius

lemma mem_inter_orthRadius_iff_radius_nonneg_and_vsub_mem_and_norm_sq {s : Sphere P} {p q : P} :
    q ∈ (s ∩ s.orthRadius p : Set P) ↔ 0 ≤ s.radius ∧
      q -ᵥ p ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ ∧ ‖q -ᵥ p‖ ^ 2 = s.radius ^ 2 - (dist p s.center) ^ 2 := by
  simp only [Set.mem_inter_iff, Metric.mem_sphere, mem_coe', SetLike.mem_coe,
    ← dist_sq_eq_iff_mem_orthRadius, ← direction_orthRadius,
    vsub_right_mem_direction_iff_mem (s.self_mem_orthRadius p), ← dist_eq_norm_vsub]
  nth_rw 3 [and_comm]
  rw [← and_assoc, and_congr_left_iff]
  intro h
  rw [← sub_eq_iff_eq_add'] at h
  rw [← h]
  rcases le_or_gt 0 s.radius with h0 | h0
  · simp [h0]
  · simp only [h0.not_ge, sub_left_inj, false_and, iff_false]
    intro hm
    exact h0.not_ge (radius_nonneg_of_mem hm)

lemma mem_inter_orthRadius_iff_vsub_mem_and_norm_sq {s : Sphere P} {p q : P} (h : 0 ≤ s.radius) :
    q ∈ (s ∩ s.orthRadius p : Set P) ↔
      q -ᵥ p ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ ∧ ‖q -ᵥ p‖ ^ 2 = s.radius ^ 2 - (dist p s.center) ^ 2 := by
  rw [mem_inter_orthRadius_iff_radius_nonneg_and_vsub_mem_and_norm_sq]
  simp [h]

lemma vadd_mem_inter_orthRadius_iff_norm_sq {s : Sphere P} {p : P} {v : V} (h : 0 ≤ s.radius)
    (hv : v ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ) :
    v +ᵥ p ∈ (s ∩ s.orthRadius p : Set P) ↔ ‖v‖ ^ 2 = s.radius ^ 2 - (dist p s.center) ^ 2 := by
  rw [mem_inter_orthRadius_iff_vsub_mem_and_norm_sq h]
  simp [hv]

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

lemma inter_orthRadius_eq_singleton_of_dist_eq_radius {s : Sphere P} {p : P}
    (hp : dist p s.center = s.radius) : (s ∩ s.orthRadius p : Set P) = {p} := by
  ext p'
  simp only [Set.mem_inter_iff, Metric.mem_sphere, mem_coe', SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp's, hp'i⟩
    have h' := dist_sq_eq_of_mem_orthRadius hp'i
    rw [hp's, hp] at h'
    simpa using h'
  · rintro rfl
    simpa using hp

lemma inter_orthRadius_eq_singleton_iff {s : Sphere P} {p q : P} :
    (s ∩ s.orthRadius p : Set P) = {q} ↔ q = p ∧ dist p s.center = s.radius := by
  constructor
  · intro h
    have hq : q ∈ (s ∩ s.orthRadius p : Set P) := h ▸ Set.mem_singleton _
    have h' (q' : P) : q' ∈ (s ∩ s.orthRadius p : Set P) ↔ q' = q := by simp [h]
    have hr : 0 ≤ s.radius := radius_nonneg_of_mem hq.1
    simp_rw [mem_inter_orthRadius_iff_vsub_mem_and_norm_sq hr] at h'
    have hq' := (h' q).2 rfl
    have hq'' : (-(q -ᵥ p) +ᵥ p) -ᵥ p ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ ∧
        ‖(-(q -ᵥ p) +ᵥ p) -ᵥ p‖ ^ 2 = s.radius ^ 2 - dist p s.center ^ 2 := by
      simpa [-neg_vsub_eq_vsub_rev] using hq'
    have hqq := (h' _).1 hq''
    rw [eq_comm, eq_vadd_iff_vsub_eq, eq_neg_iff_add_eq_zero, ← two_smul ℝ,
      smul_eq_zero_iff_right (by norm_num), vsub_eq_zero_iff_eq] at hqq
    refine ⟨hqq, ?_⟩
    subst hqq
    exact hq.1
  · rintro ⟨rfl, h⟩
    exact inter_orthRadius_eq_singleton_of_dist_eq_radius h

lemma inter_orthRadius_eq_empty_of_radius_lt_dist {s : Sphere P} {p : P}
    (hp : s.radius < dist p s.center) : (s ∩ s.orthRadius p : Set P) = ∅ := by
  ext p'
  rw [mem_inter_orthRadius_iff_radius_nonneg_and_vsub_mem_and_norm_sq]
  simp only [Set.mem_empty_iff_false, iff_false, not_and]
  rintro hle - h
  nlinarith

lemma inter_orthRadius_eq_empty_of_finrank_eq_one {s : Sphere P} {p : P} (hpc : p ≠ s.center)
    (hp : dist p s.center ≠ s.radius) (hf : Module.finrank ℝ V = 1) :
    (s ∩ s.orthRadius p : Set P) = ∅ := by
  ext p'
  rw [mem_inter_orthRadius_iff_radius_nonneg_and_vsub_mem_and_norm_sq]
  simp only [Set.mem_empty_iff_false, iff_false, not_and]
  intro hr hpo
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hf
  have ha := (ℝ ∙ (p -ᵥ s.center)).finrank_add_finrank_orthogonal
  simp only [finrank_span_singleton (vsub_ne_zero.2 hpc), hf, Nat.add_eq_left,
    Submodule.finrank_eq_zero, Submodule.orthogonal_eq_bot_iff] at ha
  simp only [ha, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot, vsub_eq_zero_iff_eq] at hpo
  simp only [hpo, vsub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [eq_comm, sub_eq_zero, eq_comm, sq_eq_sq₀ dist_nonneg hr]
  exact hp

lemma inter_orthRadius_eq_empty_iff {s : Sphere P} {p : P} :
    (s ∩ s.orthRadius p : Set P) = ∅ ↔ s.radius < dist p s.center ∨
      (Module.finrank ℝ V = 1 ∧ dist p s.center < s.radius ∧ p ≠ s.center) ∨
      (Subsingleton V ∧ s.radius ≠ 0) := by
  rcases lt_trichotomy (dist p s.center) s.radius with h | h | h
  · simp only [h.not_gt, h, ne_eq, true_and, (dist_nonneg.trans_lt h).ne', not_false_eq_true,
      and_true, false_or]
    obtain rfl | hp := eq_or_ne p s.center
    · rcases subsingleton_or_nontrivial V with hs | hs
      · have hs' := (AddTorsor.subsingleton_iff V P).1 hs
        simp [hs, Metric.sphere_eq_empty_of_subsingleton (dist_nonneg.trans_lt h).ne']
      · simp only [orthRadius_center, top_coe, Set.inter_univ, not_true_eq_false, and_false,
          not_subsingleton_iff_nontrivial.2 hs, or_self, iff_false, ← Set.nonempty_iff_ne_empty]
        obtain ⟨v, hv⟩ := exists_norm_eq V (dist_nonneg.trans_lt h).le
        exact ⟨v +ᵥ s.center, by simp [hv]⟩
    · simp only [hp, not_false_eq_true, and_true]
      rcases eq_or_ne (ℝ ∙ (p -ᵥ s.center)) ⊤ with hb | hb
      · have hb' := hb
        rw [Submodule.span_singleton_eq_top_iff] at hb'
        have hf := finrank_eq_one_iff'.2 ⟨p -ᵥ s.center, vsub_ne_zero.2 hp, hb'⟩
        simpa [hf] using inter_orthRadius_eq_empty_of_finrank_eq_one hp h.ne
      · have hn : ¬Subsingleton V := by
          rw [AddTorsor.subsingleton_iff V P]
          intro hs
          simp [Subsingleton.elim p s.center] at hp
        have hnf : Module.finrank ℝ V ≠ 1 := by
          intro hf
          apply hb
          rw [Submodule.span_singleton_eq_top_iff]
          rw [finrank_eq_one_iff'] at hf
          obtain ⟨v, hv0, hv⟩ := hf
          obtain ⟨c, hc⟩ := hv (p -ᵥ s.center)
          have hc0 : c ≠ 0 := by
            rintro rfl
            rw [zero_smul, eq_comm, vsub_eq_zero_iff_eq] at hc
            simp [hc] at hp
          intro v'
          obtain ⟨c', rfl⟩ := hv v'
          refine ⟨c' / c, ?_⟩
          simp [← hc, smul_smul, hc0]
        simp only [hnf, hn, or_self, iff_false, ← Set.nonempty_iff_ne_empty]
        rw [ne_eq, ← Submodule.orthogonal_eq_bot_iff] at hb
        obtain ⟨v, hvm, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
        refine ⟨(√(s.radius ^ 2 - (dist p s.center) ^ 2) / ‖v‖) • v +ᵥ p, ?_⟩
        rw [vadd_mem_inter_orthRadius_iff_norm_sq (dist_nonneg.trans_lt h).le
          (Submodule.smul_mem _ _ hvm)]
        rw [norm_smul, norm_div, norm_norm, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hv0)]
        simp only [Real.norm_eq_abs, sq_abs]
        refine Real.sq_sqrt ?_
        rw [sub_nonneg, sq_le_sq, abs_of_nonneg dist_nonneg]
        exact h.le.trans (le_abs_self _)
  · rw [inter_orthRadius_eq_singleton_of_dist_eq_radius h]
    simp only [Set.singleton_ne_empty, h, lt_self_iff_false, ne_eq, false_and, and_false, false_or,
      false_iff, not_and, not_not]
    intro hs
    rw [AddTorsor.subsingleton_iff V P] at hs
    rw [Subsingleton.elim p s.center] at h
    simpa using h.symm
  · simp [h, inter_orthRadius_eq_empty_of_radius_lt_dist]

/-- In 2D, the line defined by `s.orthRadius p` intersects `s` at at most two points so long as `p`
lies within `s` and not at its center.

This version provides expressions for those points in terms of an arbitrary vector in
`s.orthRadius p` with norm `1`. -/
lemma inter_orthRadius_eq_of_dist_le_radius_of_norm_eq_one [hf2 : Fact (Module.finrank ℝ V = 2)]
    {s : Sphere P} {p : P} (hp : dist p s.center ≤ s.radius) (hpc : p ≠ s.center) {v : V}
    (hv : v ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ) (hv1 : ‖v‖ = 1) :
    (s ∩ s.orthRadius p : Set P) = {√(s.radius ^ 2 - (dist p s.center) ^ 2) • v +ᵥ p,
      -√(s.radius ^ 2 - (dist p s.center) ^ 2) • v +ᵥ p} := by
  have hr : 0 ≤ s.radius := dist_nonneg.trans hp
  have hv0 : v ≠ 0 := by rw [← norm_ne_zero_iff, hv1]; simp
  rw [neg_smul]
  have hf := finrank_orthRadius hpc
  rw [direction_orthRadius] at hf
  simp only [hf2.out, Nat.reduceEqDiff] at hf
  rw [finrank_eq_one_iff_of_nonzero' ⟨v, hv⟩ (by simpa using hv0)] at hf
  have hvc : ∀ w ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ, ∃ c : ℝ, c • v = w := by
    intro w hw
    simpa using hf ⟨w, hw⟩
  have hvp : 0 ≤ s.radius ^ 2 - (dist p s.center) ^ 2 := by
    rw [sub_nonneg, sq_le_sq, abs_of_nonneg dist_nonneg]
    exact le_abs.2 (.inl hp)
  ext p'
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← vsub_vadd p' p, Set.mem_insert_iff, Set.mem_singleton_iff, vadd_right_cancel_iff,
      vadd_right_cancel_iff]
    have h' : p' -ᵥ p ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ := by
      rw [← direction_orthRadius, vsub_right_mem_direction_iff_mem (s.self_mem_orthRadius p)]
      exact h.2
    rw [← vsub_vadd p' p, vadd_mem_inter_orthRadius_iff_norm_sq hr h'] at h
    obtain ⟨c, hc⟩ := hvc _ h'
    rw [← hc] at h ⊢
    rw [← neg_smul]
    simp_rw [(smul_left_injective ℝ hv0).eq_iff, ← sq_eq_sq_iff_eq_or_eq_neg, Real.sq_sqrt hvp]
    simpa [norm_smul, hv1] using h
  · rw [← neg_smul] at h
    rcases h with rfl | rfl <;>
      rw [vadd_mem_inter_orthRadius_iff_norm_sq hr (Submodule.smul_mem _ _ hv)] <;>
      simp [norm_smul, hv1, hvp]

/-- In 2D, the line defined by `s.orthRadius p` intersects `s` at at most two points so long as `p`
lies within `s` and not at its center.

This version provides expressions for those points in terms of an arbitrary vector in
`s.orthRadius p`. -/
lemma inter_orthRadius_eq_of_dist_le_radius [hf2 : Fact (Module.finrank ℝ V = 2)]
    {s : Sphere P} {p : P} (hp : dist p s.center ≤ s.radius) (hpc : p ≠ s.center) {v : V}
    (hv : v ∈ (ℝ ∙ (p -ᵥ s.center))ᗮ) (hv0 : v ≠ 0) :
    (s ∩ s.orthRadius p : Set P) = {(√(s.radius ^ 2 - (dist p s.center) ^ 2) / ‖v‖) • v +ᵥ p,
      -(√(s.radius ^ 2 - (dist p s.center) ^ 2) / ‖v‖) • v +ᵥ p} := by
  convert inter_orthRadius_eq_of_dist_le_radius_of_norm_eq_one hp hpc (v := ‖v‖⁻¹ • v)
    (Submodule.smul_mem _ _ hv) ?_ using 2
  · simp [div_eq_mul_inv, smul_smul]
  · simp [div_eq_mul_inv, smul_smul]
  · simp [norm_smul, norm_ne_zero_iff.2 hv0]

/-- In 2D, the line defined by `s.orthRadius p` intersects `s` at exactly two points so long as `p`
lies strictly within `s` and not at its center. -/
lemma ncard_inter_orthRadius_eq_two_of_dist_lt_radius [hf2 : Fact (Module.finrank ℝ V = 2)]
    {s : Sphere P} {p : P} (hp : dist p s.center < s.radius) (hpc : p ≠ s.center) :
    (s ∩ s.orthRadius p : Set P).ncard = 2 := by
  have hf := finrank_orthRadius hpc
  simp only [hf2.out, Nat.reduceEqDiff, finrank_eq_one_iff'] at hf
  obtain ⟨v, hv0, hv⟩ := hf
  replace hv0 : (v : V) ≠ 0 := by simpa using hv0
  rw [inter_orthRadius_eq_of_dist_le_radius hp.le hpc (by simpa using v.property) hv0,
    Submodule.norm_coe, neg_smul, Set.ncard_pair]
  rw [ne_eq, vadd_right_cancel_iff, ← add_eq_zero_iff_eq_neg, ← two_smul ℝ,
    smul_eq_zero_iff_right two_ne_zero, smul_eq_zero_iff_left hv0, div_eq_iff, zero_mul]
  · have hvp : 0 < √(s.radius ^ 2 - dist p s.center ^ 2) := by
      rw [Real.sqrt_pos, sub_pos, sq_lt_sq, abs_of_nonneg dist_nonneg]
      exact lt_abs.2 (.inl hp)
    exact hvp.ne'
  · simpa using hv0

lemma ncard_inter_orthRadius_le_two [hf2 : Fact (Module.finrank ℝ V = 2)]
    {s : Sphere P} {p : P} (hpc : p ≠ s.center) : (s ∩ s.orthRadius p : Set P).ncard ≤ 2 := by
  rcases lt_trichotomy (dist p s.center) s.radius with h | h | h
  · exact (ncard_inter_orthRadius_eq_two_of_dist_lt_radius h hpc).le
  · simp [inter_orthRadius_eq_singleton_of_dist_eq_radius h]
  · simp [inter_orthRadius_eq_empty_of_radius_lt_dist h]

end Sphere

end EuclideanGeometry
