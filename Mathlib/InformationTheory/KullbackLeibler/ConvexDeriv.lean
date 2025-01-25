/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Convex.Deriv


open Set Filter Topology

open scoped ENNReal NNReal

variable {f : ℝ → ℝ} {s : Set ℝ} {x y : ℝ}

namespace ConvexOn

lemma comp_neg {𝕜 F β : Type*} [LinearOrderedField 𝕜] [AddCommGroup F]
    [OrderedAddCommMonoid β] [Module 𝕜 F] [SMul 𝕜 β] {f : F → β} {s : Set F}
    (hf : ConvexOn 𝕜 s f) :
    ConvexOn 𝕜 (-s) (fun x ↦ f (-x)) := by
  refine ⟨hf.1.neg, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simp_rw [neg_add_rev, ← smul_neg, add_comm]
  exact hf.2 hx hy ha hb hab

lemma comp_neg_iff {𝕜 F β : Type*} [LinearOrderedField 𝕜] [AddCommGroup F]
    [OrderedAddCommMonoid β] [Module 𝕜 F] [SMul 𝕜 β] {f : F → β} {s : Set F}  :
    ConvexOn 𝕜 (-s) (fun x ↦ f (-x)) ↔ ConvexOn 𝕜 s f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ConvexOn.comp_neg h⟩
  rw [← neg_neg s, ← Function.comp_id f, ← neg_comp_neg, ← Function.comp_assoc]
  exact h.comp_neg

lemma affine_rightDeriv_le_of_mem_interior (hf : ConvexOn ℝ s f)
    (hx : x ∈ interior s) (hy : y ∈ s) :
    derivWithin f (Ioi x) x * y + (f x - derivWithin f (Ioi x) x * x) ≤ f y := by
  rw [add_comm]
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · have : derivWithin f (Ioi x) x ≤ slope f x y := rightDeriv_le_slope_of_mem_interior hf hx hy hxy
    rw [slope_def_field] at this
    rwa [le_div_iff₀ (by simp [hxy]), le_sub_iff_add_le, add_comm, mul_sub, add_sub,
      add_sub_right_comm] at this
  · simp [h_eq]
  · have : slope f y x ≤ derivWithin f (Ioi x) x :=
      (slope_le_leftDeriv_of_mem_interior hf hy hx hyx).trans
        (leftDeriv_le_rightDeriv_of_mem_interior hf hx)
    rw [slope_comm, slope_def_field] at this
    rw [← neg_div_neg_eq, neg_sub, neg_sub] at this
    rwa [div_le_iff₀ (by simp [hyx]), sub_le_iff_le_add, mul_sub, ← sub_le_iff_le_add',
      sub_sub_eq_add_sub, add_sub_right_comm] at this

lemma affine_leftDeriv_le_of_mem_interior (hf : ConvexOn ℝ s f) (hx : x ∈ interior s) (hy : y ∈ s) :
    derivWithin f (Iio x) x * y + (f x - derivWithin f (Iio x) x * x) ≤ f y := by
  rw [add_comm]
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · have : derivWithin f (Iio x) x ≤ slope f x y :=
      (leftDeriv_le_rightDeriv_of_mem_interior hf hx).trans
        (rightDeriv_le_slope_of_mem_interior hf hx hy hxy)
    rwa [slope_def_field, le_div_iff₀ (by simp [hxy]), le_sub_iff_add_le, add_comm, mul_sub,
      add_sub, add_sub_right_comm] at this
  · simp [h_eq]
  · have : slope f y x ≤ derivWithin f (Iio x) x := slope_le_leftDeriv_of_mem_interior hf hy hx hyx
    rwa [slope_comm, slope_def_field, ← neg_div_neg_eq, neg_sub, neg_sub,
      div_le_iff₀ (by simp [hyx]), sub_le_iff_le_add, mul_sub, ← sub_le_iff_le_add',
      sub_sub_eq_add_sub, add_sub_right_comm] at this

lemma nonneg_of_todo (hf : ConvexOn ℝ (Ioi 0) f)
    (hf_one : f 1 = 0) (hf_deriv : derivWithin f (Ioi 1) 1 = 0) (hx : 0 < x) :
    0 ≤ f x := by
  rw [← hf_one]
  refine ge_of_leftDeriv_nonpos_of_rightDeriv_nonneg hf (by simp) ?_ hf_deriv.ge hx
  exact (leftDeriv_le_rightDeriv_of_mem_interior hf (by simp)).trans hf_deriv.le

lemma nonneg_of_todo' (hf : ConvexOn ℝ (Ioi 0) f)
    (hf_one : f 1 = 0) (hf_ld : derivWithin f (Iio 1) 1 ≤ 0) (hf_rd : 0 ≤ derivWithin f (Ioi 1) 1)
    (hx : 0 < x) :
    0 ≤ f x := by
  rw [← hf_one]
  exact ge_of_leftDeriv_nonpos_of_rightDeriv_nonneg hf (by simp) hf_ld hf_rd hx

end ConvexOn
