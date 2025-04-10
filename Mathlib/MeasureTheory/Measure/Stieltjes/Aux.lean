/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# EReal lemmas
-/

open Filter Topology

open scoped ENNReal

namespace EReal

@[simp]
lemma toENNReal_one : (1 : EReal).toENNReal = 1 := by
  rw [toENNReal_of_ne_top]
  · simp
  · simpa using natCast_ne_top 1

lemma toENNReal_toEReal (x : ℝ) : EReal.toENNReal x = ENNReal.ofReal x := rfl

lemma continuousAt_sub {p : EReal × EReal} (h : p.1 ≠ ⊤ ∨ p.2 ≠ ⊤) (h' : p.1 ≠ ⊥ ∨ p.2 ≠ ⊥) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 - p.2) p := by
  simp_rw [sub_eq_add_neg]
  change ContinuousAt ((fun p : EReal × EReal => p.1 + p.2) ∘ (fun p ↦ (p.1, -p.2))) p
  exact (EReal.continuousAt_add (by simp [h]) (by simp [h'])).comp (by fun_prop)

lemma continuousAt_const_sub {c x : EReal} (h' : x ≠ ⊤ ∨ c ≠ ⊤) :
    ContinuousAt (fun x : EReal ↦ c - x) x := by
  by_cases hc_top : c = ⊥
  · simpa [hc_top] using continuous_const.continuousAt
  change ContinuousAt ((fun p : EReal × EReal ↦ p.1 - p.2) ∘ (fun x ↦ (c, x))) x
  exact (EReal.continuousAt_sub h'.symm (Or.inl hc_top)).comp (by fun_prop)

lemma continuousAt_sub_const {c x : EReal} (h' : x ≠ ⊥ ∨ c ≠ ⊥) :
    ContinuousAt (fun x : EReal ↦ x - c) x := by
  by_cases hc_top : c = ⊤
  · simpa [hc_top] using continuous_const.continuousAt
  change ContinuousAt ((fun p : EReal × EReal ↦ p.1 - p.2) ∘ (fun x ↦ (x, c))) x
  exact (EReal.continuousAt_sub (Or.inr hc_top) h').comp (by fun_prop)

lemma continuous_coe_mul {c : ℝ} : Continuous (fun x : EReal ↦ c * x) := by
  by_cases hc0 : c = 0
  · simpa [hc0] using continuous_const
  rw [continuous_iff_continuousAt]
  intro x
  have h_cont : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (c, x) := by
    refine EReal.continuousAt_mul ?_ ?_ ?_ ?_ <;> exact Or.inl (by simp [hc0])
  refine h_cont.comp ?_
  fun_prop

lemma coe_mul_add_of_nonneg {x : ℝ} (hx_nonneg : 0 ≤ x) (y z : EReal) :
    x * (y + z) = x * y + x * z := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx_pos : 0 < x := hx_nonneg.lt_of_ne' hx0
  induction y
  · simp [EReal.coe_mul_bot_of_pos hx_pos]
  · induction z
    · simp [EReal.coe_mul_bot_of_pos hx_pos]
    · norm_cast
      rw [mul_add]
    · simp only [coe_add_top, EReal.coe_mul_top_of_pos hx_pos]
      rw [← EReal.coe_mul, EReal.coe_add_top]
  · simp only [EReal.coe_mul_top_of_pos hx_pos]
    induction z
    · simp [EReal.coe_mul_bot_of_pos hx_pos]
    · simp only [top_add_coe, EReal.coe_mul_top_of_pos hx_pos]
      rw [← EReal.coe_mul, EReal.top_add_coe]
    · simp [EReal.coe_mul_top_of_pos hx_pos]

lemma top_mul_add_of_nonneg {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ⊤ * (x + y) = ⊤ * x + ⊤ * y := by
  induction x, y using EReal.induction₂_symm with
  | symm h =>
    rw [add_comm, add_comm (⊤ * _)]
    exact h hy hx
  | top_top => simp
  | top_pos _ h =>
    rw [top_add_coe, top_mul_top, top_mul_of_pos, top_add_top]
    exact mod_cast h
  | top_zero => simp
  | top_neg _ h =>
    refine absurd hy ?_
    exact mod_cast h.not_le
  | top_bot => simp
  | pos_bot => simp
  | coe_coe x y =>
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hy0 : y = 0
    · simp [hy0]
    have hx_pos : 0 < (x : EReal) := by
      refine hx.lt_of_ne' ?_
      exact mod_cast hx0
    have hy_pos : 0 < (y : EReal) := by
      refine hy.lt_of_ne' ?_
      exact mod_cast hy0
    rw [top_mul_of_pos hx_pos, top_mul_of_pos hy_pos, top_mul_of_pos]
    · simp
    · exact add_pos hx_pos hy_pos
  | zero_bot => simp
  | neg_bot => simp
  | bot_bot => simp

lemma mul_add_coe_of_nonneg (x : EReal) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * (y + z) = x * y + x * z := by
  by_cases hx_top : x = ⊤
  · rw [hx_top]
    exact top_mul_add_of_nonneg (mod_cast hy) (mod_cast hz)
  by_cases hx_bot : x = ⊥
  · rw [hx_bot]
    by_cases hy0 : y = 0
    · simp [hy0]
    by_cases hz0 : z = 0
    · simp [hz0]
    have hy_pos : 0 < (y : EReal) := lt_of_le_of_ne' (mod_cast hy) (mod_cast hy0)
    have hz_pos : 0 < (z : EReal) := lt_of_le_of_ne' (mod_cast hz) (mod_cast hz0)
    rw [bot_mul_of_pos hy_pos, bot_mul_of_pos hz_pos, bot_mul_of_pos]
    · simp
    · exact add_pos hy_pos hz_pos
  lift x to ℝ using ⟨hx_top, hx_bot⟩
  norm_cast
  rw [mul_add]

lemma coe_add_mul_of_nonneg (x : EReal) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (y + z) * x = y * x + z * x := by
  simp_rw [mul_comm _ x]
  exact EReal.mul_add_coe_of_nonneg x hy hz

lemma sub_add_sub_cancel (b a : EReal) (c : ℝ) :
    b - c + (c - a) = b - a := by
  induction a <;> induction b
  · simp
  · simp only [coe_sub_bot]
    rw [← coe_sub, coe_add_top]
  · simp
  · simp
  · norm_cast
    ring
  · simp only [top_sub_coe]
    rw [← coe_sub, top_add_coe]
  · simp
  · simp
  · simp

lemma top_sub_of_ne_top {x : EReal} (hx : x ≠ ⊤) : ⊤ - x = ⊤ := by
  induction x <;> tauto

lemma toENNReal_sub_le_add (b a c : EReal) :
    (b - a).toENNReal ≤ (b - c).toENNReal + (c - a).toENNReal := by
  by_cases hc_top : c = ⊤
  · simp only [hc_top, sub_top, ne_eq, bot_ne_top, not_false_eq_true,
      toENNReal_of_ne_top, toReal_bot, ENNReal.ofReal_zero, zero_add]
    by_cases ha : a = ⊤
    · simp [ha]
    · simp [top_sub_of_ne_top ha]
  by_cases hc_bot : c = ⊥
  · simp [hc_bot, sub_eq_add_neg]
    by_cases hb_bot : b = ⊥
    · simp [hb_bot]
    · simp [add_top_of_ne_bot hb_bot]
  refine (toENNReal_le_toENNReal ?_).trans toENNReal_add_le
  lift c to ℝ using ⟨hc_top, hc_bot⟩ with c
  rw [sub_add_sub_cancel]

lemma toENNReal_sub_add_cancel {b a c : EReal} (hac : a ≤ c) (hcb : c ≤ b) :
    (b - c).toENNReal + (c - a).toENNReal = (b - a).toENNReal := by
  induction c
  · have ha : a = ⊥ := eq_bot_iff.mpr hac
    simp [ha]
  · rw [← toENNReal_add, sub_add_sub_cancel]
    · rwa [sub_nonneg] <;> simp
    · by_cases ha : a = ⊥
      · simp [ha]
      rwa [sub_nonneg] <;> simp
  · have hb : b = ⊤ := eq_top_iff.mpr hcb
    simp [hb]

end EReal

@[simp]
lemma ENNReal.nhdsLT_ne_bot_iff {x : ℝ≥0∞} :
    (𝓝[<] x).NeBot ↔ x ≠ 0 := by
  by_cases hx_zero : x = 0
  · simp [hx_zero]
  · simp only [ne_eq, hx_zero, not_false_eq_true, iff_true]
    refine nhdsWithin_Iio_self_neBot' ?_
    simp [hx_zero]

@[simp]
lemma ENNReal.nhdsGT_ne_bot_iff {x : ℝ≥0∞} :
    (𝓝[>] x).NeBot ↔ x ≠ ∞ := by
  by_cases hx : x = ∞
  · simp [hx]
  · simp only [ne_eq, hx, not_false_eq_true, iff_true]
    exact nhdsGT_neBot_of_exists_gt ⟨∞, Ne.lt_top hx⟩
