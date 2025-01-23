/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Analysis.Calculus.FirstDerivativeTest
import Mathlib.Order.Interval.Set.Basic

/-!
# The Second-Derivative Test

We prove the Second-Derivative test from calculus using the First-Derivative test.
Source: [Wikipedia](https://en.wikipedia.org/wiki/Derivative_test#Proof_of_the_second-derivative_test).

## Main results

* `isLocalMin_of_deriv_deriv_pos`: The second-derivative test, minimum version.

## Tags

derivative test, calculus
-/

open Set Filter Topology


/-- Insert a missing point between two adjacent open real intervals. -/
theorem insert_Ioo₀ {x ε₀ ε₁ : ℝ} (hε₀ : ε₀ > 0) (hε₁ : ε₁ > 0):
    insert x (Ioo (x - ε₀) x ∪ Ioo x (x + ε₁)) = Ioo (x - ε₀) (x + ε₁) :=
  insert_Ioo ⟨by linarith,by linarith⟩


section SecondDeriv

variable {f : ℝ → ℝ} {x₀ : ℝ}


lemma slope_pos_iff {𝕜} [LinearOrderedField 𝕜] {f : 𝕜 → 𝕜} {x₀ b : 𝕜} (hb : x₀ < b) :
    0 < slope f x₀ b ↔ f x₀ < f b := by
  simp [slope, hb]

lemma slope_pos_iff_gt {𝕜} [LinearOrderedField 𝕜] {f : 𝕜 → 𝕜} {x₀ b : 𝕜} (hb : b < x₀) :
    0 < slope f x₀ b ↔ f b < f x₀ := by
  rw [slope_comm, slope_pos_iff hb]


lemma neg_of_deriv_pos (hf : deriv f x₀ > 0)
    (hd : f x₀ = 0) : ∃ u < x₀, ∀ b ∈ Ioo u x₀, f b < 0 := by
  obtain ⟨u,hu⟩ := (mem_nhdsWithin_Iio_iff_exists_mem_Ico_Ioo_subset
    (show x₀ - 1 < x₀ by simp)).mp
      <| nhds_left'_le_nhds_ne x₀ <| (tendsto_nhds.mp <| hasDerivAt_iff_tendsto_slope.mp
      (differentiableAt_of_deriv_ne_zero <| ne_of_gt hf).hasDerivAt) (Ioi 0) isOpen_Ioi hf
  exact ⟨u, hu.1.2, fun _ hb => (hd ▸ (slope_pos_iff_gt (f := f) hb.2).mp) <| hu.2 hb⟩

lemma pos_of_deriv_pos (hf : deriv f x₀ > 0)
    (hd : f x₀ = 0) : ∃ u > x₀, ∀ b ∈ Ioo x₀ u, f b > 0 := by
  obtain ⟨u,hu⟩ := (mem_nhdsWithin_Ioi_iff_exists_mem_Ioc_Ioo_subset (show x₀ < x₀ + 1 by simp)).mp
    <| nhds_right'_le_nhds_ne x₀ <|(tendsto_nhds.mp <| hasDerivAt_iff_tendsto_slope.mp
    (differentiableAt_of_deriv_ne_zero <| ne_of_gt hf).hasDerivAt) (Ioi 0) isOpen_Ioi hf
  exact ⟨u, hu.1.1, fun _ hb => (hd ▸ (slope_pos_iff (f := f) hb.1).mp) <| hu.2 hb⟩

lemma neg_pos_of_deriv_pos
    (hf : deriv (f) x₀ > 0) (hd : f x₀ = 0) :
    ∃ ε > 0, (∀ b ∈ Ioo (x₀-ε) x₀, f b < 0) ∧
              ∀ b ∈ Ioo x₀ (x₀ + ε), 0 < f b := by
  obtain ⟨u₀,hu₀⟩ := pos_of_deriv_pos hf hd
  have h₀ : 2 * (x₀ + 2⁻¹ * (u₀ - x₀)) < 2 * u₀ := by
    ring_nf
    rw [mul_two, add_lt_add_iff_right]
    exact hu₀.1
  obtain ⟨u₁,hu₁⟩ := neg_of_deriv_pos hf hd
  have h₁ : x₀ - (x₀ - u₁) < x₀ - 2⁻¹ * (x₀ - u₁) := sub_lt_sub_left
    ((inv_mul_lt_iff₀ zero_lt_two).mpr <|lt_two_mul_self <|sub_pos.mpr hu₁.1) x₀
  use 2⁻¹ * min (u₀ - x₀) (x₀ - u₁)
  constructor
  · aesop
  · constructor
    · exact fun b hb => hu₁.2 _ <| by
        simp_all only [mem_Ioo, sub_sub_cancel, and_true]
        calc u₁ < _ := h₁
             _  ≤ _ := tsub_le_tsub_left ((inv_mul_le_iff₀ zero_lt_two).mpr (by simp)) x₀
             _  < _ := hb.1
    · exact fun b hb => hu₀.2 _ ⟨hb.1,
        calc _ < _                    := hb.2
             _ ≤ x₀ + 2⁻¹ * (u₀ - x₀) := by simp
             _ < _                    := by rw[← mul_lt_mul_left zero_lt_two]; exact h₀⟩


/-- The Second-Derivative Test from calculus, minimum version.
This version applies to functions like `x^2 + 1[x ≥ 0]` as well as twice differentiable
functions.
 -/
theorem isLocalMin_of_deriv_deriv_pos
    (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMin f x₀ := by
  obtain ⟨ε,hε⟩    := neg_pos_of_deriv_pos hf hd
  have hε₀ := fun b hb => ne_of_lt <| hε.2.1 b hb
  have hε₁ := fun b hb => ne_of_gt <| hε.2.2 b hb
  obtain ⟨p,hp⟩ : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, DifferentiableAt ℝ f x :=
    (eventually_mem_set.mpr <| insert_mem_nhds_iff.mp <| insert_Ioo₀ hε.1 hε.1 ▸
      Ioo_mem_nhds (by linarith) (by linarith)).mono
      fun _ hb => differentiableAt_of_deriv_ne_zero <| hb.elim (hε₀ _) (hε₁ _)
  obtain ⟨l,u,hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hp.1
  let δ := min (x₀ - l) (u - x₀)
  have hζ : (1/2) * min δ ε > 0 := by aesop
  have hζ₀ : x₀ - (1/2) * min δ ε < x₀ := by linarith
  have hζ₁ : x₀ < x₀ + (1/2) * min δ ε := by linarith
  have : x₀ ≤ x₀ + (1/2) * (ε - min δ ε) := by aesop
  have h₀ :  l < x₀ - 1 / 2 * min δ ε := by linarith[min_le_left δ ε, min_le_left (x₀ - l) (u - x₀)]
  have h₁ : x₀ + 1 / 2 * min δ ε < u := by linarith[min_le_left δ ε, min_le_right (x₀ - l) (u - x₀)]
  obtain ⟨b,hb⟩ := hp.2
  exact isLocalMin_of_deriv_Ioo hζ₀ hζ₁ hc
    (fun _ hx => (hb.2.symm.subset ⟨hlu.2 ⟨h₀.trans hx.1, hx.2.trans hlu.1.2⟩,
      hb.1 <| ne_of_lt hx.2⟩).differentiableWithinAt)
    (fun _ hx => (hb.2.symm.subset ⟨hlu.2 ⟨hlu.1.1.trans hx.1, hx.2.trans h₁⟩,
      hb.1 <| ne_of_gt hx.1⟩).differentiableWithinAt)
    (fun _ hx => le_of_lt <| hε.2.1 _ ⟨by simp only [mem_Ioo] at hx;linarith, hx.2⟩)
    (fun _ hx => le_of_lt <| hε.2.2 _ ⟨hx.1, by simp only [mem_Ioo] at hx;linarith⟩)

lemma pos_of_slope_pos {b : ℝ} (hb : x₀ < b) (hbf : 0 < slope f x₀ b)
    (hf : f x₀ = 0) : 0 < f b := by
  simp_all [slope, hf]

lemma neg_of_slope_pos {b : ℝ} (hb : b < x₀) (hbf : 0 < slope f x₀ b)
    (hf : f x₀ = 0) : f b < 0 := by
  simp_all [slope, hf]
  exact neg_of_mul_pos_right hbf <| le_of_lt <| inv_lt_zero.mpr <| by linarith

lemma neg_of_slope_neg {b : ℝ} (hb : b < x₀) (hbf : 0 < slope f x₀ b)
    (hf : f x₀ = 0) : f b < 0 := by
  simp_all [slope]
  exact neg_of_mul_pos_right hbf <| le_of_lt <| inv_lt_zero.mpr <| by linarith

open SignType in
lemma eventually_nhdsWithin_sign_eq_of_deriv_pos (hf : deriv f x₀ > 0) (hx : f x₀ = 0) :
    ∀ᶠ x in 𝓝 x₀, sign (f x) = sign (x - x₀) := by
  rw [← nhdsWithin_compl_singleton_sup_pure x₀, eventually_sup]
  refine ⟨?_, by simpa⟩
  have h_tendsto := hasDerivAt_iff_tendsto_slope.mp
    (differentiableAt_of_deriv_ne_zero <| ne_of_gt hf).hasDerivAt
  filter_upwards [(h_tendsto.eventually <| eventually_gt_nhds hf),
    self_mem_nhdsWithin] with x hx₀ hx₁
  rw [mem_compl_iff, mem_singleton_iff, ← Ne.eq_def] at hx₁
  obtain (hx' | hx') := hx₁.lt_or_lt
  · rw [sign_neg (neg_of_slope_pos hx' hx₀ hx), sign_neg (sub_neg.mpr hx')]
  · rw [sign_pos (pos_of_slope_pos hx' hx₀ hx), sign_pos (sub_pos.mpr hx')]

end SecondDeriv
