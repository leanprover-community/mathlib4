/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Analysis.Calculus.FirstDerivativeTest
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
/-!
# The Second-Derivative Test

We prove the Second-Derivative test from calculus using the First-Derivative test.
Source: [Wikipedia](https://en.wikipedia.org/wiki/Derivative_test#Proof_of_the_second-derivative_test).

## Main results

* `isLocalMin_of_deriv_deriv_pos`: The second-derivative test.

## Tags

derivative test, calculus
-/

open Set Filter Topology

/-- Add to Mathlib/Algebra/Order/GroupWithZero/Unbundled.lean -/
lemma neg_of_div_pos_left (a b : ℝ) (h : 0 < a/b) (h₁ : b < 0) : a < 0 := by
  contrapose h
  rw [not_lt] at h ⊢
  exact div_nonpos_of_nonneg_of_nonpos h (le_of_lt h₁)

/-- If `f''(x) > 0` then `f' < 0` on an interval to the left of `x`. -/
lemma deriv_neg_of_deriv_deriv_pos {f : ℝ → ℝ}  {x₀ : ℝ} (hf : deriv (deriv f) x₀ > 0)
    (hd : deriv f x₀ = 0) : ∃ u < x₀, ∀ b ∈ Ioo u x₀, deriv f b < 0 := by
    obtain ⟨u,hu⟩ := (mem_nhdsWithin_Iio_iff_exists_mem_Ico_Ioo_subset
      (show x₀ - 1 < x₀ by simp)).mp
        <| nhds_left'_le_nhds_ne x₀
        <| (tendsto_nhds.mp
          <| hasDerivAt_iff_tendsto_slope.mp
          <| hasDerivAt_deriv_iff.mpr (differentiableAt_of_deriv_ne_zero <| ne_of_gt hf))
        (Set.Ioi 0) isOpen_Ioi hf
    unfold slope at hu
    rw [hd] at hu
    have G₁ : ∀ b ∈ Ioo u x₀, deriv f b < 0 := fun b hb => neg_of_div_pos_left _ _ (by
        have hub := hu.2 hb
        field_simp at hub
        exact hub
      ) (by aesop)
    exact ⟨u, hu.1.2, G₁⟩

/-- If `f''(x) > 0` then `f' > 0` on an interval to the right of `x`. -/
lemma deriv_pos_of_deriv_deriv_pos {f : ℝ → ℝ}  {x₀ : ℝ} (hf : deriv (deriv f) x₀ > 0)
    (hd : deriv f x₀ = 0) : ∃ u > x₀, ∀ b ∈ Ioo x₀ u, deriv f b > 0 := by
  obtain ⟨u,hu⟩ := (mem_nhdsWithin_Ioi_iff_exists_mem_Ioc_Ioo_subset (show x₀ < x₀ + 1 by simp)).mp
      <| nhds_right'_le_nhds_ne x₀
      <|(tendsto_nhds.mp <| hasDerivAt_iff_tendsto_slope.mp
        <| hasDerivAt_deriv_iff.mpr (differentiableAt_of_deriv_ne_zero <| ne_of_gt hf))
        (Set.Ioi 0) isOpen_Ioi hf
  unfold slope at hu
  rw [hd] at hu
  have G₀ : ∀ b ∈ Ioo x₀ u, deriv f b > 0 := fun b hb => by
    have := hu.2 hb
    simp only [vsub_eq_sub, sub_zero, smul_eq_mul, mem_preimage, mem_Ioi] at this
    exact pos_of_mul_pos_right this <|le_of_lt (by aesop)
  exact ⟨u, hu.1.1, G₀⟩

/-- If `f''(x) > 0` then `f'` changes sign at `x`.
This lemma applies to functions like `x^2 + 1[x ≥ 0]` as well as twice differentiable
functions.
-/
lemma deriv_neg_pos_of_deriv_deriv_pos {f : ℝ → ℝ}  {x₀ : ℝ}
    (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0) :
    ∃ ε > 0, (∀ b ∈ Ioo (x₀-ε) x₀, deriv f b < 0) ∧
              ∀ b ∈ Ioo x₀ (x₀ + ε), 0 < deriv f b := by
  obtain ⟨u₀,hu₀⟩ := deriv_pos_of_deriv_deriv_pos hf hd
  obtain ⟨u₁,hu₁⟩ := deriv_neg_of_deriv_deriv_pos hf hd
  have h₁ : x₀ - (x₀ - u₁) < x₀ - 2⁻¹ * (x₀ - u₁) := sub_lt_sub_left
    ((inv_mul_lt_iff₀ zero_lt_two).mpr <|lt_two_mul_self <|sub_pos.mpr hu₁.1) x₀
  have h₂ : 2 * (x₀ + 2⁻¹ * (u₀ - x₀)) < 2 * u₀ := by
    ring_nf
    rw [mul_two, add_lt_add_iff_right]
    exact hu₀.1
  use 2⁻¹ * min (u₀ - x₀) (x₀ - u₁)
  constructor
  · aesop
  · constructor
    · exact fun b hb => hu₁.2 _ <| by
        simp_all only [mem_Ioo, and_imp, sub_sub_cancel, Nat.ofNat_pos, mul_lt_mul_left, and_true]
        calc u₁ < _ := h₁
             _  ≤ _ := tsub_le_tsub_left ((inv_mul_le_iff₀ zero_lt_two).mpr (by simp)) x₀
             _  < _ := hb.1
    · exact fun b hb => hu₀.2 _ <| ⟨hb.1,
        calc _ < _                    := hb.2
             _ ≤ x₀ + 2⁻¹ * (u₀ - x₀) := by simp
             _ < _                    := by rw[← mul_lt_mul_left zero_lt_two]; exact h₂⟩

theorem differentiableOn_right {f : ℝ → ℝ} {x₀ : ℝ}
    {p : Set ℝ} (hp2 : ∃ b ∈ 𝓟 {x₀}ᶜ, {x | DifferentiableAt ℝ f x} = p ∩ b)
    {l u : ℝ} (hlu1 : x₀ ∈ Ioo l u) (hlu2: Ioo l u ⊆ p) :
    DifferentiableOn ℝ f (Ioo x₀ u) := fun x hx => DifferentiableAt.differentiableWithinAt <| by
  obtain ⟨b,hb⟩ := hp2
  have : x ∈ p ∩ b := ⟨hlu2 <|by
      simp_all only [mem_Ioo, mem_principal, and_true]
      exact lt_trans hlu1.1 hx.1, hb.1 <| ne_of_gt hx.1⟩
  rw [← hb.2] at this
  exact this

theorem differentiableOn_left {f : ℝ → ℝ} {x₀ : ℝ}
    {p : Set ℝ} (hp2 : ∃ b ∈ 𝓟 {x₀}ᶜ, {x | DifferentiableAt ℝ f x} = p ∩ b)
    {l u : ℝ} (hlu1 : x₀ ∈ Ioo l u) (hlu2: Ioo l u ⊆ p) :
    DifferentiableOn ℝ f (Ioo l x₀) := fun x hx => DifferentiableAt.differentiableWithinAt <| by
  obtain ⟨b,hb⟩ := hp2
  have : x ∈ p ∩ b := ⟨hlu2 <|by
      simp_all only [mem_Ioo, mem_principal, true_and]
      exact lt_trans hx.2 hlu1.2, hb.1 <| ne_of_lt hx.2⟩
  rw [← hb.2] at this
  exact this

/-- Insert a missing point between two adjacent open intervals. -/
theorem insert_Ioo {x ε₀ ε₁ : ℝ} (hε₀ : ε₀ > 0) (hε₁ : ε₁ > 0):
    insert x (Ioo (x - ε₀) x ∪ Ioo x (x + ε₁)) = Ioo (x - ε₀) (x + ε₁) := by
  rw [← insert_union, Ioo_insert_right (by linarith)]
  exact Ioc_union_Ioo_eq_Ioo (by linarith) (by linarith)

/-- Already in FirstDerivativeTest? -/
theorem eventually_differentiable_of_deriv_nonzero {f : ℝ → ℝ} {x₀ ε : ℝ}
    (hε : ε > 0 ∧ (∀ b ∈ Ioo (x₀ - ε) x₀, deriv f b < 0)
                ∧ ∀ b ∈ Ioo x₀ (x₀ + ε), 0 < deriv f b) :
    ∀ᶠ x in 𝓝[≠] x₀, DifferentiableAt ℝ f x :=
  Eventually.mono
    (eventually_mem_set.mpr <| insert_mem_nhds_iff.mp <| insert_Ioo hε.1 hε.1 ▸
    Ioo_mem_nhds (by linarith) (by linarith))
    fun _ hb => differentiableAt_of_deriv_ne_zero <| hb.elim
      (fun h => ne_of_lt <| hε.2.1 _ h)
      (fun h => ne_of_gt <| hε.2.2 _ h)

/-- The Second-Derivative Test from calculus. -/
theorem isLocalMin_of_deriv_deriv_pos {f : ℝ → ℝ}  {x₀ : ℝ}
    (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMin f x₀ := by
  obtain ⟨ε,hε⟩    := deriv_neg_pos_of_deriv_deriv_pos hf hd
  obtain ⟨p,hp⟩    := eventually_differentiable_of_deriv_nonzero hε
  obtain ⟨l,u,hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hp.1
  let δ := min (x₀ - l) (u - x₀)
  have hζ : (1/2) * min δ ε > 0 := by aesop
  have hζ₀ : x₀ - (1/2) * min δ ε < x₀ := by linarith
  have hζ₁ : x₀ < x₀ + (1/2) * min δ ε := by linarith
  have hεζ : x₀ - ε ≤ x₀ - (1/2) * min δ ε := by
    suffices x₀ ≤ x₀ + (1/2) * (ε - min δ ε) by linarith
    aesop
  have hu :  x₀ + (1/2) * min δ ε ≤ u := by
    linarith[min_le_left δ ε, min_le_right (x₀ - l) (u - x₀), hlu.1.2]
  have hl : l ≤ x₀ - (1/2) * min δ ε := by
    linarith[min_le_left δ ε, min_le_left (x₀ - l) (u - x₀), hlu.1.1]
  exact isLocalMin_of_deriv_Ioo hζ₀ hζ₁ hc
    ((differentiableOn_left hp.2 hlu.1 hlu.2).mono <| Ioo_subset_Ioo_left <| by linarith)
    ((differentiableOn_right hp.2 hlu.1 hlu.2).mono <| Ioo_subset_Ioo_right <| by linarith)
    (fun x hx => le_of_lt <| hε.2.1 _ ⟨by simp only [mem_Ioo] at hx;linarith, hx.2⟩)
    (fun x hx => le_of_lt <| hε.2.2 _ ⟨hx.1, by simp only [mem_Ioo] at hx;linarith⟩)
