/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Jireh Loreaux, Floris van Doorn, Eric Wieser
-/
import Mathlib.Analysis.Calculus.FirstDerivativeTest
import Mathlib.Order.Interval.Set.Basic
import Mathlib.LinearAlgebra.AffineSpace.Slope

/-!
# The Second-Derivative Test

We prove the Second-Derivative test from calculus using the First-Derivative test.
Source: [Wikipedia](https://en.wikipedia.org/wiki/Derivative_test#Proof_of_the_second-derivative_test).

## Main results

* `isLocalMin_of_deriv_deriv_pos`: The second-derivative test, minimum version.

## Tags

derivative test, calculus
-/

open Set Filter Topology SignType

section SecondDeriv

variable {f : ℝ → ℝ} {x₀ : ℝ}


lemma slope_pos_iff {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 → 𝕜} {x₀ b : 𝕜} (hb : x₀ < b) :
    0 < slope f x₀ b ↔ f x₀ < f b := by
  simp [slope, hb]

lemma slope_pos_iff_gt {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 → 𝕜} {x₀ b : 𝕜} (hb : b < x₀) :
    0 < slope f x₀ b ↔ f b < f x₀ := by
  rw [slope_comm, slope_pos_iff hb]

lemma pos_of_slope_pos {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 → 𝕜} {x₀ b : 𝕜}
    (hb : x₀ < b) (hbf : 0 < slope f x₀ b) (hf : f x₀ = 0) : 0 < f b := by
  simp_all [slope, hf]

lemma neg_of_slope_pos {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 → 𝕜} {x₀ b : 𝕜}
    (hb : b < x₀) (hbf : 0 < slope f x₀ b) (hf : f x₀ = 0) : f b < 0 := by
  rwa [slope_pos_iff_gt, hf] at hbf
  exact hb

/-- Predict the sign of f when it crosses the x-axis from below. -/
lemma eventually_nhdsWithin_sign_eq_of_deriv_pos (hf : deriv f x₀ > 0) (hx : f x₀ = 0) :
    ∀ᶠ x in 𝓝 x₀, sign (f x) = sign (x - x₀) := by
  rw [← nhdsNE_sup_pure x₀, eventually_sup]
  refine ⟨?_, by simpa⟩
  have h_tendsto := hasDerivAt_iff_tendsto_slope.mp
    (differentiableAt_of_deriv_ne_zero <| ne_of_gt hf).hasDerivAt
  filter_upwards [(h_tendsto.eventually <| eventually_gt_nhds hf),
    self_mem_nhdsWithin] with x hx₀ hx₁
  rw [mem_compl_iff, mem_singleton_iff, ← Ne.eq_def] at hx₁
  obtain (hx' | hx') := hx₁.lt_or_lt
  · rw [sign_neg (neg_of_slope_pos hx' hx₀ hx), sign_neg (sub_neg.mpr hx')]
  · rw [sign_pos (pos_of_slope_pos hx' hx₀ hx), sign_pos (sub_pos.mpr hx')]

/-- Predict the sign of f when it crosses the x-axis from above. -/
lemma eventually_nhdsWithin_sign_eq_of_deriv_neg (hf : deriv f x₀ < 0) (hx : f x₀ = 0) :
    ∀ᶠ x in 𝓝 x₀, sign (f x) = sign (x₀ - x) := by
  have h₀ : deriv (-f) x₀ = - deriv f x₀ := by
    have := @deriv_comp ℝ _ x₀ ℝ _ _ f Neg.neg
        differentiable_neg.differentiableAt
        (differentiableAt_of_deriv_ne_zero (ne_of_gt hf).symm)
    simp only [deriv_neg'', neg_mul, one_mul] at this
    rw [← this]
    congr
  have h₂ (x : ℝ) : - sign (-f x) = sign (f x) := neg_eq_iff_eq_neg.mpr <| Right.sign_neg (f x)
  simp_rw [← h₂, fun x => (neg_sub x x₀).symm, fun x => Right.sign_neg (x - x₀)]
  simp only [neg_inj]
  exact eventually_nhdsWithin_sign_eq_of_deriv_pos (by
    show deriv (-f) x₀ > 0
    rw [h₀]
    simp only [Left.neg_pos_iff]
    exact hf) (by show (-f) x₀ = 0; simp_all)

lemma deriv_neg_left_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝 x₀, sign (deriv f x) = sign (x - x₀)) :
    ∀ᶠ (b : ℝ) in 𝓝[<] x₀, deriv f b < 0 :=
  (eventually_nhdsWithin_of_eventually_nhds h₀).mp <|
   eventually_nhdsWithin_of_forall <| fun x hx₀ hx₁ => by
    rw [sign_neg <| sub_neg.mpr hx₀] at hx₁
    simp only [sign, OrderHom.coe_mk] at hx₁
    split at hx₁
    · simp only [self_eq_neg_iff, one_ne_zero] at hx₁
    · split at hx₁ <;> tauto

lemma deriv_neg_right_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝 x₀, sign (deriv f x) = sign (x₀ - x)) :
    ∀ᶠ (b : ℝ) in 𝓝[>] x₀, deriv f b < 0 :=
  (eventually_nhdsWithin_of_eventually_nhds h₀).mp <|
    eventually_nhdsWithin_of_forall <| fun x hx₀ hx₁ => by
      rw [sign_neg <| sub_neg.mpr hx₀] at hx₁
      simp only [sign, OrderHom.coe_mk] at hx₁
      split at hx₁
      · simp only [self_eq_neg_iff, one_ne_zero] at hx₁
      · split at hx₁ <;> tauto

lemma deriv_pos_right_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝 x₀, sign (deriv f x) = sign (x - x₀)) :
    ∀ᶠ (b : ℝ) in 𝓝[>] x₀, deriv f b > 0 :=
  (eventually_nhdsWithin_of_eventually_nhds h₀).mp <|
    eventually_nhdsWithin_of_forall <| fun x hx₀ hx₁ => by
      rw [sign_pos <| sub_pos.mpr hx₀] at hx₁
      simp only [sign, OrderHom.coe_mk, ite_eq_left_iff, not_lt] at hx₁
      split_ifs at hx₁ with g₀ <;> (simp only [imp_false, not_le] at hx₁; exact hx₁)

lemma deriv_pos_left_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝 x₀, sign (deriv f x) = sign (x₀ - x)) :
    ∀ᶠ (b : ℝ) in 𝓝[<] x₀, deriv f b > 0 :=
  (eventually_nhdsWithin_of_eventually_nhds h₀).mp <|
    eventually_nhdsWithin_of_forall <| fun x hx₀ hx₁ => by
      rw [sign_pos <| sub_pos.mpr hx₀] at hx₁
      simp only [sign, OrderHom.coe_mk, ite_eq_left_iff, not_lt] at hx₁
      split_ifs at hx₁ with g₀ <;> (simp only [imp_false, not_le] at hx₁; exact hx₁)

/-- The Second-Derivative Test from calculus, minimum version.
Applies to functions like `x^2 + 1[x ≥ 0]` as well as twice differentiable
functions. -/
theorem isLocalMin_of_deriv_deriv_pos (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMin f x₀ := by
  have h₀ := eventually_nhdsWithin_sign_eq_of_deriv_pos hf hd
  have hl := deriv_neg_left_of_sign_deriv h₀
  have hg := deriv_pos_right_of_sign_deriv h₀
  have hf₀ := eventually_sup.mpr ⟨hl.mono fun x hx => (ne_of_gt hx).symm,
                                  hg.mono fun x hx => (ne_of_lt hx).symm⟩
  have hf := (nhdsLT_sup_nhdsGT x₀) ▸ hf₀
  exact isLocalMin_of_deriv hc (hf.mono fun x a ↦ differentiableAt_of_deriv_ne_zero a)
    (hl.mono fun _ => le_of_lt) (hg.mono fun _ => le_of_lt)

/-- The Second-Derivative Test from calculus, maximum version. -/
theorem isLocalMax_of_deriv_deriv_neg (hf : deriv (deriv f) x₀ < 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMax f x₀ := by
  have h := eventually_nhdsWithin_sign_eq_of_deriv_neg hf hd
  have h₀ := deriv_pos_left_of_sign_deriv h
  have h₁ := deriv_neg_right_of_sign_deriv h
  have hf₀ := eventually_sup.mpr ⟨h₀.mono fun x hx => (ne_of_lt hx).symm,
                                  h₁.mono fun x hx => (ne_of_gt hx).symm⟩
  have hf : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, deriv f x ≠ 0 := (nhdsLT_sup_nhdsGT x₀) ▸ hf₀
  exact isLocalMax_of_deriv hc (hf.mono fun _ => differentiableAt_of_deriv_ne_zero)
    (h₀.mono fun _ => le_of_lt) (h₁.mono fun _ => le_of_lt)

end SecondDeriv
