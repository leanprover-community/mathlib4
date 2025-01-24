/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Jireh Loreaux, Floris van Doorn, Eric Wieser
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

section SecondDeriv

variable {f : ℝ → ℝ} {x₀ : ℝ}


lemma slope_pos_iff {𝕜} [LinearOrderedField 𝕜] {f : 𝕜 → 𝕜} {x₀ b : 𝕜} (hb : x₀ < b) :
    0 < slope f x₀ b ↔ f x₀ < f b := by
  simp [slope, hb]

lemma slope_pos_iff_gt {𝕜} [LinearOrderedField 𝕜] {f : 𝕜 → 𝕜} {x₀ b : 𝕜} (hb : b < x₀) :
    0 < slope f x₀ b ↔ f b < f x₀ := by
  rw [slope_comm, slope_pos_iff hb]

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

/-- The Second-Derivative Test from calculus, minimum version.
This version applies to functions like `x^2 + 1[x ≥ 0]` as well as twice differentiable
functions.
 -/
theorem isLocalMin_of_deriv_deriv_pos (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMin f x₀ := by
  have h₀ : ∀ᶠ (b : ℝ) in 𝓝[<] x₀, deriv f b < 0 := by
    have := eventually_nhdsWithin_sign_eq_of_deriv_pos hf hd
    exact (eventually_nhdsWithin_of_eventually_nhds this).mp <|
      eventually_nhdsWithin_of_forall <| fun x hx₀ hx₁ => by
        rw [sign_neg <| sub_neg.mpr hx₀] at hx₁
        simp only [SignType.sign, OrderHom.coe_mk] at hx₁
        split at hx₁
        · simp at hx₁
        · split at hx₁ <;> tauto
  have h₁ : ∀ᶠ (b : ℝ) in 𝓝[>] x₀, deriv f b > 0 := by
    have := eventually_nhdsWithin_sign_eq_of_deriv_pos hf hd
    exact (eventually_nhdsWithin_of_eventually_nhds this).mp <|
      eventually_nhdsWithin_of_forall <| fun x hx₀ hx₁ => by
        rw [sign_pos <| sub_pos.mpr hx₀] at hx₁
        simp [SignType.sign] at hx₁
        split_ifs at hx₁ with g₀ <;>
        (simp only [imp_false, not_le] at hx₁; exact hx₁)
  have hf₀ : ∀ᶠ (x : ℝ) in (𝓝[<] x₀ ⊔ 𝓝[>] x₀), deriv f x ≠ 0 :=
    eventually_sup.mpr ⟨h₀.mono fun x hx => (ne_of_gt hx).symm,
                        h₁.mono fun x hx => (ne_of_lt hx).symm⟩
  have hf : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, deriv f x ≠ 0 := (nhdsLT_sup_nhdsGT x₀) ▸ hf₀
  exact isLocalMin_of_deriv hc (hf.mono fun x a ↦ differentiableAt_of_deriv_ne_zero a)
    (h₀.mono fun _ => le_of_lt) (h₁.mono fun _ => le_of_lt)

end SecondDeriv
