/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Jireh Loreaux, Floris van Doorn, Eric Wieser
-/
import Mathlib.Analysis.Calculus.FirstDerivativeTest
import Mathlib.Order.Interval.Set.Basic
import Mathlib.LinearAlgebra.AffineSpace.Ordered

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

/-- If the derivative of `f` is positive at a root `x₀` of `f`, then locally the sign of `f x`
matches `x - x₀`. -/
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

/-- If the derivative of `f` is negative at a root `x₀` of `f`, then locally the sign of `f x`
matches `x₀ - x`. -/
lemma eventually_nhdsWithin_sign_eq_of_deriv_neg (hf : deriv f x₀ < 0) (hx : f x₀ = 0) :
    ∀ᶠ x in 𝓝 x₀, sign (f x) = sign (x₀ - x) := by
  simpa [Left.sign_neg, -neg_sub, ← neg_sub x₀] using
    eventually_nhdsWithin_sign_eq_of_deriv_pos
        (f := (-f ·)) (x₀ := x₀) (by simpa [deriv.neg]) (by simpa)

lemma deriv_neg_left_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝 x₀, sign (deriv f x) = sign (x - x₀)) :
    ∀ᶠ (b : ℝ) in 𝓝[<] x₀, deriv f b < 0 := by
  filter_upwards [inter_mem_nhdsWithin _ h₀] with x ⟨(hx : x < x₀), (hx' : sign _ = _)⟩
  rwa [← sub_neg, ← sign_eq_neg_one_iff, ← hx', sign_eq_neg_one_iff] at hx

lemma deriv_neg_right_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝 x₀, sign (deriv f x) = sign (x₀ - x)) :
     ∀ᶠ (b : ℝ) in 𝓝[>] x₀, deriv f b < 0 := by
  filter_upwards [inter_mem_nhdsWithin _ h₀] with x ⟨(hx : x₀ < x), (hx' : sign _ = _)⟩
  rwa [← sub_neg, ← sign_eq_neg_one_iff, ← hx', sign_eq_neg_one_iff] at hx

lemma deriv_pos_right_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝 x₀, sign (deriv f x) = sign (x - x₀)) :
     ∀ᶠ (b : ℝ) in 𝓝[>] x₀, deriv f b > 0 := by
  filter_upwards [inter_mem_nhdsWithin _ h₀] with x ⟨(hx : x₀ < x), (hx' : sign _ = _)⟩
  rwa [← sub_pos, ← sign_eq_one_iff, ← hx', sign_eq_one_iff] at hx

lemma deriv_pos_left_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝 x₀, sign (deriv f x) = sign (x₀ - x)) :
    ∀ᶠ (b : ℝ) in 𝓝[<] x₀, deriv f b > 0 := by
  filter_upwards [inter_mem_nhdsWithin _ h₀] with x ⟨(hx : x < x₀), (hx' : sign _ = _)⟩
  rwa [← sub_pos, ← sign_eq_one_iff, ← hx', sign_eq_one_iff] at hx

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
  simpa using isLocalMin_of_deriv_deriv_pos (by simpa) (by simpa) hc.neg |>.neg

end SecondDeriv
