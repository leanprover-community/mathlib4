/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Patrick Massot, Floris van Doorn, Jireh Loreaux, Eric Wieser
-/
import Mathlib.Topology.Order.OrderClosedExtr
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Order.Interval.Set.Basic
import Mathlib.LinearAlgebra.AffineSpace.Ordered

/-!
# The First-Derivative Test

We prove the first-derivative test from calculus, in the strong form given on [Wikipedia](https://en.wikipedia.org/wiki/Derivative_test#First-derivative_test).

The test is proved over the real numbers ℝ
using `monotoneOn_of_deriv_nonneg` from [Mathlib.Analysis.Calculus.MeanValue].

# The Second-Derivative Test

We prove the Second-Derivative Test using the First-Derivative Test.
Source: [Wikipedia](https://en.wikipedia.org/wiki/Derivative_test#Proof_of_the_second-derivative_test).

## Main results

* `isLocalMax_of_deriv_Ioo`: Suppose `f` is a real-valued function of a real variable
  defined on some interval containing the point `a`.
  Further suppose that `f` is continuous at `a` and differentiable on some open interval
  containing `a`, except possibly at `a` itself.

  If there exists a positive number `r > 0` such that for every `x` in `(a − r, a)`
  we have `f′(x) ≥ 0`, and for every `x` in `(a, a + r)` we have `f′(x) ≤ 0`,
  then `f` has a local maximum at `a`.

* `isLocalMin_of_deriv_Ioo`: The dual of `first_derivative_max`, for minima.

* `isLocalMax_of_deriv`: 1st derivative test for maxima using filters.

* `isLocalMin_of_deriv`: 1st derivative test for minima using filters.

* `isLocalMin_of_deriv_deriv_pos`: The second-derivative test, minimum version.


## Tags

derivative test, calculus
-/


open Set Topology


/-- The First-Derivative Test from calculus, maxima version.
Suppose `a < b < c`, `f : ℝ → ℝ` is continuous at `b`,
the derivative `f'` is nonnegative on `(a,b)`, and
the derivative `f'` is nonpositive on `(b,c)`. Then `f` has a local maximum at `a`. -/
lemma isLocalMax_of_deriv_Ioo {f : ℝ → ℝ} {a b c : ℝ} (g₀ : a < b) (g₁ : b < c)
    (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, 0 ≤ deriv f x)
    (h₁ : ∀ x ∈ Ioo b c, deriv f x ≤ 0) : IsLocalMax f b :=
  have hIoc : ContinuousOn f (Ioc a b) :=
    Ioo_union_right g₀ ▸ hd₀.continuousOn.union_continuousAt (isOpen_Ioo (a := a) (b := b))
      (by simp_all)
  have hIco : ContinuousOn f (Ico b c) :=
    Ioo_union_left g₁ ▸ hd₁.continuousOn.union_continuousAt (isOpen_Ioo (a := b) (b := c))
      (by simp_all)
  isLocalMax_of_mono_anti g₀ g₁
    (monotoneOn_of_deriv_nonneg (convex_Ioc a b) hIoc (by simp_all) (by simp_all))
    (antitoneOn_of_deriv_nonpos (convex_Ico b c) hIco (by simp_all) (by simp_all))


/-- The First-Derivative Test from calculus, minima version. -/
lemma isLocalMin_of_deriv_Ioo {f : ℝ → ℝ} {a b c : ℝ}
    (g₀ : a < b) (g₁ : b < c) (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0)
    (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) : IsLocalMin f b := by
  have := isLocalMax_of_deriv_Ioo (f := -f) g₀ g₁
    (by simp_all) hd₀.neg hd₁.neg
    (fun x hx => deriv.neg (f := f) ▸ Left.nonneg_neg_iff.mpr <|h₀ x hx)
    (fun x hx => deriv.neg (f := f) ▸ Left.neg_nonpos_iff.mpr <|h₁ x hx)
  exact (neg_neg f) ▸ IsLocalMax.neg this

/-- The First-Derivative Test from calculus, maxima version,
expressed in terms of left and right filters. -/
lemma isLocalMax_of_deriv' {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd₀ : ∀ᶠ x in 𝓝[<] b, DifferentiableAt ℝ f x) (hd₁ : ∀ᶠ x in 𝓝[>] b, DifferentiableAt ℝ f x)
    (h₀ : ∀ᶠ x in 𝓝[<] b, 0 ≤ deriv f x) (h₁ : ∀ᶠ x in 𝓝[>] b, deriv f x ≤ 0) :
    IsLocalMax f b := by
  obtain ⟨a, ha⟩ := (nhdsLT_basis b).eventually_iff.mp <| hd₀.and h₀
  obtain ⟨c, hc⟩ := (nhdsGT_basis b).eventually_iff.mp <| hd₁.and h₁
  exact isLocalMax_of_deriv_Ioo ha.1 hc.1 h
    (fun _ hx => (ha.2 hx).1.differentiableWithinAt)
    (fun _ hx => (hc.2 hx).1.differentiableWithinAt)
    (fun _ hx => (ha.2 hx).2) (fun x hx => (hc.2 hx).2)

/-- The First-Derivative Test from calculus, minima version,
expressed in terms of left and right filters. -/
lemma isLocalMin_of_deriv' {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd₀ : ∀ᶠ x in 𝓝[<] b, DifferentiableAt ℝ f x) (hd₁ : ∀ᶠ x in 𝓝[>] b, DifferentiableAt ℝ f x)
    (h₀ : ∀ᶠ x in 𝓝[<] b, deriv f x ≤ 0) (h₁ : ∀ᶠ x in 𝓝[>] b, deriv f x ≥ 0) :
    IsLocalMin f b := by
  obtain ⟨a, ha⟩ := (nhdsLT_basis b).eventually_iff.mp <| hd₀.and h₀
  obtain ⟨c, hc⟩ := (nhdsGT_basis b).eventually_iff.mp <| hd₁.and h₁
  exact isLocalMin_of_deriv_Ioo ha.1 hc.1 h
    (fun _ hx => (ha.2 hx).1.differentiableWithinAt)
    (fun _ hx => (hc.2 hx).1.differentiableWithinAt)
    (fun _ hx => (ha.2 hx).2) (fun x hx => (hc.2 hx).2)

/-- The First Derivative test, maximum version. -/
theorem isLocalMax_of_deriv {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℝ f x)
    (h₀ : ∀ᶠ x in 𝓝[<] b, 0 ≤ deriv f x) (h₁ : ∀ᶠ x in 𝓝[>] b, deriv f x ≤ 0) :
    IsLocalMax f b :=
  isLocalMax_of_deriv' h (nhdsLT_le_nhdsNE _ (by tauto)) (nhdsGT_le_nhdsNE _ (by tauto)) h₀ h₁

/-- The First Derivative test, minimum version. -/
theorem isLocalMin_of_deriv {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℝ f x)
    (h₀ : ∀ᶠ x in 𝓝[<] b, deriv f x ≤ 0) (h₁ : ∀ᶠ x in 𝓝[>] b, 0 ≤ deriv f x) :
    IsLocalMin f b :=
  isLocalMin_of_deriv' h (nhdsLT_le_nhdsNE _ (by tauto)) (nhdsGT_le_nhdsNE _ (by tauto)) h₀ h₁

open Filter SignType

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
  obtain (hx' | hx') := hx₁.lt_or_gt
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
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, sign (deriv f x) = sign (x - x₀)) :
    ∀ᶠ (b : ℝ) in 𝓝[<] x₀, deriv f b < 0 := by
  filter_upwards [nhdsLT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x < x₀)
  rwa [← sub_neg, ← sign_eq_neg_one_iff, ← hx', sign_eq_neg_one_iff] at hx

lemma deriv_neg_right_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, sign (deriv f x) = sign (x₀ - x)) :
     ∀ᶠ (b : ℝ) in 𝓝[>] x₀, deriv f b < 0 := by
  filter_upwards [nhdsGT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x₀ < x)
  rwa [← sub_neg, ← sign_eq_neg_one_iff, ← hx', sign_eq_neg_one_iff] at hx

lemma deriv_pos_right_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, sign (deriv f x) = sign (x - x₀)) :
     ∀ᶠ (b : ℝ) in 𝓝[>] x₀, deriv f b > 0 := by
  filter_upwards [nhdsGT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x₀ < x)
  rwa [← sub_pos, ← sign_eq_one_iff, ← hx', sign_eq_one_iff] at hx

lemma deriv_pos_left_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ}
    (h₀ : ∀ᶠ (x : ℝ) in 𝓝[≠] x₀, sign (deriv f x) = sign (x₀ - x)) :
    ∀ᶠ (b : ℝ) in 𝓝[<] x₀, deriv f b > 0 := by
  filter_upwards [nhdsLT_le_nhdsNE _ h₀, self_mem_nhdsWithin] with x hx' (hx : x < x₀)
  rwa [← sub_pos, ← sign_eq_one_iff, ← hx', sign_eq_one_iff] at hx

/-- The First Derivative test with a hypothesis on the sign of the derivative, maximum version. -/
theorem isLocalMax_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ} (h : ContinuousAt f x₀)
    (hf : ∀ᶠ x in 𝓝[≠] x₀, sign (deriv f x) = sign (x₀ - x)) :
    IsLocalMax f x₀ := by
  have hl := deriv_pos_left_of_sign_deriv hf
  have hg := deriv_neg_right_of_sign_deriv hf
  replace hf := (nhdsLT_sup_nhdsGT x₀) ▸
    eventually_sup.mpr ⟨hl.mono fun x hx => hx.ne', hg.mono fun x hx => hx.ne⟩
  exact isLocalMax_of_deriv h (hf.mono fun x hx ↦ differentiableAt_of_deriv_ne_zero hx)
    (hl.mono fun _ => le_of_lt) (hg.mono fun _ => le_of_lt)

/-- The First Derivative test with a hypothesis on the sign of the derivative, minimum version. -/
theorem isLocalMin_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ} (h : ContinuousAt f x₀)
    (hf : ∀ᶠ x in 𝓝[≠] x₀, sign (deriv f x) = sign (x - x₀)) :
    IsLocalMin f x₀ := by
  refine neg_neg f ▸ (isLocalMax_of_sign_deriv (f := (-f ·)) h.neg ?foo |>.neg)
  simpa [Left.sign_neg, -neg_sub, ← neg_sub _ x₀, deriv.neg]

/-- The Second-Derivative Test from calculus, minimum version.
Applies to functions like `x^2 + 1[x ≥ 0]` as well as twice differentiable
functions. -/
theorem isLocalMin_of_deriv_deriv_pos (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMin f x₀ :=
  isLocalMin_of_sign_deriv hc <| nhdsWithin_le_nhds <|
    eventually_nhdsWithin_sign_eq_of_deriv_pos hf hd

/-- The Second-Derivative Test from calculus, maximum version. -/
theorem isLocalMax_of_deriv_deriv_neg (hf : deriv (deriv f) x₀ < 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMax f x₀ := by
  simpa using isLocalMin_of_deriv_deriv_pos (by simpa) (by simpa) hc.neg |>.neg

end SecondDeriv
