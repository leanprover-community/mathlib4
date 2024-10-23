/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Patrick Massot
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.OrderClosedExtr
/-!
# The First-Derivative Test

We prove the first-derivative test in the strong form given on [Wikipedia](https://en.wikipedia.org/wiki/Derivative_test#First-derivative_test).

The test is proved over the real numbers ℝ
using `monotoneOn_of_deriv_nonneg` from [Mathlib.Analysis.Calculus.MeanValue].

## Main results

* `localMax_of_deriv_Ioo`: Suppose `f` is a real-valued function of a real variable
  defined on some interval containing the point `a`.
  Further suppose that `f` is continuous at `a` and differentiable on some open interval
  containing `a`, except possibly at `a` itself.

  If there exists a positive number `r > 0` such that for every `x` in `(a − r, a)`
  we have `f′(x) ≥ 0`, and for every `x` in `(a, a + r)` we have `f′(x) ≤ 0`,
  then `f` has a local maximum at `a`.

* `localMin_of_deriv_Ioo`: The dual of `first_derivative_max`, for minima.

* `localMax_of_deriv`: 1st derivative test for maxima using filters.

## Tags

derivative test, calculus
-/

open Set Topology


 /-- The First-Derivative Test from calculus, maxima version.
  Suppose `a < b < c`, `f : ℝ → ℝ` is continuous at `b`,
  the derivative `f'` is nonnegative on `(a,b)`, and
  the derivative `f'` is nonpositive on `(b,c)`. Then `f` has a local maximum at `a`. -/
lemma localMax_of_deriv_Ioo {f : ℝ → ℝ} {a b c : ℝ} (g₀ : a < b) (g₁ : b < c)
    (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ :  ∀ x ∈ Ioo a b, 0 ≤ deriv f x)
    (h₁ :  ∀ x ∈ Ioo b c, deriv f x ≤ 0) : IsLocalMax f b :=
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
lemma localMin_of_deriv_Ioo {f : ℝ → ℝ} {a b c : ℝ} (h : ContinuousAt f b)
    (g₀ : a < b) (g₁ : b < c)
    (hd₀ : DifferentiableOn ℝ f (Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Ioo b c))
    (h₀ : ∀ x ∈ Ioo a b, deriv f x ≤ 0)
    (h₁ : ∀ x ∈ Ioo b c, 0 ≤ deriv f x) : IsLocalMin f b := by
    have := localMax_of_deriv_Ioo (f := -f) g₀ g₁
      (by simp_all) hd₀.neg hd₁.neg
      (fun x hx => deriv.neg (f := f) ▸ Left.nonneg_neg_iff.mpr <|h₀ x hx)
      (fun x hx => deriv.neg (f := f) ▸ Left.neg_nonpos_iff.mpr <|h₁ x hx)
    exact (neg_neg f) ▸ IsLocalMax.neg this

 /-- The First-Derivative Test from calculus, maxima version,
 expressed in terms of left and right filters. -/
lemma localMax_of_deriv' {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd₀ : ∀ᶠ x in 𝓝[<] b, DifferentiableAt ℝ f x) (hd₁ : ∀ᶠ x in 𝓝[>] b, DifferentiableAt ℝ f x)
    (h₀  : ∀ᶠ x in 𝓝[<] b, 0 ≤ deriv f x) (h₁  : ∀ᶠ x in 𝓝[>] b, deriv f x ≤ 0) :
    IsLocalMax f b := by
  obtain ⟨a,ha⟩ := (Filter.HasBasis.eventually_iff
    (nhdsWithin_Iio_basis' ⟨b - 1, sub_one_lt b⟩)).mp <|Filter.Eventually.and hd₀ h₀
  obtain ⟨c,hc⟩ := (Filter.HasBasis.eventually_iff
    (nhdsWithin_Ioi_basis' ⟨b + 1, lt_add_one b⟩)).mp <|Filter.Eventually.and hd₁ h₁
  exact localMax_of_deriv_Ioo ha.1 hc.1 h
    (fun _ hx => (ha.2 hx).1.differentiableWithinAt)
    (fun _ hx => (hc.2 hx).1.differentiableWithinAt)
    (fun _ hx => (ha.2 hx).2) (fun x hx => (hc.2 hx).2)

/-- The First Derivative test, maximum version. -/
theorem localMax_of_deriv {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℝ f x)
    (h₀  : ∀ᶠ x in 𝓝[<] b, 0 ≤ deriv f x) (h₁  : ∀ᶠ x in 𝓝[>] b, deriv f x ≤ 0) :
    IsLocalMax f b :=
  localMax_of_deriv' h
    (nhds_left'_le_nhds_ne _ (by tauto)) (nhds_right'_le_nhds_ne _ (by tauto)) h₀ h₁
