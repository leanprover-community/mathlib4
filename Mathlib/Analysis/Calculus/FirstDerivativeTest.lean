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
    (hd₀ : DifferentiableOn ℝ f (Set.Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Set.Ioo b c))
    (h₀ :  ∀ x ∈ Set.Ioo a b, 0 ≤ deriv f x)
    (h₁ :  ∀ x ∈ Set.Ioo b c, deriv f x ≤ 0) : IsLocalMax f b :=
  have hIoc : ContinuousOn f (Ioc a b) :=
    Ioo_union_right g₀ ▸ ContinuousOn.union_continuousAt (isOpen_Ioo (a := a) (b := b))
        (DifferentiableOn.continuousOn hd₀) (by simp_all)
  have hIco : ContinuousOn f (Ico b c) :=
    Ioo_union_left g₁ ▸ ContinuousOn.union_continuousAt (isOpen_Ioo (a := b) (b := c))
        (DifferentiableOn.continuousOn hd₁) (by simp_all)
  isLocalMax_of_mono_anti g₀ g₁
    (monotoneOn_of_deriv_nonneg (convex_Ioc a b) hIoc (by simp_all) (by simp_all))
    (antitoneOn_of_deriv_nonpos (convex_Ico b c) hIco (by simp_all) (by simp_all))


/-- The First-Derivative Test from calculus, minima version. -/
lemma localMin_of_deriv_Ioo {f : ℝ → ℝ} {a b c : ℝ} (h : ContinuousAt f b)
    (g₀ : a < b) (g₁ : b < c)
    (hd₀ : DifferentiableOn ℝ f (Set.Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Set.Ioo b c))
    (h₀ : ∀ x ∈ Set.Ioo a b, deriv f x ≤ 0)
    (h₁ : ∀ x ∈ Set.Ioo b c, 0 ≤ deriv f x) : IsLocalMin f b := by
    have := localMax_of_deriv_Ioo (f := -f) g₀ g₁
      (by simp_all) (DifferentiableOn.neg hd₀) (DifferentiableOn.neg hd₁)
      (fun x hx => deriv.neg (f := f) ▸ Left.nonneg_neg_iff.mpr <|h₀ x hx)
      (fun x hx => deriv.neg (f := f) ▸ Left.neg_nonpos_iff.mpr <|h₁ x hx)
    exact (neg_neg f) ▸ IsLocalMax.neg this

/-- If `p` holds to the left of `a` then it holds in an open interval `(l, a)`. -/
lemma Filter.Eventually.exists_lt_forall_Ioo {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [NoMinOrder α] {a : α} {p : α → Prop} (h : ∀ᶠ x in 𝓝[<] a, p x) :
    ∃ l < a, ∀ x ∈ Ioo l a, p x :=
  mem_nhdsWithin_Iio_iff_exists_Ioo_subset.1 h

/-- If `p` holds to the right of `a` then it holds in an open interval `(a, l)`. -/
lemma Filter.Eventually.exists_gt_forall_Ioo {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [NoMaxOrder α] {a : α} {p : α → Prop} (h : ∀ᶠ x in 𝓝[>] a, p x) :
    ∃ l > a, ∀ x ∈ Ioo a l, p x :=
  mem_nhdsWithin_Ioi_iff_exists_Ioo_subset.1 h


/-- Monotonicity of open intervals under removal of `max` at a left endpoint. -/
theorem mem_Ioo_of_mem_Ioo_max_left {R : Type*} [LinearOrder R]
    {b u₀ v₀ x : R} (hx : x ∈ Ioo (max u₀ v₀) b) :
    x ∈ Ioo u₀ b := by simp_all

/-- Monotonicity of open intervals under removal of `min` at a right endpoint. -/
theorem mem_Ioo_of_mem_Ioo_min_right {R : Type*} [LinearOrder R]
    {b u₁ v₁ x : R} (hx : x ∈ Ioo b (min u₁ v₁)) :
    x ∈ Ioo b u₁ := by simp_all

/-- The interval inclusion `(a,b] \ {b} ⊆ (a,b)`. -/
theorem mem_Ioo_of_mem_Ioc_of_ne {R : Type*} [LinearOrder R]
    {b u₀ x : R} (hx : x ∈ Ioc u₀ b) (H : ¬x = b) :
    x ∈ Ioo u₀ b := by
    have := hx.2
    simp_all only [mem_Ioc, and_true, mem_Ioo, true_and, gt_iff_lt]
    exact lt_of_le_of_ne this H

/-- The interval inclusion `[a,b) \ {a} ⊆ (a,b)`. -/
theorem mem_Ioo_of_mem_Ico_of_ne {R : Type*} [LinearOrder R]
    {b u₀ x : R} (hx : x ∈ Ico u₀ b) (H : ¬x = u₀) :
    x ∈ Ioo u₀ b := by
    have := hx.2
    simp_all only [mem_Ico, and_true, mem_Ioo, gt_iff_lt]
    exact lt_of_le_of_ne hx fun a ↦ H (id (Eq.symm a))


 /-- The First-Derivative Test from calculus, maxima version,
 expressed in terms of left and right filters. -/
lemma localMax_of_deriv' {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd₀ : ∀ᶠ x in 𝓝[<] b, DifferentiableAt ℝ f x) (hd₁ : ∀ᶠ x in 𝓝[>] b, DifferentiableAt ℝ f x)
    (h₀  : ∀ᶠ x in 𝓝[<] b, 0 ≤ deriv f x) (h₁  : ∀ᶠ x in 𝓝[>] b, deriv f x ≤ 0) :
    IsLocalMax f b := by
  obtain ⟨u₀, hu₀, diff_u₀ : Ioo u₀ b ⊆ {x | DifferentiableAt ℝ f x}⟩ := hd₀.exists_lt_forall_Ioo
  obtain ⟨u₁, hu₁, diff_u₁ : Ioo b u₁ ⊆ {x | DifferentiableAt ℝ f x}⟩ := hd₁.exists_gt_forall_Ioo
  obtain ⟨v₀, hv₀, diff_v₀⟩ := h₀.exists_lt_forall_Ioo
  obtain ⟨v₁, hv₁, diff_v₁⟩ := h₁.exists_gt_forall_Ioo
  apply isLocalMax_of_mono_anti
  · show max u₀ v₀ < b; exact max_lt (by simp_all) (by simp_all)
  · show b < min u₁ v₁; exact lt_min (by simp_all) (by simp_all)
  · exact monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
      (fun x hx => ContinuousAt.continuousWithinAt
        <|(em (x = b)).elim (fun H => H ▸ h)
          fun H => DifferentiableAt.continuousAt <|diff_u₀
            <|mem_Ioo_of_mem_Ioo_max_left <|mem_Ioo_of_mem_Ioc_of_ne hx H)
      (fun _ _ => DifferentiableAt.differentiableWithinAt (by aesop)) (by aesop)
  · exact antitoneOn_of_deriv_nonpos (convex_Ico _ _)
      (fun x hx => ContinuousAt.continuousWithinAt
        <|(em (x = b)).elim (fun H => H ▸ h)
          fun H => DifferentiableAt.continuousAt <|diff_u₁
            <|mem_Ioo_of_mem_Ioo_min_right <|mem_Ioo_of_mem_Ico_of_ne hx H
        )
      (fun _ _ => DifferentiableAt.differentiableWithinAt (by aesop)) (by aesop)

/-- The First Derivative test, maximum version. -/
theorem localMax_of_deriv {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℝ f x)
    (h₀  : ∀ᶠ x in 𝓝[<] b, 0 ≤ deriv f x) (h₁  : ∀ᶠ x in 𝓝[>] b, deriv f x ≤ 0) :
    IsLocalMax f b :=
  localMax_of_deriv' h
    (nhds_left'_le_nhds_ne _ (by tauto)) (nhds_right'_le_nhds_ne _ (by tauto)) h₀ h₁
