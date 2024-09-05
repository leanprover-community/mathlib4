/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosedExtr
import Mathlib.Analysis.Calculus.FDeriv.Add
/-!
# The First-Derivative Test

We prove the first-derivative test in the strong form given on Wikipedia.

The test is proved over the real numbers ℝ
using `monotoneOn_of_deriv_nonneg` from [Mathlib.Analysis.Calculus.MeanValue].

## Main results

* `first_derivative_test_max`: Suppose `f` is a real-valued function of a real variable
  defined on some interval containing the point `a`.
  Further suppose that `f` is continuous at `a` and differentiable on some open interval
  containing `a`, except possibly at `a` itself.

  If there exists a positive number `r > 0` such that for every `x` in `(a − r, a)`
  we have `f′(x) ≥ 0`, and for every `x` in `(a, a + r)` we have `f′(x) ≤ 0`,
  then `f` has a local maximum at `a`.

* `first_derivative_test_min`: The dual of `first_derivative_max`, for minima.

* `first_derivative_test_max'`: A version of `first_derivative_test_max` for filters.

## Tags

derivative test, calculus
-/

open Set Topology

/-!
### Some facts about differentiability and continuity

We prove a couple of auxiliary lemmas elaborating on facts such as
"differentiable implies continuous",
"an open interval is an open set", and "`fun x => -x` is antitone". -/

/-- If `f'` is the derivative of `f` then  `f' x ≤ 0 → 0 ≤ (-f)' x`. -/
theorem deriv_neg_nonneg {f : ℝ → ℝ} {a b : ℝ} (hd₀ : DifferentiableOn ℝ f (Set.Ioo a b))
    (h₀ : ∀ x ∈ Set.Ioo a b, deriv f x ≤ 0) {x : ℝ} (hx : x ∈ Set.Ioo a b) : 0 ≤ deriv (-f) x :=
  (@deriv.comp ℝ _ x ℝ _ _ f (fun x => -x)
    (Differentiable.differentiableAt differentiable_neg)
    (DifferentiableOn.differentiableAt hd₀ (Ioo_mem_nhds hx.1 hx.2))) ▸ (by
    rw [deriv_neg'', neg_mul, one_mul, Left.nonneg_neg_iff];
    exact h₀ _ hx
  )

/-- If `f'` is the derivative of `f` then  `0 ≤ f' x → (-f)' x ≤ 0`. -/
theorem deriv_neg_nonpos {f : ℝ → ℝ} {b c : ℝ} (hd₁ : DifferentiableOn ℝ f (Set.Ioo b c))
    (h₁ : ∀ x ∈ Set.Ioo b c, 0 ≤ deriv f x) {x : ℝ} (hx : x ∈ Set.Ioo b c) : deriv (-f) x ≤ 0 :=
    (@deriv.comp ℝ _ x ℝ _ _ f (fun x => -x)
    (Differentiable.differentiableAt differentiable_neg)
    (DifferentiableOn.differentiableAt hd₁ (Ioo_mem_nhds hx.1 hx.2))) ▸ (by
    rw [deriv_neg'', neg_mul, one_mul, Left.neg_nonpos_iff]
    exact h₁ _ hx
  )

/-!
### The First-Derivative Test

Using the connection beetween monotonicity and derivatives we obtain the familiar
First-Derivative Test from calculus.
-/


 /-- The First-Derivative Test from calculus, maxima version.
  Suppose `a < b < c`, `f : ℝ → ℝ` is continuous at `b`,
  the derivative `f'` is nonnegative on `(a,b)`, and
  the derivative `f'` is nonpositive on `(b,c)`. Then `f` has a local maximum at `a`. -/
lemma first_derivative_test_Ioo_max {f : ℝ → ℝ} {a b c : ℝ} (g₀ : a < b) (g₁ : b < c)
    (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Set.Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Set.Ioo b c))
    (h₀ :  ∀ x ∈ Set.Ioo a b, 0 ≤ deriv f x)
    (h₁ :  ∀ x ∈ Set.Ioo b c, deriv f x ≤ 0) : IsLocalMax f b :=
  have continuous_Ioc : ContinuousOn f (Ioc a b) :=
    fun _ hx ↦ (Ioo_union_right g₀ ▸ hx).elim
    (fun hx ↦ (hd₀.differentiableAt <| Ioo_mem_nhds hx.1 hx.2).continuousAt.continuousWithinAt)
    (fun hx ↦ mem_singleton_iff.1 hx ▸ h.continuousWithinAt)
  have continuous_Ico : ContinuousOn f (Ico b c) :=
    fun _ hx ↦ (Ioo_union_left g₁ ▸ hx).elim
    (fun hx ↦ (hd₁.differentiableAt <| Ioo_mem_nhds hx.1 hx.2).continuousAt.continuousWithinAt)
    (fun hx ↦ mem_singleton_iff.1 hx ▸ h.continuousWithinAt)
  isLocalMax_of_mono_anti g₀ g₁
    (monotoneOn_of_deriv_nonneg (convex_Ioc a b)
    continuous_Ioc (by simp_all) (by simp_all))
    (antitoneOn_of_deriv_nonpos (convex_Ico b c)
    continuous_Ico (by simp_all) (by simp_all))

/-- The First-Derivative Test from calculus, minima version. -/
lemma first_derivative_test_Ioo_min {f : ℝ → ℝ} {a b c : ℝ} (h : ContinuousAt f b)
    (g₀ : a < b) (g₁ : b < c)
    (hd₀ : DifferentiableOn ℝ f (Set.Ioo a b)) (hd₁ : DifferentiableOn ℝ f (Set.Ioo b c))
    (h₀ : ∀ x ∈ Set.Ioo a b, deriv f x ≤ 0)
    (h₁ : ∀ x ∈ Set.Ioo b c, 0 ≤ deriv f x) : IsLocalMin f b := by
    have Q := @first_derivative_test_Ioo_max (-f) a b c g₀ g₁
      (by simp_all) (DifferentiableOn.neg hd₀) (DifferentiableOn.neg hd₁)
      (fun _ => deriv_neg_nonneg hd₀ h₀) (fun _ => deriv_neg_nonpos hd₁ h₁)
    unfold IsLocalMax IsMaxFilter at Q
    simp only [Pi.neg_apply, neg_le_neg_iff] at Q
    exact Q


 /-- The First-Derivative Test from calculus, maxima version,
 expressed in terms of left and right filters. -/
lemma first_derivative_test_max₀ {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd₀ : ∀ᶠ x in 𝓝[<] b, DifferentiableAt ℝ f x) (hd₁ : ∀ᶠ x in 𝓝[>] b, DifferentiableAt ℝ f x)
    (h₀  : ∀ᶠ x in 𝓝[<] b, 0 ≤ deriv f x) (h₁  : ∀ᶠ x in 𝓝[>] b, deriv f x ≤ 0) :
    IsLocalMax f b := by
  unfold Filter.Eventually at h₀ h₁ hd₀ hd₁
  rw [mem_nhdsWithin_Iio_iff_exists_Ioo_subset] at h₀ hd₀
  rw [mem_nhdsWithin_Ioi_iff_exists_Ioo_subset] at h₁ hd₁
  obtain ⟨u₀,hu₀⟩ := hd₀; obtain ⟨u₁,hu₁⟩ := hd₁
  obtain ⟨v₀,hv₀⟩ := h₀; obtain ⟨v₁,hv₁⟩ := h₁
  apply isLocalMax_of_mono_anti
  · show max u₀ v₀ < b; exact max_lt (by simp_all) (by simp_all)
  · show b < min u₁ v₁; exact lt_min (by simp_all) (by simp_all)
  · exact monotoneOn_of_deriv_nonneg
      (convex_Ioc _ _)
      (fun x _ => ContinuousAt.continuousWithinAt ((em (x = b)).elim (fun H => H ▸ h)
        (fun H => DifferentiableAt.continuousAt (hu₀.2 (by contrapose H;simp_all;linarith)))))
      (fun x _ => DifferentiableAt.differentiableWithinAt (hu₀.2 (by simp_all)))
      (fun x _ => by apply hv₀.2;simp_all)
  · exact antitoneOn_of_deriv_nonpos
      (convex_Ico _ _)
      (fun x _ => ContinuousAt.continuousWithinAt ((em (x = b)).elim (fun H => H ▸ h)
        (fun H => DifferentiableAt.continuousAt (hu₁.2 (by contrapose H;simp_all;linarith)))))
      (fun x _ => DifferentiableAt.differentiableWithinAt (hu₁.2 (by simp_all)))
      (fun x _ => by apply hv₁.2;simp_all)

/-- If a set `P` contains left and right neighborhoods of a point `x`
then `P` contains a punctured neighborhood. -/
lemma nhdsWithin_punctured_of_Iio_Ioi (P : Set ℝ)
    (hl : P ∈ nhdsWithin 0 (Set.Iio 0)) (hr : P ∈ nhdsWithin 0 (Set.Ioi 0)) :
    P ∈ nhdsWithin 0 {0}ᶜ := by
  rw [mem_nhdsWithin]
  rw [mem_nhdsWithin] at hl hr
  obtain ⟨u,hu⟩ := hl
  obtain ⟨v,hv⟩ := hr
  use u ∩ v
  simp_all only [Set.mem_inter_iff, and_self, true_and]
  exact ⟨
    IsOpen.inter (by tauto) (by tauto),
    fun x hx => by
      simp_all only [Set.mem_inter_iff]
      exact  ((lt_or_gt_of_ne hx.2)).elim (fun _ => hu.2.2 (by tauto)) (fun _ => hv.2.2 (by tauto))
  ⟩

/-- If a set `P` contains a punctured neighborhood of `x`
then `P` contains a left neighborhoods of `x`. -/
lemma nhdsWithin_Iio_of_punctured {b:ℝ} {P : Set ℝ} (h : P ∈ nhdsWithin b {b}ᶜ) :
  P ∈ nhdsWithin b (Set.Iio b) := by
  rw [mem_nhdsWithin] at *
  obtain ⟨u,hu⟩ := h
  use u
  simp_all only [true_and]
  intro x hx;apply hu.2.2;simp_all only [mem_inter_iff, mem_Iio, mem_compl_iff, mem_singleton_iff,
    true_and];linarith;

/-- If a set `P` contains a punctured neighborhood of `x`
then `P` contains a right neighborhoods of `x`. -/
lemma nhdsWithin_Ioi_of_punctured {b:ℝ} {P : Set ℝ} (h : P ∈ nhdsWithin b {b}ᶜ) :
  P ∈ nhdsWithin b (Set.Ioi b) := by
  rw [mem_nhdsWithin] at *
  obtain ⟨u,hu⟩ := h
  use u
  simp_all only [true_and]
  intro x hx;apply hu.2.2;simp_all;linarith

/-- The First Derivative test, maximum version. -/
theorem first_derivative_test_max {f : ℝ → ℝ} {b : ℝ} (h : ContinuousAt f b)
    (hd : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℝ f x)
    (h₀  : ∀ᶠ x in 𝓝[<] b, 0 ≤ deriv f x) (h₁  : ∀ᶠ x in 𝓝[>] b, deriv f x ≤ 0) :
    IsLocalMax f b :=
  first_derivative_test_max₀ h
    (nhdsWithin_Iio_of_punctured (by tauto)) (nhdsWithin_Ioi_of_punctured (by tauto)) h₀ h₁
