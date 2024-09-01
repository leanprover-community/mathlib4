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

## Tags

derivative test, calculus
-/

open Set Topology

/-!
### Some facts about differentiability and continuity

We prove a couple of auxiliary lemmas elaborating on facts such as
"differentiable implies continuous",
"an open interval is an open set", and "`fun x => -x` is antitone". -/


/-- If `f` is differentiable on `(a,b)`, and `x ∈ (a,b)`, then `f` is differentiable at `x`.-/
theorem differentiableOn_differentiableAt_Ioo.{u_1, u_2, u_3} {𝕜 : Type u_1}
  [NontriviallyNormedField 𝕜] {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [LinearOrder E] [OrderClosedTopology E]
    {a x b : E} (hab : x ∈ Set.Ioo a b)
    {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F}
    (hd₀ : DifferentiableOn 𝕜 f (Set.Ioo a b)) :
    DifferentiableAt 𝕜 f x := by
  apply DifferentiableOn.differentiableAt
  exact hd₀
  refine IsOpen.mem_nhds ?hs.hs hab
  apply isOpen_Ioo


/-- If `f'` is the derivative of `f` then  `f' x ≤ 0 → 0 ≤ (-f)' x`. -/
theorem deriv_neg_nonneg {f : ℝ → ℝ} {a b : ℝ}
  (hd₀ : DifferentiableOn ℝ f (Set.Ioo a b))
    (h₀ : ∀ x ∈ Set.Ioo a b, deriv f x ≤ 0) (x : ℝ)
    (hx : x ∈ Set.Ioo a b) : 0 ≤ deriv (-f) x :=
  (@deriv.comp ℝ _ x ℝ _ _ f (fun x => -x)
    (Differentiable.differentiableAt differentiable_neg)
    (DifferentiableOn.differentiableAt hd₀ (Ioo_mem_nhds hx.1 hx.2))) ▸ (by
    rw [deriv_neg'', neg_mul, one_mul, Left.nonneg_neg_iff];
    exact h₀ _ hx
  )

/-- If `f'` is the derivative of `f` then  `0 ≤ f' x → (-f)' x ≤ 0`. -/
theorem deriv_neg_nonpos {f : ℝ → ℝ} {b c : ℝ}
  (hd₁ : DifferentiableOn ℝ f (Set.Ioo b c))
  (h₁ : ∀ x ∈ Set.Ioo b c, 0 ≤ deriv f x) (x : ℝ) :
  x ∈ Set.Ioo b c → deriv (-f) x ≤ 0 :=
    fun hx => (@deriv.comp ℝ _ x ℝ _ _ f (fun x => -x)
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
  Suppose `a < b < c`,
    `f : ℝ → ℝ` is continuous at `b`,
    the derivative `f'` is nonnegative on `(a,b)`, and
    the derivative `f'` is nonpositive on `(b,c)`.
  Then `f` has a local maximum at `a`. -/
lemma first_derivative_test_max {f : ℝ → ℝ} {a b c : ℝ}
  (g₀ : a < b) (g₁ : b < c)
    (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Set.Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Set.Ioo b c))
    (h₀ :  ∀ x ∈ Set.Ioo a b, 0 ≤ deriv f x)
    (h₁ :  ∀ x ∈ Set.Ioo b c, deriv f x ≤ 0)
    : IsLocalMax f b :=
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
lemma first_derivative_test_min {f : ℝ → ℝ} {a b c : ℝ}
  (h : ContinuousAt f b)
    {g₀ : a < b} {g₁ : b < c}
    (hd₀ : DifferentiableOn ℝ f (Set.Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Set.Ioo b c))
    (h₀ : ∀ x ∈ Set.Ioo a b, deriv f x ≤ 0)
    (h₁ : ∀ x ∈ Set.Ioo b c, 0 ≤ deriv f x)
    : IsLocalMin f b := by
    have Q := @first_derivative_test_max (-f) a b c g₀ g₁
      (by simp_all)
      (DifferentiableOn.neg hd₀)
      (DifferentiableOn.neg hd₁)
      (by intro x;apply deriv_neg_nonneg;repeat tauto)
      (by intro x;apply deriv_neg_nonpos;repeat tauto)
    unfold IsLocalMin IsMinFilter
    unfold IsLocalMax IsMaxFilter at Q
    simp only [Pi.neg_apply, neg_le_neg_iff] at Q; exact Q
