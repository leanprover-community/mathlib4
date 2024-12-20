/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.JensenFormula

/-!
# The Logarithmic Counting Function of Value Distribution Theory

For nontrivially normed fields `𝕜`, this file defines the logarithmic counting function of a
meromorphic function defined on `𝕜`.  Also known as the `Nevanlinna counting function`, this is one
of the three main functions used in Value Distribution Theory.

The logarithmic counting function of a meromorphic function `f` is a logarithmically weighted
measure of the number of times the function `f` takes a given value `a` within the disk `∣z∣ ≤ r`,
taking multiplicities into account.

See Section VI.1 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.

## Implementation Notes

- This file defines the logarithmic counting function first for functions with locally finite
  support on `𝕜` and then specializes to the setting where the function with locally finite support
  is the pole or zero-divisor of a meromorphic function.

- Even though value distribution theory is best developed for meromorphic functions on the complex
  plane (and therefore placed in the complex analysis section of Mathlib), we introduce the
  logarithmic counting function for arbitrary normed fields.

## TODO

- Discuss the logarithmic counting function for rational functions, add a forward reference to the
  upcoming converse, formulated in terms of the Nevanlinna height.
-/

@[expose] public section

open Function MeromorphicOn Metric Real Set

/-!
## Supporting Notation
-/

namespace Function.locallyFinsuppWithin

variable {E : Type*} [NormedAddCommGroup E]

/--
Shorthand notation for the restriction of a function with locally finite support within `Set.univ`
to the closed unit ball of radius `r`.
-/
noncomputable def toClosedBall (r : ℝ) :
    locallyFinsuppWithin (univ : Set E) ℤ →+ locallyFinsuppWithin (closedBall (0 : E) |r|) ℤ := by
  apply restrictMonoidHom
  tauto

@[simp]
lemma toClosedBall_eval_within {r : ℝ} {z : E} (f : locallyFinsuppWithin (univ : Set E) ℤ)
    (ha : z ∈ closedBall 0 |r|) :
    toClosedBall r f z = f z := by
  unfold toClosedBall
  simp_all [restrict_apply]

@[simp]
lemma toClosedBall_divisor {r : ℝ} {f : ℂ → ℂ} (h : MeromorphicOn f univ) :
    (divisor f (closedBall 0 |r|)) = (locallyFinsuppWithin.toClosedBall r) (divisor f univ) := by
  simp_all [locallyFinsuppWithin.toClosedBall]

/-!
## The Logarithmic Counting Function of a Function with Locally Finite Support
-/

/--
Definition of the logarithmic counting function, as a group morphism mapping functions `D` with
locally finite support to maps `ℝ → ℝ`.  Given `D`, the result map `logCounting D` takes `r : ℝ` to
a logarithmically weighted measure of values that `D` takes within the disk `∣z∣ ≤ r`.

Implementation Note: In case where `z = 0`, the term `log (r * ‖z‖⁻¹)` evaluates to zero, which is
typically different from `log r - log ‖z‖ = log r`. The summand `(D 0) * log r` compensates this,
producing cleaner formulas when the logarithmic counting function is used in the main theorems of
Value Distribution Theory.  We refer the reader to page 164 of [Lang: Introduction to Complex
Hyperbolic Spaces](https://link.springer.com/book/10.1007/978-1-4757-1945-1) for more details, and
to the lemma `countingFunction_finsum_eq_finsum_add` in
`Mathlib/Analysis/Complex/JensenFormula.lean` for a formal statement.
-/
noncomputable def logCounting {E : Type*} [NormedAddCommGroup E] [ProperSpace E] :
    locallyFinsuppWithin (univ : Set E) ℤ →+ (ℝ → ℝ) where
  toFun D := fun r ↦ ∑ᶠ z, D.toClosedBall r z * log (r * ‖z‖⁻¹) + (D 0) * log r
  map_zero' := by aesop
  map_add' D₁ D₂ := by
    simp only [map_add, coe_add, Pi.add_apply, Int.cast_add]
    ext r
    have {A B C D : ℝ} : A + B + (C + D) = A + C + (B + D) := by ring
    rw [Pi.add_apply, this]
    congr 1
    · have h₁s : ((D₁.toClosedBall r).support ∪ (D₂.toClosedBall r).support).Finite := by
        apply Set.finite_union.2
        constructor
        <;> apply finiteSupport _ (isCompact_closedBall 0 |r|)
      repeat
        rw [finsum_eq_sum_of_support_subset (s := h₁s.toFinset)]
        try simp_rw [← Finset.sum_add_distrib, ← add_mul]
      repeat
        intro x hx
        by_contra
        simp_all
    · ring

/--
Evaluation of the logarithmic counting function at zero yields zero.
-/
@[simp] lemma logCounting_eval_zero {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsuppWithin (univ : Set E) ℤ) :
    logCounting D 0 = 0 := by
  simp [logCounting]

/--
For `1 ≤ r`, the logarithmic counting function is non-negative.
-/
theorem logCounting_nonneg {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f : locallyFinsuppWithin (univ : Set E) ℤ} {r : ℝ} (h : 0 ≤ f) (hr : 1 ≤ r) :
    0 ≤ logCounting f r := by
  have h₃r : 0 < r := by linarith
  suffices ∀ z, 0 ≤ toClosedBall r f z * log (r * ‖z‖⁻¹) from
    add_nonneg (finsum_nonneg this) <| mul_nonneg (by simpa using h 0) (log_nonneg hr)
  intro a
  by_cases h₁a : a = 0
  · simp_all
  by_cases h₂a : a ∈ closedBall 0 |r|
  · refine mul_nonneg ?_ <| log_nonneg ?_
    · simpa [h₂a] using h a
    · simpa [mul_comm r, one_le_inv_mul₀ (norm_pos_iff.mpr h₁a), abs_of_pos h₃r] using h₂a
  · simp [apply_eq_zero_of_notMem ((toClosedBall r) _) h₂a]

/--
For `1 ≤ r`, the logarithmic counting function respects the `≤` relation.
-/
theorem logCounting_le {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f₁ f₂ : locallyFinsuppWithin (univ : Set E) ℤ} {r : ℝ} (h : f₁ ≤ f₂) (hr : 1 ≤ r) :
    logCounting f₁ r ≤ logCounting f₂ r := by
  rw [← sub_nonneg] at h ⊢
  simpa using logCounting_nonneg h hr

/--
The logarithmic counting function respects the `≤` relation asymptotically.
-/
theorem logCounting_eventuallyLE {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f₁ f₂ : locallyFinsuppWithin (univ : Set E) ℤ} (h : f₁ ≤ f₂) :
    logCounting f₁ ≤ᶠ[Filter.atTop] logCounting f₂ := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ logCounting_le h hr

@[deprecated (since := "2025-12-11")] alias logCounting_eventually_le := logCounting_eventuallyLE

end Function.locallyFinsuppWithin

/-!
## The Logarithmic Counting Function of a Meromorphic Function
-/

namespace ValueDistribution

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

variable (f a) in
/--
The logarithmic counting function of a meromorphic function.

If `f : 𝕜 → E` is meromorphic and `a : WithTop E` is any value, this is a logarithmically weighted
measure of the number of times the function `f` takes a given value `a` within the disk `∣z∣ ≤ r`,
taking multiplicities into account.  In the special case where `a = ⊤`, it counts the poles of `f`.
-/
noncomputable def logCounting : ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact (divisor f univ)⁻.logCounting
  · exact (divisor (fun z ↦ f z - a.untop₀) univ)⁺.logCounting

/--
Relation between `ValueDistribution.logCounting` and `locallyFinsuppWithin.logCounting`.
-/
lemma _root_.locallyFinsuppWithin.logCounting_divisor {f : ℂ → ℂ} :
    locallyFinsuppWithin.logCounting (divisor f ⊤) = logCounting f 0 - logCounting f ⊤ := by
  simp [logCounting, ← locallyFinsuppWithin.logCounting.map_sub]

/--
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` is the logarithmic
counting function for the zeros of `f - a₀`.
-/
lemma logCounting_coe :
    logCounting f a₀ = (divisor (fun z ↦ f z - a₀) univ)⁺.logCounting := by
  simp [logCounting]

/--
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` equals the logarithmic
counting function for the zeros of `f - a₀`.
-/
lemma logCounting_coe_eq_logCounting_sub_const_zero :
    logCounting f a₀ = logCounting (f - fun _ ↦ a₀) 0 := by
  simp [logCounting]

/--
The logarithmic counting function `logCounting f 0` is the logarithmic counting function associated
with the zero-divisor of `f`.
-/
lemma logCounting_zero :
    logCounting f 0 = (divisor f univ)⁺.logCounting := by
  simp [logCounting]

/--
The logarithmic counting function `logCounting f ⊤` is the logarithmic counting function associated
with the pole-divisor of `f`.
-/
lemma logCounting_top :
    logCounting f ⊤ = (divisor f univ)⁻.logCounting := by
  simp [logCounting]

/--
Evaluation of the logarithmic counting function at zero yields zero.
-/
@[simp] lemma logCounting_eval_zero :
    logCounting f a 0 = 0 := by
  by_cases h : a = ⊤ <;> simp [logCounting, h]

-- TODO rename logCounting_zero_sub_logCounting_top
/--
The logarithmic counting function associated with the divisor of `f` is the difference between
`logCounting f 0` and `logCounting f ⊤`.
-/
theorem log_counting_zero_sub_logCounting_top {f : 𝕜 → E} :
    (divisor f univ).logCounting = logCounting f 0 - logCounting f ⊤ := by
  rw [← posPart_sub_negPart (divisor f univ), logCounting_zero, logCounting_top, map_sub]

/--
The logarithmic counting function of a constant function is zero.
-/
@[simp] theorem logCounting_const {c : E} {e : WithTop E} :
    logCounting (fun _ ↦ c : 𝕜 → E) e = 0 := by
  simp [logCounting]

/--
The logarithmic counting function of the constant function zero is zero.
-/
@[simp] theorem logCounting_const_zero {e : WithTop E} :
    logCounting (0 : 𝕜 → E) e = 0 := logCounting_const


/-!
## Elementary Properties of the Logarithmic Counting Function
-/

/--
Relation between the logarithmic counting functions of `f` and of `f⁻¹`.
-/
@[simp] theorem logCounting_inv {f : 𝕜 → 𝕜} :
     logCounting f⁻¹ ⊤ = logCounting f 0 := by
  simp [logCounting_zero, logCounting_top]

/--
Adding an analytic function does not change the logarithmic counting function for the poles.
-/
theorem logCounting_add_analyticOn (hf : MeromorphicOn f univ) (hg : AnalyticOn 𝕜 g univ) :
    logCounting (f + g) ⊤ = logCounting f ⊤ := by
  simp only [logCounting, ↓reduceDIte]
  rw [hf.negPart_divisor_add_of_analyticNhdOn_right (isOpen_univ.analyticOn_iff_analyticOnNhd.1 hg)]

/--
Special case of `logCounting_add_analyticOn`: Adding a constant does not change the logarithmic
counting function for the poles.
-/
@[simp] theorem logCounting_add_const (hf : MeromorphicOn f univ) :
    logCounting (f + fun _ ↦ a₀) ⊤ = logCounting f ⊤ := by
  apply logCounting_add_analyticOn hf analyticOn_const

/--
Special case of `logCounting_add_analyticOn`: Subtracting a constant does not change the logarithmic
counting function for the poles.
-/
@[simp] theorem logCounting_sub_const (hf : MeromorphicOn f univ) :
    logCounting (f - fun _ ↦ a₀) ⊤ = logCounting f ⊤ := by
  simpa [sub_eq_add_neg] using logCounting_add_const hf

/-!
## Behaviour under Arithmetic Operations
-/

/--
For `1 ≤ r`, the logarithmic counting function for the poles of `f + g` is less than or equal to the
sum of the logarithmic counting functions for the poles of `f` and `g`, respectively.
-/
theorem logCounting_add_top_le {f₁ f₂ : 𝕜 → E} {r : ℝ} (h₁f₁ : MeromorphicOn f₁ Set.univ)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (hr : 1 ≤ r) :
    logCounting (f₁ + f₂) ⊤ r ≤ (logCounting f₁ ⊤ + logCounting f₂ ⊤) r := by
  simp only [logCounting, ↓reduceDIte]
  rw [← Function.locallyFinsuppWithin.logCounting.map_add]
  exact Function.locallyFinsuppWithin.logCounting_le (negPart_divisor_add_le_add h₁f₁ h₁f₂) hr

/--
Asymptotically, the logarithmic counting function for the poles of `f + g` is less than or equal to
the sum of the logarithmic counting functions for the poles of `f` and `g`, respectively.
-/
theorem logCounting_add_top_eventuallyLE {f₁ f₂ : 𝕜 → E} (h₁f₁ : MeromorphicOn f₁ Set.univ)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) :
    logCounting (f₁ + f₂) ⊤ ≤ᶠ[Filter.atTop] logCounting f₁ ⊤ + logCounting f₂ ⊤ := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ logCounting_add_top_le h₁f₁ h₁f₂ hr

/--
For `1 ≤ r`, the logarithmic counting function for the poles of a sum `∑ a ∈ s, f a` is less than or
equal to the sum of the logarithmic counting functions for the poles of the `f ·`.
-/
theorem logCounting_sum_top_le {α : Type*} (s : Finset α) (f : α → 𝕜 → E) {r : ℝ}
    (h₁f : ∀ a, MeromorphicOn (f a) Set.univ) (hr : 1 ≤ r) :
    logCounting (∑ a ∈ s, f a) ⊤ r ≤ (∑ a ∈ s, (logCounting (f a) ⊤)) r := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s ha hs =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc logCounting (f a + ∑ x ∈ s, f x) ⊤ r
      _ ≤ (logCounting (f a) ⊤ + logCounting (∑ x ∈ s, f x) ⊤) r :=
        logCounting_add_top_le (h₁f a) (MeromorphicOn.sum h₁f) hr
      _ ≤ (logCounting (f a) ⊤ + ∑ x ∈ s, logCounting (f x) ⊤) r :=
        add_le_add (by trivial) hs

/--
Asymptotically, the logarithmic counting function for the poles of a sum `∑ a ∈ s, f a` is less than
or equal to the sum of the logarithmic counting functions for the poles of the `f ·`.
-/
theorem logCounting_sum_top_eventuallyLE {α : Type*} (s : Finset α) (f : α → 𝕜 → E)
    (h₁f : ∀ a, MeromorphicOn (f a) Set.univ) :
    logCounting (∑ a ∈ s, f a) ⊤ ≤ᶠ[Filter.atTop] ∑ a ∈ s, (logCounting (f a) ⊤) := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ logCounting_sum_top_le s f h₁f hr

/--
For `1 ≤ r`, the logarithmis counting function for the zeros of `f * g` is less than or equal to the
sum of the logarithmic counting functions for the zeros of `f` and `g`, respectively.

Note: The statement proven here is found at the top of page 169 of [Lang: Introduction to Complex
Hyperbolic Spaces](https://link.springer.com/book/10.1007/978-1-4757-1945-1) where it is written as
an inequality between functions. This could be interpreted as claiming that the inequality holds for
ALL values of `r`, which is not true. For a counterexample, take `f₁ : z → z` and `f₂ : z → z⁻¹`.
Then,

- `logCounting f₁ 0 = log`
- `logCounting f₂ 0 = 0`
- `logCounting (f₁ * f₂) 0 = 0`

But `log r` is negative for small `r`.
-/
theorem logCounting_mul_zero_le {f₁ f₂ : 𝕜 → 𝕜} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) 0 r ≤ (logCounting f₁ 0 + logCounting f₂ 0) r := by
  simp only [logCounting, WithTop.zero_ne_top, reduceDIte, WithTop.untop₀_zero, sub_zero]
  rw [divisor_mul h₁f₁ h₁f₂ (fun z _ ↦ h₂f₁ z) (fun z _ ↦ h₂f₂ z),
    ← Function.locallyFinsuppWithin.logCounting.map_add]
  apply Function.locallyFinsuppWithin.logCounting_le _ hr
  apply Function.locallyFinsuppWithin.posPart_add

@[deprecated (since := "2025-12-11")] alias logCounting_zero_mul_le := logCounting_mul_zero_le

/--
Asymptotically, the logarithmic counting function for the zeros of `f * g` is less than or equal to
the sum of the logarithmic counting functions for the zeros of `f` and `g`, respectively.
-/
theorem logCounting_mul_zero_eventuallyLE {f₁ f₂ : 𝕜 → 𝕜}
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) 0 ≤ᶠ[Filter.atTop] logCounting f₁ 0 + logCounting f₂ 0 := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ logCounting_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

@[deprecated (since := "2025-12-11")]
alias logCounting_zero_mul_eventually_le := logCounting_mul_zero_eventuallyLE

/--
For `1 ≤ r`, the logarithmic counting function for the poles of `f * g` is less than or equal to the
sum of the logarithmic counting functions for the poles of `f` and `g`, respectively.
-/
theorem logCounting_mul_top_le {f₁ f₂ : 𝕜 → 𝕜} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) ⊤ r ≤ (logCounting f₁ ⊤ + logCounting f₂ ⊤) r := by
  simp only [logCounting, reduceDIte]
  rw [divisor_mul h₁f₁ h₁f₂ (fun z _ ↦ h₂f₁ z) (fun z _ ↦ h₂f₂ z),
    ← Function.locallyFinsuppWithin.logCounting.map_add]
  apply Function.locallyFinsuppWithin.logCounting_le _ hr
  apply Function.locallyFinsuppWithin.negPart_add

@[deprecated (since := "2025-12-11")] alias logCounting_top_mul_le := logCounting_mul_top_le

/--
Asymptotically, the logarithmic counting function for the zeros of `f * g` is less than or equal to
the sum of the logarithmic counting functions for the zeros of `f` and `g`, respectively.
-/
theorem logCounting_mul_top_eventuallyLE {f₁ f₂ : 𝕜 → 𝕜}
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : MeromorphicOn f₂ Set.univ) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) ⊤ ≤ᶠ[Filter.atTop] logCounting f₁ ⊤ + logCounting f₂ ⊤ := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ logCounting_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

@[deprecated (since := "2025-12-11")]
alias logCounting_top_mul_eventually_le := logCounting_mul_top_eventuallyLE

/--
For natural numbers `n`, the logarithmic counting function for the zeros of `f ^ n` equals `n`
times the logarithmic counting function for the zeros of `f`.
-/
@[simp] theorem logCounting_pow_zero {f : 𝕜 → 𝕜} {n : ℕ} (hf : MeromorphicOn f Set.univ) :
    logCounting (f ^ n) 0 = n • logCounting f 0 := by
  simp [logCounting, divisor_fun_pow hf n]

/--
For natural numbers `n`, the logarithmic counting function for the poles of `f ^ n` equals `n` times
the logarithmic counting function for the poles of `f`.
-/
@[simp] theorem logCounting_pow_top {f : 𝕜 → 𝕜} {n : ℕ} (hf : MeromorphicOn f Set.univ) :
    logCounting (f ^ n) ⊤ = n • logCounting f ⊤ := by
  simp [logCounting, divisor_pow hf n]

end ValueDistribution

/-!
## Representation by Integrals

For `𝕜 = ℂ`, the theorems below describe the logarithmic counting function in terms of circle
averages.
-/

/--
Over the complex numbers, present the logarithmic counting function attached to the divisor of a
meromorphic function `f` as a circle average over `log ‖f ·‖`.

This is a reformulation of Jensen's formula of complex analysis. See
`MeromorphicOn.circleAverage_log_norm` for Jensen's formula in the original context.
-/
theorem Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const {R : ℝ}
    {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) (hR : R ≠ 0) :
    locallyFinsuppWithin.logCounting (divisor f ⊤) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have h₁f : MeromorphicOn f (closedBall 0 |R|) := by tauto
  simp only [MeromorphicOn.circleAverage_log_norm hR h₁f, locallyFinsuppWithin.logCounting,
    top_eq_univ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, zero_sub, norm_neg, add_sub_cancel_right]
  congr 1
  · simp_all
  · rw [divisor_apply, divisor_apply]
    all_goals aesop

/--
Variant of `locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const`, using
`ValueDistribution.logCounting` instead of `locallyFinsuppWithin.logCounting`.
-/
theorem ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const {R : ℝ}
    {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) (hR : R ≠ 0) :
    (logCounting f 0 - logCounting f ⊤) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  rw [← locallyFinsuppWithin.logCounting_divisor]
  exact locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const h hR
