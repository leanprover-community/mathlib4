/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Counting Function of Value Distribution Theory

For nontrivially normed fields `𝕜`, this file defines the logarithmic counting function of a
meromorphic function defined on `𝕜`.  Also known as the `Nevanlinna counting function`, this is one
of the three main functions used in Value Distribution Theory.

The counting function of a meromorphic function `f` is a logarithmically weighted measure of the
number of times the function `f` takes a given value `a` within the disk `∣z∣ ≤ r`, counting
multiplicities.

See Section VI.1 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.

## Implementation Notes

- This file defines the logarithmic counting function first for functions with locally finite
  support on `𝕜` and then specializes to the setting where the function with locally finite support
  is the pole or zero-divisor of a meromorphic function.

- Even though value distribution theory is best developed for meromorphic functions on the complex
  plane (and therefore placed in the complex analysis section of Mathlib), we introduce the counting
  function for arbitrary normed fields.

## TODO

- For `𝕜 = ℂ`, add the integral presentation of the logarithmic counting function
- Discuss the counting function for rational functions, add a forward reference to the upcoming
  converse, formulated in terms of the Nevanlinna height.
- Counting function of powers.
-/

open MeromorphicOn Metric Real Set

/-!
## Supporting Notation
-/

namespace Function.locallyFinsuppWithin

/--
Shorthand notation for the restriction of a function with locally finite support within `Set.univ`
to the closed unit ball of radius `r`.
-/
noncomputable def toClosedBall {E : Type*} [NormedAddCommGroup E] (r : ℝ) :
    locallyFinsuppWithin (univ : Set E) ℤ →+ locallyFinsuppWithin (closedBall (0 : E) |r|) ℤ := by
  apply restrictMonoidHom
  tauto

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
to the lemma `countingFunction_finsum_eq_finsum_add` for a formal statement.
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
Alternate presentation of the finsum that appears in the definition of the counting function.
-/
lemma countingFunction_finsum_eq_finsum_add {c : ℂ} {R : ℝ} {D : ℂ → ℤ} (hR : R ≠ 0)
    (hD : D.support.Finite) :
    ∑ᶠ u, D u * (log R - log ‖c - u‖) = ∑ᶠ u, D u * log (R * ‖c - u‖⁻¹) + D c * log R := by
  by_cases h : c ∈ D.support
  · have {g : ℂ → ℝ} : (fun u ↦ D u * g u).support ⊆ hD.toFinset :=
      fun x ↦ by simp +contextual
    simp only [finsum_eq_sum_of_support_subset _ this,
      Finset.sum_eq_sum_diff_singleton_add ((Set.Finite.mem_toFinset hD).mpr h), sub_self,
      norm_zero, log_zero, sub_zero, inv_zero, mul_zero, add_zero, add_left_inj]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp only [Finset.mem_sdiff, Finset.notMem_singleton] at hx
    rw [log_mul hR (inv_ne_zero (norm_ne_zero_iff.mpr (sub_eq_zero.not.2 hx.2.symm))), log_inv]
    ring
  · simp_all only [mem_support, Decidable.not_not, Int.cast_zero, zero_mul, add_zero]
    refine finsum_congr fun x ↦ ?_
    by_cases h₁ : c = x
    · simp_all
    · rw [log_mul hR (inv_ne_zero (norm_ne_zero_iff.mpr (sub_eq_zero.not.2 h₁))), log_inv]
      ring

/--
Evaluation of the logarithmic counting function at zero yields zero.
-/
@[simp] lemma logCounting_eval_zero {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsuppWithin (univ : Set E) ℤ) :
    logCounting D 0 = 0 := by
  simp [logCounting]

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
counting multiplicities.  In the special case where `a = ⊤`, it counts the poles of `f`.
-/
noncomputable def logCounting : ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact (divisor f univ)⁻.logCounting
  · exact (divisor (fun z ↦ f z - a.untop₀) univ)⁺.logCounting

/--
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` is the counting
function associated with the zero-divisor of the meromorphic function `f - a₀`.
-/
lemma logCounting_coe :
    logCounting f a₀ = (divisor (fun z ↦ f z - a₀) univ)⁺.logCounting := by
  simp [logCounting]

/--
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` equals the logarithmic
counting function for the value zero of the shifted function `f - a₀`.
-/
lemma logCounting_coe_eq_logCounting_sub_const_zero :
    logCounting f a₀ = logCounting (f - fun _ ↦ a₀) 0 := by
  simp [logCounting]

/--
The logarithmic counting function `logCounting f 0` is the counting function associated with the
zero-divisor of `f`.
-/
lemma logCounting_zero :
    logCounting f 0 = (divisor f univ)⁺.logCounting := by
  simp [logCounting]

/--
The logarithmic counting function `logCounting f ⊤` is the counting function associated with
the pole-divisor of `f`.
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

/--
The counting function associated with the divisor of `f` is the difference between `logCounting f 0`
and `logCounting f ⊤`.
-/
theorem log_counting_zero_sub_logCounting_top {f : 𝕜 → E} :
    (divisor f univ).logCounting = logCounting f 0 - logCounting f ⊤ := by
  rw [← posPart_sub_negPart (divisor f univ), logCounting_zero, logCounting_top, map_sub]

/-!
## Elementary Properties of the Counting Function
-/

/--
Relation between the logarithmic counting function of `f` and of `f⁻¹`.
-/
@[simp] theorem logCounting_inv {f : 𝕜 → 𝕜} :
     logCounting f⁻¹ ⊤ = logCounting f 0 := by
  simp [logCounting_zero, logCounting_top]

/--
Adding an analytic function does not change the counting function counting poles.
-/
theorem logCounting_add_analyticOn (hf : MeromorphicOn f univ) (hg : AnalyticOn 𝕜 g univ) :
    logCounting (f + g) ⊤ = logCounting f ⊤ := by
  simp only [logCounting, ↓reduceDIte]
  rw [hf.negPart_divisor_add_of_analyticNhdOn_right (isOpen_univ.analyticOn_iff_analyticOnNhd.1 hg)]

/--
Special case of `logCounting_add_analyticOn`: Adding a constant does not change the counting
function counting poles.
-/
@[simp] theorem logCounting_add_const (hf : MeromorphicOn f univ) :
    logCounting (f + fun _ ↦ a₀) ⊤ = logCounting f ⊤ := by
  apply logCounting_add_analyticOn hf analyticOn_const

/--
Special case of `logCounting_add_analyticOn`: Subtracting a constant does not change the counting
function counting poles.
-/
@[simp] theorem logCounting_sub_const (hf : MeromorphicOn f univ) :
    logCounting (f - fun _ ↦ a₀) ⊤ = logCounting f ⊤ := by
  simpa [sub_eq_add_neg] using logCounting_add_const hf

end ValueDistribution
