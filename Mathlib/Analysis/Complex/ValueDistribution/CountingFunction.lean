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
multiplicities.  See Section~VI.1 of [Lang: Introduction to Complex Hyperbolic
Spaces](https://link.springer.com/book/10.1007/978-1-4757-1945-1) or Section~1.1 of
[Noguchi-Winkelmann: Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation](https://link.springer.com/book/10.1007/978-4-431-54571-2) for a detailed discussion.

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

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-!
## Supporting Notation
-/

namespace Function.locallyFinsuppWithin

/--
Shorthand notation for the restriction of a function with locally finite support within `Set.univ`
to the closed unit ball of radius `r`.
-/
noncomputable def toBall (r : ℝ) :
    locallyFinsuppWithin (univ : Set 𝕜) ℤ →+ locallyFinsuppWithin (closedBall (0 : 𝕜) |r|) ℤ := by
  apply restrictMonoidHom
  tauto

/-!
## The Logarithmic Counting Function of a Function with Locally Finite Support
-/

/--
Definition of the logarithmic counting function for a function with locally finite support within
`Set.univ`, as a group morphism.
-/
noncomputable def logCounting [ProperSpace 𝕜] :
    locallyFinsuppWithin (univ : Set 𝕜) ℤ →+ (ℝ → ℝ) where
  toFun D := fun r ↦ ∑ᶠ z, D.toBall r z * log (r * ‖z‖⁻¹) + (D 0) * log r
  map_zero' := by
    simp
    rfl
  map_add' D₁ D₂ := by
    simp only [Set.top_eq_univ, map_add, coe_add, Pi.add_apply, Int.cast_add]
    ext r
    have {A B C D : ℝ} : A + B + (C + D) = A + C + (B + D) := by ring
    rw [Pi.add_apply, this]
    congr 1
    · have h₁s : ((D₁.toBall r).support ∪ (D₂.toBall r).support).Finite := by
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
@[simp] lemma logCounting_eval_zero [ProperSpace 𝕜]
    (D : locallyFinsuppWithin (univ : Set 𝕜) ℤ) :
    logCounting D 0 = 0 := by
  rw [logCounting]
  simp

end Function.locallyFinsuppWithin

/-!
## The Logarithmic Counting Function of a Meromorphic Function
-/

namespace VD

variable
  [ProperSpace 𝕜]
  {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

variable (f a) in
/--
The logarithmic counting function of a meromorphic function.

If `f : 𝕜 → E` is meromorphic and `a : WithTop E` is any value, this is a logarithmically weighted
measure of the number of times the function `f` takes a given value `a` within the disk `∣z∣ ≤ r`,
counting multiplicities.  In the special case where `a = ⊤`, it counts the poles of `f`.
-/
noncomputable def logCounting :
    ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact (divisor f univ)⁻.logCounting
  · exact (divisor (fun z ↦ f z - a.untop₀) univ)⁺.logCounting

/--
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` is the counting
function associated with the zero-divisor of the meromorphic function `f - a₀`.
-/
lemma logCounting_finite :
    logCounting f a₀ = (divisor (fun z ↦ f z - a₀) univ)⁺.logCounting := by
  simp [logCounting]

/--
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` is equals the
logarithmic counting function for the value zero of the shifted function `f - a₀`.
-/
lemma logCounting_finite_eq_logCounting_zero_of_shifted :
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
The logarithmic counting function `logCounting f Set.univ` is the counting function associated with
the pole-divisor of `f`.
-/
lemma logCounting_top :
    logCounting f ⊤ = (divisor f univ)⁻.logCounting := by
  simp [logCounting]

/--
Evaluation of the logarithmic counting function at zero yields zero.
-/
lemma logCounting_eval_zero :
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
theorem logCounting_inv [CompleteSpace 𝕜] {f : 𝕜 → 𝕜} :
    logCounting f 0 = logCounting f⁻¹ ⊤ := by
  simp [logCounting_zero, logCounting_top]

/--
Adding an analytic function does not change the counting function counting poles.
-/
theorem logCounting_add_analyticOn_right (hf : MeromorphicOn f univ) (hg : AnalyticOn 𝕜 g univ) :
    logCounting (f + g) ⊤ = logCounting f ⊤ := by
  simp only [logCounting, ↓reduceDIte]
  rw [hf.negPart_divisor_add_of_analyticNhdOn_right (isOpen_univ.analyticOn_iff_analyticOnNhd.1 hg)]

/--
Special case of `VD.logCounting_add_analyticOn_right`: Adding a constant does not change the
counting function counting poles.
-/
theorem logCounting_add_const_right (hf : MeromorphicOn f univ) :
    logCounting (f + fun _ ↦ a₀) ⊤ = logCounting f ⊤ := by
  apply logCounting_add_analyticOn_right hf analyticOn_const

/--
Special case of `VD.logCounting_add_analyticOn_right`: Subtracting a constant does not change the
counting function counting poles.
-/
theorem logCounting_sub_const_right (hf : MeromorphicOn f univ) :
    logCounting (f - fun _ ↦ a₀) ⊤ = logCounting f ⊤ := by
  have : f - (fun x ↦ a₀) = f + fun x ↦ -a₀ := by
    funext x
    simp [sub_eq_add_neg]
  rw [this]
  apply logCounting_add_analyticOn_right hf analyticOn_const

end VD
