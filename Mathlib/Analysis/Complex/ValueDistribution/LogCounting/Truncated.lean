/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus using Claude Code
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic

/-!
# Truncated Divisors and Truncated Counting Functions

This file introduces (and provides API for) the Truncated Logarithmic Counting Functions. These
differ from the Logarithmic Counting Function in that they disregard pole orders, and count all
poles with multiplicity one.

The truncated counting function is the quantity through which the Second Main Theorem
of Value Distribution Theory is classically stated.

The theorems `ValueDistribution.logCounting_deriv_top` and
`ValueDistribution.sum_logCounting_sub_truncatedLogCounting_le` relate the counting functions of the
derivative `deriv f` to the counting functions and truncated counting functions of `f`.
-/

@[expose] public section

open Filter Function MeromorphicOn Metric Real Set

namespace Function.locallyFinsuppWithin

/-!
## The Truncated Counting Function of a Function with Locally Finite Support
-/

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/--
For `1 ≤ r`, the counting function of a truncated divisor is bounded above by the counting function
of the divisor itself.
-/
theorem logCounting_truncate_le (D : locallyFinsupp E ℤ) {r : ℝ} (hr : 1 ≤ r) :
    logCounting D.truncate₁ r ≤ logCounting D r := logCounting_le (D.truncate_le 1 _) hr

/-- For `1 ≤ r`, the counting function of a truncated non-negative divisor is non-negative. -/
theorem logCounting_truncate_nonneg {D : locallyFinsupp E ℤ} (h : 0 ≤ D) {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ logCounting D.truncate₁ r := logCounting_nonneg (truncate_nonneg 1 _ h) hr

end Function.locallyFinsuppWithin

/-!
## The Truncated Logarithmic Counting Function of a Meromorphic Function
-/

namespace ValueDistribution

open locallyFinsuppWithin

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {a : WithTop E} {a₀ : E}

variable (f a) in
/--
The truncated logarithmic counting function of Value Distribution Theory: like `logCounting f a`,
but counting each zero/pole once, regardless of multiplicity.  In the special case where `a = ⊤`, it
counts the poles of `f`, each with multiplicity one.
-/
noncomputable def truncatedLogCounting : ℝ → ℝ :=
  a.recTopCoe ((divisor f Set.univ)⁻.truncate₁).logCounting
    fun a₀ ↦ ((divisor (f · - a₀) Set.univ)⁺.truncate₁).logCounting

/--
The truncated logarithmic counting function `truncatedLogCounting f ⊤` counts the poles of `f`, each
with multiplicity one.
-/
lemma truncatedLogCounting_top :
    truncatedLogCounting f ⊤ = ((divisor f Set.univ)⁻.truncate₁).logCounting := rfl

/--
For finite values `a₀`, the truncated logarithmic counting function `truncatedLogCounting f a₀`
counts the zeros of `f - a₀`, each with multiplicity one.
-/
lemma truncatedLogCounting_coe :
    truncatedLogCounting f a₀ = ((divisor (f · - a₀) Set.univ)⁺.truncate₁).logCounting := rfl

attribute [local simp] truncatedLogCounting_top truncatedLogCounting_coe

/--
The truncated logarithmic counting function `truncatedLogCounting f 0` counts the zeros of `f`, each
with multiplicity one.
-/
lemma truncatedLogCounting_zero :
    truncatedLogCounting f 0 = ((divisor f Set.univ)⁺.truncate₁).logCounting := by
  simpa using truncatedLogCounting_coe (f := f) (a₀ := 0)

/-- Evaluation of the truncated logarithmic counting function at zero yields zero. -/
@[simp] lemma truncatedLogCounting_eval_zero :
    truncatedLogCounting f a 0 = 0 := by
  cases a <;> simp [truncatedLogCounting_top, truncatedLogCounting_coe]

/--
For `1 ≤ r`, the truncated logarithmic counting function is bounded above by the ordinary
logarithmic counting function.
-/
theorem truncatedLogCounting_le {r : ℝ} (hr : 1 ≤ r) :
    truncatedLogCounting f a r ≤ logCounting f a r := by
  cases a <;>
  simpa [logCounting_top, logCounting_coe] using logCounting_truncate_le _ hr

/-- For `1 ≤ r`, the truncated logarithmic counting function is non-negative. -/
theorem truncatedLogCounting_nonneg {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ truncatedLogCounting f a r := by
  cases a <;>
  simpa using logCounting_truncate_nonneg (by positivity) hr

/-- The truncated logarithmic counting function is monotonous. -/
theorem truncatedLogCounting_monotoneOn :
    MonotoneOn (truncatedLogCounting f a) (Set.Ioi 0) := by
  cases a <;>
  simpa using logCounting_mono <| truncate_nonneg 1 _ <| by positivity

/-- Relation between the truncated logarithmic counting functions of `f` and of `f⁻¹`. -/
@[simp] theorem truncatedLogCounting_inv {f : 𝕜 → 𝕜} :
    truncatedLogCounting f⁻¹ ⊤ = truncatedLogCounting f 0 := by
  simp [truncatedLogCounting_zero]

/--
If two functions differ only on a discrete set, then their truncated logarithmic counting functions
agree.
-/
theorem truncatedLogCounting_congr_codiscrete [NormedSpace ℂ E] {f g : ℂ → E}
    (hfg : f =ᶠ[codiscrete ℂ] g) :
    truncatedLogCounting f = truncatedLogCounting g := by
  ext a : 1
  cases a
  all_goals
    simp only [truncatedLogCounting_top, truncatedLogCounting_coe]
    congr! 3
    exact divisor_congr_codiscreteWithin (hfg.mono <| by simp) isOpen_univ

/-!
## Counting Functions of the Derivative
-/

/--
The poles of `deriv f` are exactly the poles of `f`, each with multiplicity increased by one:
the counting function for the poles of `deriv f` is the sum of the counting function and the
truncated counting function for the poles of `f`.
-/
theorem logCounting_deriv_top [CompleteSpace E] [CharZero 𝕜] (hf : Meromorphic f) :
    logCounting (deriv f) ⊤ = logCounting f ⊤ + truncatedLogCounting f ⊤ := by
  rw [logCounting_top, logCounting_top, truncatedLogCounting_top,
    hf.meromorphicOn.negPart_divisor_deriv, map_add]

/--
The `a`-points of `f`, for `a` in a finite set `s` and counted with multiplicity beyond the first,
are zeros of `deriv f`: for `1 ≤ r`, the differences between the counting functions and the
truncated counting functions for the `a`-points of `f` sum up to at most the counting function for
the zeros of `deriv f`.
-/
theorem sum_logCounting_sub_truncatedLogCounting_le [CompleteSpace E] [CharZero 𝕜]
    (hf : Meromorphic f) (s : Finset E) {r : ℝ} (hr : 1 ≤ r) :
    ∑ a ∈ s, (logCounting f a r - truncatedLogCounting f a r) ≤ logCounting (deriv f) 0 r := by
  calc ∑ a ∈ s, (logCounting f a r - truncatedLogCounting f a r)
    _ = (∑ a ∈ s, ((divisor (f · - a) univ)⁺ - (divisor (f · - a) univ)⁺.truncate₁)).logCounting
        r := by
      simp [logCounting_coe, truncatedLogCounting_coe]
    _ ≤ (divisor (deriv f) univ)⁺.logCounting r :=
      locallyFinsuppWithin.logCounting_le
        (hf.meromorphicOn.sum_posPart_divisor_sub_truncate_le_divisor_deriv s) hr
    _ = logCounting (deriv f) 0 r := by rw [logCounting_zero]

end ValueDistribution
