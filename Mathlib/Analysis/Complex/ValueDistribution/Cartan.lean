/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Stefan Kebekus
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# Cartan's Formula

This file will, in the future, establish Cartan's classic formula, describing the characteristic
function `characteristic f ⊤ r` as a sum of two circle averages,

- `circleAverage (logCounting f · r) 0 1` and
- `circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1`.

As a corollary, Cartan's formula implies the (surprising, non-trival) fact that the characteristic
function is monotone.

At present, this file establishes circle integrability of the function
`a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖` and computes values of the circle integral.

## References

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.


## TODO

- Establish Cartan's Formula in full
- Prove monotonicity of the characteristic function
-/

public section

open Filter Metric Real Set Topology

variable {f : ℂ → ℂ}

namespace ValueDistribution

/-!
## Terms in Cartan's formula
-/

private lemma log_trailingCoeff_eq_zero_on_unitSphere {a : ℂ} (h : 0 < meromorphicOrderAt f 0)
    (ha : a ∈ sphere 0 |1|) :
    log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ = 0 := by
  simp_rw [sub_eq_neg_add]
  rw [(meromorphicAt_of_meromorphicOrderAt_ne_zero
    h.ne').meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt]
  · aesop
  · rw [meromorphicOrderAt_const]
    aesop

private lemma eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero (h₁ : MeromorphicAt f 0)
    (h₂ : meromorphicOrderAt f 0 = 0) :
    (log ‖meromorphicTrailingCoeffAt f 0 - ·‖) =ᶠ[codiscreteWithin (sphere 0 |1|)]
      fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ := by
  filter_upwards [self_mem_codiscreteWithin (sphere 0 |1|), compl_singleton_mem_codiscreteWithin
    (meromorphicTrailingCoeffAt f 0)] with a ha_sphere ha_ne
  congr
  rw [h₁.meromorphicTrailingCoeffAt_fun_sub_eq_sub
    (by fun_prop), meromorphicTrailingCoeffAt_const, sub_eq_add_neg]
  · simp only [meromorphicOrderAt_const]
    aesop
  · simp only [meromorphicTrailingCoeffAt_const, ne_eq]
    grind

/--
Circle integrability of the term `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖` that
appears in Cartan's formula.
-/
theorem circleIntegrable_log_meromorphicTrailingCoeffAt :
    CircleIntegrable (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  by_cases h: ¬MeromorphicAt f 0
  · have {a : ℂ} : ¬MeromorphicAt (fun x ↦ f x - a) 0 := by
      rwa [MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt₂ (by fun_prop)]
    simp_all
  rcases lt_trichotomy (meromorphicOrderAt f 0) 0 with hneg | hzero | hpos
  · apply (circleIntegrable_congr _).2 (circleIntegrable_const
      (log ‖meromorphicTrailingCoeffAt f 0‖) 0 1)
    intro a ha
    simp only
    rw [(MeromorphicAt.const a 0).meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt]
    rw [meromorphicOrderAt_const]
    aesop
  · apply CircleIntegrable.congr_codiscreteWithin
     (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero (not_not.1 h) hzero)
    convert circleIntegrable_log_norm_sub_const (a := meromorphicTrailingCoeffAt f 0) 1 using 1
    simp_rw [norm_sub_rev]
  · apply (circleIntegrable_congr _).2 (circleIntegrable_const 0 0 1)
    exact fun x hx ↦ log_trailingCoeff_eq_zero_on_unitSphere hpos hx

/--
Circle average of the function `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖` that appears
in Cartan's formula, in case where `f` has a zero at the origin.
-/
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos
    (h : 0 < meromorphicOrderAt f 0) :
    circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 = 0 :=
  circleAverage_const_on_circle (fun _ hx ↦ log_trailingCoeff_eq_zero_on_unitSphere h hx)

/--
Circle average of the function `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖` that appears
in Cartan's formula, in case where  `f` has order zero at the origin.
-/
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_eq_zero
    (h : meromorphicOrderAt f 0 = 0) :
    circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1
      = log⁺ ‖meromorphicTrailingCoeffAt f 0‖ := by
  by_cases hf: MeromorphicAt f 0
  · rw [← circleAverage_congr_codiscreteWithin
      (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero hf h) zero_ne_one.symm]
    simp_rw [norm_sub_rev]
    rw [circleAverage_log_norm_sub_const_eq_posLog]
  simp_all
  have {a : ℂ} : ¬MeromorphicAt (fun x ↦ f x - a) 0 := by
    rwa [MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt₂ (by fun_prop)]
  simp_all [circleAverage_const]

/--
Circle average of the function `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖` that appears
in Cartan's formula, in case where `f` has a pole at the origin.
-/
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_lt_zero
    (h : meromorphicOrderAt f 0 < 0) :
    circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1
      = log ‖meromorphicTrailingCoeffAt f 0‖ := by
  rw [circleAverage_congr_sphere (f₂ := fun _ ↦ log ‖meromorphicTrailingCoeffAt f 0‖),
    circleAverage_const]
  intro a ha
  simp only
  congr 2
  rw [(MeromorphicAt.const a 0).meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt]
  rw [meromorphicOrderAt_const]
  aesop

end ValueDistribution
