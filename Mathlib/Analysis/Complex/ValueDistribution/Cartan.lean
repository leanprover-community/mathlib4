/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Stefan Kebekus
-/

module

public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.IntegralPresentation

/-!
# Cartan's Formula

This file will, in the future, establish Cartan's classic formula, describing the characteristic
function `characteristic f ⊤ r` as a sum of two circle averages,

- `circleAverage (logCounting f · r) 0 1` and
- `circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1`.

As a corollary, Cartan's formula implies the (surprising, non-trival) fact that the characteristic
function is monotone.

## Main results

- Cartan's formula: `characteristic_top_eq_circleAverage_add_circleAverage`
- Monotonicity of the characteristic function `characteristic_monotoneOn`

## References

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.
-/

public section

open Filter Metric Real Set Topology

variable {f : ℂ → ℂ} {R : ℝ}

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
  · refine (circleIntegrable_congr fun a ha ↦ ?_).2 (circleIntegrable_const
      (log ‖meromorphicTrailingCoeffAt f 0‖) 0 1)
    rw [(MeromorphicAt.const a 0).meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt]
    rw [meromorphicOrderAt_const]
    aesop
  · apply CircleIntegrable.congr_codiscreteWithin
     (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero (not_not.1 h) hzero)
    simpa [norm_sub_rev] using circleIntegrable_log_norm_sub_const 1
  · apply (circleIntegrable_congr _).2 (circleIntegrable_const 0 0 1)
    exact fun _ ↦ log_trailingCoeff_eq_zero_on_unitSphere hpos

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
  by_cases hf : MeromorphicAt f 0
  · rw [← circleAverage_congr_codiscreteWithin
      (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero hf h) zero_ne_one.symm]
    simp_rw [norm_sub_rev]
    rw [circleAverage_log_norm_sub_const_eq_posLog]
  have {a : ℂ} : ¬ MeromorphicAt (fun x ↦ f x - a) 0 := by
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

/- Specialized Jensen-type identity -/
private lemma logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top
    (h : Meromorphic f) (hR : R ≠ 0) (a : ℂ) :
    logCounting f a R + log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ =
      circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R := by
  have : logCounting f a R - logCounting f ⊤ R = circleAverage (log ‖f · - a‖) 0 R
        - log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ := by
    rw [logCounting_coe_eq_logCounting_sub_const_zero, ← logCounting_sub_const h]
    exact logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const (by fun_prop) hR
  linarith

/--
Circle integrability of the term `logCounting f · R` that appears in Cartan's formula.
-/
theorem circleIntegrable_logCounting (h : Meromorphic f) :
    CircleIntegrable (logCounting f · R) 0 1 := by
  by_cases hR : R = 0
  · simp [hR, ValueDistribution.logCounting_eval_zero]
  let H1 := fun a ↦ circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R
  let H2 := fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖
  have : (fun a : ℂ ↦ logCounting f a R) = H1 - H2 := by
    ext a
    simpa [Pi.sub_apply, H1, H2] using eq_sub_of_add_eq
      (logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top h hR a)
  rw [this]
  exact CircleIntegrable.sub ((circleIntegrable_circleAverage_log_norm_sub h).add
      (circleIntegrable_const (logCounting f ⊤ R) 0 1))
    circleIntegrable_log_meromorphicTrailingCoeffAt

/-!
## Cartan's formula
-/

/--
**Cartan's formula** with the additive constant written explicitly as a circle average of the
logarithm of the first nonzero Laurent coefficient of `f - a` at the origin.

See `circleIntegrable_logCounting` and `circleIntegrable_log_trailingCoeff_of_meromorphic` for the
facts that the summands are acutally circle integrable.
-/
theorem characteristic_top_eq_circleAverage_add_circleAverage (h : Meromorphic f) (hR : R ≠ 0) :
    characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1
      + circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  calc characteristic f ⊤ R
    _ = circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R) 0 1 := by
      simp only [characteristic, proximity, ↓reduceDIte, Pi.add_apply]
      rw [← proximity_top, ← proximity_top_eq_circleAverage_circleAverage h,
        circleAverage_fun_add (circleIntegrable_circleAverage_log_norm_sub h)
          (circleIntegrable_const (logCounting f ⊤ R) 0 1), circleAverage_const]
    _ = circleAverage (logCounting f · R) 0 1
          + circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
      rw [← circleAverage_add (circleIntegrable_logCounting h)
        circleIntegrable_log_meromorphicTrailingCoeffAt, circleAverage_congr_sphere]
      intro a ha
      simp [logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top h hR a]

/--
**Cartan's formula** in case where `0 < meromorphicOrderAt f 0`.
-/
theorem characteristic_top_eq_circleAverage_of_meromorphicOrderAt_pos
    (h₁f : Meromorphic f) (h₂f : 0 < meromorphicOrderAt f 0) (hR : R ≠ 0) :
    characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1 := by
  rw [characteristic_top_eq_circleAverage_add_circleAverage h₁f hR]
  simp [circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos h₂f]

/--
Qualitative version of **Cartan's formula**: Away from `0`, the difference between
`characteristic f ⊤` and `circleAverage (logCounting f · ·) 0 1` is constant.
-/
theorem characteristic_top_eq_circleAverage_add_const (h : Meromorphic f) :
    ∃ const, ∀ R ≠ 0, characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1 + const :=
  ⟨circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1,
    fun _ hr ↦ characteristic_top_eq_circleAverage_add_circleAverage h hr⟩

/-!
## Application: Monotonicity of the Characteristic Function
-/

/--
The characteristic function is monotone on `(0, ∞)`.

This result is surprisingly non-trivial, given that the proximity function is not monotone in
general.
-/
theorem characteristic_monotoneOn (h : Meromorphic f) :
    MonotoneOn (characteristic f ⊤) (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [characteristic_top_eq_circleAverage_add_circleAverage h ha.ne',
    characteristic_top_eq_circleAverage_add_circleAverage h hb.ne']
  gcongr
  <;> try exact circleIntegrable_logCounting h
  exact logCounting_monotoneOn ha hb hab

end ValueDistribution
