/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Ville's inequality

A nonnegative supermartingale reaches a positive threshold on a set of measure at most its initial
expectation divided by that threshold. We prove both the finite-horizon inequality and the
inequality over all natural-number times. Nonnegativity is only required almost everywhere at
each time.

## Main results

* `MeasureTheory.Supermartingale.ville_ineq_finite`: Ville's inequality up to a fixed time.
* `MeasureTheory.Supermartingale.ville_ineq`: Ville's inequality over all natural-number times.
-/

public section

open scoped ENNReal ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

namespace Supermartingale

private lemma expected_stoppedValue_le_initial (hf : Supermartingale f 𝒢 μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hN : ∀ ω, τ ω ≤ N) :
    μ[stoppedValue f τ] ≤ μ[f 0] := by
  have h := hf.neg.expected_stoppedValue_mono
    (isStoppingTime_const 𝒢 0) hτ (fun _ ↦ bot_le) hN
  simpa [stoppedValue_const, stoppedValue, Pi.neg_apply, integral_neg] using h

/-- **Ville's inequality** up to a fixed time: a nonnegative supermartingale reaches a positive
threshold on a set of measure at most its initial expectation divided by the threshold. -/
theorem ville_ineq_finite (hf : Supermartingale f 𝒢 μ) (hnonneg : ∀ n, 0 ≤ᵐ[μ] f n)
    {a : ℝ} (ha : 0 < a) (N : ℕ) :
    μ.real {ω | ∃ k ≤ N, a ≤ f k ω} ≤ μ[f 0] / a := by
  let τ : Ω → WithTop ℕ := fun ω ↦ (hittingBtwn f (Set.Ici a) 0 N ω : ℕ)
  have hτ : IsStoppingTime 𝒢 τ :=
    hf.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hN (ω) : τ ω ≤ N := WithTop.coe_le_coe.mpr (hittingBtwn_le ω)
  have hint : Integrable (stoppedValue f τ) μ :=
    integrable_stoppedValue ℕ hτ hf.integrable hN
  have hnonnegτ : 0 ≤ᵐ[μ] stoppedValue f τ :=
    (ae_all_iff.mpr hnonneg).mono fun _ hω ↦ hω _
  have hsub : {ω | ∃ k ≤ N, a ≤ f k ω} ⊆ {ω | a ≤ stoppedValue f τ ω} := by
    rintro ω ⟨k, hk, hfk⟩
    exact stoppedValue_hittingBtwn_mem (u := f) (s := Set.Ici a) (n := 0) (m := N)
      ⟨k, ⟨Nat.zero_le _, hk⟩, hfk⟩
  apply (le_div_iff₀ ha).mpr
  calc
    μ.real {ω | ∃ k ≤ N, a ≤ f k ω} * a
      ≤ μ.real {ω | a ≤ stoppedValue f τ ω} * a :=
        mul_le_mul_of_nonneg_right (measureReal_mono hsub) ha.le
    _ ≤ μ[stoppedValue f τ] := by
      simpa [mul_comm] using mul_meas_ge_le_integral_of_nonneg hnonnegτ hint a
    _ ≤ μ[f 0] := hf.expected_stoppedValue_le_initial hτ hN

/-- **Ville's inequality**: a nonnegative supermartingale reaches a positive threshold on a set of
measure at most its initial expectation divided by the threshold. -/
theorem ville_ineq (hf : Supermartingale f 𝒢 μ) (hnonneg : ∀ n, 0 ≤ᵐ[μ] f n)
    {a : ℝ} (ha : 0 < a) : μ.real {ω | ∃ n, a ≤ f n ω} ≤ μ[f 0] / a := by
  rw [Set.ofPred_exists, measureReal_def, measure_iUnion_eq_iSup_accumulate,
    ENNReal.toReal_iSup (fun _ ↦ measure_ne_top _ _)]
  refine ciSup_le fun N ↦ ?_
  simpa only [Set.accumulate, ← Set.ofPred_exists, exists_prop, measureReal_def] using
    hf.ville_ineq_finite hnonneg ha N

end Supermartingale

end MeasureTheory
