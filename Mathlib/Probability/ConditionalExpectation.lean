/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Notation
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!

# Probabilistic properties of the conditional expectation

This file contains some properties about the conditional expectation which does not belong in
the main conditional expectation file.

## Main result

* `MeasureTheory.condExp_indep_eq`: If `m₁, m₂` are independent σ-algebras and `f` is an
  `m₁`-measurable function, then `𝔼[f | m₂] = 𝔼[f]` almost everywhere.

-/

public section


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {m₁ m₂ m : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → E}

/-- If `m₁, m₂` are independent σ-algebras and `f` is `m₁`-measurable, then `𝔼[f | m₂] = 𝔼[f]`
almost everywhere. -/
theorem condExp_indep_eq (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m) [SigmaFinite (μ.trim hle₂)]
    (hf : StronglyMeasurable[m₁] f) (hindp : Indep m₁ m₂ μ) : μ[f | m₂] =ᵐ[μ] fun _ => μ[f] := by
  by_cases hfint : Integrable f μ
  swap; · rw [condExp_of_not_integrable hfint, integral_undef hfint]; rfl
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle₂ hfint
    (fun s _ hs ↦ integrableOn_const hs.ne) (fun s hms hs => ?_)
      stronglyMeasurable_const.aestronglyMeasurable).symm
  rw [setIntegral_const]
  rw [← memLp_one_iff_integrable] at hfint
  refine MemLp.induction_stronglyMeasurable hle₁ ENNReal.one_ne_top _ ?_ ?_ ?_ ?_ hfint ?_
  · exact ⟨f, hf, EventuallyEq.rfl⟩
  · intro c t hmt _
    rw [Indep_iff] at hindp
    rw [integral_indicator (hle₁ _ hmt), setIntegral_const, smul_smul, measureReal_def,
      measureReal_def, ← ENNReal.toReal_mul,
      mul_comm, ← hindp _ _ hmt hms, setIntegral_indicator (hle₁ _ hmt), setIntegral_const,
      Set.inter_comm, measureReal_def]
  · intro u v _ huint hvint hu hv hu_eq hv_eq
    rw [memLp_one_iff_integrable] at huint hvint
    rw [integral_add' huint hvint, smul_add, hu_eq, hv_eq,
      integral_add' huint.integrableOn hvint.integrableOn]
  · have h_integral : Continuous fun f : lpMeas E ℝ m₁ 1 μ => ∫ x, (f : Ω → E) x ∂μ := by
      simpa using continuous_integral.comp (ContinuousLinearMap.continuous (Submodule.subtypeL _))
    have h_setIntegral : Continuous fun f : lpMeas E ℝ m₁ 1 μ => ∫ x in s, (f : Ω → E) x ∂μ := by
      simpa using (continuous_setIntegral s).comp
        (ContinuousLinearMap.continuous (Submodule.subtypeL _))
    exact isClosed_eq (Continuous.const_smul h_integral _) h_setIntegral
  · intro u v huv _ hueq
    rwa [← integral_congr_ae huv, ←
      (setIntegral_congr_ae (hle₂ _ hms) _ : ∫ x in s, u x ∂μ = ∫ x in s, v x ∂μ)]
    filter_upwards [huv] with x hx _ using hx

end MeasureTheory
