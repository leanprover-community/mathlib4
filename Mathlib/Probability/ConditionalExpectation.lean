/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

! This file was ported from Lean 3 source module probability.conditional_expectation
! leanprover-community/mathlib commit 2f8347015b12b0864dfaf366ec4909eb70c78740
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Probability.Notation
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!

# Probabilistic properties of the conditional expectation

This file contains some properties about the conditional expectation which does not belong in
the main conditional expectation file.

## Main result

* `measure_theory.condexp_indep_eq`: If `m₁, m₂` are independent σ-algebras and `f` is a
  `m₁`-measurable function, then `𝔼[f | m₂] = 𝔼[f]` almost everywhere.

-/


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory BigOperators

namespace MeasureTheory

open ProbabilityTheory

variable {Ω E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {m₁ m₂ m : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → E}

/-- If `m₁, m₂` are independent σ-algebras and `f` is `m₁`-measurable, then `𝔼[f | m₂] = 𝔼[f]`
almost everywhere. -/
theorem condexp_indep_eq (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m) [SigmaFinite (μ.trim hle₂)]
    (hf : strongly_measurable[m₁] f) (hindp : Indep m₁ m₂ μ) : μ[f|m₂] =ᵐ[μ] fun x => μ[f] := by
  by_cases hfint : integrable f μ
  swap; · rw [condexp_undef hfint, integral_undef hfint]; rfl
  have hfint₁ := hfint.trim hle₁ hf
  refine'
    (ae_eq_condexp_of_forall_set_integral_eq hle₂ hfint
        (fun s _ hs => integrable_on_const.2 (Or.inr hs)) (fun s hms hs => _)
        strongly_measurable_const.ae_strongly_measurable').symm
  rw [set_integral_const]
  rw [← mem_ℒp_one_iff_integrable] at hfint 
  refine' hfint.induction_strongly_measurable hle₁ ENNReal.one_ne_top _ _ _ _ _ _
  · intro c t hmt ht
    rw [integral_indicator (hle₁ _ hmt), set_integral_const, smul_smul, ← ENNReal.toReal_mul,
      mul_comm, ← hindp _ _ hmt hms, set_integral_indicator (hle₁ _ hmt), set_integral_const,
      Set.inter_comm]
  · intro u v hdisj huint hvint hu hv hu_eq hv_eq
    rw [mem_ℒp_one_iff_integrable] at huint hvint 
    rw [integral_add' huint hvint, smul_add, hu_eq, hv_eq,
      integral_add' huint.integrable_on hvint.integrable_on]
  · have heq₁ :
      (fun f : Lp_meas E ℝ m₁ 1 μ => ∫ x, f x ∂μ) =
        (fun f : Lp E 1 μ => ∫ x, f x ∂μ) ∘ Submodule.subtypeL _ := by
      refine' funext fun f => integral_congr_ae _
      simp_rw [Submodule.coe_subtypeL', Submodule.coeSubtype, ← coeFn_coeBase]
    have heq₂ :
      (fun f : Lp_meas E ℝ m₁ 1 μ => ∫ x in s, f x ∂μ) =
        (fun f : Lp E 1 μ => ∫ x in s, f x ∂μ) ∘ Submodule.subtypeL _ := by
      refine' funext fun f => integral_congr_ae (ae_restrict_of_ae _)
      simp_rw [Submodule.coe_subtypeL', Submodule.coeSubtype, ← coeFn_coeBase]
      exact eventually_of_forall fun _ => rfl
    refine' isClosed_eq (Continuous.const_smul _ _) _
    · rw [heq₁]
      exact continuous_integral.comp (ContinuousLinearMap.continuous _)
    · rw [heq₂]
      exact (continuous_set_integral _).comp (ContinuousLinearMap.continuous _)
  · intro u v huv huint hueq
    rwa [← integral_congr_ae huv, ←
      (set_integral_congr_ae (hle₂ _ hms) _ : ∫ x in s, u x ∂μ = ∫ x in s, v x ∂μ)]
    filter_upwards [huv] with x hx _ using hx
  · exact ⟨f, hf, eventually_eq.rfl⟩
#align measure_theory.condexp_indep_eq MeasureTheory.condexp_indep_eq

end MeasureTheory

