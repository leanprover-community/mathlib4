/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Probability.Notation
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

#align_import probability.conditional_expectation from "leanprover-community/mathlib"@"2f8347015b12b0864dfaf366ec4909eb70c78740"

/-!

# Probabilistic properties of the conditional expectation

This file contains some properties about the conditional expectation which does not belong in
the main conditional expectation file.

## Main result

* `MeasureTheory.condexp_indep_eq`: If `m₁, m₂` are independent σ-algebras and `f` is an
  `m₁`-measurable function, then `𝔼[f | m₂] = 𝔼[f]` almost everywhere.

-/


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory BigOperators

namespace MeasureTheory

open ProbabilityTheory

variable {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {m₁ m₂ m : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → E}

/-- If `m₁, m₂` are independent σ-algebras and `f` is `m₁`-measurable, then `𝔼[f | m₂] = 𝔼[f]`
almost everywhere. -/
theorem condexp_indep_eq (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m) [SigmaFinite (μ.trim hle₂)]
    (hf : StronglyMeasurable[m₁] f) (hindp : Indep m₁ m₂ μ) : μ[f|m₂] =ᵐ[μ] fun _ => μ[f] := by
  by_cases hfint : Integrable f μ
  -- ⊢ μ[f|m₂] =ᵐ[μ] fun x => ∫ (x : Ω), f x ∂μ
  swap; · rw [condexp_undef hfint, integral_undef hfint]; rfl
  -- ⊢ μ[f|m₂] =ᵐ[μ] fun x => ∫ (x : Ω), f x ∂μ
          -- ⊢ 0 =ᵐ[μ] fun x => 0
                                                          -- 🎉 no goals
  refine' (ae_eq_condexp_of_forall_set_integral_eq hle₂ hfint
    (fun s _ hs => integrableOn_const.2 (Or.inr hs)) (fun s hms hs => _)
      stronglyMeasurable_const.aeStronglyMeasurable').symm
  rw [set_integral_const]
  -- ⊢ ENNReal.toReal (↑↑μ s) • ∫ (x : Ω), f x ∂μ = ∫ (x : Ω) in s, f x ∂μ
  rw [← memℒp_one_iff_integrable] at hfint
  -- ⊢ ENNReal.toReal (↑↑μ s) • ∫ (x : Ω), f x ∂μ = ∫ (x : Ω) in s, f x ∂μ
  refine' Memℒp.induction_stronglyMeasurable hle₁ ENNReal.one_ne_top _ _ _ _ hfint _
  · exact ⟨f, hf, EventuallyEq.rfl⟩
    -- 🎉 no goals
  · intro c t hmt _
    -- ⊢ ENNReal.toReal (↑↑μ s) • ∫ (x : Ω), Set.indicator t (fun x => c) x ∂μ = ∫ (x …
    rw [Indep_iff] at hindp
    -- ⊢ ENNReal.toReal (↑↑μ s) • ∫ (x : Ω), Set.indicator t (fun x => c) x ∂μ = ∫ (x …
    rw [integral_indicator (hle₁ _ hmt), set_integral_const, smul_smul, ← ENNReal.toReal_mul,
      mul_comm, ← hindp _ _ hmt hms, set_integral_indicator (hle₁ _ hmt), set_integral_const,
      Set.inter_comm]
  · intro u v _ huint hvint hu hv hu_eq hv_eq
    -- ⊢ ENNReal.toReal (↑↑μ s) • ∫ (x : Ω), (u + v) x ∂μ = ∫ (x : Ω) in s, (u + v) x …
    rw [memℒp_one_iff_integrable] at huint hvint
    -- ⊢ ENNReal.toReal (↑↑μ s) • ∫ (x : Ω), (u + v) x ∂μ = ∫ (x : Ω) in s, (u + v) x …
    rw [integral_add' huint hvint, smul_add, hu_eq, hv_eq,
      integral_add' huint.integrableOn hvint.integrableOn]
  · have heq₁ : (fun f : lpMeas E ℝ m₁ 1 μ => ∫ x, (f : Ω → E) x ∂μ) =
        (fun f : Lp E 1 μ => ∫ x, f x ∂μ) ∘ Submodule.subtypeL _ := by
      refine' funext fun f => integral_congr_ae _
      simp_rw [Submodule.coe_subtypeL', Submodule.coeSubtype]; norm_cast
    have heq₂ : (fun f : lpMeas E ℝ m₁ 1 μ => ∫ x in s, (f : Ω → E) x ∂μ) =
        (fun f : Lp E 1 μ => ∫ x in s, f x ∂μ) ∘ Submodule.subtypeL _ := by
      refine' funext fun f => integral_congr_ae (ae_restrict_of_ae _)
      simp_rw [Submodule.coe_subtypeL', Submodule.coeSubtype]
      exact eventually_of_forall fun _ => (by trivial)
    refine' isClosed_eq (Continuous.const_smul _ _) _
    -- ⊢ Continuous fun f => ∫ (x : Ω), ↑↑↑f x ∂μ
    · rw [heq₁]
      -- ⊢ Continuous ((fun f => ∫ (x : Ω), ↑↑f x ∂μ) ∘ ↑(Submodule.subtypeL (lpMeas E  …
      exact continuous_integral.comp (ContinuousLinearMap.continuous _)
      -- 🎉 no goals
    · rw [heq₂]
      -- ⊢ Continuous ((fun f => ∫ (x : Ω) in s, ↑↑f x ∂μ) ∘ ↑(Submodule.subtypeL (lpMe …
      exact (continuous_set_integral _).comp (ContinuousLinearMap.continuous _)
      -- 🎉 no goals
  · intro u v huv _ hueq
    -- ⊢ ENNReal.toReal (↑↑μ s) • ∫ (x : Ω), v x ∂μ = ∫ (x : Ω) in s, v x ∂μ
    rwa [← integral_congr_ae huv, ←
      (set_integral_congr_ae (hle₂ _ hms) _ : ∫ x in s, u x ∂μ = ∫ x in s, v x ∂μ)]
    filter_upwards [huv] with x hx _ using hx
    -- 🎉 no goals
#align measure_theory.condexp_indep_eq MeasureTheory.condexp_indep_eq

end MeasureTheory
