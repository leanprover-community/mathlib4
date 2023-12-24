/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Divergences.KullbackLeibler

/-!
# E-Values

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y : Ω → ℝ} {S T : Set (Measure Ω)}

structure IsEValue (X : Ω → ℝ) (S : Set (Measure Ω)) : Prop :=
(integrable : ∀ μ ∈ S, Integrable X μ)
(nonneg : 0 ≤ X)
(integral_le_one : ∀ μ ∈ S, ∫ ω, X ω ∂μ ≤ 1)

lemma IsEValue.mono (hXY : X ≤ Y) (hST : S ⊆ T) (h : IsEValue Y T)
    (hX_nonneg : 0 ≤ X) (hX_int : ∀ μ ∈ S, Integrable X μ) :
    IsEValue X S where
  integrable := hX_int
  nonneg := hX_nonneg
  integral_le_one := fun μ hμS ↦ (integral_mono (hX_int μ hμS) (h.integrable μ (hST hμS)) hXY).trans
    (h.integral_le_one μ (hST hμS))

lemma isEValue_exp (h_ne_zero : ∀ μ ∈ S, NeZero μ)
    (h_int : ∀ μ ∈ S, Integrable (fun ω ↦ exp (X ω)) μ)
    (h_log : ∀ μ ∈ S, log (∫ ω, exp (X ω) ∂μ) ≤ 0) :
    IsEValue (fun ω ↦ exp (X ω)) S where
  integrable := h_int
  nonneg := fun x ↦ (exp_pos _).le
  integral_le_one := fun μ hμS ↦ by
    rw [← Real.log_le_log_iff _ zero_lt_one]
    · simp only [log_one]
      exact h_log μ hμS
    · have := h_ne_zero μ hμS
      exact integral_exp_pos (h_int μ hμS)

lemma isEValue_exp_sub_logIntegralExp (h_ne_zero : ∀ μ ∈ S, NeZero μ)
    (h_int : ∀ μ ∈ S, Integrable (fun ω ↦ exp (X ω)) μ)
    (h_bdd : BddAbove (Set.range fun μ ↦ ⨆ (_ : μ ∈ S), log (∫ ω, exp (X ω) ∂μ))) :
   IsEValue (fun ω ↦ exp (X ω - ⨆ μ ∈ S, log (∫ ω, exp (X ω) ∂μ))) S where
  integrable := fun μ hμS ↦ by
    simp_rw [exp_sub]
    exact Integrable.div_const (h_int μ hμS) _
  nonneg := fun x ↦ (exp_pos _).le
  integral_le_one := fun μ hμS ↦ by
    rw [← Real.log_le_log_iff _ zero_lt_one]
    · simp only [log_one, exp_sub]
      rw [integral_div, log_div]
      · simp only [log_exp, tsub_le_iff_right, zero_add]
        change log (∫ ω, exp (X ω) ∂μ) ≤ ⨆ μ ∈ S, log (∫ ω, exp (X ω) ∂μ)
        refine le_ciSup_of_le h_bdd μ ?_
        simp [hμS]
      · have := h_ne_zero μ hμS
        exact (integral_exp_pos (h_int μ hμS)).ne'
      · exact (exp_pos _).ne'
    · have := h_ne_zero μ hμS
      refine integral_exp_pos ?_
      simp_rw [exp_sub]
      exact Integrable.div_const (h_int μ hμS) _

theorem DonskerVaradhan_eValue {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ ν x ∂μ
      = ⨆ (f : Ω → ℝ) (_ : Integrable (fun x ↦ log (f x)) μ) (_ : IsEValue f {ν}),
        ∫ x, log (f x) ∂μ - log (∫ x, f x ∂ν) := by
  rw [DonskerVaradhan hμν h_int]
  apply le_antisymm
  · refine ciSup_le (fun f ↦ ?_)
    refine le_ciSup_of_le ?_ (fun x ↦ exp (f x - log (∫ ω, exp (X ω) ∂μ))) ?_
    · sorry
    · simp only [log_exp]
      by_cases hfμ : Integrable f μ
      · simp only [hfμ, ciSup_unique]
        by_cases hf : Integrable (fun x ↦ exp (f x)) ν
        · simp only [hf, ciSup_unique]
          have : IsEValue (fun x ↦ exp (f x)) {ν} := isEValue_exp ?_ ?_ ?_
          · sorry
          · simp only [Set.mem_singleton_iff, forall_eq]; infer_instance
          · simpa using hf
          sorry
          --· simp only [Set.mem_singleton_iff, forall_eq]
          --exact integral_sub_logIntegralExp_le hμν h_int f hfμ hf
        · simp only [hf, ciSup_empty]
          sorry
          --exact integral_llr_nonneg hμν h_int
      · simp only [hfμ, ciSup_empty]
        sorry
        --exact integral_llr_nonneg hμν h_int
  · sorry

end MeasureTheory
