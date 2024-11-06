import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalProbability

open MeasureTheory Set Filter TopologicalSpace MeasurableSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/- We show that, for `s : Set α`, denoting `ms = generateFrom {s}`, for any `x ∈ s`, we have
`μ[|s] = μ[|ms] x`. -/

variable {Ω F : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {s t : Set Ω}
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma condexp_generateFrom_singleton (hs : MeasurableSet s) {f : Ω → F} (hf : Integrable f μ) :
    μ[f | MeasurableSpace.generateFrom {s}] =ᵐ[μ.restrict s]
    fun _ ↦ ∫ x, f x ∂μ[|s] := by
  by_cases hμs : μ s = 0
  · rw [Measure.restrict_eq_zero.2 hμs]
    rfl
  refine ae_eq_trans (condexp_restrict_ae_eq_restrict
    (MeasurableSpace.generateFrom_singleton_le hs)
    (MeasurableSpace.measurableSet_generateFrom rfl) hf).symm ?_
  · refine (ae_eq_condexp_of_forall_setIntegral_eq
      (MeasurableSpace.generateFrom_singleton_le hs) hf.restrict ?_ ?_
      stronglyMeasurable_const.aeStronglyMeasurable').symm
    · rintro t - -
      rw [integrableOn_const]
      exact Or.inr <| measure_lt_top (μ.restrict s) t
    · rintro t ht -
      obtain (h | h | h | h) := measurableSet_generateFrom_singleton_iff.1 ht
      · simp [h]
      · simp only [h, cond, integral_smul_measure, ENNReal.toReal_inv, integral_const,
          MeasurableSet.univ, Measure.restrict_apply, univ_inter, Measure.restrict_apply_self]
        rw [smul_inv_smul₀, Measure.restrict_restrict hs, inter_self]
        exact ENNReal.toReal_ne_zero.2 ⟨hμs, measure_ne_top _ _⟩
      · simp only [h, integral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
          ((Measure.restrict_apply_eq_zero hs.compl).2 <| compl_inter_self s ▸ measure_empty),
          ENNReal.zero_toReal, zero_smul, setIntegral_zero_measure]
      · simp only [h, Measure.restrict_univ, cond, integral_smul_measure, ENNReal.toReal_inv,
          integral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
          smul_inv_smul₀ <| ENNReal.toReal_ne_zero.2 ⟨hμs, measure_ne_top _ _⟩]

lemma condexp_set_generateFrom_singleton (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ⟦t | MeasurableSpace.generateFrom {s}⟧ =ᵐ[μ.restrict s]
    fun _ ↦ (μ[t|s]).toReal := by
  rw [← integral_indicator_one ht]
  exact condexp_generateFrom_singleton hs <| Integrable.indicator (integrable_const 1) ht

lemma condexpKernel_ae_eq_cond [StandardBorelSpace Ω] (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    ∀ᵐ ω ∂μ.restrict s,
      condexpKernel μ (MeasurableSpace.generateFrom {s}) ω t = μ[t|s] := by
  have : (fun ω ↦ (condexpKernel μ (MeasurableSpace.generateFrom {s}) ω t).toReal) =ᵐ[μ.restrict s]
      μ⟦t | MeasurableSpace.generateFrom {s}⟧ :=
    ae_restrict_le μ hs <| condexpKernel_ae_eq_condexp
      (MeasurableSpace.generateFrom_singleton_le hs) ht
  filter_upwards [condexp_set_generateFrom_singleton hs ht, this] with ω hω₁ hω₂
  rwa [hω₁, ENNReal.toReal_eq_toReal (measure_ne_top _ t) (measure_ne_top _ t)] at hω₂

end ProbabilityTheory
