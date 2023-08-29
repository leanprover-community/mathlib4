/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration
import Mathlib.Probability.Notation

#align_import probability.kernel.cond_distrib from "leanprover-community/mathlib"@"00abe0695d8767201e6d008afa22393978bb324d"

/-!
# Regular conditional probability distribution

We define the regular conditional probability distribution of `Y : α → Ω` given `X : α → β`, where
`Ω` is a standard Borel space. This is a `kernel β Ω` such that for almost all `a`, `condDistrib`
evaluated at `X a` and a measurable set `s` is equal to the conditional expectation
`μ⟦Y ⁻¹' s | mβ.comap X⟧` evaluated at `a`.

`μ⟦Y ⁻¹' s | mβ.comap X⟧` maps a measurable set `s` to a function `α → ℝ≥0∞`, and for all `s` that
map is unique up to a `μ`-null set. For all `a`, the map from sets to `ℝ≥0∞` that we obtain that way
verifies some of the properties of a measure, but in general the fact that the `μ`-null set depends
on `s` can prevent us from finding versions of the conditional expectation that combine into a true
measure. The standard Borel space assumption on `Ω` allows us to do so.

The case `Y = X = id` is developed in more detail in `Probability/Kernel/Condexp.lean`: here `X` is
understood as a map from `Ω` with a sub-σ-algebra `m` to `Ω` with its default σ-algebra and the
conditional distribution defines a kernel associated with the conditional expectation with respect
to `m`.

## Main definitions

* `condDistrib Y X μ`: regular conditional probability distribution of `Y : α → Ω` given
  `X : α → β`, where `Ω` is a standard Borel space.

## Main statements

* `condDistrib_ae_eq_condexp`: for almost all `a`, `condDistrib` evaluated at `X a` and a
  measurable set `s` is equal to the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`.
* `condexp_prod_ae_eq_integral_condDistrib`: the conditional expectation
  `μ[(fun a => f (X a, Y a)) | X; mβ]` is almost everywhere equal to the integral
  `∫ y, f (X a, y) ∂(condDistrib Y X μ (X a))`.

-/


open MeasureTheory Set Filter TopologicalSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {α β Ω F : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [PolishSpace Ω] [BorelSpace Ω]
  [Nonempty Ω] [NormedAddCommGroup F] {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
  {X : α → β} {Y : α → Ω}

/-- **Regular conditional probability distribution**: kernel associated with the conditional
expectation of `Y` given `X`.
For almost all `a`, `condDistrib Y X μ` evaluated at `X a` and a measurable set `s` is equal to
the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`. It also satisfies the equality
`μ[(fun a => f (X a, Y a)) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂(condDistrib Y X μ (X a))`
for all integrable functions `f`. -/
noncomputable irreducible_def condDistrib {_ : MeasurableSpace α} [MeasurableSpace β] (Y : α → Ω)
    (X : α → β) (μ : Measure α) [IsFiniteMeasure μ] : kernel β Ω :=
  (μ.map fun a => (X a, Y a)).condKernel
#align probability_theory.cond_distrib ProbabilityTheory.condDistrib

instance [MeasurableSpace β] : IsMarkovKernel (condDistrib Y X μ) := by
  rw [condDistrib]; infer_instance
  -- ⊢ IsMarkovKernel (Measure.condKernel (Measure.map (fun a => (X a, Y a)) μ))
                    -- 🎉 no goals

variable {mβ : MeasurableSpace β} {s : Set Ω} {t : Set β} {f : β × Ω → F}

section Measurability

theorem measurable_condDistrib (hs : MeasurableSet s) :
    Measurable[mβ.comap X] fun a => condDistrib Y X μ (X a) s :=
  (kernel.measurable_coe _ hs).comp (Measurable.of_comap_le le_rfl)
#align probability_theory.measurable_cond_distrib ProbabilityTheory.measurable_condDistrib

theorem _root_.MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    (∀ᵐ a ∂μ.map X, Integrable (fun ω => f (a, ω)) (condDistrib Y X μ a)) ∧
      Integrable (fun a => ∫ ω, ‖f (a, ω)‖ ∂condDistrib Y X μ a) (μ.map X) ↔
    Integrable f (μ.map fun a => (X a, Y a)) := by
  rw [condDistrib, ← hf.ae_integrable_condKernel_iff, Measure.fst_map_prod_mk₀ hY]
  -- 🎉 no goals
#align measure_theory.ae_strongly_measurable.ae_integrable_cond_distrib_map_iff MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff

variable [NormedSpace ℝ F] [CompleteSpace F]

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂condDistrib Y X μ x) (μ.map X) := by
  rw [← Measure.fst_map_prod_mk₀ hY, condDistrib]; exact hf.integral_condKernel
  -- ⊢ AEStronglyMeasurable (fun x => ∫ (y : Ω), f (x, y) ∂↑(Measure.condKernel (Me …
                                                   -- 🎉 no goals
#align measure_theory.ae_strongly_measurable.integral_cond_distrib_map MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf.integral_condDistrib_map hY).comp_aemeasurable hX
#align measure_theory.ae_strongly_measurable.integral_cond_distrib MeasureTheory.AEStronglyMeasurable.integral_condDistrib

theorem aestronglyMeasurable'_integral_condDistrib (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable' (mβ.comap X) (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf.integral_condDistrib_map hY).comp_ae_measurable' hX
#align probability_theory.ae_strongly_measurable'_integral_cond_distrib ProbabilityTheory.aestronglyMeasurable'_integral_condDistrib

end Measurability

section Integrability

theorem integrable_toReal_condDistrib (hX : AEMeasurable X μ) (hs : MeasurableSet s) :
    Integrable (fun a => (condDistrib Y X μ (X a) s).toReal) μ := by
  refine' integrable_toReal_of_lintegral_ne_top _ _
  -- ⊢ AEMeasurable fun a => ↑↑(↑(condDistrib Y X μ) (X a)) s
  · exact Measurable.comp_aemeasurable (kernel.measurable_coe _ hs) hX
    -- 🎉 no goals
  · refine' ne_of_lt _
    -- ⊢ ∫⁻ (x : α), ↑↑(↑(condDistrib Y X μ) (X x)) s ∂μ < ⊤
    calc
      ∫⁻ a, condDistrib Y X μ (X a) s ∂μ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun a => prob_le_one
      _ = μ univ := lintegral_one
      _ < ∞ := measure_lt_top _ _
#align probability_theory.integrable_to_real_cond_distrib ProbabilityTheory.integrable_toReal_condDistrib

theorem _root_.MeasureTheory.Integrable.condDistrib_ae_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    ∀ᵐ b ∂μ.map X, Integrable (fun ω => f (b, ω)) (condDistrib Y X μ b) := by
  rw [condDistrib, ← Measure.fst_map_prod_mk₀ (X := X) hY]; exact hf_int.condKernel_ae
  -- ⊢ ∀ᵐ (b : β) ∂Measure.fst (Measure.map (fun a => (X a, Y a)) μ), Integrable fu …
                                                            -- 🎉 no goals
#align measure_theory.integrable.cond_distrib_ae_map MeasureTheory.Integrable.condDistrib_ae_map

theorem _root_.MeasureTheory.Integrable.condDistrib_ae (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    ∀ᵐ a ∂μ, Integrable (fun ω => f (X a, ω)) (condDistrib Y X μ (X a)) :=
  ae_of_ae_map hX (hf_int.condDistrib_ae_map hY)
#align measure_theory.integrable.cond_distrib_ae MeasureTheory.Integrable.condDistrib_ae

theorem _root_.MeasureTheory.Integrable.integral_norm_condDistrib_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂condDistrib Y X μ x) (μ.map X) := by
  rw [condDistrib, ← Measure.fst_map_prod_mk₀ (X := X) hY]; exact hf_int.integral_norm_condKernel
  -- ⊢ Integrable fun x => ∫ (y : Ω), ‖f (x, y)‖ ∂↑(Measure.condKernel (Measure.map …
                                                            -- 🎉 no goals
#align measure_theory.integrable.integral_norm_cond_distrib_map MeasureTheory.Integrable.integral_norm_condDistrib_map

theorem _root_.MeasureTheory.Integrable.integral_norm_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ∫ y, ‖f (X a, y)‖ ∂condDistrib Y X μ (X a)) μ :=
  (hf_int.integral_norm_condDistrib_map hY).comp_aemeasurable hX
#align measure_theory.integrable.integral_norm_cond_distrib MeasureTheory.Integrable.integral_norm_condDistrib

variable [NormedSpace ℝ F] [CompleteSpace F]

theorem _root_.MeasureTheory.Integrable.norm_integral_condDistrib_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ‖∫ y, f (x, y) ∂condDistrib Y X μ x‖) (μ.map X) := by
  rw [condDistrib, ← Measure.fst_map_prod_mk₀ (X := X) hY]; exact hf_int.norm_integral_condKernel
  -- ⊢ Integrable fun x => ‖∫ (y : Ω), f (x, y) ∂↑(Measure.condKernel (Measure.map  …
                                                            -- 🎉 no goals
#align measure_theory.integrable.norm_integral_cond_distrib_map MeasureTheory.Integrable.norm_integral_condDistrib_map

theorem _root_.MeasureTheory.Integrable.norm_integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ‖∫ y, f (X a, y) ∂condDistrib Y X μ (X a)‖) μ :=
  (hf_int.norm_integral_condDistrib_map hY).comp_aemeasurable hX
#align measure_theory.integrable.norm_integral_cond_distrib MeasureTheory.Integrable.norm_integral_condDistrib

theorem _root_.MeasureTheory.Integrable.integral_condDistrib_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ∫ y, f (x, y) ∂condDistrib Y X μ x) (μ.map X) :=
  (integrable_norm_iff (hf_int.1.integral_condDistrib_map hY)).mp
    (hf_int.norm_integral_condDistrib_map hY)
#align measure_theory.integrable.integral_cond_distrib_map MeasureTheory.Integrable.integral_condDistrib_map

theorem _root_.MeasureTheory.Integrable.integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf_int.integral_condDistrib_map hY).comp_aemeasurable hX
#align measure_theory.integrable.integral_cond_distrib MeasureTheory.Integrable.integral_condDistrib

end Integrability

theorem set_lintegral_preimage_condDistrib (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫⁻ a in X ⁻¹' t, condDistrib Y X μ (X a) s ∂μ = μ (X ⁻¹' t ∩ Y ⁻¹' s) := by
  -- Porting note: need to massage the LHS integrand into the form accepted by `lintegral_comp`
  -- (`rw` does not see that the two forms are defeq)
  conv_lhs => arg 2; change (fun a => ((condDistrib Y X μ) a) s) ∘ X
  -- ⊢ lintegral (Measure.restrict μ (X ⁻¹' t)) ((fun a => ↑↑(↑(condDistrib Y X μ)  …
  rw [lintegral_comp (kernel.measurable_coe _ hs) hX, condDistrib, ← Measure.restrict_map hX ht, ←
    Measure.fst_map_prod_mk₀ hY, set_lintegral_condKernel_eq_measure_prod _ ht hs,
    Measure.map_apply_of_aemeasurable (hX.aemeasurable.prod_mk hY) (ht.prod hs), mk_preimage_prod]
#align probability_theory.set_lintegral_preimage_cond_distrib ProbabilityTheory.set_lintegral_preimage_condDistrib

theorem set_lintegral_condDistrib_of_measurableSet (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hs : MeasurableSet s) {t : Set α} (ht : MeasurableSet[mβ.comap X] t) :
    ∫⁻ a in t, condDistrib Y X μ (X a) s ∂μ = μ (t ∩ Y ⁻¹' s) := by
  obtain ⟨t', ht', rfl⟩ := ht
  -- ⊢ ∫⁻ (a : α) in X ⁻¹' t', ↑↑(↑(condDistrib Y X μ) (X a)) s ∂μ = ↑↑μ (X ⁻¹' t'  …
  rw [set_lintegral_preimage_condDistrib hX hY hs ht']
  -- 🎉 no goals
#align probability_theory.set_lintegral_cond_distrib_of_measurable_set ProbabilityTheory.set_lintegral_condDistrib_of_measurableSet

/-- For almost every `a : α`, the `condDistrib Y X μ` kernel applied to `X a` and a measurable set
`s` is equal to the conditional expectation of the indicator of `Y ⁻¹' s`. -/
theorem condDistrib_ae_eq_condexp (hX : Measurable X) (hY : Measurable Y) (hs : MeasurableSet s) :
    (fun a => (condDistrib Y X μ (X a) s).toReal) =ᵐ[μ] μ⟦Y ⁻¹' s|mβ.comap X⟧ := by
  refine' ae_eq_condexp_of_forall_set_integral_eq hX.comap_le _ _ _ _
  · exact (integrable_const _).indicator (hY hs)
    -- 🎉 no goals
  · exact fun t _ _ => (integrable_toReal_condDistrib hX.aemeasurable hs).integrableOn
    -- 🎉 no goals
  · intro t ht _
    -- ⊢ ∫ (x : α) in t, ENNReal.toReal (↑↑(↑(condDistrib Y X μ) (X x)) s) ∂μ = ∫ (x  …
    rw [integral_toReal ((measurable_condDistrib hs).mono hX.comap_le le_rfl).aemeasurable
      (eventually_of_forall fun ω => measure_lt_top (condDistrib Y X μ (X ω)) _),
      integral_indicator_const _ (hY hs), Measure.restrict_apply (hY hs), smul_eq_mul, mul_one,
      inter_comm, set_lintegral_condDistrib_of_measurableSet hX hY.aemeasurable hs ht]
  · refine' (Measurable.stronglyMeasurable _).aeStronglyMeasurable'
    -- ⊢ Measurable fun a => ENNReal.toReal (↑↑(↑(condDistrib Y X μ) (X a)) s)
    exact @Measurable.ennreal_toReal _ (mβ.comap X) _ (measurable_condDistrib hs)
    -- 🎉 no goals
#align probability_theory.cond_distrib_ae_eq_condexp ProbabilityTheory.condDistrib_ae_eq_condexp

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `condDistrib` kernel. -/
theorem condexp_prod_ae_eq_integral_condDistrib' [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    μ[fun a => f (X a, Y a)|mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a,y) ∂condDistrib Y X μ (X a) := by
  have hf_int' : Integrable (fun a => f (X a, Y a)) μ :=
    (integrable_map_measure hf_int.1 (hX.aemeasurable.prod_mk hY)).mp hf_int
  refine' (ae_eq_condexp_of_forall_set_integral_eq hX.comap_le hf_int' (fun s _ _ => _) _ _).symm
  · exact (hf_int.integral_condDistrib hX.aemeasurable hY).integrableOn
    -- 🎉 no goals
  · rintro s ⟨t, ht, rfl⟩ _
    -- ⊢ ∫ (x : α) in X ⁻¹' t, ∫ (y : Ω), f (X x, y) ∂↑(condDistrib Y X μ) (X x) ∂μ = …
    change ∫ a in X ⁻¹' t, ((fun x' => ∫ y, f (x', y) ∂(condDistrib Y X μ) x') ∘ X) a ∂μ =
      ∫ a in X ⁻¹' t, f (X a, Y a) ∂μ
    simp only [Function.comp_apply]
    -- ⊢ ∫ (a : α) in X ⁻¹' t, ∫ (y : Ω), f (X a, y) ∂↑(condDistrib Y X μ) (X a) ∂μ = …
    rw [← integral_map hX.aemeasurable (f := fun x' => ∫ y, f (x', y) ∂(condDistrib Y X μ) x')]
    -- ⊢ ∫ (y : β), ∫ (y_1 : Ω), f (y, y_1) ∂↑(condDistrib Y X μ) y ∂Measure.map X (M …
    swap
    -- ⊢ AEStronglyMeasurable (fun x' => ∫ (y : Ω), f (x', y) ∂↑(condDistrib Y X μ) x …
    · rw [← Measure.restrict_map hX ht]
      -- ⊢ AEStronglyMeasurable (fun x' => ∫ (y : Ω), f (x', y) ∂↑(condDistrib Y X μ) x …
      exact (hf_int.1.integral_condDistrib_map hY).restrict
      -- 🎉 no goals
    rw [← Measure.restrict_map hX ht, ← Measure.fst_map_prod_mk₀ hY, condDistrib,
      set_integral_condKernel_univ_right ht hf_int.integrableOn,
      set_integral_map (ht.prod MeasurableSet.univ) hf_int.1 (hX.aemeasurable.prod_mk hY),
      mk_preimage_prod, preimage_univ, inter_univ]
  · exact aestronglyMeasurable'_integral_condDistrib hX.aemeasurable hY hf_int.1
    -- 🎉 no goals
#align probability_theory.condexp_prod_ae_eq_integral_cond_distrib' ProbabilityTheory.condexp_prod_ae_eq_integral_condDistrib'

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `condDistrib` kernel. -/
theorem condexp_prod_ae_eq_integral_condDistrib₀ [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a)))
    (hf_int : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a)|mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a) :=
  haveI hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure hf (hX.aemeasurable.prod_mk hY)]
    -- 🎉 no goals
  condexp_prod_ae_eq_integral_condDistrib' hX hY hf_int'
#align probability_theory.condexp_prod_ae_eq_integral_cond_distrib₀ ProbabilityTheory.condexp_prod_ae_eq_integral_condDistrib₀

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `condDistrib` kernel. -/
theorem condexp_prod_ae_eq_integral_condDistrib [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ) (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a)|mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a) :=
  haveI hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure hf.aestronglyMeasurable (hX.aemeasurable.prod_mk hY)]
    -- 🎉 no goals
  condexp_prod_ae_eq_integral_condDistrib' hX hY hf_int'
#align probability_theory.condexp_prod_ae_eq_integral_cond_distrib ProbabilityTheory.condexp_prod_ae_eq_integral_condDistrib

theorem condexp_ae_eq_integral_condDistrib [NormedSpace ℝ F] [CompleteSpace F] (hX : Measurable X)
    (hY : AEMeasurable Y μ) {f : Ω → F} (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun a => f (Y a)) μ) :
    μ[fun a => f (Y a)|mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂condDistrib Y X μ (X a) :=
  condexp_prod_ae_eq_integral_condDistrib hX hY (hf.comp_measurable measurable_snd) hf_int
#align probability_theory.condexp_ae_eq_integral_cond_distrib ProbabilityTheory.condexp_ae_eq_integral_condDistrib

/-- The conditional expectation of `Y` given `X` is almost everywhere equal to the integral
`∫ y, y ∂(condDistrib Y X μ (X a))`. -/
theorem condexp_ae_eq_integral_condDistrib' {Ω} [NormedAddCommGroup Ω] [NormedSpace ℝ Ω]
    [CompleteSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω] {Y : α → Ω}
    (hX : Measurable X) (hY_int : Integrable Y μ) :
    μ[Y|mβ.comap X] =ᵐ[μ] fun a => ∫ y, y ∂condDistrib Y X μ (X a) :=
  condexp_ae_eq_integral_condDistrib hX hY_int.1.aemeasurable stronglyMeasurable_id hY_int
#align probability_theory.condexp_ae_eq_integral_cond_distrib' ProbabilityTheory.condexp_ae_eq_integral_condDistrib'

open MeasureTheory

theorem _root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_mk
    {Ω F} {mΩ : MeasurableSpace Ω} (X : Ω → β) {μ : Measure Ω} [TopologicalSpace F] {f : Ω → F}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) := by
  refine' ⟨fun x => hf.mk f x.2, hf.stronglyMeasurable_mk.comp_measurable measurable_snd, _⟩
  -- ⊢ (fun x => f x.snd) =ᵐ[Measure.map (fun ω => (X ω, ω)) μ] fun x => AEStrongly …
  suffices h : Measure.QuasiMeasurePreserving Prod.snd (μ.map fun ω => (X ω, ω)) μ
  -- ⊢ (fun x => f x.snd) =ᵐ[Measure.map (fun ω => (X ω, ω)) μ] fun x => AEStrongly …
  · exact Measure.QuasiMeasurePreserving.ae_eq h hf.ae_eq_mk
    -- 🎉 no goals
  refine' ⟨measurable_snd, Measure.AbsolutelyContinuous.mk fun s hs hμs => _⟩
  -- ⊢ ↑↑(Measure.map Prod.snd (Measure.map (fun ω => (X ω, ω)) μ)) s = 0
  rw [Measure.map_apply _ hs]
  -- ⊢ ↑↑(Measure.map (fun ω => (X ω, ω)) μ) (Prod.snd ⁻¹' s) = 0
  swap; · exact measurable_snd
  -- ⊢ Measurable Prod.snd
          -- 🎉 no goals
  by_cases hX : AEMeasurable X μ
  -- ⊢ ↑↑(Measure.map (fun ω => (X ω, ω)) μ) (Prod.snd ⁻¹' s) = 0
  · rw [Measure.map_apply_of_aemeasurable]
    · rw [← univ_prod, mk_preimage_prod, preimage_univ, univ_inter, preimage_id']
      -- ⊢ ↑↑μ s = 0
      exact hμs
      -- 🎉 no goals
    · exact hX.prod_mk aemeasurable_id
      -- 🎉 no goals
    · exact measurable_snd hs
      -- 🎉 no goals
  · rw [Measure.map_of_not_aemeasurable]
    -- ⊢ ↑↑0 (Prod.snd ⁻¹' s) = 0
    · simp
      -- 🎉 no goals
    · contrapose! hX; exact measurable_fst.comp_aemeasurable hX
      -- ⊢ AEMeasurable X
                      -- 🎉 no goals
#align measure_theory.ae_strongly_measurable.comp_snd_map_prod_mk MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_mk

theorem _root_.MeasureTheory.Integrable.comp_snd_map_prod_mk
    {Ω} {mΩ : MeasurableSpace Ω} (X : Ω → β) {μ : Measure Ω} {f : Ω → F} (hf_int : Integrable f μ) :
    Integrable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) := by
  by_cases hX : AEMeasurable X μ
  -- ⊢ Integrable fun x => f x.snd
  · have hf := hf_int.1.comp_snd_map_prod_mk X (mΩ := mΩ) (mβ := mβ)
    -- ⊢ Integrable fun x => f x.snd
    refine' ⟨hf, _⟩
    -- ⊢ HasFiniteIntegral fun x => f x.snd
    rw [HasFiniteIntegral, lintegral_map' hf.ennnorm (hX.prod_mk aemeasurable_id)]
    -- ⊢ ∫⁻ (a : Ω), ↑‖f (X a, a).snd‖₊ ∂μ < ⊤
    exact hf_int.2
    -- 🎉 no goals
  · rw [Measure.map_of_not_aemeasurable]
    -- ⊢ Integrable fun x => f x.snd
    · simp
      -- 🎉 no goals
    · contrapose! hX; exact measurable_fst.comp_aemeasurable hX
      -- ⊢ AEMeasurable X
                      -- 🎉 no goals
#align measure_theory.integrable.comp_snd_map_prod_mk MeasureTheory.Integrable.comp_snd_map_prod_mk

theorem aestronglyMeasurable_comp_snd_map_prod_mk_iff {Ω F} {_ : MeasurableSpace Ω}
    [TopologicalSpace F] {X : Ω → β} {μ : Measure Ω} (hX : Measurable X) {f : Ω → F} :
    AEStronglyMeasurable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) ↔
    AEStronglyMeasurable f μ :=
  ⟨fun h => h.comp_measurable (hX.prod_mk measurable_id), fun h => h.comp_snd_map_prod_mk X⟩
#align probability_theory.ae_strongly_measurable_comp_snd_map_prod_mk_iff ProbabilityTheory.aestronglyMeasurable_comp_snd_map_prod_mk_iff

theorem integrable_comp_snd_map_prod_mk_iff {Ω} {_ : MeasurableSpace Ω} {X : Ω → β} {μ : Measure Ω}
    (hX : Measurable X) {f : Ω → F} :
    Integrable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) ↔ Integrable f μ :=
  ⟨fun h => h.comp_measurable (hX.prod_mk measurable_id), fun h => h.comp_snd_map_prod_mk X⟩
#align probability_theory.integrable_comp_snd_map_prod_mk_iff ProbabilityTheory.integrable_comp_snd_map_prod_mk_iff

theorem condexp_ae_eq_integral_condDistrib_id [NormedSpace ℝ F] [CompleteSpace F] {X : Ω → β}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hX : Measurable X) {f : Ω → F} (hf_int : Integrable f μ) :
    μ[f|mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂condDistrib id X μ (X a) :=
  condexp_prod_ae_eq_integral_condDistrib' hX aemeasurable_id (hf_int.comp_snd_map_prod_mk X)
#align probability_theory.condexp_ae_eq_integral_cond_distrib_id ProbabilityTheory.condexp_ae_eq_integral_condDistrib_id

end ProbabilityTheory
