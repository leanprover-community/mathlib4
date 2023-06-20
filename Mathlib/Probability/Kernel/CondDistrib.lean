/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module probability.kernel.cond_distrib
! leanprover-community/mathlib commit 00abe0695d8767201e6d008afa22393978bb324d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Probability.Kernel.Disintegration
import Mathlib.Probability.Notation

/-!
# Regular conditional probability distribution

We define the regular conditional probability distribution of `Y : α → Ω` given `X : α → β`, where
`Ω` is a standard Borel space. This is a `kernel β Ω` such that for almost all `a`, `cond_distrib`
evaluated at `X a` and a measurable set `s` is equal to the conditional expectation
`μ⟦Y ⁻¹' s | mβ.comap X⟧` evaluated at `a`.

`μ⟦Y ⁻¹' s | mβ.comap X⟧` maps a measurable set `s` to a function `α → ℝ≥0∞`, and for all `s` that
map is unique up to a `μ`-null set. For all `a`, the map from sets to `ℝ≥0∞` that we obtain that way
verifies some of the properties of a measure, but in general the fact that the `μ`-null set depends
on `s` can prevent us from finding versions of the conditional expectation that combine into a true
measure. The standard Borel space assumption on `Ω` allows us to do so.

The case `Y = X = id` is developed in more detail in `probability/kernel/condexp.lean`: here `X` is
understood as a map from `Ω` with a sub-σ-algebra to `Ω` with its default σ-algebra and the
conditional distribution defines a kernel associated with the conditional expectation with respect
to `m`.

## Main definitions

* `cond_distrib Y X μ`: regular conditional probability distribution of `Y : α → Ω` given
  `X : α → β`, where `Ω` is a standard Borel space.

## Main statements

* `cond_distrib_ae_eq_condexp`: for almost all `a`, `cond_distrib` evaluated at `X a` and a
  measurable set `s` is equal to the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`.
* `condexp_prod_ae_eq_integral_cond_distrib`: the conditional expectation
  `μ[(λ a, f (X a, Y a)) | X ; mβ]` is almost everywhere equal to the integral
  `∫ y, f (X a, y) ∂(cond_distrib Y X μ (X a))`.

-/


open MeasureTheory Set Filter TopologicalSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {α β Ω F : Type _} [TopologicalSpace Ω] [MeasurableSpace Ω] [PolishSpace Ω] [BorelSpace Ω]
  [Nonempty Ω] [NormedAddCommGroup F] {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
  {X : α → β} {Y : α → Ω}

/-- **Regular conditional probability distribution**: kernel associated with the conditional
expectation of `Y` given `X`.
For almost all `a`, `cond_distrib Y X μ` evaluated at `X a` and a measurable set `s` is equal to
the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`. It also satisfies the equality
`μ[(λ a, f (X a, Y a)) | mβ.comap X] =ᵐ[μ] λ a, ∫ y, f (X a, y) ∂(cond_distrib Y X μ (X a))` for
all integrable functions `f`. -/
noncomputable irreducible_def condDistrib {mα : MeasurableSpace α} [MeasurableSpace β] (Y : α → Ω)
    (X : α → β) (μ : Measure α) [IsFiniteMeasure μ] : kernel β Ω :=
  (μ.map fun a => (X a, Y a)).condKernel
#align probability_theory.cond_distrib ProbabilityTheory.condDistrib

instance [MeasurableSpace β] : IsMarkovKernel (condDistrib Y X μ) := by rw [cond_distrib];
  infer_instance

variable {mβ : MeasurableSpace β} {s : Set Ω} {t : Set β} {f : β × Ω → F}

section Measurability

theorem measurable_condDistrib (hs : MeasurableSet s) :
    measurable[mβ.comap X] fun a => condDistrib Y X μ (X a) s :=
  (kernel.measurable_coe _ hs).comp (Measurable.of_comap_le le_rfl)
#align probability_theory.measurable_cond_distrib ProbabilityTheory.measurable_condDistrib

theorem MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    (∀ᵐ a ∂μ.map X, Integrable (fun ω => f (a, ω)) (condDistrib Y X μ a)) ∧
        Integrable (fun a => ∫ ω, ‖f (a, ω)‖ ∂condDistrib Y X μ a) (μ.map X) ↔
      Integrable f (μ.map fun a => (X a, Y a)) :=
  by rw [cond_distrib, ← hf.ae_integrable_cond_kernel_iff, measure.fst_map_prod_mk₀ hX hY]
#align measure_theory.ae_strongly_measurable.ae_integrable_cond_distrib_map_iff MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff

variable [NormedSpace ℝ F] [CompleteSpace F]

theorem MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂condDistrib Y X μ x) (μ.map X) := by
  rw [← measure.fst_map_prod_mk₀ hX hY, cond_distrib]; exact hf.integral_cond_kernel
#align measure_theory.ae_strongly_measurable.integral_cond_distrib_map MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map

theorem MeasureTheory.AEStronglyMeasurable.integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf.integral_condDistrib_map hX hY).comp_aemeasurable hX
#align measure_theory.ae_strongly_measurable.integral_cond_distrib MeasureTheory.AEStronglyMeasurable.integral_condDistrib

theorem aEStronglyMeasurable'_integral_condDistrib (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable' (mβ.comap X) (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf.integral_condDistrib_map hX hY).comp_ae_measurable' hX
#align probability_theory.ae_strongly_measurable'_integral_cond_distrib ProbabilityTheory.aEStronglyMeasurable'_integral_condDistrib

end Measurability

section Integrability

theorem integrable_toReal_condDistrib (hX : AEMeasurable X μ) (hs : MeasurableSet s) :
    Integrable (fun a => (condDistrib Y X μ (X a) s).toReal) μ := by
  refine' integrable_to_real_of_lintegral_ne_top _ _
  · exact Measurable.comp_aemeasurable (kernel.measurable_coe _ hs) hX
  · refine' ne_of_lt _
    calc
      ∫⁻ a, cond_distrib Y X μ (X a) s ∂μ ≤ ∫⁻ a, 1 ∂μ := lintegral_mono fun a => prob_le_one
      _ = μ univ := lintegral_one
      _ < ∞ := measure_lt_top _ _
#align probability_theory.integrable_to_real_cond_distrib ProbabilityTheory.integrable_toReal_condDistrib

theorem MeasureTheory.Integrable.condDistrib_ae_map (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    ∀ᵐ b ∂μ.map X, Integrable (fun ω => f (b, ω)) (condDistrib Y X μ b) := by
  rw [cond_distrib, ← measure.fst_map_prod_mk₀ hX hY]; exact hf_int.cond_kernel_ae
#align measure_theory.integrable.cond_distrib_ae_map MeasureTheory.Integrable.condDistrib_ae_map

theorem MeasureTheory.Integrable.condDistrib_ae (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    ∀ᵐ a ∂μ, Integrable (fun ω => f (X a, ω)) (condDistrib Y X μ (X a)) :=
  ae_of_ae_map hX (hf_int.condDistrib_ae_map hX hY)
#align measure_theory.integrable.cond_distrib_ae MeasureTheory.Integrable.condDistrib_ae

theorem MeasureTheory.Integrable.integral_norm_condDistrib_map (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂condDistrib Y X μ x) (μ.map X) := by
  rw [cond_distrib, ← measure.fst_map_prod_mk₀ hX hY]; exact hf_int.integral_norm_cond_kernel
#align measure_theory.integrable.integral_norm_cond_distrib_map MeasureTheory.Integrable.integral_norm_condDistrib_map

theorem MeasureTheory.Integrable.integral_norm_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ∫ y, ‖f (X a, y)‖ ∂condDistrib Y X μ (X a)) μ :=
  (hf_int.integral_norm_condDistrib_map hX hY).comp_aemeasurable hX
#align measure_theory.integrable.integral_norm_cond_distrib MeasureTheory.Integrable.integral_norm_condDistrib

variable [NormedSpace ℝ F] [CompleteSpace F]

theorem MeasureTheory.Integrable.norm_integral_condDistrib_map (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ‖∫ y, f (x, y) ∂condDistrib Y X μ x‖) (μ.map X) := by
  rw [cond_distrib, ← measure.fst_map_prod_mk₀ hX hY]; exact hf_int.norm_integral_cond_kernel
#align measure_theory.integrable.norm_integral_cond_distrib_map MeasureTheory.Integrable.norm_integral_condDistrib_map

theorem MeasureTheory.Integrable.norm_integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ‖∫ y, f (X a, y) ∂condDistrib Y X μ (X a)‖) μ :=
  (hf_int.norm_integral_condDistrib_map hX hY).comp_aemeasurable hX
#align measure_theory.integrable.norm_integral_cond_distrib MeasureTheory.Integrable.norm_integral_condDistrib

theorem MeasureTheory.Integrable.integral_condDistrib_map (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ∫ y, f (x, y) ∂condDistrib Y X μ x) (μ.map X) :=
  (integrable_norm_iff (hf_int.1.integral_condDistrib_map hX hY)).mp
    (hf_int.norm_integral_condDistrib_map hX hY)
#align measure_theory.integrable.integral_cond_distrib_map MeasureTheory.Integrable.integral_condDistrib_map

theorem MeasureTheory.Integrable.integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf_int.integral_condDistrib_map hX hY).comp_aemeasurable hX
#align measure_theory.integrable.integral_cond_distrib MeasureTheory.Integrable.integral_condDistrib

end Integrability

theorem set_lintegral_preimage_condDistrib (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫⁻ a in X ⁻¹' t, condDistrib Y X μ (X a) s ∂μ = μ (X ⁻¹' t ∩ Y ⁻¹' s) := by
  rw [lintegral_comp (kernel.measurable_coe _ hs) hX, cond_distrib, ← measure.restrict_map hX ht, ←
    measure.fst_map_prod_mk₀ hX.ae_measurable hY, set_lintegral_cond_kernel_eq_measure_prod _ ht hs,
    measure.map_apply_of_ae_measurable (hX.ae_measurable.prod_mk hY) (ht.prod hs), mk_preimage_prod]
#align probability_theory.set_lintegral_preimage_cond_distrib ProbabilityTheory.set_lintegral_preimage_condDistrib

theorem set_lintegral_condDistrib_of_measurableSet (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hs : MeasurableSet s) {t : Set α} (ht : measurable_set[mβ.comap X] t) :
    ∫⁻ a in t, condDistrib Y X μ (X a) s ∂μ = μ (t ∩ Y ⁻¹' s) := by obtain ⟨t', ht', rfl⟩ := ht;
  rw [set_lintegral_preimage_cond_distrib hX hY hs ht']
#align probability_theory.set_lintegral_cond_distrib_of_measurable_set ProbabilityTheory.set_lintegral_condDistrib_of_measurableSet

/-- For almost every `a : α`, the `cond_distrib Y X μ` kernel applied to `X a` and a measurable set
`s` is equal to the conditional expectation of the indicator of `Y ⁻¹' s`. -/
theorem condDistrib_ae_eq_condexp (hX : Measurable X) (hY : Measurable Y) (hs : MeasurableSet s) :
    (fun a => (condDistrib Y X μ (X a) s).toReal) =ᵐ[μ] μ⟦Y ⁻¹' s|mβ.comap X⟧ := by
  refine' ae_eq_condexp_of_forall_set_integral_eq hX.comap_le _ _ _ _
  · exact (integrable_const _).indicator (hY hs)
  · exact fun t ht _ => (integrable_to_real_cond_distrib hX.ae_measurable hs).IntegrableOn
  · intro t ht _
    rw [integral_to_real ((measurable_cond_distrib hs).mono hX.comap_le le_rfl).AEMeasurable
        (eventually_of_forall fun ω => measure_lt_top (cond_distrib Y X μ (X ω)) _),
      integral_indicator_const _ (hY hs), measure.restrict_apply (hY hs), smul_eq_mul, mul_one,
      inter_comm, set_lintegral_cond_distrib_of_measurable_set hX hY.ae_measurable hs ht]
  · refine' (Measurable.stronglyMeasurable _).aestronglyMeasurable'
    exact @Measurable.ennreal_toReal _ (mβ.comap X) _ (measurable_cond_distrib hs)
#align probability_theory.cond_distrib_ae_eq_condexp ProbabilityTheory.condDistrib_ae_eq_condexp

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `cond_distrib` kernel. -/
theorem condexp_prod_ae_eq_integral_cond_distrib' [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    μ[fun a => f (X a, Y a)|mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a) :=
  by
  have hf_int' : integrable (fun a => f (X a, Y a)) μ :=
    (integrable_map_measure hf_int.1 (hX.ae_measurable.prod_mk hY)).mp hf_int
  refine' (ae_eq_condexp_of_forall_set_integral_eq hX.comap_le hf_int' (fun s hs hμs => _) _ _).symm
  · exact (hf_int.integral_cond_distrib hX.ae_measurable hY).IntegrableOn
  · rintro s ⟨t, ht, rfl⟩ _
    change
      ∫ a in X ⁻¹' t, ((fun x' => ∫ y, f (x', y) ∂(cond_distrib Y X μ) x') ∘ X) a ∂μ =
        ∫ a in X ⁻¹' t, f (X a, Y a) ∂μ
    rw [← integral_map hX.ae_measurable]
    swap
    · rw [← measure.restrict_map hX ht]
      exact (hf_int.1.integral_condDistrib_map hX.ae_measurable hY).restrict
    rw [← measure.restrict_map hX ht, ← measure.fst_map_prod_mk₀ hX.ae_measurable hY, cond_distrib,
      set_integral_cond_kernel_univ_right ht hf_int.integrable_on,
      set_integral_map (ht.prod MeasurableSet.univ) hf_int.1 (hX.ae_measurable.prod_mk hY),
      mk_preimage_prod, preimage_univ, inter_univ]
  · exact ae_strongly_measurable'_integral_cond_distrib hX.ae_measurable hY hf_int.1
#align probability_theory.condexp_prod_ae_eq_integral_cond_distrib' ProbabilityTheory.condexp_prod_ae_eq_integral_cond_distrib'

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `cond_distrib` kernel. -/
theorem condexp_prod_ae_eq_integral_cond_distrib₀ [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a)))
    (hf_int : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a)|mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a) :=
  haveI hf_int' : integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure hf (hX.ae_measurable.prod_mk hY)]
  condexp_prod_ae_eq_integral_cond_distrib' hX hY hf_int'
#align probability_theory.condexp_prod_ae_eq_integral_cond_distrib₀ ProbabilityTheory.condexp_prod_ae_eq_integral_cond_distrib₀

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `cond_distrib` kernel. -/
theorem condexp_prod_ae_eq_integral_condDistrib [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ) (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a)|mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a) :=
  haveI hf_int' : integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure hf.ae_strongly_measurable (hX.ae_measurable.prod_mk hY)]
  condexp_prod_ae_eq_integral_cond_distrib' hX hY hf_int'
#align probability_theory.condexp_prod_ae_eq_integral_cond_distrib ProbabilityTheory.condexp_prod_ae_eq_integral_condDistrib

theorem condexp_ae_eq_integral_condDistrib [NormedSpace ℝ F] [CompleteSpace F] (hX : Measurable X)
    (hY : AEMeasurable Y μ) {f : Ω → F} (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun a => f (Y a)) μ) :
    μ[fun a => f (Y a)|mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂condDistrib Y X μ (X a) :=
  condexp_prod_ae_eq_integral_condDistrib hX hY (hf.comp_measurable measurable_snd) hf_int
#align probability_theory.condexp_ae_eq_integral_cond_distrib ProbabilityTheory.condexp_ae_eq_integral_condDistrib

/-- The conditional expectation of `Y` given `X` is almost everywhere equal to the integral
`∫ y, y ∂(cond_distrib Y X μ (X a))`. -/
theorem condexp_ae_eq_integral_cond_distrib' {Ω} [NormedAddCommGroup Ω] [NormedSpace ℝ Ω]
    [CompleteSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω] {Y : α → Ω}
    (hX : Measurable X) (hY_int : Integrable Y μ) :
    μ[Y|mβ.comap X] =ᵐ[μ] fun a => ∫ y, y ∂condDistrib Y X μ (X a) :=
  condexp_ae_eq_integral_condDistrib hX hY_int.1.AEMeasurable stronglyMeasurable_id hY_int
#align probability_theory.condexp_ae_eq_integral_cond_distrib' ProbabilityTheory.condexp_ae_eq_integral_cond_distrib'

theorem MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_mk {Ω F} {mΩ : MeasurableSpace Ω}
    {X : Ω → β} {μ : Measure Ω} [TopologicalSpace F] (hX : Measurable X) {f : Ω → F}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) := by
  refine' ⟨fun x => hf.mk f x.2, hf.strongly_measurable_mk.comp_measurable measurable_snd, _⟩
  suffices h : measure.quasi_measure_preserving Prod.snd (μ.map fun ω => (X ω, ω)) μ
  · exact measure.quasi_measure_preserving.ae_eq h hf.ae_eq_mk
  refine' ⟨measurable_snd, measure.absolutely_continuous.mk fun s hs hμs => _⟩
  rw [measure.map_apply _ hs]
  swap; · exact measurable_snd
  rw [measure.map_apply]
  · rw [← univ_prod, mk_preimage_prod, preimage_univ, univ_inter, preimage_id']
    exact hμs
  · exact hX.prod_mk measurable_id
  · exact measurable_snd hs
#align measure_theory.ae_strongly_measurable.comp_snd_map_prod_mk MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_mk

theorem MeasureTheory.Integrable.comp_snd_map_prod_mk {Ω} {mΩ : MeasurableSpace Ω} {X : Ω → β}
    {μ : Measure Ω} (hX : Measurable X) {f : Ω → F} (hf_int : Integrable f μ) :
    Integrable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) := by
  have hf := hf_int.1.comp_snd_map_prod_mk hX
  refine' ⟨hf, _⟩
  rw [has_finite_integral, lintegral_map' hf.ennnorm (hX.prod_mk measurable_id).AEMeasurable]
  exact hf_int.2
#align measure_theory.integrable.comp_snd_map_prod_mk MeasureTheory.Integrable.comp_snd_map_prod_mk

theorem aEStronglyMeasurable_comp_snd_map_prod_mk_iff {Ω F} {mΩ : MeasurableSpace Ω}
    [TopologicalSpace F] {X : Ω → β} {μ : Measure Ω} (hX : Measurable X) {f : Ω → F} :
    AEStronglyMeasurable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) ↔
      AEStronglyMeasurable f μ :=
  ⟨fun h => h.comp_measurable (hX.prod_mk measurable_id), fun h => h.comp_snd_map_prod_mk hX⟩
#align probability_theory.ae_strongly_measurable_comp_snd_map_prod_mk_iff ProbabilityTheory.aEStronglyMeasurable_comp_snd_map_prod_mk_iff

theorem integrable_comp_snd_map_prod_mk_iff {Ω} {mΩ : MeasurableSpace Ω} {X : Ω → β} {μ : Measure Ω}
    (hX : Measurable X) {f : Ω → F} :
    Integrable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) ↔ Integrable f μ :=
  ⟨fun h => h.comp_measurable (hX.prod_mk measurable_id), fun h => h.comp_snd_map_prod_mk hX⟩
#align probability_theory.integrable_comp_snd_map_prod_mk_iff ProbabilityTheory.integrable_comp_snd_map_prod_mk_iff

theorem condexp_ae_eq_integral_condDistrib_id [NormedSpace ℝ F] [CompleteSpace F] {X : Ω → β}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hX : Measurable X) {f : Ω → F} (hf_int : Integrable f μ) :
    μ[f|mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂condDistrib id X μ (X a) :=
  condexp_prod_ae_eq_integral_cond_distrib' hX aemeasurable_id (hf_int.comp_snd_map_prod_mk hX)
#align probability_theory.condexp_ae_eq_integral_cond_distrib_id ProbabilityTheory.condexp_ae_eq_integral_condDistrib_id

end ProbabilityTheory

