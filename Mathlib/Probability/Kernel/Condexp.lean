/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.CondDistrib

#align_import probability.kernel.condexp from "leanprover-community/mathlib"@"00abe0695d8767201e6d008afa22393978bb324d"

/-!
# Kernel associated with a conditional expectation

We define `condexpKernel μ m`, a kernel from `Ω` to `Ω` such that for all integrable functions `f`,
`μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condexpKernel μ m ω)`.

This kernel is defined if `Ω` is a standard Borel space. In general, `μ⟦s | m⟧` maps a measurable
set `s` to a function `Ω → ℝ≥0∞`, and for all `s` that map is unique up to a `μ`-null set. For all
`a`, the map from sets to `ℝ≥0∞` that we obtain that way verifies some of the properties of a
measure, but the fact that the `μ`-null set depends on `s` can prevent us from finding versions of
the conditional expectation that combine into a true measure. The standard Borel space assumption
on `Ω` allows us to do so.

## Main definitions

* `condexpKernel μ m`: kernel such that `μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condexpKernel μ m ω)`.

## Main statements

* `condexp_ae_eq_integral_condexpKernel`: `μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condexpKernel μ m ω)`.

-/


open MeasureTheory Set Filter TopologicalSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

section AuxLemmas

variable {Ω F : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → F}

theorem _root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_id [TopologicalSpace F]
    (hm : m ≤ mΩ) (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x : Ω × Ω => f x.2)
      (@Measure.map Ω (Ω × Ω) (m.prod mΩ) mΩ (fun ω => (id ω, id ω)) μ) := by
  rw [← aestronglyMeasurable_comp_snd_map_prod_mk_iff (measurable_id'' hm)] at hf
  -- ⊢ AEStronglyMeasurable (fun x => f x.snd) (Measure.map (fun ω => (id ω, id ω)) …
  simp_rw [id.def] at hf ⊢
  -- ⊢ AEStronglyMeasurable (fun x => f x.snd) (Measure.map (fun ω => (ω, ω)) μ)
  exact hf
  -- 🎉 no goals
#align measure_theory.ae_strongly_measurable.comp_snd_map_prod_id MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_id

theorem _root_.MeasureTheory.Integrable.comp_snd_map_prod_id [NormedAddCommGroup F] (hm : m ≤ mΩ)
    (hf : Integrable f μ) : Integrable (fun x : Ω × Ω => f x.2)
      (@Measure.map Ω (Ω × Ω) (m.prod mΩ) mΩ (fun ω => (id ω, id ω)) μ) := by
  rw [← integrable_comp_snd_map_prod_mk_iff (measurable_id'' hm)] at hf
  -- ⊢ Integrable fun x => f x.snd
  simp_rw [id.def] at hf ⊢
  -- ⊢ Integrable fun x => f x.snd
  exact hf
  -- 🎉 no goals
#align measure_theory.integrable.comp_snd_map_prod_id MeasureTheory.Integrable.comp_snd_map_prod_id

end AuxLemmas

variable {Ω F : Type*} [TopologicalSpace Ω] {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [PolishSpace Ω] [BorelSpace Ω] [Nonempty Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Kernel associated with the conditional expectation with respect to a σ-algebra. It satisfies
`μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condexpKernel μ m ω)`.
It is defined as the conditional distribution of the identity given the identity, where the second
identity is understood as a map from `Ω` with the σ-algebra `mΩ` to `Ω` with σ-algebra `m ⊓ mΩ`.
We use `m ⊓ mΩ` instead of `m` to ensure that it is a sub-σ-algebra of `mΩ`. We then use
`kernel.comap` to get a kernel from `m` to `mΩ` instead of from `m ⊓ mΩ` to `mΩ`. -/
noncomputable irreducible_def condexpKernel (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) : @kernel Ω Ω m mΩ :=
  kernel.comap (@condDistrib Ω Ω Ω _ mΩ _ _ _ mΩ (m ⊓ mΩ) id id μ _) id
    (measurable_id'' (inf_le_left : m ⊓ mΩ ≤ m))
#align probability_theory.condexp_kernel ProbabilityTheory.condexpKernel

set_option autoImplicit true in
lemma condexpKernel_apply_eq_condDistrib :
    condexpKernel μ m ω = @condDistrib Ω Ω Ω _ mΩ _ _ _ mΩ (m ⊓ mΩ) id id μ _ (id ω) := by
  simp_rw [condexpKernel, kernel.comap_apply]
  -- 🎉 no goals

instance : IsMarkovKernel (condexpKernel μ m) := by simp only [condexpKernel]; infer_instance
                                                    -- ⊢ IsMarkovKernel (kernel.comap (condDistrib id id μ) id (_ : Measurable id))
                                                                               -- 🎉 no goals

section Measurability

variable [NormedAddCommGroup F] {f : Ω → F}

theorem measurable_condexpKernel {s : Set Ω} (hs : MeasurableSet s) :
    Measurable[m] fun ω => condexpKernel μ m ω s := by
  simp_rw [condexpKernel_apply_eq_condDistrib]
  -- ⊢ Measurable fun ω => ↑↑(↑(condDistrib id id μ) (id ω)) s
  refine Measurable.mono ?_ (inf_le_left : m ⊓ mΩ ≤ m) le_rfl
  -- ⊢ Measurable fun ω => ↑↑(↑(condDistrib id id μ) (id ω)) s
  convert measurable_condDistrib (μ := μ) hs
  -- ⊢ m ⊓ mΩ = MeasurableSpace.comap id (m ⊓ mΩ)
  rw [MeasurableSpace.comap_id]
  -- 🎉 no goals
#align probability_theory.measurable_condexp_kernel ProbabilityTheory.measurable_condexpKernel

theorem stronglyMeasurable_condexpKernel {s : Set Ω} (hs : MeasurableSet s) :
    StronglyMeasurable[m] fun ω => condexpKernel μ m ω s :=
  Measurable.stronglyMeasurable (measurable_condexpKernel hs)

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condexpKernel [NormedSpace ℝ F]
    [CompleteSpace F] (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun ω => ∫ y, f y ∂condexpKernel μ m ω) μ := by
  simp_rw [condexpKernel_apply_eq_condDistrib]
  -- ⊢ AEStronglyMeasurable (fun ω => ∫ (y : Ω), f y ∂↑(condDistrib id id μ) (id ω) …
  exact AEStronglyMeasurable.integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf.comp_snd_map_prod_id inf_le_right)
#align measure_theory.ae_strongly_measurable.integral_condexp_kernel MeasureTheory.AEStronglyMeasurable.integral_condexpKernel

theorem aestronglyMeasurable'_integral_condexpKernel [NormedSpace ℝ F] [CompleteSpace F]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable' m (fun ω => ∫ y, f y ∂condexpKernel μ m ω) μ := by
  rw [condexpKernel]
  -- ⊢ AEStronglyMeasurable' m (fun ω => ∫ (y : Ω), f y ∂↑(kernel.comap (condDistri …
  have h := aestronglyMeasurable'_integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ))
  rw [MeasurableSpace.comap_id] at h
  -- ⊢ AEStronglyMeasurable' m (fun ω => ∫ (y : Ω), f y ∂↑(kernel.comap (condDistri …
  exact AEStronglyMeasurable'.mono h inf_le_left
  -- 🎉 no goals
#align probability_theory.ae_strongly_measurable'_integral_condexp_kernel ProbabilityTheory.aestronglyMeasurable'_integral_condexpKernel

end Measurability

section Integrability

variable [NormedAddCommGroup F] {f : Ω → F}

theorem _root_.MeasureTheory.Integrable.condexpKernel_ae (hf_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Integrable f (condexpKernel μ m ω) := by
  rw [condexpKernel]
  -- ⊢ ∀ᵐ (ω : Ω) ∂μ, Integrable f
  exact Integrable.condDistrib_ae
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf_int.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ))
#align measure_theory.integrable.condexp_kernel_ae MeasureTheory.Integrable.condexpKernel_ae

theorem _root_.MeasureTheory.Integrable.integral_norm_condexpKernel (hf_int : Integrable f μ) :
    Integrable (fun ω => ∫ y, ‖f y‖ ∂condexpKernel μ m ω) μ := by
  rw [condexpKernel]
  -- ⊢ Integrable fun ω => ∫ (y : Ω), ‖f y‖ ∂↑(kernel.comap (condDistrib id id μ) i …
  exact Integrable.integral_norm_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf_int.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ))
#align measure_theory.integrable.integral_norm_condexp_kernel MeasureTheory.Integrable.integral_norm_condexpKernel

theorem _root_.MeasureTheory.Integrable.norm_integral_condexpKernel [NormedSpace ℝ F]
    [CompleteSpace F] (hf_int : Integrable f μ) :
    Integrable (fun ω => ‖∫ y, f y ∂condexpKernel μ m ω‖) μ := by
  rw [condexpKernel]
  -- ⊢ Integrable fun ω => ‖∫ (y : Ω), f y ∂↑(kernel.comap (condDistrib id id μ) id …
  exact Integrable.norm_integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf_int.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ))
#align measure_theory.integrable.norm_integral_condexp_kernel MeasureTheory.Integrable.norm_integral_condexpKernel

theorem _root_.MeasureTheory.Integrable.integral_condexpKernel [NormedSpace ℝ F] [CompleteSpace F]
    (hf_int : Integrable f μ) :
    Integrable (fun ω => ∫ y, f y ∂condexpKernel μ m ω) μ := by
  rw [condexpKernel]
  -- ⊢ Integrable fun ω => ∫ (y : Ω), f y ∂↑(kernel.comap (condDistrib id id μ) id  …
  exact Integrable.integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf_int.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ))
#align measure_theory.integrable.integral_condexp_kernel MeasureTheory.Integrable.integral_condexpKernel

theorem integrable_toReal_condexpKernel {s : Set Ω} (hs : MeasurableSet s) :
    Integrable (fun ω => (condexpKernel μ m ω s).toReal) μ := by
  rw [condexpKernel]
  -- ⊢ Integrable fun ω => ENNReal.toReal (↑↑(↑(kernel.comap (condDistrib id id μ)  …
  exact integrable_toReal_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) hs
  -- 🎉 no goals
#align probability_theory.integrable_to_real_condexp_kernel ProbabilityTheory.integrable_toReal_condexpKernel

end Integrability

lemma condexpKernel_ae_eq_condexp' [IsFiniteMeasure μ] {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω ↦ (condexpKernel μ m ω s).toReal) =ᵐ[μ] μ⟦s | m ⊓ mΩ⟧ := by
  have h := condDistrib_ae_eq_condexp (μ := μ)
    (measurable_id'' (inf_le_right : m ⊓ mΩ ≤ mΩ)) measurable_id hs
  simp only [id_eq, ge_iff_le, MeasurableSpace.comap_id, preimage_id_eq] at h
  -- ⊢ (fun ω => ENNReal.toReal (↑↑(↑(condexpKernel μ m) ω) s)) =ᵐ[μ] μ[indicator s …
  simp_rw [condexpKernel_apply_eq_condDistrib]
  -- ⊢ (fun ω => ENNReal.toReal (↑↑(↑(condDistrib id id μ) (id ω)) s)) =ᵐ[μ] μ[indi …
  exact h
  -- 🎉 no goals

lemma condexpKernel_ae_eq_condexp [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω ↦ (condexpKernel μ m ω s).toReal) =ᵐ[μ] μ⟦s | m⟧ :=
  (condexpKernel_ae_eq_condexp' hs).trans (by rw [inf_of_le_left hm])
                                              -- 🎉 no goals

lemma condexpKernel_ae_eq_trim_condexp [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω ↦ (condexpKernel μ m ω s).toReal) =ᵐ[μ.trim hm] μ⟦s | m⟧ := by
  rw [ae_eq_trim_iff hm _ stronglyMeasurable_condexp]
  -- ⊢ (fun ω => ENNReal.toReal (↑↑(↑(condexpKernel μ m) ω) s)) =ᵐ[μ] μ[indicator s …
  · exact condexpKernel_ae_eq_condexp hm hs
    -- 🎉 no goals
  · refine Measurable.stronglyMeasurable ?_
    -- ⊢ Measurable fun ω => ENNReal.toReal (↑↑(↑(condexpKernel μ m) ω) s)
    exact @Measurable.ennreal_toReal _ m _ (measurable_condexpKernel hs)
    -- 🎉 no goals

theorem condexp_ae_eq_integral_condexpKernel' [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] (hf_int : Integrable f μ) :
    μ[f|m ⊓ mΩ] =ᵐ[μ] fun ω => ∫ y, f y ∂condexpKernel μ m ω := by
  have hX : @Measurable Ω Ω mΩ (m ⊓ mΩ) id := measurable_id.mono le_rfl (inf_le_right : m ⊓ mΩ ≤ mΩ)
  -- ⊢ μ[f|m ⊓ mΩ] =ᵐ[μ] fun ω => ∫ (y : Ω), f y ∂↑(condexpKernel μ m) ω
  simp_rw [condexpKernel_apply_eq_condDistrib]
  -- ⊢ μ[f|m ⊓ mΩ] =ᵐ[μ] fun ω => ∫ (y : Ω), f y ∂↑(condDistrib id id μ) (id ω)
  have h := condexp_ae_eq_integral_condDistrib_id hX hf_int
  -- ⊢ μ[f|m ⊓ mΩ] =ᵐ[μ] fun ω => ∫ (y : Ω), f y ∂↑(condDistrib id id μ) (id ω)
  simpa only [MeasurableSpace.comap_id, id_eq] using h
  -- 🎉 no goals

/-- The conditional expectation of `f` with respect to a σ-algebra `m` is almost everywhere equal to
the integral `∫ y, f y ∂(condexpKernel μ m ω)`. -/
theorem condexp_ae_eq_integral_condexpKernel [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] (hm : m ≤ mΩ) (hf_int : Integrable f μ) :
    μ[f|m] =ᵐ[μ] fun ω => ∫ y, f y ∂condexpKernel μ m ω :=
  ((condexp_ae_eq_integral_condexpKernel' hf_int).symm.trans (by rw [inf_of_le_left hm])).symm
                                                                 -- 🎉 no goals
#align probability_theory.condexp_ae_eq_integral_condexp_kernel ProbabilityTheory.condexp_ae_eq_integral_condexpKernel

end ProbabilityTheory
