/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.CondDistrib

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
  simp_rw [id] at hf ⊢
  exact hf

theorem _root_.MeasureTheory.Integrable.comp_snd_map_prod_id [NormedAddCommGroup F] (hm : m ≤ mΩ)
    (hf : Integrable f μ) : Integrable (fun x : Ω × Ω => f x.2)
      (@Measure.map Ω (Ω × Ω) (m.prod mΩ) mΩ (fun ω => (id ω, id ω)) μ) := by
  rw [← integrable_comp_snd_map_prod_mk_iff (measurable_id'' hm)] at hf
  simp_rw [id] at hf ⊢
  exact hf

end AuxLemmas

variable {Ω F : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

open Classical in
/-- Kernel associated with the conditional expectation with respect to a σ-algebra. It satisfies
`μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condexpKernel μ m ω)`.
It is defined as the conditional distribution of the identity given the identity, where the second
identity is understood as a map from `Ω` with the σ-algebra `mΩ` to `Ω` with σ-algebra `m ⊓ mΩ`.
We use `m ⊓ mΩ` instead of `m` to ensure that it is a sub-σ-algebra of `mΩ`. We then use
`Kernel.comap` to get a kernel from `m` to `mΩ` instead of from `m ⊓ mΩ` to `mΩ`. -/
noncomputable irreducible_def condexpKernel (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) : @Kernel Ω Ω m mΩ :=
  if _h : Nonempty Ω then
    Kernel.comap (@condDistrib Ω Ω Ω mΩ _ _ mΩ (m ⊓ mΩ) id id μ _) id
      (measurable_id'' (inf_le_left : m ⊓ mΩ ≤ m))
  else 0

lemma condexpKernel_eq (μ : Measure Ω) [IsFiniteMeasure μ] [h : Nonempty Ω]
    (m : MeasurableSpace Ω) :
    condexpKernel (mΩ := mΩ) μ m = Kernel.comap (@condDistrib Ω Ω Ω mΩ _ _ mΩ (m ⊓ mΩ) id id μ _) id
      (measurable_id'' (inf_le_left : m ⊓ mΩ ≤ m)) := by
  simp [condexpKernel, h]

lemma condexpKernel_apply_eq_condDistrib [Nonempty Ω] {ω : Ω} :
    condexpKernel μ m ω = @condDistrib Ω Ω Ω mΩ _ _ mΩ (m ⊓ mΩ) id id μ _ (id ω) := by
  simp [condexpKernel_eq, Kernel.comap_apply]

instance : IsMarkovKernel (condexpKernel μ m) := by
  rcases isEmpty_or_nonempty Ω with h | h
  · exact ⟨fun a ↦ (IsEmpty.false a).elim⟩
  · simp [condexpKernel, h]; infer_instance

section Measurability

variable [NormedAddCommGroup F] {f : Ω → F}

theorem measurable_condexpKernel {s : Set Ω} (hs : MeasurableSet s) :
    Measurable[m] fun ω => condexpKernel μ m ω s := by
  nontriviality Ω
  simp_rw [condexpKernel_apply_eq_condDistrib]
  refine Measurable.mono ?_ (inf_le_left : m ⊓ mΩ ≤ m) le_rfl
  convert measurable_condDistrib (μ := μ) hs
  rw [MeasurableSpace.comap_id]

theorem stronglyMeasurable_condexpKernel {s : Set Ω} (hs : MeasurableSet s) :
    StronglyMeasurable[m] fun ω => condexpKernel μ m ω s :=
  Measurable.stronglyMeasurable (measurable_condexpKernel hs)

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condexpKernel [NormedSpace ℝ F]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun ω => ∫ y, f y ∂condexpKernel μ m ω) μ := by
  nontriviality Ω
  simp_rw [condexpKernel_apply_eq_condDistrib]
  exact AEStronglyMeasurable.integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf.comp_snd_map_prod_id inf_le_right)

theorem aestronglyMeasurable'_integral_condexpKernel [NormedSpace ℝ F]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable' m (fun ω => ∫ y, f y ∂condexpKernel μ m ω) μ := by
  nontriviality Ω
  rw [condexpKernel_eq]
  have h := aestronglyMeasurable'_integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ))
  rw [MeasurableSpace.comap_id] at h
  exact AEStronglyMeasurable'.mono h inf_le_left

end Measurability

section Integrability

variable [NormedAddCommGroup F] {f : Ω → F}

theorem _root_.MeasureTheory.Integrable.condexpKernel_ae (hf_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Integrable f (condexpKernel μ m ω) := by
  nontriviality Ω
  rw [condexpKernel_eq]
  convert Integrable.condDistrib_ae
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf_int.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ)) using 1

theorem _root_.MeasureTheory.Integrable.integral_norm_condexpKernel (hf_int : Integrable f μ) :
    Integrable (fun ω => ∫ y, ‖f y‖ ∂condexpKernel μ m ω) μ := by
  nontriviality Ω
  rw [condexpKernel_eq]
  convert Integrable.integral_norm_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf_int.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ)) using 1

theorem _root_.MeasureTheory.Integrable.norm_integral_condexpKernel [NormedSpace ℝ F]
    (hf_int : Integrable f μ) :
    Integrable (fun ω => ‖∫ y, f y ∂condexpKernel μ m ω‖) μ := by
  nontriviality Ω
  rw [condexpKernel_eq]
  convert Integrable.norm_integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf_int.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ)) using 1

theorem _root_.MeasureTheory.Integrable.integral_condexpKernel [NormedSpace ℝ F]
    (hf_int : Integrable f μ) :
    Integrable (fun ω => ∫ y, f y ∂condexpKernel μ m ω) μ := by
  nontriviality Ω
  rw [condexpKernel_eq]
  convert Integrable.integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf_int.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ)) using 1

theorem integrable_toReal_condexpKernel {s : Set Ω} (hs : MeasurableSet s) :
    Integrable (fun ω => (condexpKernel μ m ω s).toReal) μ := by
  nontriviality Ω
  rw [condexpKernel_eq]
  exact integrable_toReal_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) hs

end Integrability

lemma condexpKernel_ae_eq_condexp' {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω ↦ (condexpKernel μ m ω s).toReal) =ᵐ[μ] μ⟦s | m ⊓ mΩ⟧ := by
  rcases isEmpty_or_nonempty Ω with h | h
  · have : μ = 0 := Measure.eq_zero_of_isEmpty μ
    simpa [this] using trivial
  have h := condDistrib_ae_eq_condexp (μ := μ)
    (measurable_id'' (inf_le_right : m ⊓ mΩ ≤ mΩ)) measurable_id hs
  simp only [id_eq, MeasurableSpace.comap_id, preimage_id_eq] at h
  simp_rw [condexpKernel_apply_eq_condDistrib]
  exact h

lemma condexpKernel_ae_eq_condexp
    (hm : m ≤ mΩ) {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω ↦ (condexpKernel μ m ω s).toReal) =ᵐ[μ] μ⟦s | m⟧ :=
  (condexpKernel_ae_eq_condexp' hs).trans (by rw [inf_of_le_left hm])

lemma condexpKernel_ae_eq_trim_condexp
    (hm : m ≤ mΩ) {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω ↦ (condexpKernel μ m ω s).toReal) =ᵐ[μ.trim hm] μ⟦s | m⟧ := by
  rw [ae_eq_trim_iff hm _ stronglyMeasurable_condexp]
  · exact condexpKernel_ae_eq_condexp hm hs
  · refine Measurable.stronglyMeasurable ?_
    exact @Measurable.ennreal_toReal _ m _ (measurable_condexpKernel hs)

theorem condexp_ae_eq_integral_condexpKernel' [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] (hf_int : Integrable f μ) :
    μ[f|m ⊓ mΩ] =ᵐ[μ] fun ω => ∫ y, f y ∂condexpKernel μ m ω := by
  rcases isEmpty_or_nonempty Ω with h | h
  · have : μ = 0 := Measure.eq_zero_of_isEmpty μ
    simpa [this] using trivial
  have hX : @Measurable Ω Ω mΩ (m ⊓ mΩ) id := measurable_id.mono le_rfl (inf_le_right : m ⊓ mΩ ≤ mΩ)
  simp_rw [condexpKernel_apply_eq_condDistrib]
  have h := condexp_ae_eq_integral_condDistrib_id hX hf_int
  simpa only [MeasurableSpace.comap_id, id_eq] using h

/-- The conditional expectation of `f` with respect to a σ-algebra `m` is almost everywhere equal to
the integral `∫ y, f y ∂(condexpKernel μ m ω)`. -/
theorem condexp_ae_eq_integral_condexpKernel [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] (hm : m ≤ mΩ) (hf_int : Integrable f μ) :
    μ[f|m] =ᵐ[μ] fun ω => ∫ y, f y ∂condexpKernel μ m ω :=
  ((condexp_ae_eq_integral_condexpKernel' hf_int).symm.trans (by rw [inf_of_le_left hm])).symm

end ProbabilityTheory
