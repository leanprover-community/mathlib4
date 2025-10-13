/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.ConditionalProbability

/-!
# Kernel associated with a conditional expectation

We define `condExpKernel μ m`, a kernel from `Ω` to `Ω` such that for all integrable functions `f`,
`μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condExpKernel μ m ω)`.

This kernel is defined if `Ω` is a standard Borel space. In general, `μ⟦s | m⟧` maps a measurable
set `s` to a function `Ω → ℝ≥0∞`, and for all `s` that map is unique up to a `μ`-null set. For all
`a`, the map from sets to `ℝ≥0∞` that we obtain that way verifies some of the properties of a
measure, but the fact that the `μ`-null set depends on `s` can prevent us from finding versions of
the conditional expectation that combine into a true measure. The standard Borel space assumption
on `Ω` allows us to do so.

## Main definitions

* `condExpKernel μ m`: kernel such that `μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condExpKernel μ m ω)`.

## Main statements

* `condExp_ae_eq_integral_condExpKernel`: `μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condExpKernel μ m ω)`.

-/


open MeasureTheory Set Filter TopologicalSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

section AuxLemmas

variable {Ω F : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → F}

theorem _root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_id [TopologicalSpace F]
    (hm : m ≤ mΩ) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable[m.prod mΩ] (fun x : Ω × Ω => f x.2)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω => (id ω, id ω)) μ) := by
  rw [← aestronglyMeasurable_comp_snd_map_prodMk_iff (measurable_id'' hm)] at hf
  simp_rw [id] at hf ⊢
  exact hf

theorem _root_.MeasureTheory.Integrable.comp_snd_map_prod_id [NormedAddCommGroup F] (hm : m ≤ mΩ)
    (hf : Integrable f μ) : Integrable (fun x : Ω × Ω => f x.2)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω => (id ω, id ω)) μ) := by
  rw [← integrable_comp_snd_map_prodMk_iff (measurable_id'' hm)] at hf
  simp_rw [id] at hf ⊢
  exact hf

end AuxLemmas

variable {Ω F : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

open Classical in
/-- Kernel associated with the conditional expectation with respect to a σ-algebra. It satisfies
`μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condExpKernel μ m ω)`.
It is defined as the conditional distribution of the identity given the identity, where the second
identity is understood as a map from `Ω` with the σ-algebra `mΩ` to `Ω` with σ-algebra `m ⊓ mΩ`.
We use `m ⊓ mΩ` instead of `m` to ensure that it is a sub-σ-algebra of `mΩ`. We then use
`Kernel.comap` to get a kernel from `m` to `mΩ` instead of from `m ⊓ mΩ` to `mΩ`. -/
noncomputable irreducible_def condExpKernel (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) : @Kernel Ω Ω m mΩ :=
  if _h : Nonempty Ω then
    Kernel.comap (@condDistrib Ω Ω Ω mΩ _ _ mΩ (m ⊓ mΩ) id id μ _) id
      (measurable_id'' (inf_le_left : m ⊓ mΩ ≤ m))
  else 0

@[deprecated (since := "2025-01-21")] alias condexpKernel := condExpKernel

lemma condExpKernel_eq (μ : Measure Ω) [IsFiniteMeasure μ] [h : Nonempty Ω]
    (m : MeasurableSpace Ω) :
    condExpKernel (mΩ := mΩ) μ m = Kernel.comap (@condDistrib Ω Ω Ω mΩ _ _ mΩ (m ⊓ mΩ) id id μ _) id
      (measurable_id'' (inf_le_left : m ⊓ mΩ ≤ m)) := by
  simp [condExpKernel, h]

@[deprecated (since := "2025-01-21")] alias condexpKernel_eq := condExpKernel_eq

lemma condExpKernel_apply_eq_condDistrib [Nonempty Ω] {ω : Ω} :
    condExpKernel μ m ω = @condDistrib Ω Ω Ω mΩ _ _ mΩ (m ⊓ mΩ) id id μ _ (id ω) := by
  simp [condExpKernel_eq, Kernel.comap_apply]

instance : IsMarkovKernel (condExpKernel μ m) := by
  rcases isEmpty_or_nonempty Ω with h | h
  · exact ⟨fun a ↦ (IsEmpty.false a).elim⟩
  · simpa [condExpKernel, h] using by infer_instance

lemma compProd_trim_condExpKernel (hm : m ≤ mΩ) :
    (μ.trim hm) ⊗ₘ condExpKernel μ m
      = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω ↦ (id ω, id ω)) μ := by
  rcases isEmpty_or_nonempty Ω with h | h
  · simp [Measure.eq_zero_of_isEmpty μ]
  rw [condExpKernel_eq]
  have : m ⊓ mΩ = m := inf_of_le_left hm
  have h := compProd_map_condDistrib (mβ := m) (μ := μ) (X := id) measurable_id.aemeasurable
  rw [← h, trim_eq_map hm]
  congr 1
  ext a s hs
  simp only [Kernel.coe_comap, Function.comp_apply, id_eq]
  congr

lemma condExpKernel_comp_trim (hm : m ≤ mΩ) : condExpKernel μ m ∘ₘ μ.trim hm = μ := by
  rw [← Measure.snd_compProd, compProd_trim_condExpKernel, @Measure.snd_map_prodMk, Measure.map_id]
  exact measurable_id'' hm

section Measurability

variable [NormedAddCommGroup F] {f : Ω → F}

theorem measurable_condExpKernel {s : Set Ω} (hs : MeasurableSet s) :
    Measurable[m] fun ω => condExpKernel μ m ω s := by
  nontriviality Ω
  simp_rw [condExpKernel_apply_eq_condDistrib]
  refine Measurable.mono ?_ (inf_le_left : m ⊓ mΩ ≤ m) le_rfl
  convert measurable_condDistrib (μ := μ) hs
  rw [MeasurableSpace.comap_id]

@[deprecated (since := "2025-01-21")] alias measurable_condexpKernel := measurable_condExpKernel

theorem stronglyMeasurable_condExpKernel {s : Set Ω} (hs : MeasurableSet s) :
    StronglyMeasurable[m] fun ω => condExpKernel μ m ω s :=
  Measurable.stronglyMeasurable (measurable_condExpKernel hs)

theorem _root_.MeasureTheory.StronglyMeasurable.integral_condExpKernel' [NormedSpace ℝ F]
    (hf : StronglyMeasurable f) :
    StronglyMeasurable[m ⊓ mΩ] (fun ω ↦ ∫ y, f y ∂condExpKernel μ m ω) := by
  nontriviality Ω
  simp_rw [condExpKernel_apply_eq_condDistrib]
  exact (hf.comp_measurable measurable_snd).integral_condDistrib

theorem _root_.MeasureTheory.StronglyMeasurable.integral_condExpKernel [NormedSpace ℝ F]
    (hf : StronglyMeasurable f) :
    StronglyMeasurable[m] (fun ω ↦ ∫ y, f y ∂condExpKernel μ m ω) :=
  hf.integral_condExpKernel'.mono inf_le_left

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condExpKernel [NormedSpace ℝ F]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun ω => ∫ y, f y ∂condExpKernel μ m ω) μ := by
  nontriviality Ω
  simp_rw [condExpKernel_apply_eq_condDistrib]
  exact AEStronglyMeasurable.integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf.comp_snd_map_prod_id inf_le_right)

@[deprecated (since := "2025-01-21")]
alias _root_.MeasureTheory.AEStronglyMeasurable.integral_condexpKernel :=
  _root_.MeasureTheory.AEStronglyMeasurable.integral_condExpKernel

theorem aestronglyMeasurable_integral_condExpKernel [NormedSpace ℝ F]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable[m] (fun ω => ∫ y, f y ∂condExpKernel μ m ω) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  have h := aestronglyMeasurable_integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ))
  rw [MeasurableSpace.comap_id] at h
  exact h.mono inf_le_left

@[deprecated (since := "2025-01-21")]
alias aestronglyMeasurable'_integral_condexpKernel := aestronglyMeasurable_integral_condExpKernel

lemma aestronglyMeasurable_trim_condExpKernel (hm : m ≤ mΩ) (hf : AEStronglyMeasurable f μ) :
    ∀ᵐ ω ∂(μ.trim hm), f =ᵐ[condExpKernel μ m ω] hf.mk f := by
  refine Measure.ae_ae_of_ae_comp ?_
  rw [condExpKernel_comp_trim hm]
  exact hf.ae_eq_mk

end Measurability

section Integrability

variable [NormedAddCommGroup F] {f : Ω → F}

theorem _root_.MeasureTheory.Integrable.condExpKernel_ae (hf_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Integrable f (condExpKernel μ m ω) := by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert Integrable.condDistrib_ae
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf_int.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ)) using 1

@[deprecated (since := "2025-01-21")]
alias _root_.MeasureTheory.Integrable.condexpKernel_ae :=
  _root_.MeasureTheory.Integrable.condExpKernel_ae

theorem _root_.MeasureTheory.Integrable.integral_norm_condExpKernel (hf_int : Integrable f μ) :
    Integrable (fun ω => ∫ y, ‖f y‖ ∂condExpKernel μ m ω) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert Integrable.integral_norm_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf_int.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ)) using 1

@[deprecated (since := "2025-01-21")]
alias _root_.MeasureTheory.Integrable.integral_norm_condexpKernel :=
  _root_.MeasureTheory.Integrable.integral_norm_condExpKernel

theorem _root_.MeasureTheory.Integrable.norm_integral_condExpKernel [NormedSpace ℝ F]
    (hf_int : Integrable f μ) :
    Integrable (fun ω => ‖∫ y, f y ∂condExpKernel μ m ω‖) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert Integrable.norm_integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf_int.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ)) using 1

@[deprecated (since := "2025-01-21")]
alias _root_.MeasureTheory.Integrable.norm_integral_condexpKernel :=
  _root_.MeasureTheory.Integrable.norm_integral_condExpKernel

theorem _root_.MeasureTheory.Integrable.integral_condExpKernel [NormedSpace ℝ F]
    (hf_int : Integrable f μ) :
    Integrable (fun ω => ∫ y, f y ∂condExpKernel μ m ω) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert Integrable.integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    (hf_int.comp_snd_map_prod_id (inf_le_right : m ⊓ mΩ ≤ mΩ)) using 1

@[deprecated (since := "2025-01-21")]
alias _root_.MeasureTheory.Integrable.integral_condexpKernel :=
  _root_.MeasureTheory.Integrable.integral_condExpKernel

theorem integrable_toReal_condExpKernel {s : Set Ω} (hs : MeasurableSet s) :
    Integrable (fun ω => (condExpKernel μ m ω).real s) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  exact integrable_toReal_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) hs

end Integrability

lemma condExpKernel_ae_eq_condExp' {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω ↦ (condExpKernel μ m ω).real s) =ᵐ[μ] μ⟦s | m ⊓ mΩ⟧ := by
  rcases isEmpty_or_nonempty Ω with h | h
  · have : μ = 0 := Measure.eq_zero_of_isEmpty μ
    simpa [this] using trivial
  have h := condDistrib_ae_eq_condExp (μ := μ)
    (measurable_id'' (inf_le_right : m ⊓ mΩ ≤ mΩ)) measurable_id hs
  simp only [id_eq, MeasurableSpace.comap_id, preimage_id_eq] at h
  simp_rw [condExpKernel_apply_eq_condDistrib]
  exact h

lemma condExpKernel_ae_eq_condExp
    (hm : m ≤ mΩ) {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω ↦ (condExpKernel μ m ω).real s) =ᵐ[μ] μ⟦s | m⟧ :=
  (condExpKernel_ae_eq_condExp' hs).trans (by rw [inf_of_le_left hm])

lemma condExpKernel_ae_eq_trim_condExp
    (hm : m ≤ mΩ) {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω ↦ (condExpKernel μ m ω).real s) =ᵐ[μ.trim hm] μ⟦s | m⟧ := by
  simp_rw [measureReal_def]
  rw [(measurable_condExpKernel hs).ennreal_toReal.stronglyMeasurable.ae_eq_trim_iff hm
    stronglyMeasurable_condExp]
  exact condExpKernel_ae_eq_condExp hm hs

theorem condExp_ae_eq_integral_condExpKernel' [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] (hf_int : Integrable f μ) :
    μ[f|m ⊓ mΩ] =ᵐ[μ] fun ω => ∫ y, f y ∂condExpKernel μ m ω := by
  rcases isEmpty_or_nonempty Ω with h | h
  · have : μ = 0 := Measure.eq_zero_of_isEmpty μ
    simpa [this] using trivial
  have hX : @Measurable Ω Ω mΩ (m ⊓ mΩ) id := measurable_id.mono le_rfl (inf_le_right : m ⊓ mΩ ≤ mΩ)
  simp_rw [condExpKernel_apply_eq_condDistrib]
  have h := condExp_ae_eq_integral_condDistrib_id hX hf_int
  simpa only [MeasurableSpace.comap_id, id_eq] using h

/-- The conditional expectation of `f` with respect to a σ-algebra `m` is almost everywhere equal to
the integral `∫ y, f y ∂(condExpKernel μ m ω)`. -/
theorem condExp_ae_eq_integral_condExpKernel [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] (hm : m ≤ mΩ) (hf_int : Integrable f μ) :
    μ[f|m] =ᵐ[μ] fun ω => ∫ y, f y ∂condExpKernel μ m ω :=
  ((condExp_ae_eq_integral_condExpKernel' hf_int).symm.trans (by rw [inf_of_le_left hm])).symm

/-- Auxiliary lemma for `condExp_ae_eq_trim_integral_condExpKernel`. -/
theorem condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable
    [NormedAddCommGroup F] {f : Ω → F} [NormedSpace ℝ F] [CompleteSpace F]
    (hm : m ≤ mΩ) (hf : StronglyMeasurable f) (hf_int : Integrable f μ) :
    μ[f|m] =ᵐ[μ.trim hm] fun ω ↦ ∫ y, f y ∂condExpKernel μ m ω := by
  refine StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm ?_ ?_ ?_
  · exact stronglyMeasurable_condExp
  · exact hf.integral_condExpKernel
  · exact condExp_ae_eq_integral_condExpKernel hm hf_int

/-- The conditional expectation of `f` with respect to a σ-algebra `m` is
(`μ.trim hm`)-almost everywhere equal to the integral `∫ y, f y ∂(condExpKernel μ m ω)`. -/
theorem condExp_ae_eq_trim_integral_condExpKernel [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] (hm : m ≤ mΩ) (hf_int : Integrable f μ) :
    μ[f|m] =ᵐ[μ.trim hm] fun ω ↦ ∫ y, f y ∂condExpKernel μ m ω := by
  refine (condExp_congr_ae_trim hm hf_int.1.ae_eq_mk).trans ?_
  refine (condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable hm
    hf_int.1.stronglyMeasurable_mk ?_).trans ?_
  · rwa [integrable_congr hf_int.1.ae_eq_mk.symm]
  filter_upwards [aestronglyMeasurable_trim_condExpKernel hm hf_int.1] with ω hω
  rw [integral_congr_ae hω]

section Cond

/-! ### Relation between conditional expectation, conditional kernel and the conditional measure. -/

open MeasurableSpace

variable {s t : Set Ω} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [StandardBorelSpace Ω]

lemma condExp_generateFrom_singleton (hs : MeasurableSet s) {f : Ω → F} (hf : Integrable f μ) :
    μ[f | generateFrom {s}] =ᵐ[μ.restrict s] fun _ ↦ ∫ x, f x ∂μ[|s] := by
  by_cases hμs : μ s = 0
  · rw [Measure.restrict_eq_zero.2 hμs]
    rfl
  refine ae_eq_trans (condExp_restrict_ae_eq_restrict
    (generateFrom_singleton_le hs)
    (measurableSet_generateFrom rfl) hf).symm ?_
  · refine (ae_eq_condExp_of_forall_setIntegral_eq (generateFrom_singleton_le hs) hf.restrict ?_ ?_
      stronglyMeasurable_const.aestronglyMeasurable).symm
    · rintro t - -
      rw [integrableOn_const_iff]
      exact Or.inr <| measure_lt_top (μ.restrict s) t
    · rintro t ht -
      obtain (h | h | h | h) := measurableSet_generateFrom_singleton_iff.1 ht
      · simp [h]
      · simp only [h, cond, integral_smul_measure, ENNReal.toReal_inv, integral_const,
        MeasurableSet.univ, measureReal_restrict_apply, univ_inter, measureReal_restrict_apply_self,
        ← measureReal_def]
        rw [smul_inv_smul₀, Measure.restrict_restrict hs, inter_self]
        exact ENNReal.toReal_ne_zero.2 ⟨hμs, measure_ne_top _ _⟩
      · simp only [h, integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
          measureReal_restrict_apply hs.compl, compl_inter_self, measureReal_empty, zero_smul,
          ((Measure.restrict_apply_eq_zero hs.compl).2 <| compl_inter_self s ▸ measure_empty),
          setIntegral_measure_zero]
      · simp only [h, Measure.restrict_univ, cond, integral_smul_measure, ENNReal.toReal_inv, ←
        measureReal_def, integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter]
        rw [smul_inv_smul₀]
        exact (measureReal_ne_zero_iff (by finiteness)).2 hμs

lemma condExp_set_generateFrom_singleton (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ⟦t | generateFrom {s}⟧ =ᵐ[μ.restrict s] fun _ ↦ μ[|s].real t := by
  rw [← integral_indicator_one ht]
  exact condExp_generateFrom_singleton hs <| Integrable.indicator (integrable_const 1) ht

lemma condExpKernel_singleton_ae_eq_cond [StandardBorelSpace Ω] (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    ∀ᵐ ω ∂μ.restrict s,
      condExpKernel μ (generateFrom {s}) ω t = μ[t|s] := by
  have : (fun ω ↦ (condExpKernel μ (generateFrom {s}) ω).real t) =ᵐ[μ.restrict s]
      μ⟦t | generateFrom {s}⟧ :=
    ae_restrict_le <| condExpKernel_ae_eq_condExp
      (generateFrom_singleton_le hs) ht
  filter_upwards [condExp_set_generateFrom_singleton hs ht, this] with ω hω₁ hω₂
  rwa [hω₁, measureReal_def, measureReal_def,
    ENNReal.toReal_eq_toReal (measure_ne_top _ t) (measure_ne_top _ t)] at hω₂

end Cond

end ProbabilityTheory
