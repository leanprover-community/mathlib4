/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Regular conditional probability distribution

We define the regular conditional probability distribution of `Y : α → Ω` given `X : α → β`, where
`Ω` is a standard Borel space. This is a `Kernel β Ω` such that for almost all `a`, `condDistrib`
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

* `condDistrib_ae_eq_condExp`: for almost all `a`, `condDistrib` evaluated at `X a` and a
  measurable set `s` is equal to the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`.
* `condExp_prod_ae_eq_integral_condDistrib`: the conditional expectation
  `μ[(fun a => f (X a, Y a)) | X; mβ]` is almost everywhere equal to the integral
  `∫ y, f (X a, y) ∂(condDistrib Y X μ (X a))`.

-/


open MeasureTheory Set Filter TopologicalSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {α β Ω F : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [Nonempty Ω] [NormedAddCommGroup F] {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
  {X : α → β} {Y : α → Ω}

/-- **Regular conditional probability distribution**: kernel associated with the conditional
expectation of `Y` given `X`.
For almost all `a`, `condDistrib Y X μ` evaluated at `X a` and a measurable set `s` is equal to
the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`. It also satisfies the equality
`μ[(fun a => f (X a, Y a)) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂(condDistrib Y X μ (X a))`
for all integrable functions `f`. -/
noncomputable irreducible_def condDistrib {_ : MeasurableSpace α} [MeasurableSpace β] (Y : α → Ω)
    (X : α → β) (μ : Measure α) [IsFiniteMeasure μ] : Kernel β Ω :=
  (μ.map fun a => (X a, Y a)).condKernel

instance [MeasurableSpace β] : IsMarkovKernel (condDistrib Y X μ) := by
  rw [condDistrib]; infer_instance

variable {mβ : MeasurableSpace β} {s : Set Ω} {t : Set β} {f : β × Ω → F}

/-- If the singleton `{x}` has non-zero mass for `μ.map X`, then for all `s : Set Ω`,
`condDistrib Y X μ x s = (μ.map X {x})⁻¹ * μ.map (fun a => (X a, Y a)) ({x} ×ˢ s)` . -/
lemma condDistrib_apply_of_ne_zero [MeasurableSingletonClass β]
    (hY : Measurable Y) (x : β) (hX : μ.map X {x} ≠ 0) (s : Set Ω) :
    condDistrib Y X μ x s = (μ.map X {x})⁻¹ * μ.map (fun a => (X a, Y a)) ({x} ×ˢ s) := by
  rw [condDistrib, Measure.condKernel_apply_of_ne_zero _ s]
  · rw [Measure.fst_map_prodMk hY]
  · rwa [Measure.fst_map_prodMk hY]

lemma compProd_map_condDistrib (hY : AEMeasurable Y μ) :
    (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map fun a ↦ (X a, Y a) := by
  rw [condDistrib, ← Measure.fst_map_prodMk₀ hY, Measure.disintegrate]

lemma condDistrib_comp_map (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    condDistrib Y X μ ∘ₘ (μ.map X) = μ.map Y := by
  rw [← Measure.snd_compProd, compProd_map_condDistrib hY, Measure.snd_map_prodMk₀ hX]

lemma condDistrib_congr {X' : α → β} {Y' : α → Ω} (hY : Y =ᵐ[μ] Y') (hX : X =ᵐ[μ] X') :
    condDistrib Y X μ = condDistrib Y' X' μ := by
  rw [condDistrib, condDistrib]
  congr 1
  rw [Measure.map_congr]
  filter_upwards [hX, hY] with a ha hb using by rw [ha, hb]

lemma condDistrib_congr_right {X' : α → β} (hX : X =ᵐ[μ] X') :
    condDistrib Y X μ = condDistrib Y X' μ :=
  condDistrib_congr (by rfl) hX

lemma condDistrib_congr_left {Y' : α → Ω} (hY : Y =ᵐ[μ] Y') :
    condDistrib Y X μ = condDistrib Y' X μ :=
  condDistrib_congr hY (by rfl)

section Measurability

theorem measurable_condDistrib (hs : MeasurableSet s) :
    Measurable[mβ.comap X] fun a => condDistrib Y X μ (X a) s :=
  (Kernel.measurable_coe _ hs).comp (Measurable.of_comap_le le_rfl)

theorem _root_.MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    (∀ᵐ a ∂μ.map X, Integrable (fun ω => f (a, ω)) (condDistrib Y X μ a)) ∧
      Integrable (fun a => ∫ ω, ‖f (a, ω)‖ ∂condDistrib Y X μ a) (μ.map X) ↔
    Integrable f (μ.map fun a => (X a, Y a)) := by
  rw [condDistrib, ← hf.ae_integrable_condKernel_iff, Measure.fst_map_prodMk₀ hY]

variable [NormedSpace ℝ F]

theorem _root_.MeasureTheory.StronglyMeasurable.integral_condDistrib (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun x ↦ ∫ y, f (x, y) ∂condDistrib Y X μ x) := by
  rw [condDistrib]; exact hf.integral_kernel_prod_right'

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂condDistrib Y X μ x) (μ.map X) := by
  rw [← Measure.fst_map_prodMk₀ hY, condDistrib]; exact hf.integral_condKernel

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf.integral_condDistrib_map hY).comp_aemeasurable hX

theorem stronglyMeasurable_integral_condDistrib (hf : StronglyMeasurable f) :
    StronglyMeasurable[mβ.comap X] (fun a ↦ ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) :=
  (hf.integral_condDistrib).comp_measurable <| Measurable.of_comap_le le_rfl

theorem aestronglyMeasurable_integral_condDistrib (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable[mβ.comap X] (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf.integral_condDistrib_map hY).comp_ae_measurable' hX

end Measurability

/-- `condDistrib` is a.e. uniquely defined as the kernel satisfying the defining property of
`condKernel`. -/
theorem condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (hX : Measurable X) (hY : Measurable Y)
    {κ : Kernel β Ω} [IsFiniteKernel κ] (hκ : μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ) :
    condDistrib Y X μ =ᵐ[μ.map X] κ := by
  have heq : μ.map X = (μ.map (fun x ↦ (X x, Y x))).fst := by
    ext s hs
    rw [Measure.map_apply hX hs, Measure.fst_apply hs, Measure.map_apply]
    exacts [rfl, Measurable.prod hX hY, measurable_fst hs]
  rw [heq, condDistrib]
  symm
  refine eq_condKernel_of_measure_eq_compProd _ ?_
  convert hκ
  exact heq.symm

/-- `condDistrib` is a.e. uniquely defined as the kernel satisfying the defining property of
`condKernel`. -/
lemma condDistrib_ae_eq_of_measure_eq_compProd
    (X : α → β) (hY : AEMeasurable Y μ) {κ : Kernel β Ω} [IsFiniteKernel κ]
    (hκ : μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ) :
    condDistrib Y X μ =ᵐ[μ.map X] κ := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  suffices condDistrib (hY.mk Y) (hX.mk X) μ =ᵐ[μ.map (hX.mk X)] κ by
    rwa [Measure.map_congr hX.ae_eq_mk, condDistrib_congr hY.ae_eq_mk hX.ae_eq_mk]
  refine condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (μ := μ)
    hX.measurable_mk hY.measurable_mk ((Eq.trans ?_ hκ).trans ?_)
  · refine Measure.map_congr ?_
    filter_upwards [hX.ae_eq_mk, hY.ae_eq_mk] with a haX haY using by rw [haX, haY]
  · rw [Measure.map_congr hX.ae_eq_mk]

lemma condDistrib_ae_eq_iff_measure_eq_compProd
    (X : α → β) (hY : AEMeasurable Y μ) (κ : Kernel β Ω) [IsFiniteKernel κ] :
    (condDistrib Y X μ =ᵐ[μ.map X] κ) ↔ μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ := by
  refine ⟨fun h ↦ ?_, condDistrib_ae_eq_of_measure_eq_compProd X hY⟩
  rw [Measure.compProd_congr h.symm, compProd_map_condDistrib hY]

lemma condDistrib_comp {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω']
    [Nonempty Ω'] (X : α → β) (hY : AEMeasurable Y μ) {f : Ω → Ω'} (hf : Measurable f) :
    condDistrib (f ∘ Y) X μ =ᵐ[μ.map X] (condDistrib Y X μ).map f := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  refine condDistrib_ae_eq_of_measure_eq_compProd X (by fun_prop) ?_
  calc μ.map (fun x ↦ (X x, (f ∘ Y) x))
  _ = (μ.map (fun x ↦ (X x, Y x))).map (Prod.map id f) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    simp [Function.comp_def]
  _ = (μ.map X ⊗ₘ condDistrib Y X μ).map (Prod.map id f) := by rw [compProd_map_condDistrib hY]
  _ = μ.map X ⊗ₘ (condDistrib Y X μ).map f := by rw [Measure.compProd_map hf]

lemma condDistrib_comp_self (X : α → β) {f : β → Ω} (hf : Measurable f) :
    condDistrib (f ∘ X) X μ =ᵐ[μ.map X] Kernel.deterministic f hf := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  refine condDistrib_ae_eq_of_measure_eq_compProd X (by fun_prop) ?_
  rw [Measure.compProd_deterministic, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
  simp [Function.comp_def]

lemma condDistrib_self (Y : α → Ω) : condDistrib Y Y μ =ᵐ[μ.map Y] Kernel.id := by
  simpa using condDistrib_comp_self Y measurable_id

lemma condDistrib_const (X : α → β) (c : Ω) :
    condDistrib (fun _ ↦ c) X μ =ᵐ[μ.map X] Kernel.deterministic (fun _ ↦ c) (by fun_prop) := by
  have : (fun _ : α ↦ c) = (fun _ : β ↦ c) ∘ X := rfl
  rw [this]
  filter_upwards [condDistrib_comp_self X (measurable_const (a := c))] with b hb
  rw [hb]

lemma condDistrib_map {γ : Type*} {mγ : MeasurableSpace γ}
    {ν : Measure γ} [IsFiniteMeasure ν] {f : γ → α}
    (hX : AEMeasurable X (ν.map f)) (hY : AEMeasurable Y (ν.map f)) (hf : AEMeasurable f ν) :
    condDistrib Y X (ν.map f) =ᵐ[ν.map (X ∘ f)] condDistrib (Y ∘ f) (X ∘ f) ν := by
  rw [← AEMeasurable.map_map_of_aemeasurable hX hf]
  refine condDistrib_ae_eq_of_measure_eq_compProd (μ := ν.map f) X hY ?_
  rw [AEMeasurable.map_map_of_aemeasurable hX hf, compProd_map_condDistrib (by fun_prop),
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) hf]
  simp [Function.comp_def]

lemma condDistrib_fst_prod {γ : Type*} {mγ : MeasurableSpace γ}
    (X : α → β) (hY : AEMeasurable Y μ) (ν : Measure γ) [IsProbabilityMeasure ν] :
    condDistrib (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) (μ.prod ν) =ᵐ[μ.map X] condDistrib Y X μ := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  have : μ = (μ.prod ν).map (fun ω ↦ ω.1) := by simp [Measure.map_fst_prod]
  have h_map := condDistrib_map (X := X) (Y := Y) (f := Prod.fst (α := α) (β := γ))
      (ν := μ.prod ν) (mα := inferInstance) (mβ := inferInstance)
      (by simpa) (by simpa) (by fun_prop)
  rw [← AEMeasurable.map_map_of_aemeasurable (by simpa) (by fun_prop)] at h_map
  simp only [Measure.map_fst_prod, measure_univ, one_smul] at h_map
  exact h_map.symm

lemma condDistrib_snd_prod {γ : Type*} {mγ : MeasurableSpace γ}
    (X : α → β) (hY : AEMeasurable Y μ) (ν : Measure γ) [IsProbabilityMeasure ν] :
    condDistrib (fun ω ↦ Y ω.2) (fun ω ↦ X ω.2) (ν.prod μ) =ᵐ[μ.map X] condDistrib Y X μ := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  have : μ = (μ.prod ν).map (fun ω ↦ ω.1) := by simp [Measure.map_fst_prod]
  have h_map := condDistrib_map (X := X) (Y := Y) (f := Prod.snd (β := α) (α := γ))
      (ν := ν.prod μ) (mα := inferInstance) (mβ := inferInstance)
      (by simpa) (by simpa) (by fun_prop)
  rw [← AEMeasurable.map_map_of_aemeasurable (by simpa) (by fun_prop)] at h_map
  simp only [Measure.map_snd_prod, measure_univ, one_smul] at h_map
  exact h_map.symm

section Integrability

theorem integrable_toReal_condDistrib (hX : AEMeasurable X μ) (hs : MeasurableSet s) :
    Integrable (fun a => (condDistrib Y X μ (X a)).real s) μ := by
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · exact Measurable.comp_aemeasurable (Kernel.measurable_coe _ hs) hX
  · refine ne_of_lt ?_
    calc
      ∫⁻ a, condDistrib Y X μ (X a) s ∂μ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun a => prob_le_one
      _ = μ univ := lintegral_one
      _ < ∞ := measure_lt_top _ _

theorem _root_.MeasureTheory.Integrable.condDistrib_ae_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    ∀ᵐ b ∂μ.map X, Integrable (fun ω => f (b, ω)) (condDistrib Y X μ b) := by
  rw [condDistrib, ← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.condKernel_ae

theorem _root_.MeasureTheory.Integrable.condDistrib_ae (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    ∀ᵐ a ∂μ, Integrable (fun ω => f (X a, ω)) (condDistrib Y X μ (X a)) :=
  ae_of_ae_map hX (hf_int.condDistrib_ae_map hY)

theorem _root_.MeasureTheory.Integrable.integral_norm_condDistrib_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂condDistrib Y X μ x) (μ.map X) := by
  rw [condDistrib, ← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.integral_norm_condKernel

theorem _root_.MeasureTheory.Integrable.integral_norm_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ∫ y, ‖f (X a, y)‖ ∂condDistrib Y X μ (X a)) μ :=
  (hf_int.integral_norm_condDistrib_map hY).comp_aemeasurable hX

variable [NormedSpace ℝ F]

theorem _root_.MeasureTheory.Integrable.norm_integral_condDistrib_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ‖∫ y, f (x, y) ∂condDistrib Y X μ x‖) (μ.map X) := by
  rw [condDistrib, ← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.norm_integral_condKernel

theorem _root_.MeasureTheory.Integrable.norm_integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ‖∫ y, f (X a, y) ∂condDistrib Y X μ (X a)‖) μ :=
  (hf_int.norm_integral_condDistrib_map hY).comp_aemeasurable hX

theorem _root_.MeasureTheory.Integrable.integral_condDistrib_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ∫ y, f (x, y) ∂condDistrib Y X μ x) (μ.map X) :=
  (integrable_norm_iff (hf_int.1.integral_condDistrib_map hY)).mp
    (hf_int.norm_integral_condDistrib_map hY)

theorem _root_.MeasureTheory.Integrable.integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf_int.integral_condDistrib_map hY).comp_aemeasurable hX

end Integrability

theorem setLIntegral_preimage_condDistrib (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫⁻ a in X ⁻¹' t, condDistrib Y X μ (X a) s ∂μ = μ (X ⁻¹' t ∩ Y ⁻¹' s) := by
  rw [← lintegral_map (Kernel.measurable_coe _ hs) hX, condDistrib, ← Measure.restrict_map hX ht,
    ← Measure.fst_map_prodMk₀ hY, Measure.setLIntegral_condKernel_eq_measure_prod ht hs,
    Measure.map_apply_of_aemeasurable (hX.aemeasurable.prodMk hY) (ht.prod hs), mk_preimage_prod]

theorem setLIntegral_condDistrib_of_measurableSet (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hs : MeasurableSet s) {t : Set α} (ht : MeasurableSet[mβ.comap X] t) :
    ∫⁻ a in t, condDistrib Y X μ (X a) s ∂μ = μ (t ∩ Y ⁻¹' s) := by
  obtain ⟨t', ht', rfl⟩ := ht
  rw [setLIntegral_preimage_condDistrib hX hY hs ht']

/-- For almost every `a : α`, the `condDistrib Y X μ` kernel applied to `X a` and a measurable set
`s` is equal to the conditional expectation of the indicator of `Y ⁻¹' s`. -/
theorem condDistrib_ae_eq_condExp (hX : Measurable X) (hY : Measurable Y) (hs : MeasurableSet s) :
    (fun a => (condDistrib Y X μ (X a)).real s) =ᵐ[μ] μ⟦Y ⁻¹' s|mβ.comap X⟧ := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le ?_ ?_ ?_ ?_
  · exact (integrable_const _).indicator (hY hs)
  · exact fun t _ _ => (integrable_toReal_condDistrib hX.aemeasurable hs).integrableOn
  · intro t ht _
    simp_rw [measureReal_def]
    rw [integral_toReal ((measurable_condDistrib hs).mono hX.comap_le le_rfl).aemeasurable
      (Eventually.of_forall fun ω => measure_lt_top (condDistrib Y X μ (X ω)) _),
      integral_indicator_const _ (hY hs), measureReal_restrict_apply (hY hs), smul_eq_mul, mul_one,
      inter_comm, setLIntegral_condDistrib_of_measurableSet hX hY.aemeasurable hs ht,
      measureReal_def]
  · exact (measurable_condDistrib hs).ennreal_toReal.aestronglyMeasurable

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `condDistrib` kernel. -/
theorem condExp_prod_ae_eq_integral_condDistrib' [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    μ[fun a => f (X a, Y a)|mβ.comap X] =ᵐ[μ]
      fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a) := by
  have hf_int' : Integrable (fun a => f (X a, Y a)) μ :=
    (integrable_map_measure hf_int.1 (hX.aemeasurable.prodMk hY)).mp hf_int
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hf_int' (fun s _ _ => ?_) ?_ ?_).symm
  · exact (hf_int.integral_condDistrib hX.aemeasurable hY).integrableOn
  · rintro s ⟨t, ht, rfl⟩ _
    change ∫ a in X ⁻¹' t, ((fun x' => ∫ y, f (x', y) ∂(condDistrib Y X μ) x') ∘ X) a ∂μ =
      ∫ a in X ⁻¹' t, f (X a, Y a) ∂μ
    simp only [Function.comp_apply]
    rw [← integral_map hX.aemeasurable (f := fun x' => ∫ y, f (x', y) ∂(condDistrib Y X μ) x')]
    swap
    · rw [← Measure.restrict_map hX ht]
      exact (hf_int.1.integral_condDistrib_map hY).restrict
    rw [← Measure.restrict_map hX ht, ← Measure.fst_map_prodMk₀ hY, condDistrib,
      Measure.setIntegral_condKernel_univ_right ht hf_int.integrableOn,
      setIntegral_map (ht.prod MeasurableSet.univ) hf_int.1 (hX.aemeasurable.prodMk hY),
      mk_preimage_prod, preimage_univ, inter_univ]
  · exact aestronglyMeasurable_integral_condDistrib hX.aemeasurable hY hf_int.1

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `condDistrib` kernel. -/
theorem condExp_prod_ae_eq_integral_condDistrib₀ [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a)))
    (hf_int : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a)|mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a) :=
  have hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure hf (hX.aemeasurable.prodMk hY)]
  condExp_prod_ae_eq_integral_condDistrib' hX hY hf_int'

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `condDistrib` kernel. -/
theorem condExp_prod_ae_eq_integral_condDistrib [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ) (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a)|mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a) :=
  have hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure hf.aestronglyMeasurable (hX.aemeasurable.prodMk hY)]
  condExp_prod_ae_eq_integral_condDistrib' hX hY hf_int'

theorem condExp_ae_eq_integral_condDistrib [NormedSpace ℝ F] [CompleteSpace F] (hX : Measurable X)
    (hY : AEMeasurable Y μ) {f : Ω → F} (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun a => f (Y a)) μ) :
    μ[fun a => f (Y a)|mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂condDistrib Y X μ (X a) :=
  condExp_prod_ae_eq_integral_condDistrib hX hY (hf.comp_measurable measurable_snd) hf_int

/-- The conditional expectation of `Y` given `X` is almost everywhere equal to the integral
`∫ y, y ∂(condDistrib Y X μ (X a))`. -/
theorem condExp_ae_eq_integral_condDistrib' {Ω} [NormedAddCommGroup Ω] [NormedSpace ℝ Ω]
    [CompleteSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω] {Y : α → Ω}
    (hX : Measurable X) (hY_int : Integrable Y μ) :
    μ[Y|mβ.comap X] =ᵐ[μ] fun a => ∫ y, y ∂condDistrib Y X μ (X a) :=
  condExp_ae_eq_integral_condDistrib hX hY_int.1.aemeasurable stronglyMeasurable_id hY_int

open MeasureTheory

theorem _root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prodMk {Ω F} {mΩ : MeasurableSpace Ω}
    (X : Ω → β) {μ : Measure Ω} [TopologicalSpace F] {f : Ω → F} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) := by
  refine ⟨fun x => hf.mk f x.2, hf.stronglyMeasurable_mk.comp_measurable measurable_snd, ?_⟩
  suffices h : Measure.QuasiMeasurePreserving Prod.snd (μ.map fun ω ↦ (X ω, ω)) μ from
    Measure.QuasiMeasurePreserving.ae_eq h hf.ae_eq_mk
  refine ⟨measurable_snd, Measure.AbsolutelyContinuous.mk fun s hs hμs => ?_⟩
  rw [Measure.map_apply measurable_snd hs]
  by_cases hX : AEMeasurable X μ
  · rw [Measure.map_apply_of_aemeasurable]
    · rw [← univ_prod, mk_preimage_prod, preimage_univ, univ_inter, preimage_id']
      exact hμs
    · exact hX.prodMk aemeasurable_id
    · exact measurable_snd hs
  · rw [Measure.map_of_not_aemeasurable]
    · simp
    · contrapose! hX; exact measurable_fst.comp_aemeasurable hX

@[deprecated (since := "2025-03-05")]
alias _root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_mk :=
  MeasureTheory.AEStronglyMeasurable.comp_snd_map_prodMk

theorem _root_.MeasureTheory.Integrable.comp_snd_map_prodMk
    {Ω} {mΩ : MeasurableSpace Ω} (X : Ω → β) {μ : Measure Ω} {f : Ω → F} (hf_int : Integrable f μ) :
    Integrable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) := by
  by_cases hX : AEMeasurable X μ
  · have hf := hf_int.1.comp_snd_map_prodMk X (mΩ := mΩ) (mβ := mβ)
    refine ⟨hf, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_map' hf.enorm (hX.prodMk aemeasurable_id)]
    exact hf_int.2
  · rw [Measure.map_of_not_aemeasurable]
    · simp
    · contrapose! hX; exact measurable_fst.comp_aemeasurable hX

@[deprecated (since := "2025-03-05")]
alias _root_.MeasureTheory.Integrable.comp_snd_map_prod_mk :=
  MeasureTheory.Integrable.comp_snd_map_prodMk

theorem aestronglyMeasurable_comp_snd_map_prodMk_iff {Ω F} {_ : MeasurableSpace Ω}
    [TopologicalSpace F] {X : Ω → β} {μ : Measure Ω} (hX : Measurable X) {f : Ω → F} :
    AEStronglyMeasurable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) ↔
      AEStronglyMeasurable f μ :=
  ⟨fun h => h.comp_measurable (hX.prodMk measurable_id), fun h => h.comp_snd_map_prodMk X⟩

@[deprecated (since := "2025-03-05")]
alias aestronglyMeasurable_comp_snd_map_prod_mk_iff :=
  aestronglyMeasurable_comp_snd_map_prodMk_iff

theorem integrable_comp_snd_map_prodMk_iff {Ω} {_ : MeasurableSpace Ω} {X : Ω → β} {μ : Measure Ω}
    (hX : Measurable X) {f : Ω → F} :
    Integrable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) ↔ Integrable f μ :=
  ⟨fun h => h.comp_measurable (hX.prodMk measurable_id), fun h => h.comp_snd_map_prodMk X⟩

@[deprecated (since := "2025-03-05")]
alias integrable_comp_snd_map_prod_mk_iff := integrable_comp_snd_map_prodMk_iff

theorem condExp_ae_eq_integral_condDistrib_id [NormedSpace ℝ F] [CompleteSpace F] {X : Ω → β}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hX : Measurable X) {f : Ω → F} (hf_int : Integrable f μ) :
    μ[f|mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂condDistrib id X μ (X a) :=
  condExp_prod_ae_eq_integral_condDistrib' hX aemeasurable_id (hf_int.comp_snd_map_prodMk X)

end ProbabilityTheory
