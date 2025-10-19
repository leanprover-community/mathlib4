/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Bochner integral of a function against the composition and the composition-products of two kernels

We prove properties of the composition and the composition-product of two kernels.

If `κ` is a kernel from `α` to `β` and `η` is a kernel from `β` to `γ`, we can form their
composition `η ∘ₖ κ : Kernel α γ`. We proved in `ProbabilityTheory.Kernel.lintegral_comp` that it
verifies `∫⁻ c, f c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, f c ∂(η b) ∂(κ a)`. In this file, we
prove the same equality for the Bochner integral.

If `κ` is an s-finite kernel from `α` to `β` and `η` is an s-finite kernel from `α × β` to `γ`,
we can form their composition-product `κ ⊗ₖ η : Kernel α (β × γ)`.
We proved in `ProbabilityTheory.Kernel.lintegral_compProd` that it
verifies `∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`. In this file, we
prove the same equality for the Bochner integral.

## Main statements

* `ProbabilityTheory.integral_compProd`: the integral against the composition-product is
  `∫ z, f z ∂((κ ⊗ₖ η) a) = ∫ x, ∫ y, f (x, y) ∂(η (a, x)) ∂(κ a)`.

* `ProbabilityTheory.integral_comp`: the integral against the composition is
  `∫⁻ z, f z ∂((η ∘ₖ κ) a) = ∫⁻ x, ∫⁻ y, f y ∂(η x) ∂(κ a)`.

## Implementation details

This file is to a large extent a copy of part of `Mathlib/MeasureTheory/Integral/Prod.lean`.
The product of two measures is a particular case of composition-product of kernels and
it turns out that once the measurability of the Lebesgue integral of a kernel is proved,
almost all proofs about integrals against products of measures extend with minimal modifications
to the composition-product of two kernels.

The composition of kernels can also be expressed easily with the composition-product and therefore
the proofs about the composition are only simplified versions of the ones for the
composition-product. However it is necessary to do all the proofs once again because the
composition-product requires s-finiteness while the composition does not.
-/


noncomputable section

open Set Function Real ENNReal MeasureTheory Filter ProbabilityTheory ProbabilityTheory.Kernel
open scoped Topology ENNReal MeasureTheory

variable {α β γ E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} [NormedAddCommGroup E] {a : α}

namespace ProbabilityTheory

section compProd

variable {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel (α × β) γ} [IsSFiniteKernel η]

theorem hasFiniteIntegral_prodMk_left (a : α) {s : Set (β × γ)} (h2s : (κ ⊗ₖ η) a s ≠ ∞) :
    HasFiniteIntegral (fun b => (η (a, b)).real (Prod.mk b ⁻¹' s)) (κ a) := by
  let t := toMeasurable ((κ ⊗ₖ η) a) s
  simp_rw [hasFiniteIntegral_iff_enorm, measureReal_def, enorm_eq_ofReal toReal_nonneg]
  calc
    ∫⁻ b, ENNReal.ofReal (η (a, b) (Prod.mk b ⁻¹' s)).toReal ∂κ a
    _ ≤ ∫⁻ b, η (a, b) (Prod.mk b ⁻¹' t) ∂κ a := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_kernel_lt_top a h2s] with b hb
      rw [ofReal_toReal hb.ne]
      exact measure_mono (preimage_mono (subset_toMeasurable _ _))
    _ ≤ (κ ⊗ₖ η) a t := le_compProd_apply _ _ _ _
    _ = (κ ⊗ₖ η) a s := measure_toMeasurable s
    _ < ⊤ := h2s.lt_top

@[deprecated (since := "2025-03-05")]
alias hasFiniteIntegral_prod_mk_left := hasFiniteIntegral_prodMk_left

theorem integrable_kernel_prodMk_left (a : α) {s : Set (β × γ)} (hs : MeasurableSet s)
    (h2s : (κ ⊗ₖ η) a s ≠ ∞) : Integrable (fun b => (η (a, b)).real (Prod.mk b ⁻¹' s)) (κ a) := by
  constructor
  · exact (measurable_kernel_prodMk_left' hs a).ennreal_toReal.aestronglyMeasurable
  · exact hasFiniteIntegral_prodMk_left a h2s

@[deprecated (since := "2025-03-05")]
alias integrable_kernel_prod_mk_left := integrable_kernel_prodMk_left

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_compProd [NormedSpace ℝ E]
    ⦃f : β × γ → E⦄ (hf : AEStronglyMeasurable f ((κ ⊗ₖ η) a)) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂η (a, x)) (κ a) :=
  ⟨fun x => ∫ y, hf.mk f (x, y) ∂η (a, x), hf.stronglyMeasurable_mk.integral_kernel_prod_right'', by
    filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩

theorem _root_.MeasureTheory.AEStronglyMeasurable.compProd_mk_left {δ : Type*} [TopologicalSpace δ]
    {f : β × γ → δ} (hf : AEStronglyMeasurable f ((κ ⊗ₖ η) a)) :
    ∀ᵐ x ∂κ a, AEStronglyMeasurable (fun y => f (x, y)) (η (a, x)) := by
  filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with x hx using
    ⟨fun y => hf.mk f (x, y), hf.stronglyMeasurable_mk.comp_measurable measurable_prodMk_left, hx⟩

/-! ### Integrability -/


theorem hasFiniteIntegral_compProd_iff ⦃f : β × γ → E⦄ (h1f : StronglyMeasurable f) :
    HasFiniteIntegral f ((κ ⊗ₖ η) a) ↔
      (∀ᵐ x ∂κ a, HasFiniteIntegral (fun y => f (x, y)) (η (a, x))) ∧
        HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂η (a, x)) (κ a) := by
  simp only [hasFiniteIntegral_iff_enorm]
  rw [lintegral_compProd _ _ _ h1f.enorm]
  have : ∀ x, ∀ᵐ y ∂η (a, x), 0 ≤ ‖f (x, y)‖ := fun x => Eventually.of_forall fun y => norm_nonneg _
  simp_rw [integral_eq_lintegral_of_nonneg_ae (this _)
      (h1f.norm.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
    enorm_eq_ofReal toReal_nonneg, ofReal_norm_eq_enorm]
  have : ∀ {p q r : Prop} (_ : r → p), (r ↔ p ∧ q) ↔ p → (r ↔ q) := fun {p q r} h1 => by
    rw [← and_congr_right_iff, and_iff_right_of_imp h1]
  rw [this]
  · intro h2f; rw [lintegral_congr_ae]
    filter_upwards [h2f] with x hx
    rw [ofReal_toReal]; finiteness
  · intro h2f; refine ae_lt_top ?_ h2f.ne; exact h1f.enorm.lintegral_kernel_prod_right''

theorem hasFiniteIntegral_compProd_iff' ⦃f : β × γ → E⦄
    (h1f : AEStronglyMeasurable f ((κ ⊗ₖ η) a)) :
    HasFiniteIntegral f ((κ ⊗ₖ η) a) ↔
      (∀ᵐ x ∂κ a, HasFiniteIntegral (fun y => f (x, y)) (η (a, x))) ∧
        HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂η (a, x)) (κ a) := by
  rw [hasFiniteIntegral_congr h1f.ae_eq_mk,
    hasFiniteIntegral_compProd_iff h1f.stronglyMeasurable_mk]
  apply and_congr
  · apply eventually_congr
    filter_upwards [ae_ae_of_ae_compProd h1f.ae_eq_mk.symm] with x hx using
      hasFiniteIntegral_congr hx
  · apply hasFiniteIntegral_congr
    filter_upwards [ae_ae_of_ae_compProd h1f.ae_eq_mk.symm] with _ hx using
      integral_congr_ae (EventuallyEq.fun_comp hx _)

theorem integrable_compProd_iff ⦃f : β × γ → E⦄ (hf : AEStronglyMeasurable f ((κ ⊗ₖ η) a)) :
    Integrable f ((κ ⊗ₖ η) a) ↔
      (∀ᵐ x ∂κ a, Integrable (fun y => f (x, y)) (η (a, x))) ∧
        Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂η (a, x)) (κ a) := by
  simp only [Integrable, hasFiniteIntegral_compProd_iff' hf, hf.norm.integral_kernel_compProd,
    hf, hf.compProd_mk_left, eventually_and, true_and]

theorem _root_.MeasureTheory.Integrable.ae_of_compProd ⦃f : β × γ → E⦄
    (hf : Integrable f ((κ ⊗ₖ η) a)) : ∀ᵐ x ∂κ a, Integrable (fun y => f (x, y)) (η (a, x)) :=
  ((integrable_compProd_iff hf.aestronglyMeasurable).mp hf).1

theorem _root_.MeasureTheory.Integrable.integral_norm_compProd ⦃f : β × γ → E⦄
    (hf : Integrable f ((κ ⊗ₖ η) a)) : Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂η (a, x)) (κ a) :=
  ((integrable_compProd_iff hf.aestronglyMeasurable).mp hf).2

theorem _root_.MeasureTheory.Integrable.integral_compProd [NormedSpace ℝ E]
    ⦃f : β × γ → E⦄ (hf : Integrable f ((κ ⊗ₖ η) a)) :
    Integrable (fun x => ∫ y, f (x, y) ∂η (a, x)) (κ a) :=
  Integrable.mono hf.integral_norm_compProd hf.aestronglyMeasurable.integral_kernel_compProd <|
    Eventually.of_forall fun x =>
      (norm_integral_le_integral_norm _).trans_eq <|
        (norm_of_nonneg <|
            integral_nonneg_of_ae <|
              Eventually.of_forall fun y => (norm_nonneg (f (x, y)) :)).symm

/-! ### Bochner integral -/


variable [NormedSpace ℝ E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

theorem Kernel.integral_fn_integral_add ⦃f g : β × γ → E⦄ (F : E → E')
    (hf : Integrable f ((κ ⊗ₖ η) a)) (hg : Integrable g ((κ ⊗ₖ η) a)) :
    ∫ x, F (∫ y, f (x, y) + g (x, y) ∂η (a, x)) ∂κ a =
      ∫ x, F (∫ y, f (x, y) ∂η (a, x) + ∫ y, g (x, y) ∂η (a, x)) ∂κ a := by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_add h2f h2g]

theorem Kernel.integral_fn_integral_sub ⦃f g : β × γ → E⦄ (F : E → E')
    (hf : Integrable f ((κ ⊗ₖ η) a)) (hg : Integrable g ((κ ⊗ₖ η) a)) :
    ∫ x, F (∫ y, f (x, y) - g (x, y) ∂η (a, x)) ∂κ a =
      ∫ x, F (∫ y, f (x, y) ∂η (a, x) - ∫ y, g (x, y) ∂η (a, x)) ∂κ a := by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_sub h2f h2g]

theorem Kernel.lintegral_fn_integral_sub ⦃f g : β × γ → E⦄ (F : E → ℝ≥0∞)
    (hf : Integrable f ((κ ⊗ₖ η) a)) (hg : Integrable g ((κ ⊗ₖ η) a)) :
    ∫⁻ x, F (∫ y, f (x, y) - g (x, y) ∂η (a, x)) ∂κ a =
      ∫⁻ x, F (∫ y, f (x, y) ∂η (a, x) - ∫ y, g (x, y) ∂η (a, x)) ∂κ a := by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_sub h2f h2g]

theorem Kernel.integral_integral_add ⦃f g : β × γ → E⦄ (hf : Integrable f ((κ ⊗ₖ η) a))
    (hg : Integrable g ((κ ⊗ₖ η) a)) :
    ∫ x, ∫ y, f (x, y) + g (x, y) ∂η (a, x) ∂κ a =
      ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a + ∫ x, ∫ y, g (x, y) ∂η (a, x) ∂κ a :=
  (Kernel.integral_fn_integral_add id hf hg).trans <|
    integral_add hf.integral_compProd hg.integral_compProd

theorem Kernel.integral_integral_add' ⦃f g : β × γ → E⦄ (hf : Integrable f ((κ ⊗ₖ η) a))
    (hg : Integrable g ((κ ⊗ₖ η) a)) :
    ∫ x, ∫ y, (f + g) (x, y) ∂η (a, x) ∂κ a =
      ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a + ∫ x, ∫ y, g (x, y) ∂η (a, x) ∂κ a :=
  Kernel.integral_integral_add hf hg

theorem Kernel.integral_integral_sub ⦃f g : β × γ → E⦄ (hf : Integrable f ((κ ⊗ₖ η) a))
    (hg : Integrable g ((κ ⊗ₖ η) a)) :
    ∫ x, ∫ y, f (x, y) - g (x, y) ∂η (a, x) ∂κ a =
      ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a - ∫ x, ∫ y, g (x, y) ∂η (a, x) ∂κ a :=
  (Kernel.integral_fn_integral_sub id hf hg).trans <|
    integral_sub hf.integral_compProd hg.integral_compProd

theorem Kernel.integral_integral_sub' ⦃f g : β × γ → E⦄ (hf : Integrable f ((κ ⊗ₖ η) a))
    (hg : Integrable g ((κ ⊗ₖ η) a)) :
    ∫ x, ∫ y, (f - g) (x, y) ∂η (a, x) ∂κ a =
      ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a - ∫ x, ∫ y, g (x, y) ∂η (a, x) ∂κ a :=
  Kernel.integral_integral_sub hf hg

theorem Kernel.continuous_integral_integral :
    Continuous fun f : β × γ →₁[(κ ⊗ₖ η) a] E => ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a := by
  rw [continuous_iff_continuousAt]; intro g
  refine
    tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_compProd
      (Eventually.of_forall fun h => (L1.integrable_coeFn h).integral_compProd) ?_
  simp_rw [← lintegral_fn_integral_sub (‖·‖ₑ) (L1.integrable_coeFn _) (L1.integrable_coeFn g)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun i => zero_le _) _
  · exact fun i => ∫⁻ x, ∫⁻ y, ‖i (x, y) - g (x, y)‖ₑ ∂η (a, x) ∂κ a
  swap; · exact fun i => lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
  change
    Tendsto
      (fun i : β × γ →₁[(κ ⊗ₖ η) a] E => ∫⁻ x, ∫⁻ y : γ, ‖i (x, y) - g (x, y)‖ₑ ∂η (a, x) ∂κ a)
      (𝓝 g) (𝓝 0)
  have this (i : Lp (α := β × γ) E 1 (((κ ⊗ₖ η) a) : Measure (β × γ))) :
      Measurable fun z => ‖i z - g z‖ₑ :=
    ((Lp.stronglyMeasurable i).sub (Lp.stronglyMeasurable g)).enorm
  simp_rw [← lintegral_compProd _ _ _ (this _), ← L1.ofReal_norm_sub_eq_lintegral, ← ofReal_zero]
  refine (continuous_ofReal.tendsto 0).comp ?_
  rw [← tendsto_iff_norm_sub_tendsto_zero]
  exact tendsto_id

theorem integral_compProd :
    ∀ {f : β × γ → E} (_ : Integrable f ((κ ⊗ₖ η) a)),
      ∫ z, f z ∂(κ ⊗ₖ η) a = ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  apply Integrable.induction
  · intro c s hs h2s
    simp_rw [integral_indicator hs, ← indicator_comp_right, Function.comp_def,
      integral_indicator (measurable_prodMk_left hs), MeasureTheory.setIntegral_const,
      integral_smul_const, measureReal_def]
    congr 1
    rw [integral_toReal]
    rotate_left
    · exact (Kernel.measurable_kernel_prodMk_left' hs _).aemeasurable
    · exact ae_kernel_lt_top a h2s.ne
    rw [Kernel.compProd_apply hs]
  · intro f g _ i_f i_g hf hg
    simp_rw [integral_add' i_f i_g, Kernel.integral_integral_add' i_f i_g, hf, hg]
  · exact isClosed_eq continuous_integral Kernel.continuous_integral_integral
  · intro f g hfg _ hf
    convert hf using 1
    · exact integral_congr_ae hfg.symm
    · apply integral_congr_ae
      filter_upwards [ae_ae_of_ae_compProd hfg] with x hfgx using
        integral_congr_ae (ae_eq_symm hfgx)

theorem setIntegral_compProd {f : β × γ → E} {s : Set β} {t : Set γ} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) ((κ ⊗ₖ η) a)) :
    ∫ z in s ×ˢ t, f z ∂(κ ⊗ₖ η) a = ∫ x in s, ∫ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  -- Porting note: `compProd_restrict` needed some explicit arguments
  rw [← Kernel.restrict_apply (κ ⊗ₖ η) (hs.prod ht), ← compProd_restrict hs ht, integral_compProd]
  · simp_rw [Kernel.restrict_apply]
  · rw [compProd_restrict, Kernel.restrict_apply]; exact hf

theorem setIntegral_compProd_univ_right (f : β × γ → E) {s : Set β} (hs : MeasurableSet s)
    (hf : IntegrableOn f (s ×ˢ univ) ((κ ⊗ₖ η) a)) :
    ∫ z in s ×ˢ univ, f z ∂(κ ⊗ₖ η) a = ∫ x in s, ∫ y, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [setIntegral_compProd hs MeasurableSet.univ hf, Measure.restrict_univ]

theorem setIntegral_compProd_univ_left (f : β × γ → E) {t : Set γ} (ht : MeasurableSet t)
    (hf : IntegrableOn f (univ ×ˢ t) ((κ ⊗ₖ η) a)) :
    ∫ z in univ ×ˢ t, f z ∂(κ ⊗ₖ η) a = ∫ x, ∫ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [setIntegral_compProd MeasurableSet.univ ht hf, Measure.restrict_univ]

end compProd

section comp

variable {κ : Kernel α β} {η : Kernel β γ}

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_comp [NormedSpace ℝ E]
    ⦃f : γ → E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
    AEStronglyMeasurable (fun x ↦ ∫ y, f y ∂η x) (κ a) :=
  ⟨fun x ↦ ∫ y, hf.mk f y ∂η x, hf.stronglyMeasurable_mk.integral_kernel, by
    filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩

theorem _root_.MeasureTheory.AEStronglyMeasurable.comp {δ : Type*} [TopologicalSpace δ]
    {f : γ → δ} (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
    ∀ᵐ x ∂κ a, AEStronglyMeasurable f (η x) := by
  filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk] with x hx using
    ⟨hf.mk f, hf.stronglyMeasurable_mk, hx⟩

/-! ### Integrability with respect to composition -/

theorem hasFiniteIntegral_comp_iff ⦃f : γ → E⦄ (hf : StronglyMeasurable f) :
    HasFiniteIntegral f ((η ∘ₖ κ) a) ↔
    (∀ᵐ x ∂κ a, HasFiniteIntegral f (η x)) ∧ HasFiniteIntegral (fun x ↦ ∫ y, ‖f y‖ ∂η x) (κ a) := by
  simp_rw [hasFiniteIntegral_iff_enorm, lintegral_comp _ _ _ hf.enorm]
  simp_rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y ↦ norm_nonneg _)
      hf.norm.aestronglyMeasurable, enorm_eq_ofReal toReal_nonneg, ofReal_norm_eq_enorm]
  have : ∀ {p q r : Prop} (_ : r → p), (r ↔ p ∧ q) ↔ p → (r ↔ q) := fun h ↦ by
    rw [← and_congr_right_iff, and_iff_right_of_imp h]
  rw [this]
  · intro h
    rw [lintegral_congr_ae]
    filter_upwards [h] with x hx
    rw [ofReal_toReal]
    finiteness
  · exact fun h ↦ ae_lt_top hf.enorm.lintegral_kernel h.ne

theorem hasFiniteIntegral_comp_iff' ⦃f : γ → E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
    HasFiniteIntegral f ((η ∘ₖ κ) a) ↔
    (∀ᵐ x ∂κ a, HasFiniteIntegral f (η x)) ∧ HasFiniteIntegral (fun x ↦ ∫ y, ‖f y‖ ∂η x) (κ a) := by
  rw [hasFiniteIntegral_congr hf.ae_eq_mk, hasFiniteIntegral_comp_iff hf.stronglyMeasurable_mk]
  refine and_congr (eventually_congr ?_) (hasFiniteIntegral_congr ?_)
  · filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk.symm] with _ hx using
      hasFiniteIntegral_congr hx
  · filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk.symm] with _ hx using
      integral_congr_ae (EventuallyEq.fun_comp hx _)

theorem integrable_comp_iff ⦃f : γ → E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
    Integrable f ((η ∘ₖ κ) a) ↔
    (∀ᵐ y ∂κ a, Integrable f (η y)) ∧ Integrable (fun y ↦ ∫ z, ‖f z‖ ∂η y) (κ a) := by
  simp only [Integrable, hf, hasFiniteIntegral_comp_iff' hf, true_and, eventually_and, hf.comp,
    hf.norm.integral_kernel_comp]

theorem _root_.MeasureTheory.Integrable.ae_of_comp ⦃f : γ → E⦄ (hf : Integrable f ((η ∘ₖ κ) a)) :
    ∀ᵐ x ∂κ a, Integrable f (η x) := ((integrable_comp_iff hf.1).1 hf).1

theorem _root_.MeasureTheory.Integrable.integral_norm_comp ⦃f : γ → E⦄
    (hf : Integrable f ((η ∘ₖ κ) a)) : Integrable (fun x ↦ ∫ y, ‖f y‖ ∂η x) (κ a) :=
  ((integrable_comp_iff hf.1).1 hf).2

theorem _root_.MeasureTheory.Integrable.integral_comp [NormedSpace ℝ E] ⦃f : γ → E⦄
    (hf : Integrable f ((η ∘ₖ κ) a)) : Integrable (fun x ↦ ∫ y, f y ∂η x) (κ a) :=
  Integrable.mono hf.integral_norm_comp hf.1.integral_kernel_comp <|
    ae_of_all _ fun _ ↦ (norm_integral_le_integral_norm _).trans_eq
    (norm_of_nonneg <| integral_nonneg_of_ae <| ae_of_all _ fun _ ↦ norm_nonneg _).symm

/-! ### Bochner integral with respect to the composition -/

variable [NormedSpace ℝ E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

namespace Kernel

theorem integral_fn_integral_add_comp ⦃f g : γ → E⦄ (F : E → E')
    (hf : Integrable f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, F (∫ y, f y + g y ∂η x) ∂κ a = ∫ x, F (∫ y, f y ∂η x + ∫ y, g y ∂η x) ∂κ a := by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_add h2f h2g]

theorem integral_fn_integral_sub_comp ⦃f g : γ → E⦄ (F : E → E')
    (hf : Integrable f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, F (∫ y, f y - g y ∂η x) ∂κ a = ∫ x, F (∫ y, f y ∂η x - ∫ y, g y ∂η x) ∂κ a := by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_sub h2f h2g]

theorem lintegral_fn_integral_sub_comp ⦃f g : γ → E⦄ (F : E → ℝ≥0∞)
    (hf : Integrable f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫⁻ x, F (∫ y, f y - g y ∂η x) ∂κ a = ∫⁻ x, F (∫ y, f y ∂η x - ∫ y, g y ∂η x) ∂κ a := by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_sub h2f h2g]

theorem integral_integral_add_comp ⦃f g : γ → E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
    (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, ∫ y, f y + g y ∂η x ∂κ a = ∫ x, ∫ y, f y ∂η x ∂κ a + ∫ x, ∫ y, g y ∂η x ∂κ a :=
  (integral_fn_integral_add_comp id hf hg).trans <| integral_add hf.integral_comp hg.integral_comp

theorem integral_integral_add'_comp ⦃f g : γ → E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
    (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, ∫ y, (f + g) y ∂η x ∂κ a = ∫ x, ∫ y, f y ∂η x ∂κ a + ∫ x, ∫ y, g y ∂η x ∂κ a :=
  integral_integral_add_comp hf hg

theorem integral_integral_sub_comp ⦃f g : γ → E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
    (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, ∫ y, f y - g y ∂η x ∂κ a = ∫ x, ∫ y, f y ∂η x ∂κ a - ∫ x, ∫ y, g y ∂η x ∂κ a :=
  (integral_fn_integral_sub_comp id hf hg).trans <| integral_sub hf.integral_comp hg.integral_comp

theorem integral_integral_sub'_comp ⦃f g : γ → E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
    (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, ∫ y, (f - g) y ∂η x ∂κ a = ∫ x, ∫ y, f y ∂η x ∂κ a - ∫ x, ∫ y, g y ∂η x ∂κ a :=
  integral_integral_sub_comp hf hg

theorem continuous_integral_integral_comp :
    Continuous fun f : γ →₁[(η ∘ₖ κ) a] E ↦ ∫ x, ∫ y, f y ∂η x ∂κ a := by
  refine continuous_iff_continuousAt.2 fun g ↦ ?_
  refine tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_comp
      (Eventually.of_forall fun h ↦ (L1.integrable_coeFn h).integral_comp) ?_
  simp_rw [← lintegral_fn_integral_sub_comp (‖·‖ₑ) (L1.integrable_coeFn _) (L1.integrable_coeFn g)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (h := fun i ↦ ∫⁻ x, ∫⁻ y, ‖i y - g y‖ₑ ∂η x ∂κ a)
    tendsto_const_nhds ?_ (fun _ ↦ zero_le _) ?_
  swap; · exact fun _ ↦ lintegral_mono fun _ ↦ enorm_integral_le_lintegral_enorm _
  have (i : γ →₁[(η ∘ₖ κ) a] E) : Measurable fun z ↦ ‖i z - g z‖ₑ :=
    ((Lp.stronglyMeasurable i).sub (Lp.stronglyMeasurable g)).enorm
  simp_rw [← lintegral_comp _ _ _ (this _), ← L1.ofReal_norm_sub_eq_lintegral, ← ofReal_zero]
  exact (continuous_ofReal.tendsto 0).comp (tendsto_iff_norm_sub_tendsto_zero.1 tendsto_id)

theorem integral_comp : ∀ {f : γ → E} (_ : Integrable f ((η ∘ₖ κ) a)),
    ∫ z, f z ∂(η ∘ₖ κ) a = ∫ x, ∫ y, f y ∂η x ∂κ a := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  apply Integrable.induction
  · intro c s hs ms
    simp_rw [integral_indicator hs, MeasureTheory.setIntegral_const, integral_smul_const,
      measureReal_def]
    congr
    rw [integral_toReal, Kernel.comp_apply' _ _ _ hs]
    · exact (Kernel.measurable_coe _ hs).aemeasurable
    · exact ae_lt_top_of_comp_ne_top a ms.ne
  · rintro f g - i_f i_g hf hg
    simp_rw [integral_add' i_f i_g, integral_integral_add'_comp i_f i_g, hf, hg]
  · exact isClosed_eq continuous_integral Kernel.continuous_integral_integral_comp
  · rintro f g hfg - hf
    convert hf using 1
    · exact integral_congr_ae hfg.symm
    · apply integral_congr_ae
      filter_upwards [ae_ae_of_ae_comp hfg] with x hfgx using integral_congr_ae (ae_eq_symm hfgx)

theorem setIntegral_comp {f : γ → E} {s : Set γ} (hs : MeasurableSet s)
    (hf : IntegrableOn f s ((η ∘ₖ κ) a)) :
    ∫ z in s, f z ∂(η ∘ₖ κ) a = ∫ x, ∫ y in s, f y ∂η x ∂κ a := by
  rw [← restrict_apply (η ∘ₖ κ) hs, ← comp_restrict hs, integral_comp]
  · simp_rw [restrict_apply]
  · rwa [comp_restrict, restrict_apply]

end Kernel

end comp

end ProbabilityTheory

namespace MeasureTheory

namespace Measure

variable {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [NormedAddCommGroup E] {a : α} {κ : Kernel α β} {μ : Measure α} {f : β → E}

section Integral

lemma _root_.MeasureTheory.AEStronglyMeasurable.ae_of_compProd [SFinite μ] [IsSFiniteKernel κ]
    {E : Type*} [NormedAddCommGroup E] {f : α → β → E}
    (hf : AEStronglyMeasurable f.uncurry (μ ⊗ₘ κ)) :
    ∀ᵐ x ∂μ, AEStronglyMeasurable (f x) (κ x) := by
  simpa using hf.compProd_mk_left

lemma integrable_compProd_iff [SFinite μ] [IsSFiniteKernel κ] {E : Type*} [NormedAddCommGroup E]
    {f : α × β → E} (hf : AEStronglyMeasurable f (μ ⊗ₘ κ)) :
    Integrable f (μ ⊗ₘ κ) ↔
      (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) (κ x)) ∧
        Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂(κ x)) μ := by
  simp_rw [Measure.compProd, ProbabilityTheory.integrable_compProd_iff hf, Kernel.prodMkLeft_apply,
    Kernel.const_apply]

lemma integral_compProd [SFinite μ] [IsSFiniteKernel κ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α × β → E} (hf : Integrable f (μ ⊗ₘ κ)) :
    ∫ x, f x ∂(μ ⊗ₘ κ) = ∫ a, ∫ b, f (a, b) ∂(κ a) ∂μ := by
  rw [Measure.compProd, ProbabilityTheory.integral_compProd hf]
  simp

lemma setIntegral_compProd [SFinite μ] [IsSFiniteKernel κ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t)
    {f : α × β → E} (hf : IntegrableOn f (s ×ˢ t) (μ ⊗ₘ κ)) :
    ∫ x in s ×ˢ t, f x ∂(μ ⊗ₘ κ) = ∫ a in s, ∫ b in t, f (a, b) ∂(κ a) ∂μ := by
  rw [Measure.compProd, ProbabilityTheory.setIntegral_compProd hs ht hf]
  simp

end Integral

section Integrable

lemma integrable_compProd_snd_iff [SFinite μ] [IsSFiniteKernel κ]
    (hf : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    Integrable (fun p ↦ f p.2) (μ ⊗ₘ κ) ↔ Integrable f (κ ∘ₘ μ) := by
  rw [← Measure.snd_compProd, Measure.snd, integrable_map_measure _ measurable_snd.aemeasurable,
    Function.comp_def]
  rwa [← Measure.snd, Measure.snd_compProd]

lemma ae_integrable_of_integrable_comp (h_int : Integrable f (κ ∘ₘ μ)) :
    ∀ᵐ x ∂μ, Integrable f (κ x) := by
  rw [Measure.comp_eq_comp_const_apply, integrable_comp_iff h_int.1] at h_int
  exact h_int.1

lemma integrable_integral_norm_of_integrable_comp (h_int : Integrable f (κ ∘ₘ μ)) :
    Integrable (fun x ↦ ∫ y, ‖f y‖ ∂κ x) μ := by
  rw [Measure.comp_eq_comp_const_apply, integrable_comp_iff h_int.1] at h_int
  exact h_int.2

end Integrable

end Measure

end MeasureTheory
