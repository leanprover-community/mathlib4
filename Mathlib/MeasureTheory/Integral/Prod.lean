/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Integration with respect to the product measure

In this file we prove Fubini's theorem.

## Main results

* `MeasureTheory.integrable_prod_iff` states that a binary function is integrable iff both
  * `y ↦ f (x, y)` is integrable for almost every `x`, and
  * the function `x ↦ ∫ ‖f (x, y)‖ dy` is integrable.
* `MeasureTheory.integral_prod`: Fubini's theorem. It states that for an integrable function
  `α × β → E` (where `E` is a second countable Banach space) we have
  `∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ`. This theorem has the same variants as
  Tonelli's theorem (see `MeasureTheory.lintegral_prod`). The lemma
  `MeasureTheory.Integrable.integral_prod_right` states that the inner integral of the right-hand
  side is integrable.
* `MeasureTheory.integral_integral_swap_of_hasCompactSupport`: a version of Fubini's theorem for
  continuous functions with compact support, which does not assume that the measures are σ-finite
  contrary to all the usual versions of Fubini.

## Tags

product measure, Fubini's theorem, Fubini-Tonelli theorem
-/

public section


noncomputable section

open scoped Topology ENNReal MeasureTheory

open Set Function Real ENNReal

open MeasureTheory MeasurableSpace MeasureTheory.Measure

open TopologicalSpace

open Filter hiding prod_eq map

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
variable [NormedAddCommGroup E]

/-! ### Measurability

Before we define the product measure, we can talk about the measurability of operations on binary
functions. We show that if `f` is a binary measurable function, then the function that integrates
along one of the variables (using either the Lebesgue or Bochner integral) is measurable.
-/


theorem measurableSet_integrable [SFinite ν] ⦃f : α → β → E⦄
    (hf : StronglyMeasurable (uncurry f)) : MeasurableSet {x | Integrable (f x) ν} := by
  simp_rw [Integrable, hf.of_uncurry_left.aestronglyMeasurable, true_and]
  exact measurableSet_lt (Measurable.lintegral_prod_right hf.enorm) measurable_const

section

variable [NormedSpace ℝ E]

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  Fubini's theorem is measurable.
  This version has `f` in curried form. -/
theorem MeasureTheory.StronglyMeasurable.integral_prod_right [SFinite ν] ⦃f : α → β → E⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun x => ∫ y, f x y ∂ν := by
  classical
  by_cases hE : CompleteSpace E; swap; · simp [integral, hE, stronglyMeasurable_const]
  borelize E
  haveI : SeparableSpace (range (uncurry f) ∪ {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : ℕ → SimpleFunc (α × β) E :=
    SimpleFunc.approxOn _ hf.measurable (range (uncurry f) ∪ {0}) 0 (by simp)
  let s' : ℕ → α → SimpleFunc β E := fun n x => (s n).comp (Prod.mk x) measurable_prodMk_left
  let f' : ℕ → α → E := fun n => {x | Integrable (f x) ν}.indicator fun x => (s' n x).integral ν
  have hf' : ∀ n, StronglyMeasurable (f' n) := by
    intro n; refine StronglyMeasurable.indicator ?_ (measurableSet_integrable hf)
    have : ∀ x, ((s' n x).range.filter fun x => x ≠ 0) ⊆ (s n).range := by
      intro x; refine Finset.Subset.trans (Finset.filter_subset _ _) ?_; intro y
      simp_rw [SimpleFunc.mem_range]; rintro ⟨z, rfl⟩; exact ⟨(x, z), rfl⟩
    simp only [SimpleFunc.integral_eq_sum_of_subset (this _)]
    refine Finset.stronglyMeasurable_fun_sum _ fun x _ => ?_
    refine (Measurable.ennreal_toReal ?_).stronglyMeasurable.smul_const _
    simp only [s', SimpleFunc.coe_comp, preimage_comp]
    apply measurable_measure_prodMk_left
    exact (s n).measurableSet_fiber x
  have h2f' : Tendsto f' atTop (𝓝 fun x : α => ∫ y : β, f x y ∂ν) := by
    rw [tendsto_pi_nhds]; intro x
    by_cases hfx : Integrable (f x) ν
    · have (n : _) : Integrable (s' n x) ν := by
        apply (hfx.norm.add hfx.norm).mono' (s' n x).aestronglyMeasurable
        filter_upwards with y
        simp_rw [s', SimpleFunc.coe_comp]; exact SimpleFunc.norm_approxOn_zero_le _ _ (x, y) n
      simp only [f', hfx, SimpleFunc.integral_eq_integral _ (this _), indicator_of_mem,
        mem_setOf_eq]
      refine
        tendsto_integral_of_dominated_convergence (fun y => ‖f x y‖ + ‖f x y‖)
          (fun n => (s' n x).aestronglyMeasurable) (hfx.norm.add hfx.norm) ?_ ?_
      · refine fun n => Eventually.of_forall fun y =>
          SimpleFunc.norm_approxOn_zero_le ?_ ?_ (x, y) n
        · exact hf.measurable
        · simp
      · refine Eventually.of_forall fun y => SimpleFunc.tendsto_approxOn ?_ ?_ ?_
        · exact hf.measurable.of_uncurry_left
        · simp
        apply subset_closure
        simp [-uncurry_apply_pair]
    · simp [f', hfx, integral_undef]
  exact stronglyMeasurable_of_tendsto _ hf' h2f'

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  Fubini's theorem is measurable. -/
theorem MeasureTheory.StronglyMeasurable.integral_prod_right' [SFinite ν] ⦃f : α × β → E⦄
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ∫ y, f (x, y) ∂ν := by
  rw [← uncurry_curry f] at hf; exact hf.integral_prod_right

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Fubini's theorem is measurable.
  This version has `f` in curried form. -/
theorem MeasureTheory.StronglyMeasurable.integral_prod_left [SFinite μ] ⦃f : α → β → E⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun y => ∫ x, f x y ∂μ :=
  (hf.comp_measurable measurable_swap).integral_prod_right'

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Fubini's theorem is measurable. -/
theorem MeasureTheory.StronglyMeasurable.integral_prod_left' [SFinite μ] ⦃f : α × β → E⦄
    (hf : StronglyMeasurable f) : StronglyMeasurable fun y => ∫ x, f (x, y) ∂μ :=
  (hf.comp_measurable measurable_swap).integral_prod_right'

end

/-! ### The product measure -/


namespace MeasureTheory

namespace Measure

variable [SFinite ν]

theorem integrable_measure_prodMk_left {s : Set (α × β)} (hs : MeasurableSet s)
    (h2s : (μ.prod ν) s ≠ ∞) : Integrable (fun x => ν.real (Prod.mk x ⁻¹' s)) μ := by
  refine ⟨(measurable_measure_prodMk_left hs).ennreal_toReal.aemeasurable.aestronglyMeasurable, ?_⟩
  simp_rw [hasFiniteIntegral_iff_enorm, measureReal_def, enorm_eq_ofReal toReal_nonneg]
  convert h2s.lt_top using 1
  rw [prod_apply hs]
  apply lintegral_congr_ae
  filter_upwards [ae_measure_lt_top hs h2s] with x hx
  rw [lt_top_iff_ne_top] at hx
  simp [ofReal_toReal, hx]

end Measure

end MeasureTheory

open MeasureTheory.Measure

section

variable {X : Type*} [TopologicalSpace X]

protected theorem MeasureTheory.AEStronglyMeasurable.prod_swap [SFinite μ] [SFinite ν]
    {f : β × α → X} (hf : AEStronglyMeasurable f (ν.prod μ)) :
    AEStronglyMeasurable (fun z : α × β => f z.swap) (μ.prod ν) := by
  rw [← prod_swap] at hf
  exact hf.comp_measurable measurable_swap

theorem MeasureTheory.AEStronglyMeasurable.comp_fst {γ} [TopologicalSpace γ] {f : α → γ}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun z : α × β => f z.1) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst

theorem MeasureTheory.AEStronglyMeasurable.comp_snd {γ} [TopologicalSpace γ] {f : β → γ}
    (hf : AEStronglyMeasurable f ν) : AEStronglyMeasurable (fun z : α × β => f z.2) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

/-- The Bochner integral is a.e.-measurable.
  This shows that the integrand of (the right-hand-side of) Fubini's theorem is a.e.-measurable. -/
theorem MeasureTheory.AEStronglyMeasurable.integral_prod_right' [SFinite ν] [NormedSpace ℝ E]
    ⦃f : α × β → E⦄ (hf : AEStronglyMeasurable f (μ.prod ν)) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂ν) μ :=
  ⟨fun x => ∫ y, hf.mk f (x, y) ∂ν, hf.stronglyMeasurable_mk.integral_prod_right', by
    filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩

theorem MeasureTheory.AEStronglyMeasurable.prodMk_left [SFinite ν] {f : α × β → X}
    (hf : AEStronglyMeasurable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => f (x, y)) ν := by
  filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with x hx
  exact ⟨fun y ↦ hf.mk f (x, y),
    hf.stronglyMeasurable_mk.comp_measurable measurable_prodMk_left, hx⟩

theorem MeasureTheory.AEStronglyMeasurable.prodMk_right [SFinite μ] [SFinite ν] {f : α × β → X}
    (hf : AEStronglyMeasurable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, AEStronglyMeasurable (fun x => f (x, y)) μ :=
  hf.prod_swap.prodMk_left

protected theorem MeasureTheory.AEStronglyMeasurable.of_comp_snd {f : β → X} [SFinite ν]
    (hf : AEStronglyMeasurable (f ·.2) (μ.prod ν)) (hμ : μ ≠ 0) : AEStronglyMeasurable f ν := by
  have := NeZero.mk hμ
  obtain ⟨y, hy⟩ := hf.prodMk_left.exists
  exact hy

protected theorem MeasureTheory.AEStronglyMeasurable.of_comp_fst {f : α → X} [SFinite μ] [SFinite ν]
    (hf : AEStronglyMeasurable (f ·.1) (μ.prod ν)) (hν : ν ≠ 0) : AEStronglyMeasurable f μ :=
  hf.prod_swap.of_comp_snd hν

theorem MeasureTheory.AEStronglyMeasurable.comp_fst_iff [SFinite μ] [SFinite ν] {f : α → X}
    (hν : ν ≠ 0) : AEStronglyMeasurable (f ·.1) (μ.prod ν) ↔ AEStronglyMeasurable f μ :=
  ⟨(.of_comp_fst · hν), .comp_fst⟩

theorem MeasureTheory.AEStronglyMeasurable.comp_snd_iff [SFinite ν] {f : β → X}
    (hμ : μ ≠ 0) : AEStronglyMeasurable (f ·.2) (μ.prod ν) ↔ AEStronglyMeasurable f ν :=
  ⟨(.of_comp_snd · hμ), .comp_snd⟩

end

namespace MeasureTheory

variable [SFinite ν]

/-! ### Integrability on a product -/

section

theorem integrable_swap_iff [SFinite μ] {f : α × β → E} :
    Integrable (f ∘ Prod.swap) (ν.prod μ) ↔ Integrable f (μ.prod ν) :=
  measurePreserving_swap.integrable_comp_emb MeasurableEquiv.prodComm.measurableEmbedding

theorem Integrable.swap [SFinite μ] ⦃f : α × β → E⦄ (hf : Integrable f (μ.prod ν)) :
    Integrable (f ∘ Prod.swap) (ν.prod μ) :=
  integrable_swap_iff.2 hf

theorem hasFiniteIntegral_prod_iff ⦃f : α × β → E⦄ (h1f : StronglyMeasurable f) :
    HasFiniteIntegral f (μ.prod ν) ↔
      (∀ᵐ x ∂μ, HasFiniteIntegral (fun y => f (x, y)) ν) ∧
        HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ := by
  simp only [hasFiniteIntegral_iff_enorm, lintegral_prod _ h1f.enorm.aemeasurable]
  have (x : _) : ∀ᵐ y ∂ν, 0 ≤ ‖f (x, y)‖ := by filter_upwards with y using norm_nonneg _
  simp_rw [integral_eq_lintegral_of_nonneg_ae (this _)
      (h1f.norm.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
    enorm_eq_ofReal toReal_nonneg, ofReal_norm_eq_enorm]
  -- this fact is probably too specialized to be its own lemma
  have : ∀ {p q r : Prop} (_ : r → p), (r ↔ p ∧ q) ↔ p → (r ↔ q) := fun {p q r} h1 => by
    rw [← and_congr_right_iff, and_iff_right_of_imp h1]
  rw [this]
  · intro h2f; rw [lintegral_congr_ae]
    filter_upwards [h2f] with x hx
    rw [ofReal_toReal]; rw [← lt_top_iff_ne_top]; exact hx
  · intro h2f; refine ae_lt_top ?_ h2f.ne; exact h1f.enorm.lintegral_prod_right'

theorem hasFiniteIntegral_prod_iff' ⦃f : α × β → E⦄ (h1f : AEStronglyMeasurable f (μ.prod ν)) :
    HasFiniteIntegral f (μ.prod ν) ↔
      (∀ᵐ x ∂μ, HasFiniteIntegral (fun y => f (x, y)) ν) ∧
        HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ := by
  rw [hasFiniteIntegral_congr h1f.ae_eq_mk,
    hasFiniteIntegral_prod_iff h1f.stronglyMeasurable_mk]
  apply and_congr
  · apply eventually_congr
    filter_upwards [ae_ae_of_ae_prod h1f.ae_eq_mk.symm]
    intro x hx
    exact hasFiniteIntegral_congr hx
  · apply hasFiniteIntegral_congr
    filter_upwards [ae_ae_of_ae_prod h1f.ae_eq_mk.symm] with _ hx using
      integral_congr_ae (EventuallyEq.fun_comp hx _)

/-- A binary function is integrable if the function `y ↦ f (x, y)` is integrable for almost every
  `x` and the function `x ↦ ∫ ‖f (x, y)‖ dy` is integrable. -/
theorem integrable_prod_iff ⦃f : α × β → E⦄ (h1f : AEStronglyMeasurable f (μ.prod ν)) :
    Integrable f (μ.prod ν) ↔
      (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν) ∧ Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ := by
  simp [Integrable, h1f, hasFiniteIntegral_prod_iff', h1f.norm.integral_prod_right',
    h1f.prodMk_left]

/-- A binary function is integrable if the function `x ↦ f (x, y)` is integrable for almost every
  `y` and the function `y ↦ ∫ ‖f (x, y)‖ dx` is integrable. -/
theorem integrable_prod_iff' [SFinite μ] ⦃f : α × β → E⦄
    (h1f : AEStronglyMeasurable f (μ.prod ν)) :
    Integrable f (μ.prod ν) ↔
      (∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ) ∧ Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂μ) ν := by
  convert integrable_prod_iff h1f.prod_swap using 1
  rw [funext fun _ => Function.comp_apply.symm, integrable_swap_iff]

theorem Integrable.prod_left_ae [SFinite μ] ⦃f : α × β → E⦄ (hf : Integrable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ :=
  ((integrable_prod_iff' hf.aestronglyMeasurable).mp hf).1

theorem Integrable.prod_right_ae [SFinite μ] ⦃f : α × β → E⦄ (hf : Integrable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν :=
  hf.swap.prod_left_ae

theorem Integrable.integral_norm_prod_left ⦃f : α × β → E⦄ (hf : Integrable f (μ.prod ν)) :
    Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ :=
  ((integrable_prod_iff hf.aestronglyMeasurable).mp hf).2

theorem Integrable.integral_norm_prod_right [SFinite μ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ.prod ν)) : Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂μ) ν :=
  hf.swap.integral_norm_prod_left

omit [SFinite ν] in
theorem Integrable.op_fst_snd {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    {op : E → F → G} (hop : Continuous op.uncurry) (hop_norm : ∃ C, ∀ x y, ‖op x y‖ ≤ C * ‖x‖ * ‖y‖)
    {f : α → E} {g : β → F} (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun z ↦ op (f z.1) (g z.2)) (μ.prod ν) := by
  use hop.comp_aestronglyMeasurable₂ hf.1.comp_fst hg.1.comp_snd
  rcases hop_norm with ⟨C, hC⟩
  calc
    ∫⁻ z, ‖op (f z.1) (g z.2)‖ₑ ∂μ.prod ν ≤ ∫⁻ z, .ofReal C * ‖f z.1‖ₑ * ‖g z.2‖ₑ ∂μ.prod ν := by
      gcongr with z
      simp only [enorm_eq_nnnorm, ENNReal.ofReal, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
        ← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm]
      refine (hC _ _).trans ?_
      gcongr
      apply le_coe_toNNReal
    _ ≤ ∫⁻ x, ∫⁻ y, .ofReal C * ‖f x‖ₑ * ‖g y‖ₑ ∂ν ∂μ := lintegral_prod_le _
    _ ≤ .ofReal C * (∫⁻ x, ‖f x‖ₑ ∂μ) * ∫⁻ y, ‖g y‖ₑ ∂ν := by
      simp [lintegral_const_mul', lintegral_mul_const', hg.2.ne, mul_assoc]
    _ < ∞ := by apply_rules [ENNReal.mul_lt_top, hf.2, hg.2, ENNReal.ofReal_lt_top]

lemma Integrable.comp_fst {f : α → E} (hf : Integrable f μ) (ν : Measure β) [IsFiniteMeasure ν] :
    Integrable (fun x ↦ f x.1) (μ.prod ν) := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.comp_fst ν

lemma Integrable.comp_snd {f : β → E} (hf : Integrable f ν) (μ : Measure α) [IsFiniteMeasure μ] :
    Integrable (fun x ↦ f x.2) (μ.prod ν) := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.comp_snd μ

omit [SFinite ν] in
theorem Integrable.smul_prod {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E]
    {f : α → R} {g : β → E} (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun z : α × β => f z.1 • g z.2) (μ.prod ν) :=
  hf.op_fst_snd continuous_smul ⟨1, by simpa using norm_smul_le⟩ hg

omit [SFinite ν] in
theorem Integrable.mul_prod {L : Type*} [NormedRing L] {f : α → L} {g : β → L} (hf : Integrable f μ)
    (hg : Integrable g ν) : Integrable (fun z : α × β => f z.1 * g z.2) (μ.prod ν) :=
  hf.smul_prod hg

theorem IntegrableOn.swap [SFinite μ] {f : α × β → E} {s : Set α} {t : Set β}
    (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    IntegrableOn (f ∘ Prod.swap) (t ×ˢ s) (ν.prod μ) := by
  rw [IntegrableOn, ← Measure.prod_restrict] at hf ⊢
  exact hf.swap

theorem Integrable.of_comp_snd {f : β → E} (hf : Integrable (f ·.2) (μ.prod ν)) (hμ : μ ≠ 0) :
    Integrable f ν := by
  rcases hf with ⟨hf_meas, hf_fin⟩
  use hf_meas.of_comp_snd hμ
  have := hf_meas.enorm
  aesop (add simp [HasFiniteIntegral, lintegral_prod, ENNReal.mul_lt_top_iff])

theorem Integrable.of_comp_fst [SFinite μ] {f : α → E} (hf : Integrable (f ·.1) (μ.prod ν))
    (hν : ν ≠ 0) : Integrable f μ :=
  hf.swap.of_comp_snd hν

theorem Integrable.comp_snd_iff [IsFiniteMeasure μ] {f : β → E} (hμ : μ ≠ 0) :
    Integrable (f ·.2) (μ.prod ν) ↔ Integrable f ν :=
  ⟨(.of_comp_snd · hμ), (.comp_snd · μ)⟩

omit [SFinite ν] in
theorem Integrable.comp_fst_iff [SFinite μ] [IsFiniteMeasure ν] {f : α → E} (hν : ν ≠ 0) :
    Integrable (f ·.1) (μ.prod ν) ↔ Integrable f μ :=
  ⟨(.of_comp_fst · hν), (.comp_fst · ν)⟩

end

variable [NormedSpace ℝ E]

theorem Integrable.integral_prod_left ⦃f : α × β → E⦄ (hf : Integrable f (μ.prod ν)) :
    Integrable (fun x => ∫ y, f (x, y) ∂ν) μ :=
  Integrable.mono hf.integral_norm_prod_left hf.aestronglyMeasurable.integral_prod_right' <|
    Eventually.of_forall fun x =>
      (norm_integral_le_integral_norm _).trans_eq <|
        (norm_of_nonneg <|
            integral_nonneg_of_ae <|
              Eventually.of_forall fun y => (norm_nonneg (f (x, y)) :)).symm

theorem Integrable.integral_prod_right [SFinite μ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ.prod ν)) : Integrable (fun y => ∫ x, f (x, y) ∂μ) ν :=
  hf.swap.integral_prod_left

/-! ### The Bochner integral on a product -/

variable [SFinite μ]

theorem integral_prod_swap (f : α × β → E) :
    ∫ z, f z.swap ∂ν.prod μ = ∫ z, f z ∂μ.prod ν :=
  measurePreserving_swap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding _

theorem setIntegral_prod_swap (s : Set α) (t : Set β) (f : α × β → E) :
    ∫ (z : β × α) in t ×ˢ s, f z.swap ∂ν.prod μ = ∫ (z : α × β) in s ×ˢ t, f z ∂μ.prod ν := by
  rw [← Measure.prod_restrict, ← Measure.prod_restrict, integral_prod_swap]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-! Some rules about the sum/difference of double integrals. They follow from `integral_add`, but
  we separate them out as separate lemmas, because they involve quite some steps. -/


/-- Integrals commute with addition inside another integral. `F` can be any function. -/
theorem integral_fn_integral_add ⦃f g : α × β → E⦄ (F : E → E') (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, F (∫ y, f (x, y) + g (x, y) ∂ν) ∂μ) =
      ∫ x, F ((∫ y, f (x, y) ∂ν) + ∫ y, g (x, y) ∂ν) ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_add h2f h2g]

/-- Integrals commute with subtraction inside another integral.
  `F` can be any measurable function. -/
theorem integral_fn_integral_sub ⦃f g : α × β → E⦄ (F : E → E') (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, F (∫ y, f (x, y) - g (x, y) ∂ν) ∂μ) =
      ∫ x, F ((∫ y, f (x, y) ∂ν) - ∫ y, g (x, y) ∂ν) ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_sub h2f h2g]

/-- Integrals commute with subtraction inside a lower Lebesgue integral.
  `F` can be any function. -/
theorem lintegral_fn_integral_sub ⦃f g : α × β → E⦄ (F : E → ℝ≥0∞) (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫⁻ x, F (∫ y, f (x, y) - g (x, y) ∂ν) ∂μ) =
      ∫⁻ x, F ((∫ y, f (x, y) ∂ν) - ∫ y, g (x, y) ∂ν) ∂μ := by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_sub h2f h2g]

/-- Double integrals commute with addition. -/
theorem integral_integral_add ⦃f g : α × β → E⦄ (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, ∫ y, f (x, y) + g (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) + ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
  (integral_fn_integral_add id hf hg).trans <|
    integral_add hf.integral_prod_left hg.integral_prod_left

/-- Double integrals commute with addition. This is the version with `(f + g) (x, y)`
  (instead of `f (x, y) + g (x, y)`) in the LHS. -/
theorem integral_integral_add' ⦃f g : α × β → E⦄ (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, ∫ y, (f + g) (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) + ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
  integral_integral_add hf hg

/-- Double integrals commute with subtraction. -/
theorem integral_integral_sub ⦃f g : α × β → E⦄ (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, ∫ y, f (x, y) - g (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) - ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
  (integral_fn_integral_sub id hf hg).trans <|
    integral_sub hf.integral_prod_left hg.integral_prod_left

/-- Double integrals commute with subtraction. This is the version with `(f - g) (x, y)`
  (instead of `f (x, y) - g (x, y)`) in the LHS. -/
theorem integral_integral_sub' ⦃f g : α × β → E⦄ (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, ∫ y, (f - g) (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) - ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
  integral_integral_sub hf hg

/-- The map that sends an L¹-function `f : α × β → E` to `∫∫f` is continuous. -/
theorem continuous_integral_integral :
    Continuous fun f : α × β →₁[μ.prod ν] E => ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  rw [continuous_iff_continuousAt]; intro g
  refine
    tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_prod_left
      (Eventually.of_forall fun h => (L1.integrable_coeFn h).integral_prod_left) ?_
  simp_rw [← lintegral_fn_integral_sub _ (L1.integrable_coeFn _) (L1.integrable_coeFn g)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun i => zero_le) _
  · exact fun i => ∫⁻ x, ∫⁻ y, ‖i (x, y) - g (x, y)‖ₑ ∂ν ∂μ
  swap; · exact fun i => lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
  change
    Tendsto (fun i : α × β →₁[μ.prod ν] E => ∫⁻ x, ∫⁻ y : β, ‖i (x, y) - g (x, y)‖ₑ ∂ν ∂μ) (𝓝 g)
      (𝓝 0)
  have this (i : α × β →₁[μ.prod ν] E) : Measurable fun z => ‖i z - g z‖ₑ :=
    ((Lp.stronglyMeasurable i).sub (Lp.stronglyMeasurable g)).enorm
  simp_rw [← lintegral_prod _ (this _).aemeasurable, ← L1.ofReal_norm_sub_eq_lintegral,
    ← ofReal_zero]
  refine (continuous_ofReal.tendsto 0).comp ?_
  rw [← tendsto_iff_norm_sub_tendsto_zero]; exact tendsto_id

/-- **Fubini's Theorem**: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral.
  `integrable_prod_iff` can be useful to show that the function in question in integrable.
  `MeasureTheory.Integrable.integral_prod_right` is useful to show that the inner integral
  of the right-hand side is integrable. -/
theorem integral_prod (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  by_cases hE : CompleteSpace E; swap; · simp only [integral, dif_neg hE]
  revert f
  apply Integrable.induction
  · intro c s hs h2s
    simp_rw [integral_indicator hs, ← indicator_comp_right, Function.comp_def,
      integral_indicator (measurable_prodMk_left hs), setIntegral_const, integral_smul_const,
      measureReal_def,
      integral_toReal (measurable_measure_prodMk_left hs).aemeasurable
        (ae_measure_lt_top hs h2s.ne)]
    rw [prod_apply hs]
  · rintro f g - i_f i_g hf hg
    simp_rw [integral_add' i_f i_g, integral_integral_add' i_f i_g, hf, hg]
  · exact isClosed_eq continuous_integral continuous_integral_integral
  · rintro f g hfg - hf; convert hf using 1
    · exact integral_congr_ae hfg.symm
    · apply integral_congr_ae
      filter_upwards [ae_ae_of_ae_prod hfg] with x hfgx using integral_congr_ae (ae_eq_symm hfgx)

/-- Symmetric version of **Fubini's Theorem**: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral.
  This version has the integrals on the right-hand side in the other order. -/
theorem integral_prod_symm (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ y, ∫ x, f (x, y) ∂μ ∂ν := by
  rw [← integral_prod_swap f]; exact integral_prod _ hf.swap

/-- Reversed version of **Fubini's Theorem**. -/
theorem integral_integral {f : α → β → E} (hf : Integrable (uncurry f) (μ.prod ν)) :
    ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ z, f z.1 z.2 ∂μ.prod ν :=
  (integral_prod _ hf).symm

/-- Reversed version of **Fubini's Theorem** (symmetric version). -/
theorem integral_integral_symm {f : α → β → E} (hf : Integrable (uncurry f) (μ.prod ν)) :
    ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ z, f z.2 z.1 ∂ν.prod μ :=
  (integral_prod_symm _ hf.swap).symm

/-- Change the order of Bochner integration. -/
theorem integral_integral_swap ⦃f : α → β → E⦄ (hf : Integrable (uncurry f) (μ.prod ν)) :
    ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν :=
  (integral_integral hf).trans (integral_prod_symm _ hf)

/-- Change the order of integration, when one of the integrals is an interval integral. -/
lemma intervalIntegral_integral_swap {a b : ℝ} {f : ℝ → α → E}
    (h_int : Integrable (uncurry f) ((volume.restrict (Set.uIoc a b)).prod μ)) :
    ∫ x in a..b, ∫ y, f x y ∂μ = ∫ y, (∫ x in a..b, f x y) ∂μ := by
  rcases le_total a b with (hab | hab)
  · simp_rw [intervalIntegral.integral_of_le hab]
    simp only [hab, Set.uIoc_of_le] at h_int
    exact integral_integral_swap h_int
  · simp_rw [intervalIntegral.integral_of_ge hab]
    simp only [hab, Set.uIoc_of_ge] at h_int
    rw [integral_integral_swap h_int, integral_neg]

/-- **Fubini's Theorem** for set integrals. -/
theorem setIntegral_prod (f : α × β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    ∫ z in s ×ˢ t, f z ∂μ.prod ν = ∫ x in s, ∫ y in t, f (x, y) ∂ν ∂μ := by
  simp only [← Measure.prod_restrict s t, IntegrableOn] at hf ⊢
  exact integral_prod f hf

theorem integral_prod_bilin {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (B : E →L[ℝ] F →L[ℝ] G) {f : α → E} {g : β → F}
    (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ z, B (f z.1) (g z.2) ∂μ.prod ν = B (∫ x, f x ∂μ) (∫ y, g y ∂ν) := by
  have : Integrable (fun z ↦ B (f z.1) (g z.2)) (μ.prod ν) :=
    hf.op_fst_snd (by fun_prop) ⟨‖B‖, B.le_opNorm₂⟩ hg
  simp_rw [integral_prod _ this, ContinuousLinearMap.integral_comp_comm _ hg]
  change ∫ x, B.flip (∫ y, g y ∂ν) (f x) ∂μ = _
  rw [ContinuousLinearMap.integral_comp_comm _ hf]
  simp

theorem integral_prod_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] (f : α → 𝕜) (g : β → E) :
    ∫ z, f z.1 • g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) • ∫ y, g y ∂ν := by
  by_cases hE : CompleteSpace E; swap; · simp [integral, hE]
  by_cases h : Integrable (fun z : α × β => f z.1 • g z.2) (μ.prod ν)
  · rw [integral_prod _ h]
    simp_rw [integral_smul, integral_smul_const]
  have H : ¬Integrable f μ ∨ ¬Integrable g ν := by
    contrapose! h
    exact h.1.smul_prod h.2
  rcases H with H | H <;> simp [integral_undef h, integral_undef H]

theorem integral_prod_mul {L : Type*} [RCLike L] (f : α → L) (g : β → L) :
    ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y, g y ∂ν :=
  integral_prod_smul f g

theorem setIntegral_prod_mul {L : Type*} [RCLike L] (f : α → L) (g : β → L) (s : Set α)
    (t : Set β) :
    ∫ z in s ×ˢ t, f z.1 * g z.2 ∂μ.prod ν = (∫ x in s, f x ∂μ) * ∫ y in t, g y ∂ν := by
  rw [← Measure.prod_restrict s t]
  apply integral_prod_mul

theorem integral_fun_snd (f : β → E) : ∫ z, f z.2 ∂μ.prod ν = μ.real univ • ∫ y, f y ∂ν := by
  simpa using integral_prod_smul (1 : α → ℝ) f

theorem integral_fun_fst (f : α → E) : ∫ z, f z.1 ∂μ.prod ν = ν.real univ • ∫ x, f x ∂μ := by
  rw [← integral_prod_swap]
  apply integral_fun_snd

section ContinuousLinearMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {mE : MeasurableSpace E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mF : MeasurableSpace F}
  [NormedAddCommGroup G] [NormedSpace ℝ G] {mG : MeasurableSpace G}
  {μ : Measure E} [IsProbabilityMeasure μ] {ν : Measure F} [IsProbabilityMeasure ν]
  {L : E × F →L[ℝ] G}

lemma integrable_continuousLinearMap_prod'
    (hLμ : Integrable (L.comp (.inl ℝ E F)) μ) (hLν : Integrable (L.comp (.inr ℝ E F)) ν) :
    Integrable L (μ.prod ν) := by
  change Integrable (fun v ↦ L v) (μ.prod ν)
  simp_rw [← L.comp_inl_add_comp_inr]
  exact (hLμ.comp_fst ν).add (hLν.comp_snd μ)

lemma integrable_continuousLinearMap_prod (hμ : Integrable id μ) (hν : Integrable id ν) :
    Integrable L (μ.prod ν) :=
  integrable_continuousLinearMap_prod' (ContinuousLinearMap.integrable_comp _ hμ)
    (ContinuousLinearMap.integrable_comp _ hν)

variable [CompleteSpace G]

lemma integral_continuousLinearMap_prod'
    (hLμ : Integrable (L.comp (.inl ℝ E F)) μ) (hLν : Integrable (L.comp (.inr ℝ E F)) ν) :
    ∫ p, L p ∂(μ.prod ν) = ∫ x, L.comp (.inl ℝ E F) x ∂μ + ∫ y, L.comp (.inr ℝ E F) y ∂ν := by
  simp_rw [← L.comp_inl_add_comp_inr]
  replace hLμ := ((memLp_one_iff_integrable.mpr hLμ).comp_fst ν).integrable le_rfl
  replace hLν := ((memLp_one_iff_integrable.mpr hLν).comp_snd μ).integrable le_rfl
  rw [integral_add hLμ hLν, integral_prod _ hLμ, integral_prod _ hLν]
  simp

lemma integral_continuousLinearMap_prod (hμ : Integrable id μ) (hν : Integrable id ν) :
    ∫ p, L p ∂(μ.prod ν) = ∫ x, L.comp (.inl ℝ E F) x ∂μ + ∫ y, L.comp (.inr ℝ E F) y ∂ν :=
  integral_continuousLinearMap_prod' (ContinuousLinearMap.integrable_comp _ hμ)
    (ContinuousLinearMap.integrable_comp _ hν)

end ContinuousLinearMap

section

variable {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]

/-- A version of *Fubini theorem* for continuous functions with compact support: one may swap
the order of integration with respect to locally finite measures. One does not assume that the
measures are σ-finite, contrary to the usual Fubini theorem. -/
lemma integral_integral_swap_of_hasCompactSupport
    {f : X → Y → E} (hf : Continuous f.uncurry) (h'f : HasCompactSupport f.uncurry)
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    ∫ x, (∫ y, f x y ∂ν) ∂μ = ∫ y, (∫ x, f x y ∂μ) ∂ν := by
  let U := Prod.fst '' (tsupport f.uncurry)
  have : Fact (μ U < ∞) := ⟨(IsCompact.image h'f continuous_fst).measure_lt_top⟩
  let V := Prod.snd '' (tsupport f.uncurry)
  have : Fact (ν V < ∞) := ⟨(IsCompact.image h'f continuous_snd).measure_lt_top⟩
  calc
  ∫ x, (∫ y, f x y ∂ν) ∂μ = ∫ x, (∫ y in V, f x y ∂ν) ∂μ := by
    congr 1 with x
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)).symm
    contrapose! hy
    have : (x, y) ∈ Function.support f.uncurry := hy
    exact mem_image_of_mem _ (subset_tsupport _ this)
  _ = ∫ x in U, (∫ y in V, f x y ∂ν) ∂μ := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ ?_)).symm
    have : ∀ y, f x y = 0 := by
      intro y
      contrapose! hx
      have : (x, y) ∈ Function.support f.uncurry := hx
      exact mem_image_of_mem _ (subset_tsupport _ this)
    simp [this]
  _ = ∫ y in V, (∫ x in U, f x y ∂μ) ∂ν := by
    apply integral_integral_swap
    apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f.uncurry)).mp
    refine ⟨(h'f.stronglyMeasurable_of_prod hf).aestronglyMeasurable, ?_⟩
    obtain ⟨C, hC⟩ : ∃ C, ∀ p, ‖f.uncurry p‖ ≤ C := hf.bounded_above_of_compact_support h'f
    exact .of_bounded (C := C) (.of_forall hC)
  _ = ∫ y, (∫ x in U, f x y ∂μ) ∂ν := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)
    have : ∀ x, f x y = 0 := by
      intro x
      contrapose! hy
      have : (x, y) ∈ Function.support f.uncurry := hy
      exact mem_image_of_mem _ (subset_tsupport _ this)
    simp [this]
  _ = ∫ y, (∫ x, f x y ∂μ) ∂ν := by
    congr 1 with y
    apply setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ ?_)
    contrapose! hx
    have : (x, y) ∈ Function.support f.uncurry := hx
    exact mem_image_of_mem _ (subset_tsupport _ this)

end

end MeasureTheory
