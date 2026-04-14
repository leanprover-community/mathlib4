/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Function with finite integral

In this file we define the predicate `HasFiniteIntegral`, which is then used to define the
predicate `Integrable` in the corresponding file.

## Main definition

* Let `f : α → β` be a function, where `α` is a `MeasureSpace` and `β` a `NormedAddCommGroup`.
  Then `HasFiniteIntegral f` means `∫⁻ a, ‖f a‖ₑ < ∞`.

## Tags

finite integral

-/

@[expose] public section

noncomputable section

open Topology ENNReal MeasureTheory NNReal

open Set Filter TopologicalSpace ENNReal EMetric MeasureTheory

variable {α β γ ε ε' ε'' : Type*} {m : MeasurableSpace α} {μ ν : Measure α}
variable [NormedAddCommGroup β] [NormedAddCommGroup γ] [ENorm ε] [ENorm ε']
  [TopologicalSpace ε''] [AddMonoid ε''] [ESeminormedAddMonoid ε'']

namespace MeasureTheory

/-! ### Some results about the Lebesgue integral involving a normed group -/

lemma lintegral_enorm_eq_lintegral_edist (f : α → β) :
    ∫⁻ a, ‖f a‖ₑ ∂μ = ∫⁻ a, edist (f a) 0 ∂μ := by simp only [edist_zero_right]

theorem lintegral_norm_eq_lintegral_edist (f : α → β) :
    ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ = ∫⁻ a, edist (f a) 0 ∂μ := by
  simp only [ofReal_norm_eq_enorm, edist_zero_right]

theorem lintegral_edist_triangle {f g h : α → β} (hf : AEStronglyMeasurable f μ)
    (hh : AEStronglyMeasurable h μ) :
    (∫⁻ a, edist (f a) (g a) ∂μ) ≤ (∫⁻ a, edist (f a) (h a) ∂μ) + ∫⁻ a, edist (g a) (h a) ∂μ := by
  rw [← lintegral_add_left' (hf.edist hh)]
  refine lintegral_mono fun a => ?_
  apply edist_triangle_right

-- Yaël: Why do the following four lemmas even exist?
theorem lintegral_enorm_zero : ∫⁻ _ : α, ‖(0 : ε'')‖ₑ ∂μ = 0 := by simp

theorem lintegral_enorm_add_left {f : α → ε''} (hf : AEStronglyMeasurable f μ) (g : α → ε') :
    ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ + ∫⁻ a, ‖g a‖ₑ ∂μ :=
  lintegral_add_left' hf.enorm _

theorem lintegral_enorm_add_right (f : α → ε') {g : α → ε''} (hg : AEStronglyMeasurable g μ) :
    ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ + ∫⁻ a, ‖g a‖ₑ ∂μ :=
  lintegral_add_right' _ hg.enorm

theorem lintegral_enorm_neg {f : α → β} : ∫⁻ a, ‖(-f) a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ := by simp

/-! ### The predicate `HasFiniteIntegral` -/


/-- `HasFiniteIntegral f μ` means that the integral `∫⁻ a, ‖f a‖ ∂μ` is finite.
  `HasFiniteIntegral f` means `HasFiniteIntegral f volume`. -/
@[fun_prop]
def HasFiniteIntegral {_ : MeasurableSpace α} (f : α → ε)
    (μ : Measure α := by volume_tac) : Prop :=
  ∫⁻ a, ‖f a‖ₑ ∂μ < ∞

theorem hasFiniteIntegral_def {_ : MeasurableSpace α} (f : α → ε) (μ : Measure α) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, ‖f a‖ₑ ∂μ < ∞) :=
  Iff.rfl

theorem hasFiniteIntegral_iff_enorm {f : α → ε} : HasFiniteIntegral f μ ↔ ∫⁻ a, ‖f a‖ₑ ∂μ < ∞ := by
  simp only [HasFiniteIntegral]

theorem hasFiniteIntegral_iff_norm (f : α → β) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) < ∞ := by
  simp only [hasFiniteIntegral_iff_enorm, ofReal_norm_eq_enorm]

theorem hasFiniteIntegral_iff_edist (f : α → β) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, edist (f a) 0 ∂μ) < ∞ := by
  simp only [hasFiniteIntegral_iff_norm, edist_dist, dist_zero_right]

theorem hasFiniteIntegral_iff_ofReal {f : α → ℝ} (h : 0 ≤ᵐ[μ] f) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofReal (f a) ∂μ) < ∞ := by
  rw [hasFiniteIntegral_iff_enorm, lintegral_enorm_of_ae_nonneg h]

theorem hasFiniteIntegral_iff_ofNNReal {f : α → ℝ≥0} :
    HasFiniteIntegral (fun x => (f x : ℝ)) μ ↔ (∫⁻ a, f a ∂μ) < ∞ := by
  simp [hasFiniteIntegral_iff_norm]

theorem HasFiniteIntegral.mono_enorm {f : α → ε} {g : α → ε'} (hg : HasFiniteIntegral g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ₑ ≤ ‖g a‖ₑ) : HasFiniteIntegral f μ := by
  simp only [hasFiniteIntegral_iff_enorm] at *
  calc
    (∫⁻ a, ‖f a‖ₑ ∂μ) ≤ ∫⁻ a : α, ‖g a‖ₑ ∂μ := lintegral_mono_ae h
    _ < ∞ := hg

theorem HasFiniteIntegral.mono {f : α → β} {g : α → γ} (hg : HasFiniteIntegral g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ ‖g a‖) : HasFiniteIntegral f μ :=
  hg.mono_enorm <| h.mono fun _x hx ↦ enorm_le_iff_norm_le.mpr hx

theorem HasFiniteIntegral.mono_nonneg [Lattice β] [HasSolidNorm β] [AddLeftMono β] {f g : α → β}
    (hg : HasFiniteIntegral g μ) (hnonneg : ∀ᵐ a ∂μ, 0 ≤ f a) (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    HasFiniteIntegral f μ := by
  refine HasFiniteIntegral.mono hg ?_
  filter_upwards [hnonneg, h] with a hn ha
  apply norm_le_norm_of_abs_le_abs
  rwa [abs_of_nonneg hn, abs_of_nonneg (hn.trans ha)]

theorem HasFiniteIntegral.mono'_enorm {f : α → ε} {g : α → ℝ≥0∞} (hg : HasFiniteIntegral g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ₑ ≤ g a) : HasFiniteIntegral f μ :=
  hg.mono_enorm <| h.mono fun _x hx ↦ le_trans hx le_rfl

theorem HasFiniteIntegral.mono' {f : α → β} {g : α → ℝ} (hg : HasFiniteIntegral g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : HasFiniteIntegral f μ :=
  hg.mono <| h.mono fun _x hx => le_trans hx (le_abs_self _)

theorem HasFiniteIntegral.congr'_enorm {f : α → ε} {g : α → ε'} (hf : HasFiniteIntegral f μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : HasFiniteIntegral g μ :=
  hf.mono_enorm <| EventuallyEq.le <| EventuallyEq.symm h

theorem HasFiniteIntegral.congr' {f : α → β} {g : α → γ} (hf : HasFiniteIntegral f μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) : HasFiniteIntegral g μ :=
  hf.mono <| EventuallyEq.le <| EventuallyEq.symm h

theorem hasFiniteIntegral_congr'_enorm {f : α → ε} {g : α → ε'} (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) :
    HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ :=
  ⟨fun hf => hf.congr'_enorm h, fun hg => hg.congr'_enorm <| EventuallyEq.symm h⟩

theorem hasFiniteIntegral_congr' {f : α → β} {g : α → γ} (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) :
    HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ :=
  ⟨fun hf => hf.congr' h, fun hg => hg.congr' <| EventuallyEq.symm h⟩

theorem HasFiniteIntegral.congr {f g : α → ε} (hf : HasFiniteIntegral f μ) (h : f =ᵐ[μ] g) :
    HasFiniteIntegral g μ :=
  hf.congr'_enorm <| h.fun_comp enorm

theorem hasFiniteIntegral_congr {f g : α → ε} (h : f =ᵐ[μ] g) :
    HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ :=
  hasFiniteIntegral_congr'_enorm <| h.fun_comp enorm

theorem hasFiniteIntegral_const_iff_enorm {c : ε} (hc : ‖c‖ₑ ≠ ∞) :
    HasFiniteIntegral (fun _ : α ↦ c) μ ↔ ‖c‖ₑ = 0 ∨ IsFiniteMeasure μ := by
  simpa [hasFiniteIntegral_iff_enorm, lt_top_iff_ne_top, ENNReal.mul_eq_top,
    or_iff_not_imp_left, isFiniteMeasure_iff] using fun h h' ↦ (hc h').elim

theorem hasFiniteIntegral_const_iff {c : β} :
    HasFiniteIntegral (fun _ : α => c) μ ↔ c = 0 ∨ IsFiniteMeasure μ := by
  simp [hasFiniteIntegral_const_iff_enorm enorm_ne_top]

lemma hasFiniteIntegral_const_iff_isFiniteMeasure_enorm {c : ε} (hc : ‖c‖ₑ ≠ 0) (hc' : ‖c‖ₑ ≠ ∞) :
    HasFiniteIntegral (fun _ ↦ c) μ ↔ IsFiniteMeasure μ := by
  simp [hasFiniteIntegral_const_iff_enorm hc', hc, isFiniteMeasure_iff]

lemma hasFiniteIntegral_const_iff_isFiniteMeasure {c : β} (hc : c ≠ 0) :
    HasFiniteIntegral (fun _ ↦ c) μ ↔ IsFiniteMeasure μ :=
  hasFiniteIntegral_const_iff_isFiniteMeasure_enorm (enorm_ne_zero.mpr hc) enorm_ne_top

@[fun_prop]
theorem hasFiniteIntegral_const_enorm [IsFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ ≠ ∞) :
    HasFiniteIntegral (fun _ : α ↦ c) μ :=
  (hasFiniteIntegral_const_iff_enorm hc).2 <| .inr ‹_›

@[fun_prop]
theorem hasFiniteIntegral_const [IsFiniteMeasure μ] (c : β) :
    HasFiniteIntegral (fun _ : α => c) μ :=
  hasFiniteIntegral_const_iff.2 <| .inr ‹_›

theorem HasFiniteIntegral.of_mem_Icc_of_ne_top [IsFiniteMeasure μ]
    {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) {X : α → ℝ≥0∞} (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    HasFiniteIntegral X μ := by
  have : ‖max ‖a‖ₑ ‖b‖ₑ‖ₑ ≠ ⊤ := by simp [ha, hb]
  apply (hasFiniteIntegral_const_enorm this (μ := μ)).mono'_enorm
  filter_upwards [h.mono fun ω h ↦ h.1, h.mono fun ω h ↦ h.2] with ω h₁ h₂ using by simp [h₂]

theorem HasFiniteIntegral.of_mem_Icc [IsFiniteMeasure μ] (a b : ℝ) {X : α → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    HasFiniteIntegral X μ := by
  apply (hasFiniteIntegral_const (max ‖a‖ ‖b‖)).mono'
  filter_upwards [h.mono fun ω h ↦ h.1, h.mono fun ω h ↦ h.2] with ω using abs_le_max_abs_abs

theorem HasFiniteIntegral.of_bounded_enorm [IsFiniteMeasure μ] {f : α → ε} {C : ℝ≥0∞}
    (hC' : ‖C‖ₑ ≠ ∞ := by finiteness) (hC : ∀ᵐ a ∂μ, ‖f a‖ₑ ≤ C) : HasFiniteIntegral f μ :=
  (hasFiniteIntegral_const_enorm hC').mono'_enorm hC

theorem HasFiniteIntegral.of_bounded [IsFiniteMeasure μ] {f : α → β} {C : ℝ}
    (hC : ∀ᵐ a ∂μ, ‖f a‖ ≤ C) : HasFiniteIntegral f μ :=
  (hasFiniteIntegral_const C).mono' hC

-- TODO: generalise this to f with codomain ε
-- requires generalising `norm_le_pi_norm` and friends to enorms
@[simp]
theorem HasFiniteIntegral.of_finite [Finite α] [IsFiniteMeasure μ] {f : α → β} :
    HasFiniteIntegral f μ :=
  let ⟨_⟩ := nonempty_fintype α
  .of_bounded <| ae_of_all μ <| norm_le_pi_norm f

theorem HasFiniteIntegral.mono_measure {f : α → ε} (h : HasFiniteIntegral f ν) (hμ : μ ≤ ν) :
    HasFiniteIntegral f μ :=
  lt_of_le_of_lt (lintegral_mono' hμ le_rfl) h

@[fun_prop]
theorem HasFiniteIntegral.add_measure {f : α → ε} (hμ : HasFiniteIntegral f μ)
    (hν : HasFiniteIntegral f ν) : HasFiniteIntegral f (μ + ν) := by
  simp only [HasFiniteIntegral, lintegral_add_measure] at *
  exact add_lt_top.2 ⟨hμ, hν⟩

theorem HasFiniteIntegral.left_of_add_measure {f : α → ε} (h : HasFiniteIntegral f (μ + ν)) :
    HasFiniteIntegral f μ :=
  h.mono_measure <| Measure.le_add_right <| le_rfl

theorem HasFiniteIntegral.right_of_add_measure {f : α → ε} (h : HasFiniteIntegral f (μ + ν)) :
    HasFiniteIntegral f ν :=
  h.mono_measure <| Measure.le_add_left <| le_rfl

@[simp]
theorem hasFiniteIntegral_add_measure {f : α → ε} :
    HasFiniteIntegral f (μ + ν) ↔ HasFiniteIntegral f μ ∧ HasFiniteIntegral f ν :=
  ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

theorem HasFiniteIntegral.smul_measure {f : α → ε} (h : HasFiniteIntegral f μ) {c : ℝ≥0∞}
    (hc : c ≠ ∞) : HasFiniteIntegral f (c • μ) := by
  simp only [HasFiniteIntegral, lintegral_smul_measure] at *
  exact mul_lt_top hc.lt_top h

@[fun_prop, simp]
theorem hasFiniteIntegral_zero_measure {m : MeasurableSpace α} (f : α → ε) :
    HasFiniteIntegral f (0 : Measure α) := by
  simp only [HasFiniteIntegral, lintegral_zero_measure, zero_lt_top]

variable (α μ) in
@[fun_prop, simp]
theorem hasFiniteIntegral_zero {ε : Type*}
    [TopologicalSpace ε] [AddMonoid ε] [ESeminormedAddMonoid ε] :
    HasFiniteIntegral (fun _ : α => (0 : ε)) μ := by
  simp [hasFiniteIntegral_iff_enorm]

@[fun_prop]
theorem HasFiniteIntegral.neg {f : α → β} (hfi : HasFiniteIntegral f μ) :
    HasFiniteIntegral (-f) μ := by simpa [hasFiniteIntegral_iff_enorm] using hfi

@[simp]
theorem hasFiniteIntegral_neg_iff {f : α → β} : HasFiniteIntegral (-f) μ ↔ HasFiniteIntegral f μ :=
  ⟨fun h => neg_neg f ▸ h.neg, HasFiniteIntegral.neg⟩

@[fun_prop]
theorem HasFiniteIntegral.enorm {f : α → ε} (hfi : HasFiniteIntegral f μ) :
    HasFiniteIntegral (‖f ·‖ₑ) μ := by simpa [hasFiniteIntegral_iff_enorm] using hfi

@[fun_prop]
theorem HasFiniteIntegral.norm {f : α → β} (hfi : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun a => ‖f a‖) μ := by simpa [hasFiniteIntegral_iff_enorm] using hfi

theorem hasFiniteIntegral_enorm_iff (f : α → ε) :
    HasFiniteIntegral (‖f ·‖ₑ) μ ↔ HasFiniteIntegral f μ :=
  hasFiniteIntegral_congr'_enorm <| Eventually.of_forall fun x => enorm_enorm (f x)

theorem hasFiniteIntegral_norm_iff (f : α → β) :
    HasFiniteIntegral (fun a => ‖f a‖) μ ↔ HasFiniteIntegral f μ :=
  hasFiniteIntegral_congr' <| Eventually.of_forall fun x => norm_norm (f x)

theorem HasFiniteIntegral.of_subsingleton [Subsingleton α] [IsFiniteMeasure μ] {f : α → β} :
    HasFiniteIntegral f μ :=
  .of_finite

theorem HasFiniteIntegral.of_isEmpty [IsEmpty α] {f : α → β} :
    HasFiniteIntegral f μ :=
  .of_finite

@[simp]
theorem HasFiniteIntegral.of_subsingleton_codomain
    {ε : Type*} [TopologicalSpace ε] [AddMonoid ε] [ESeminormedAddMonoid ε]
    [Subsingleton ε] {f : α → ε} :
    HasFiniteIntegral f μ :=
  hasFiniteIntegral_zero _ _ |>.congr <| .of_forall fun _ ↦ Subsingleton.elim _ _

theorem hasFiniteIntegral_toReal_of_lintegral_ne_top {f : α → ℝ≥0∞} (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
    HasFiniteIntegral (fun x ↦ (f x).toReal) μ := by
  have h x : ‖(f x).toReal‖ₑ = .ofReal (f x).toReal := by
    rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg]
  simp_rw [hasFiniteIntegral_iff_enorm, h]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) (lt_top_iff_ne_top.2 hf)
  by_cases hfx : f x = ∞
  · simp [hfx]
  · lift f x to ℝ≥0 using hfx with fx h
    simp

lemma hasFiniteIntegral_toReal_iff {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    HasFiniteIntegral (fun x ↦ (f x).toReal) μ ↔ ∫⁻ x, f x ∂μ ≠ ∞ := by
  have : ∀ᵐ x ∂μ, .ofReal (f x).toReal = f x := by filter_upwards [hf] with x hx; simp [hx]
  simp [hasFiniteIntegral_iff_enorm, Real.enorm_of_nonneg ENNReal.toReal_nonneg,
    lintegral_congr_ae this, lt_top_iff_ne_top]

theorem isFiniteMeasure_withDensity_ofReal {f : α → ℝ} (hfi : HasFiniteIntegral f μ) :
    IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal <| f x) := by
  refine isFiniteMeasure_withDensity ((lintegral_mono fun x => ?_).trans_lt hfi).ne
  exact Real.ofReal_le_enorm (f x)

section DominatedConvergence

variable {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
  {ε : Type*} [TopologicalSpace ε] [AddMonoid ε] [ESeminormedAddMonoid ε]
  {F' : ℕ → α → ε} {f' : α → ε} {bound' : α → ℝ≥0∞}

theorem all_ae_norm_ofReal_F_le_bound (h : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a) :
    ∀ n, ∀ᵐ a ∂μ, ENNReal.ofReal ‖F n a‖ ≤ ENNReal.ofReal (bound a) := fun n =>
  (h n).mono fun _ h => ENNReal.ofReal_le_ofReal h

@[deprecated (since := "2026-01-26")] alias
all_ae_ofReal_F_le_bound := all_ae_norm_ofReal_F_le_bound

theorem ae_tendsto_enorm (h : ∀ᵐ a ∂μ, Tendsto (fun n ↦ F' n a) atTop <| 𝓝 <| f' a) :
    ∀ᵐ a ∂μ, Tendsto (fun n ↦ ‖F' n a‖ₑ) atTop <| 𝓝 <| ‖f' a‖ₑ :=
  h.mono fun _ h ↦ Tendsto.comp (Continuous.tendsto continuous_enorm _) h

theorem ae_tendsto_ofReal_norm (h : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop <| 𝓝 <| f a) :
    ∀ᵐ a ∂μ, Tendsto (fun n => ENNReal.ofReal ‖F n a‖) atTop <| 𝓝 <| ENNReal.ofReal ‖f a‖ := by
  convert ae_tendsto_enorm h <;> simp

@[deprecated (since := "2026-01-26")] alias all_ae_tendsto_ofReal_norm := ae_tendsto_ofReal_norm

theorem ae_norm_ofReal_f_le_bound (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    ∀ᵐ a ∂μ, ENNReal.ofReal ‖f a‖ ≤ ENNReal.ofReal (bound a) := by
  have F_le_bound := all_ae_norm_ofReal_F_le_bound h_bound
  rw [← ae_all_iff] at F_le_bound
  apply F_le_bound.mp ((ae_tendsto_ofReal_norm h_lim).mono _)
  intro a tendsto_norm F_le_bound
  exact le_of_tendsto' tendsto_norm F_le_bound

@[deprecated (since := "2026-01-26")] alias all_ae_ofReal_f_le_bound := ae_norm_ofReal_f_le_bound

theorem ae_enorm_le_bound (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F' n a‖ₑ ≤ bound' a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n ↦ F' n a) atTop (𝓝 (f' a))) :
    ∀ᵐ a ∂μ, ‖f' a‖ₑ ≤ bound' a := by
  rw [← ae_all_iff] at h_bound
  apply h_bound.mp ((ae_tendsto_enorm h_lim).mono _)
  intro a tendsto_norm h_bound
  exact le_of_tendsto' tendsto_norm h_bound

theorem hasFiniteIntegral_of_dominated_convergence_enorm
    (bound_hasFiniteIntegral : HasFiniteIntegral bound' μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F' n a‖ₑ ≤ bound' a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n ↦ F' n a) atTop (𝓝 (f' a))) : HasFiniteIntegral f' μ := by
  /- `‖F' n a‖ₑ ≤ bound' a` and `‖F' n a‖ₑ --> ‖f' a‖ₑ` implies `‖f a‖ₑ ≤ bound' a`,
    and so `∫ ‖f'‖ₑ ≤ ∫ bound' < ∞` since `bound'` has finite integral -/
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ a, ‖f' a‖ₑ ∂μ) ≤ ∫⁻ a, bound' a ∂μ :=
      lintegral_mono_ae <| ae_enorm_le_bound h_bound h_lim
    _ < ∞ := bound_hasFiniteIntegral

theorem hasFiniteIntegral_of_dominated_convergence
    (bound_hasFiniteIntegral : HasFiniteIntegral bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : HasFiniteIntegral f μ := by
  /- `‖F n a‖ ≤ bound a` and `‖F n a‖ --> ‖f a‖` implies `‖f a‖ ≤ bound a`,
    and so `∫ ‖f‖ ≤ ∫ bound < ∞` since `bound` is has_finite_integral -/
  rw [hasFiniteIntegral_iff_norm]
  calc
    (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (bound a) ∂μ :=
      lintegral_mono_ae <| ae_norm_ofReal_f_le_bound h_bound h_lim
    _ < ∞ := by
      rw [← hasFiniteIntegral_iff_ofReal]
      · exact bound_hasFiniteIntegral
      exact (h_bound 0).mono fun a h => le_trans (norm_nonneg _) h

-- TODO: generalise this to `f` and `F` taking values in a new class `ENormedSubmonoid`
theorem tendsto_lintegral_norm_of_dominated_convergence
    (F_measurable : ∀ n, AEStronglyMeasurable (F n) μ)
    (bound_hasFiniteIntegral : HasFiniteIntegral bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, ENNReal.ofReal ‖F n a - f a‖ ∂μ) atTop (𝓝 0) := by
  have f_measurable : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ F_measurable h_lim
  let b a := 2 * ENNReal.ofReal (bound a)
  /- `‖F n a‖ ≤ bound a` and `F n a --> f a` implies `‖f a‖ ≤ bound a`, and thus by the
    triangle inequality, have `‖F n a - f a‖ ≤ 2 * (bound a)`. -/
  have hb : ∀ n, ∀ᵐ a ∂μ, ENNReal.ofReal ‖F n a - f a‖ ≤ b a := by
    intro n
    filter_upwards [all_ae_norm_ofReal_F_le_bound h_bound n,
      ae_norm_ofReal_f_le_bound h_bound h_lim] with a h₁ h₂
    calc
      ENNReal.ofReal ‖F n a - f a‖ ≤ ENNReal.ofReal ‖F n a‖ + ENNReal.ofReal ‖f a‖ := by
        rw [← ENNReal.ofReal_add]
        · apply ofReal_le_ofReal
          apply norm_sub_le
        · exact norm_nonneg _
        · exact norm_nonneg _
      _ ≤ ENNReal.ofReal (bound a) + ENNReal.ofReal (bound a) := add_le_add h₁ h₂
      _ = b a := by rw [← two_mul]
  -- On the other hand, `F n a --> f a` implies that `‖F n a - f a‖ --> 0`
  have h : ∀ᵐ a ∂μ, Tendsto (fun n => ENNReal.ofReal ‖F n a - f a‖) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine h_lim.mono fun a h => (continuous_ofReal.tendsto _).comp ?_
    rwa [← tendsto_iff_norm_sub_tendsto_zero]
  /- Therefore, by the dominated convergence theorem for nonnegative integration, have
    ` ∫ ‖f a - F n a‖ --> 0 ` -/
  suffices Tendsto (fun n => ∫⁻ a, ENNReal.ofReal ‖F n a - f a‖ ∂μ) atTop (𝓝 (∫⁻ _ : α, 0 ∂μ)) by
    rwa [lintegral_zero] at this
  -- Using the dominated convergence theorem.
  refine tendsto_lintegral_of_dominated_convergence' _ ?_ hb ?_ ?_
  -- Show `fun a => ‖f a - F n a‖` is almost everywhere measurable for all `n`
  · exact fun n =>
      measurable_ofReal.comp_aemeasurable ((F_measurable n).sub f_measurable).norm.aemeasurable
  -- Show `2 * bound` `HasFiniteIntegral`
  · rw [hasFiniteIntegral_iff_ofReal] at bound_hasFiniteIntegral
    · calc
        ∫⁻ a, b a ∂μ = 2 * ∫⁻ a, ENNReal.ofReal (bound a) ∂μ := by
          rw [lintegral_const_mul']
          finiteness
        _ ≠ ∞ := mul_ne_top coe_ne_top bound_hasFiniteIntegral.ne
    filter_upwards [h_bound 0] with _ h using le_trans (norm_nonneg _) h
  -- Show `‖f a - F n a‖ --> 0`
  · exact h

end DominatedConvergence

section PosPart

/-! Lemmas used for defining the positive part of an `L¹` function -/

@[fun_prop]
theorem HasFiniteIntegral.max_zero {f : α → ℝ} (hf : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun a => max (f a) 0) μ :=
  hf.mono <| Eventually.of_forall fun x => by simp [abs_le, le_abs_self]

@[fun_prop]
theorem HasFiniteIntegral.min_zero {f : α → ℝ} (hf : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun a => min (f a) 0) μ :=
  hf.mono <| Eventually.of_forall fun x => by simpa [abs_le] using neg_abs_le _

end PosPart

section NormedSpace

variable {𝕜 : Type*}

@[fun_prop]
theorem HasFiniteIntegral.smul [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 β] [IsBoundedSMul 𝕜 β]
    (c : 𝕜) {f : α → β} (hf : HasFiniteIntegral f μ) :
    HasFiniteIntegral (c • f) μ := by
  simp only [HasFiniteIntegral]
  calc
    ∫⁻ a : α, ‖c • f a‖ₑ ∂μ ≤ ∫⁻ a : α, ‖c‖ₑ * ‖f a‖ₑ ∂μ := lintegral_mono fun i ↦ enorm_smul_le
    _ < ∞ := by
      rw [lintegral_const_mul']
      exacts [mul_lt_top coe_lt_top hf, coe_ne_top]

-- TODO: weaken the hypothesis to a version of `ENormSMulClass` with `≤`,
-- once such a typeclass exists.
-- This will let us unify with `HasFiniteIntegral.smul` above.
@[fun_prop]
theorem HasFiniteIntegral.smul_enorm [NormedAddGroup 𝕜] [SMul 𝕜 ε''] [ENormSMulClass 𝕜 ε'']
    (c : 𝕜) {f : α → ε''} (hf : HasFiniteIntegral f μ) : HasFiniteIntegral (c • f) μ := by
  simp only [HasFiniteIntegral]
  calc
    ∫⁻ a : α, ‖c • f a‖ₑ ∂μ = ∫⁻ a : α, ‖c‖ₑ * ‖f a‖ₑ ∂μ := lintegral_congr fun i ↦ enorm_smul _ _
    _ < ∞ := by
      rw [lintegral_const_mul']
      exacts [mul_lt_top coe_lt_top hf, coe_ne_top]

theorem hasFiniteIntegral_smul_iff [NormedRing 𝕜] [MulActionWithZero 𝕜 β] [IsBoundedSMul 𝕜 β]
    {c : 𝕜} (hc : IsUnit c) (f : α → β) :
    HasFiniteIntegral (c • f) μ ↔ HasFiniteIntegral f μ := by
  obtain ⟨c, rfl⟩ := hc
  constructor
  · intro h
    simpa only [smul_smul, Units.inv_mul, one_smul] using h.smul ((c⁻¹ : 𝕜ˣ) : 𝕜)
  exact HasFiniteIntegral.smul _

@[fun_prop]
theorem HasFiniteIntegral.const_mul [NormedRing 𝕜] {f : α → 𝕜} (h : HasFiniteIntegral f μ) (c : 𝕜) :
    HasFiniteIntegral (fun x => c * f x) μ :=
  h.smul c

@[fun_prop]
theorem HasFiniteIntegral.mul_const [NormedRing 𝕜] {f : α → 𝕜} (h : HasFiniteIntegral f μ) (c : 𝕜) :
    HasFiniteIntegral (fun x => f x * c) μ :=
  h.smul (MulOpposite.op c)

section count

variable [MeasurableSingletonClass α]

/-- A function has finite integral for the counting measure iff its enorm has finite `tsum`. -/
-- Note that asking for mere summability makes no sense, as every sequence in ℝ≥0∞ is summable.
lemma hasFiniteIntegral_count_iff_enorm {f : α → ε} :
    HasFiniteIntegral f Measure.count ↔ tsum (‖f ·‖ₑ) < ⊤ := by
  simp only [hasFiniteIntegral_iff_enorm, lintegral_count]

/-- A function has finite integral for the counting measure iff its norm is summable. -/
lemma hasFiniteIntegral_count_iff {f : α → β} :
    HasFiniteIntegral f Measure.count ↔ Summable (‖f ·‖) := by
  simp only [hasFiniteIntegral_iff_enorm, enorm, lintegral_count, lt_top_iff_ne_top,
    tsum_coe_ne_top_iff_summable, ← summable_coe, coe_nnnorm]

end count

section restrict

variable {E : Type*} [NormedAddCommGroup E] {f : α → ε}

@[fun_prop]
lemma HasFiniteIntegral.restrict (h : HasFiniteIntegral f μ) {s : Set α} :
    HasFiniteIntegral f (μ.restrict s) := by
  refine lt_of_le_of_lt ?_ h
  simpa [Measure.restrict_univ] using lintegral_mono_set (subset_univ s)

end restrict

end NormedSpace

end MeasureTheory
