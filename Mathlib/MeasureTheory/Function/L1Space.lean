/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Integrable functions and `L¹` space

In the first part of this file, the predicate `Integrable` is defined and basic properties of
integrable functions are proved.

Such a predicate is already available under the name `Memℒp 1`. We give a direct definition which
is easier to use, and show that it is equivalent to `Memℒp 1`

In the second part, we establish an API between `Integrable` and the space `L¹` of equivalence
classes of integrable functions, already defined as a special case of `L^p` spaces for `p = 1`.

## Notation

* `α →₁[μ] β` is the type of `L¹` space, where `α` is a `MeasureSpace` and `β` is a
  `NormedAddCommGroup` with a `SecondCountableTopology`. `f : α →ₘ β` is a "function" in `L¹`.
  In comments, `[f]` is also used to denote an `L¹` function.

  `₁` can be typed as `\1`.

## Main definitions

* Let `f : α → β` be a function, where `α` is a `MeasureSpace` and `β` a `NormedAddCommGroup`.
  Then `HasFiniteIntegral f` means `(∫⁻ a, ‖f a‖₊) < ∞`.

* If `β` is moreover a `MeasurableSpace` then `f` is called `Integrable` if
  `f` is `Measurable` and `HasFiniteIntegral f` holds.

## Implementation notes

To prove something for an arbitrary integrable function, a useful theorem is
`Integrable.induction` in the file `SetIntegral`.

## Tags

integrable, function space, l1

-/


noncomputable section

open scoped Classical
open Topology ENNReal MeasureTheory NNReal

open Set Filter TopologicalSpace ENNReal EMetric MeasureTheory

variable {α β γ δ ε : Type*} {m : MeasurableSpace α} {μ ν : Measure α} [MeasurableSpace δ]
variable [NormedAddCommGroup β] [NormedAddCommGroup γ] [ENorm ε]

namespace MeasureTheory

/-! ### Some results about the Lebesgue integral involving a normed group -/


theorem lintegral_nnnorm_eq_lintegral_edist (f : α → β) :
    ∫⁻ a, ‖f a‖₊ ∂μ = ∫⁻ a, edist (f a) 0 ∂μ := by simp only [edist_eq_coe_nnnorm]

theorem lintegral_norm_eq_lintegral_edist (f : α → β) :
    ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ = ∫⁻ a, edist (f a) 0 ∂μ := by
  simp only [ofReal_norm_eq_coe_nnnorm, edist_eq_coe_nnnorm]

theorem lintegral_edist_triangle {f g h : α → β} (hf : AEStronglyMeasurable f μ)
    (hh : AEStronglyMeasurable h μ) :
    (∫⁻ a, edist (f a) (g a) ∂μ) ≤ (∫⁻ a, edist (f a) (h a) ∂μ) + ∫⁻ a, edist (g a) (h a) ∂μ := by
  rw [← lintegral_add_left' (hf.edist hh)]
  refine lintegral_mono fun a => ?_
  apply edist_triangle_right

theorem lintegral_nnnorm_zero : (∫⁻ _ : α, ‖(0 : β)‖₊ ∂μ) = 0 := by simp

theorem lintegral_nnnorm_add_left {f : α → β} (hf : AEStronglyMeasurable f μ) (g : α → γ) :
    ∫⁻ a, ‖f a‖₊ + ‖g a‖₊ ∂μ = (∫⁻ a, ‖f a‖₊ ∂μ) + ∫⁻ a, ‖g a‖₊ ∂μ :=
  lintegral_add_left' hf.ennnorm _

theorem lintegral_nnnorm_add_right (f : α → β) {g : α → γ} (hg : AEStronglyMeasurable g μ) :
    ∫⁻ a, ‖f a‖₊ + ‖g a‖₊ ∂μ = (∫⁻ a, ‖f a‖₊ ∂μ) + ∫⁻ a, ‖g a‖₊ ∂μ :=
  lintegral_add_right' _ hg.ennnorm

theorem lintegral_nnnorm_neg {f : α → β} : (∫⁻ a, ‖(-f) a‖₊ ∂μ) = ∫⁻ a, ‖f a‖₊ ∂μ := by
  simp only [Pi.neg_apply, nnnorm_neg]

/-! ### The predicate `HasFiniteIntegral` -/


/-- `HasFiniteIntegral f μ` means that the integral `∫⁻ a, ‖f a‖ ∂μ` is finite.
  `HasFiniteIntegral f` means `HasFiniteIntegral f volume`. -/
def HasFiniteIntegral {_ : MeasurableSpace α} (f : α → ε)
    (μ : Measure α := by volume_tac) : Prop :=
  (∫⁻ a, ‖f a‖ₑ ∂μ) < ∞

theorem hasFiniteIntegral_def {_ : MeasurableSpace α} (f : α → ε) (μ : Measure α) :
    HasFiniteIntegral f μ ↔ ((∫⁻ a, ‖f a‖ₑ ∂μ) < ∞) :=
  Iff.rfl

theorem hasFiniteIntegral_iff_nnnorm {f : α → β} :
    HasFiniteIntegral f μ ↔ (∫⁻ a, ‖f a‖₊ ∂μ) < ∞ := by
  simp only [HasFiniteIntegral, ofReal_norm_eq_coe_nnnorm, enorm_eq_nnnorm]

theorem hasFiniteIntegral_iff_norm (f : α → β) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) < ∞ := by
  simp only [hasFiniteIntegral_iff_nnnorm, ofReal_norm_eq_coe_nnnorm]

theorem hasFiniteIntegral_iff_edist (f : α → β) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, edist (f a) 0 ∂μ) < ∞ := by
  simp only [hasFiniteIntegral_iff_norm, edist_dist, dist_zero_right]

theorem hasFiniteIntegral_iff_ofReal {f : α → ℝ} (h : 0 ≤ᵐ[μ] f) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofReal (f a) ∂μ) < ∞ := by
  rw [hasFiniteIntegral_iff_nnnorm, lintegral_nnnorm_eq_of_ae_nonneg h]

theorem hasFiniteIntegral_iff_ofNNReal {f : α → ℝ≥0} :
    HasFiniteIntegral (fun x => (f x : ℝ)) μ ↔ (∫⁻ a, f a ∂μ) < ∞ := by
  simp [hasFiniteIntegral_iff_norm]

theorem HasFiniteIntegral.mono {f : α → β} {g : α → γ} (hg : HasFiniteIntegral g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ ‖g a‖) : HasFiniteIntegral f μ := by
  simp only [hasFiniteIntegral_iff_norm] at *
  calc
    (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) ≤ ∫⁻ a : α, ENNReal.ofReal ‖g a‖ ∂μ :=
      lintegral_mono_ae (h.mono fun a h => ofReal_le_ofReal h)
    _ < ∞ := hg

theorem HasFiniteIntegral.mono' {f : α → β} {g : α → ℝ} (hg : HasFiniteIntegral g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : HasFiniteIntegral f μ :=
  hg.mono <| h.mono fun _x hx => le_trans hx (le_abs_self _)

theorem HasFiniteIntegral.congr' {f : α → β} {g : α → γ} (hf : HasFiniteIntegral f μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) : HasFiniteIntegral g μ :=
  hf.mono <| EventuallyEq.le <| EventuallyEq.symm h

theorem hasFiniteIntegral_congr' {f : α → β} {g : α → γ} (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) :
    HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ :=
  ⟨fun hf => hf.congr' h, fun hg => hg.congr' <| EventuallyEq.symm h⟩

theorem HasFiniteIntegral.congr {f g : α → β} (hf : HasFiniteIntegral f μ) (h : f =ᵐ[μ] g) :
    HasFiniteIntegral g μ :=
  hf.congr' <| h.fun_comp norm

theorem hasFiniteIntegral_congr {f g : α → β} (h : f =ᵐ[μ] g) :
    HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ :=
  hasFiniteIntegral_congr' <| h.fun_comp norm

theorem hasFiniteIntegral_const_iff {c : β} :
    HasFiniteIntegral (fun _ : α => c) μ ↔ c = 0 ∨ μ univ < ∞ := by
  simp [hasFiniteIntegral_iff_nnnorm, lintegral_const, lt_top_iff_ne_top, ENNReal.mul_eq_top,
    or_iff_not_imp_left]

theorem hasFiniteIntegral_const [IsFiniteMeasure μ] (c : β) :
    HasFiniteIntegral (fun _ : α => c) μ :=
  hasFiniteIntegral_const_iff.2 (Or.inr <| measure_lt_top _ _)

theorem HasFiniteIntegral.of_mem_Icc [IsFiniteMeasure μ] (a b : ℝ) {X : α → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    HasFiniteIntegral X μ := by
  apply (hasFiniteIntegral_const (max ‖a‖ ‖b‖)).mono'
  filter_upwards [h.mono fun ω h ↦ h.1, h.mono fun ω h ↦ h.2] with ω using abs_le_max_abs_abs

theorem hasFiniteIntegral_of_bounded [IsFiniteMeasure μ] {f : α → β} {C : ℝ}
    (hC : ∀ᵐ a ∂μ, ‖f a‖ ≤ C) : HasFiniteIntegral f μ :=
  (hasFiniteIntegral_const C).mono' hC

theorem HasFiniteIntegral.of_finite [Finite α] [IsFiniteMeasure μ] {f : α → β} :
    HasFiniteIntegral f μ :=
  let ⟨_⟩ := nonempty_fintype α
  hasFiniteIntegral_of_bounded <| ae_of_all μ <| norm_le_pi_norm f

theorem HasFiniteIntegral.mono_measure {f : α → β} (h : HasFiniteIntegral f ν) (hμ : μ ≤ ν) :
    HasFiniteIntegral f μ :=
  lt_of_le_of_lt (lintegral_mono' hμ le_rfl) h

theorem HasFiniteIntegral.add_measure {f : α → β} (hμ : HasFiniteIntegral f μ)
    (hν : HasFiniteIntegral f ν) : HasFiniteIntegral f (μ + ν) := by
  simp only [HasFiniteIntegral, lintegral_add_measure] at *
  exact add_lt_top.2 ⟨hμ, hν⟩

theorem HasFiniteIntegral.left_of_add_measure {f : α → β} (h : HasFiniteIntegral f (μ + ν)) :
    HasFiniteIntegral f μ :=
  h.mono_measure <| Measure.le_add_right <| le_rfl

theorem HasFiniteIntegral.right_of_add_measure {f : α → β} (h : HasFiniteIntegral f (μ + ν)) :
    HasFiniteIntegral f ν :=
  h.mono_measure <| Measure.le_add_left <| le_rfl

@[simp]
theorem hasFiniteIntegral_add_measure {f : α → β} :
    HasFiniteIntegral f (μ + ν) ↔ HasFiniteIntegral f μ ∧ HasFiniteIntegral f ν :=
  ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

theorem HasFiniteIntegral.smul_measure {f : α → β} (h : HasFiniteIntegral f μ) {c : ℝ≥0∞}
    (hc : c ≠ ∞) : HasFiniteIntegral f (c • μ) := by
  simp only [HasFiniteIntegral, lintegral_smul_measure] at *
  exact mul_lt_top hc.lt_top h

@[simp]
theorem hasFiniteIntegral_zero_measure {m : MeasurableSpace α} (f : α → β) :
    HasFiniteIntegral f (0 : Measure α) := by
  simp only [HasFiniteIntegral, lintegral_zero_measure, zero_lt_top]

variable (α β μ)

@[simp]
theorem hasFiniteIntegral_zero : HasFiniteIntegral (fun _ : α => (0 : β)) μ := by
  simp [hasFiniteIntegral_iff_nnnorm]

variable {α β μ}

theorem HasFiniteIntegral.neg {f : α → β} (hfi : HasFiniteIntegral f μ) :
    HasFiniteIntegral (-f) μ := by simpa [hasFiniteIntegral_iff_nnnorm] using hfi

@[simp]
theorem hasFiniteIntegral_neg_iff {f : α → β} : HasFiniteIntegral (-f) μ ↔ HasFiniteIntegral f μ :=
  ⟨fun h => neg_neg f ▸ h.neg, HasFiniteIntegral.neg⟩

theorem HasFiniteIntegral.norm {f : α → β} (hfi : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun a => ‖f a‖) μ := by
  have eq : (fun a => (nnnorm ‖f a‖ : ℝ≥0∞)) = fun a => (‖f a‖₊ : ℝ≥0∞) := by
    funext
    rw [nnnorm_norm]
  rwa [hasFiniteIntegral_iff_nnnorm, eq]

theorem hasFiniteIntegral_norm_iff (f : α → β) :
    HasFiniteIntegral (fun a => ‖f a‖) μ ↔ HasFiniteIntegral f μ :=
  hasFiniteIntegral_congr' <| Eventually.of_forall fun x => norm_norm (f x)

theorem hasFiniteIntegral_toReal_of_lintegral_ne_top {f : α → ℝ≥0∞} (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
    HasFiniteIntegral (fun x ↦ (f x).toReal) μ := by
  have h x : (‖(f x).toReal‖₊ : ℝ≥0∞) = ENNReal.ofNNReal ⟨(f x).toReal, ENNReal.toReal_nonneg⟩ := by
    rw [Real.nnnorm_of_nonneg]
  simp_rw [hasFiniteIntegral_iff_nnnorm, h]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) (lt_top_iff_ne_top.2 hf)
  by_cases hfx : f x = ∞
  · simp [hfx]
  · lift f x to ℝ≥0 using hfx with fx h
    simp [← h, ← NNReal.coe_le_coe]

lemma hasFiniteIntegral_toReal_iff {f : α → ℝ≥0∞} (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    HasFiniteIntegral (fun x ↦ (f x).toReal) μ ↔ ∫⁻ x, f x ∂μ ≠ ∞ := by
  have h_eq x : (‖(f x).toReal‖₊ : ℝ≥0∞)
      = ENNReal.ofNNReal ⟨(f x).toReal, ENNReal.toReal_nonneg⟩ := by
    rw [Real.nnnorm_of_nonneg]
  simp_rw [hasFiniteIntegral_iff_nnnorm, h_eq, lt_top_iff_ne_top]
  convert Iff.rfl using 2
  refine lintegral_congr_ae ?_
  filter_upwards [hf_ne_top] with x hfx
  lift f x to ℝ≥0 using hfx with fx h
  simp only [coe_toReal, ENNReal.coe_inj]
  rfl

theorem isFiniteMeasure_withDensity_ofReal {f : α → ℝ} (hfi : HasFiniteIntegral f μ) :
    IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal <| f x) := by
  refine isFiniteMeasure_withDensity ((lintegral_mono fun x => ?_).trans_lt hfi).ne
  exact Real.ofReal_le_ennnorm (f x)

section DominatedConvergence

variable {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}

theorem all_ae_ofReal_F_le_bound (h : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a) :
    ∀ n, ∀ᵐ a ∂μ, ENNReal.ofReal ‖F n a‖ ≤ ENNReal.ofReal (bound a) := fun n =>
  (h n).mono fun _ h => ENNReal.ofReal_le_ofReal h

theorem all_ae_tendsto_ofReal_norm (h : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop <| 𝓝 <| f a) :
    ∀ᵐ a ∂μ, Tendsto (fun n => ENNReal.ofReal ‖F n a‖) atTop <| 𝓝 <| ENNReal.ofReal ‖f a‖ :=
  h.mono fun _ h => tendsto_ofReal <| Tendsto.comp (Continuous.tendsto continuous_norm _) h

theorem all_ae_ofReal_f_le_bound (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    ∀ᵐ a ∂μ, ENNReal.ofReal ‖f a‖ ≤ ENNReal.ofReal (bound a) := by
  have F_le_bound := all_ae_ofReal_F_le_bound h_bound
  rw [← ae_all_iff] at F_le_bound
  apply F_le_bound.mp ((all_ae_tendsto_ofReal_norm h_lim).mono _)
  intro a tendsto_norm F_le_bound
  exact le_of_tendsto' tendsto_norm F_le_bound

theorem hasFiniteIntegral_of_dominated_convergence {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
    (bound_hasFiniteIntegral : HasFiniteIntegral bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : HasFiniteIntegral f μ := by
  /- `‖F n a‖ ≤ bound a` and `‖F n a‖ --> ‖f a‖` implies `‖f a‖ ≤ bound a`,
    and so `∫ ‖f‖ ≤ ∫ bound < ∞` since `bound` is has_finite_integral -/
  rw [hasFiniteIntegral_iff_norm]
  calc
    (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (bound a) ∂μ :=
      lintegral_mono_ae <| all_ae_ofReal_f_le_bound h_bound h_lim
    _ < ∞ := by
      rw [← hasFiniteIntegral_iff_ofReal]
      · exact bound_hasFiniteIntegral
      exact (h_bound 0).mono fun a h => le_trans (norm_nonneg _) h

theorem tendsto_lintegral_norm_of_dominated_convergence {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
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
    filter_upwards [all_ae_ofReal_F_le_bound h_bound n,
      all_ae_ofReal_f_le_bound h_bound h_lim] with a h₁ h₂
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
          exact coe_ne_top
        _ ≠ ∞ := mul_ne_top coe_ne_top bound_hasFiniteIntegral.ne
    filter_upwards [h_bound 0] with _ h using le_trans (norm_nonneg _) h
  -- Show `‖f a - F n a‖ --> 0`
  · exact h

end DominatedConvergence

section PosPart

/-! Lemmas used for defining the positive part of an `L¹` function -/


theorem HasFiniteIntegral.max_zero {f : α → ℝ} (hf : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun a => max (f a) 0) μ :=
  hf.mono <| Eventually.of_forall fun x => by simp [abs_le, le_abs_self]

theorem HasFiniteIntegral.min_zero {f : α → ℝ} (hf : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun a => min (f a) 0) μ :=
  hf.mono <| Eventually.of_forall fun x => by simpa [abs_le] using neg_abs_le _

end PosPart

section NormedSpace

variable {𝕜 : Type*}

theorem HasFiniteIntegral.smul [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 β] [BoundedSMul 𝕜 β] (c : 𝕜)
    {f : α → β} : HasFiniteIntegral f μ → HasFiniteIntegral (c • f) μ := by
  simp only [HasFiniteIntegral]; intro hfi
  calc
    (∫⁻ a : α, ‖c • f a‖₊ ∂μ) ≤ ∫⁻ a : α, ‖c‖₊ * ‖f a‖₊ ∂μ := by
      refine lintegral_mono ?_
      intro i
      -- After https://github.com/leanprover/lean4/pull/2734, we need to do beta reduction `exact mod_cast`
      beta_reduce
      exact mod_cast (nnnorm_smul_le c (f i))
    _ < ∞ := by
      rw [lintegral_const_mul']
      exacts [mul_lt_top coe_lt_top hfi, coe_ne_top]

theorem hasFiniteIntegral_smul_iff [NormedRing 𝕜] [MulActionWithZero 𝕜 β] [BoundedSMul 𝕜 β] {c : 𝕜}
    (hc : IsUnit c) (f : α → β) : HasFiniteIntegral (c • f) μ ↔ HasFiniteIntegral f μ := by
  obtain ⟨c, rfl⟩ := hc
  constructor
  · intro h
    simpa only [smul_smul, Units.inv_mul, one_smul] using h.smul ((c⁻¹ : 𝕜ˣ) : 𝕜)
  exact HasFiniteIntegral.smul _

theorem HasFiniteIntegral.const_mul [NormedRing 𝕜] {f : α → 𝕜} (h : HasFiniteIntegral f μ) (c : 𝕜) :
    HasFiniteIntegral (fun x => c * f x) μ :=
  h.smul c

theorem HasFiniteIntegral.mul_const [NormedRing 𝕜] {f : α → 𝕜} (h : HasFiniteIntegral f μ) (c : 𝕜) :
    HasFiniteIntegral (fun x => f x * c) μ :=
  h.smul (MulOpposite.op c)

end NormedSpace

/-! ### The predicate `Integrable` -/

variable [TopologicalSpace ε]


/-- `Integrable f μ` means that `f` is measurable and that the integral `∫⁻ a, ‖f a‖ ∂μ` is finite.
  `Integrable f` means `Integrable f volume`. -/
def Integrable {α} {_ : MeasurableSpace α} (f : α → ε)
    (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ

/-- Notation for `Integrable` with respect to a non-standard σ-algebra. -/
scoped notation "Integrable[" mα "]" => @Integrable _ _ _ _ mα

theorem memℒp_one_iff_integrable {f : α → β} : Memℒp f 1 μ ↔ Integrable f μ := by
  simp_rw [Integrable, hasFiniteIntegral_iff_nnnorm, Memℒp, eLpNorm_one_eq_lintegral_nnnorm]

theorem Integrable.aestronglyMeasurable {f : α → β} (hf : Integrable f μ) :
    AEStronglyMeasurable f μ :=
  hf.1

theorem Integrable.aemeasurable [MeasurableSpace β] [BorelSpace β] {f : α → β}
    (hf : Integrable f μ) : AEMeasurable f μ :=
  hf.aestronglyMeasurable.aemeasurable

theorem Integrable.hasFiniteIntegral {f : α → β} (hf : Integrable f μ) : HasFiniteIntegral f μ :=
  hf.2

theorem Integrable.mono {f : α → β} {g : α → γ} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ ‖g a‖) : Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono h⟩

theorem Integrable.mono' {f : α → β} {g : α → ℝ} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono' h⟩

theorem Integrable.congr' {f : α → β} {g : α → γ} (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) : Integrable g μ :=
  ⟨hg, hf.hasFiniteIntegral.congr' h⟩

theorem integrable_congr' {f : α → β} {g : α → γ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) :
    Integrable f μ ↔ Integrable g μ :=
  ⟨fun h2f => h2f.congr' hg h, fun h2g => h2g.congr' hf <| EventuallyEq.symm h⟩

theorem Integrable.congr {f g : α → β} (hf : Integrable f μ) (h : f =ᵐ[μ] g) : Integrable g μ :=
  ⟨hf.1.congr h, hf.2.congr h⟩

theorem integrable_congr {f g : α → β} (h : f =ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

theorem integrable_const_iff {c : β} : Integrable (fun _ : α => c) μ ↔ c = 0 ∨ μ univ < ∞ := by
  have : AEStronglyMeasurable (fun _ : α => c) μ := aestronglyMeasurable_const
  rw [Integrable, and_iff_right this, hasFiniteIntegral_const_iff]

theorem Integrable.of_mem_Icc [IsFiniteMeasure μ] (a b : ℝ) {X : α → ℝ} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable X μ :=
  ⟨hX.aestronglyMeasurable, .of_mem_Icc a b h⟩

@[simp]
theorem integrable_const [IsFiniteMeasure μ] (c : β) : Integrable (fun _ : α => c) μ :=
  integrable_const_iff.2 <| Or.inr <| measure_lt_top _ _

@[simp]
lemma Integrable.of_finite [Finite α] [MeasurableSingletonClass α] [IsFiniteMeasure μ] {f : α → β} :
    Integrable f μ := ⟨.of_finite, .of_finite⟩

/-- This lemma is a special case of `Integrable.of_finite`. -/
-- Eternal deprecation for discoverability, don't remove
@[deprecated Integrable.of_finite (since := "2024-10-05"), nolint deprecatedNoSince]
lemma Integrable.of_isEmpty [IsEmpty α] {f : α → β} : Integrable f μ := .of_finite


theorem Memℒp.integrable_norm_rpow {f : α → β} {p : ℝ≥0∞} (hf : Memℒp f p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : Integrable (fun x : α => ‖f x‖ ^ p.toReal) μ := by
  rw [← memℒp_one_iff_integrable]
  exact hf.norm_rpow hp_ne_zero hp_ne_top

theorem Memℒp.integrable_norm_rpow' [IsFiniteMeasure μ] {f : α → β} {p : ℝ≥0∞} (hf : Memℒp f p μ) :
    Integrable (fun x : α => ‖f x‖ ^ p.toReal) μ := by
  by_cases h_zero : p = 0
  · simp [h_zero, integrable_const]
  by_cases h_top : p = ∞
  · simp [h_top, integrable_const]
  exact hf.integrable_norm_rpow h_zero h_top

theorem Integrable.mono_measure {f : α → β} (h : Integrable f ν) (hμ : μ ≤ ν) : Integrable f μ :=
  ⟨h.aestronglyMeasurable.mono_measure hμ, h.hasFiniteIntegral.mono_measure hμ⟩

theorem Integrable.of_measure_le_smul {μ' : Measure α} (c : ℝ≥0∞) (hc : c ≠ ∞) (hμ'_le : μ' ≤ c • μ)
    {f : α → β} (hf : Integrable f μ) : Integrable f μ' := by
  rw [← memℒp_one_iff_integrable] at hf ⊢
  exact hf.of_measure_le_smul c hc hμ'_le

theorem Integrable.add_measure {f : α → β} (hμ : Integrable f μ) (hν : Integrable f ν) :
    Integrable f (μ + ν) := by
  simp_rw [← memℒp_one_iff_integrable] at hμ hν ⊢
  refine ⟨hμ.aestronglyMeasurable.add_measure hν.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_one_add_measure, ENNReal.add_lt_top]
  exact ⟨hμ.eLpNorm_lt_top, hν.eLpNorm_lt_top⟩

theorem Integrable.left_of_add_measure {f : α → β} (h : Integrable f (μ + ν)) : Integrable f μ := by
  rw [← memℒp_one_iff_integrable] at h ⊢
  exact h.left_of_add_measure

theorem Integrable.right_of_add_measure {f : α → β} (h : Integrable f (μ + ν)) :
    Integrable f ν := by
  rw [← memℒp_one_iff_integrable] at h ⊢
  exact h.right_of_add_measure

@[simp]
theorem integrable_add_measure {f : α → β} :
    Integrable f (μ + ν) ↔ Integrable f μ ∧ Integrable f ν :=
  ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

@[simp]
theorem integrable_zero_measure {_ : MeasurableSpace α} {f : α → β} :
    Integrable f (0 : Measure α) :=
  ⟨aestronglyMeasurable_zero_measure f, hasFiniteIntegral_zero_measure f⟩

theorem integrable_finset_sum_measure {ι} {m : MeasurableSpace α} {f : α → β} {μ : ι → Measure α}
    {s : Finset ι} : Integrable f (∑ i ∈ s, μ i) ↔ ∀ i ∈ s, Integrable f (μ i) := by
  induction s using Finset.induction_on <;> simp [*]

theorem Integrable.smul_measure {f : α → β} (h : Integrable f μ) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    Integrable f (c • μ) := by
  rw [← memℒp_one_iff_integrable] at h ⊢
  exact h.smul_measure hc

theorem Integrable.smul_measure_nnreal {f : α → β} (h : Integrable f μ) {c : ℝ≥0} :
    Integrable f (c • μ) := by
  apply h.smul_measure
  simp

theorem integrable_smul_measure {f : α → β} {c : ℝ≥0∞} (h₁ : c ≠ 0) (h₂ : c ≠ ∞) :
    Integrable f (c • μ) ↔ Integrable f μ :=
  ⟨fun h => by
    simpa only [smul_smul, ENNReal.inv_mul_cancel h₁ h₂, one_smul] using
      h.smul_measure (ENNReal.inv_ne_top.2 h₁),
    fun h => h.smul_measure h₂⟩

theorem integrable_inv_smul_measure {f : α → β} {c : ℝ≥0∞} (h₁ : c ≠ 0) (h₂ : c ≠ ∞) :
    Integrable f (c⁻¹ • μ) ↔ Integrable f μ :=
  integrable_smul_measure (by simpa using h₂) (by simpa using h₁)

theorem Integrable.to_average {f : α → β} (h : Integrable f μ) : Integrable f ((μ univ)⁻¹ • μ) := by
  rcases eq_or_ne μ 0 with (rfl | hne)
  · rwa [smul_zero]
  · apply h.smul_measure
    simpa

theorem integrable_average [IsFiniteMeasure μ] {f : α → β} :
    Integrable f ((μ univ)⁻¹ • μ) ↔ Integrable f μ :=
  (eq_or_ne μ 0).by_cases (fun h => by simp [h]) fun h =>
    integrable_smul_measure (ENNReal.inv_ne_zero.2 <| measure_ne_top _ _)
      (ENNReal.inv_ne_top.2 <| mt Measure.measure_univ_eq_zero.1 h)

theorem integrable_map_measure {f : α → δ} {g : δ → β}
    (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← memℒp_one_iff_integrable]
  exact memℒp_map_measure_iff hg hf

theorem Integrable.comp_aemeasurable {f : α → δ} {g : δ → β} (hg : Integrable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : Integrable (g ∘ f) μ :=
  (integrable_map_measure hg.aestronglyMeasurable hf).mp hg

theorem Integrable.comp_measurable {f : α → δ} {g : δ → β} (hg : Integrable g (Measure.map f μ))
    (hf : Measurable f) : Integrable (g ∘ f) μ :=
  hg.comp_aemeasurable hf.aemeasurable

theorem _root_.MeasurableEmbedding.integrable_map_iff {f : α → δ} (hf : MeasurableEmbedding f)
    {g : δ → β} : Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← memℒp_one_iff_integrable]
  exact hf.memℒp_map_measure_iff

theorem integrable_map_equiv (f : α ≃ᵐ δ) (g : δ → β) :
    Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← memℒp_one_iff_integrable]
  exact f.memℒp_map_measure_iff

theorem MeasurePreserving.integrable_comp {ν : Measure δ} {g : δ → β} {f : α → δ}
    (hf : MeasurePreserving f μ ν) (hg : AEStronglyMeasurable g ν) :
    Integrable (g ∘ f) μ ↔ Integrable g ν := by
  rw [← hf.map_eq] at hg ⊢
  exact (integrable_map_measure hg hf.measurable.aemeasurable).symm

theorem MeasurePreserving.integrable_comp_emb {f : α → δ} {ν} (h₁ : MeasurePreserving f μ ν)
    (h₂ : MeasurableEmbedding f) {g : δ → β} : Integrable (g ∘ f) μ ↔ Integrable g ν :=
  h₁.map_eq ▸ Iff.symm h₂.integrable_map_iff

theorem lintegral_edist_lt_top {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫⁻ a, edist (f a) (g a) ∂μ) < ∞ :=
  lt_of_le_of_lt (lintegral_edist_triangle hf.aestronglyMeasurable aestronglyMeasurable_zero)
    (ENNReal.add_lt_top.2 <| by
      simp_rw [Pi.zero_apply, ← hasFiniteIntegral_iff_edist]
      exact ⟨hf.hasFiniteIntegral, hg.hasFiniteIntegral⟩)

variable (α β μ)

@[simp]
theorem integrable_zero : Integrable (fun _ => (0 : β)) μ := by
  simp [Integrable, aestronglyMeasurable_const]

variable {α β μ}

theorem Integrable.add' {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
    HasFiniteIntegral (f + g) μ :=
  calc
    (∫⁻ a, ‖f a + g a‖₊ ∂μ) ≤ ∫⁻ a, ‖f a‖₊ + ‖g a‖₊ ∂μ :=
      lintegral_mono fun a => by
        -- After https://github.com/leanprover/lean4/pull/2734, we need to do beta reduction before `exact mod_cast`
        beta_reduce
        exact mod_cast nnnorm_add_le _ _
    _ = _ := lintegral_nnnorm_add_left hf.aestronglyMeasurable _
    _ < ∞ := add_lt_top.2 ⟨hf.hasFiniteIntegral, hg.hasFiniteIntegral⟩

theorem Integrable.add {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (f + g) μ :=
  ⟨hf.aestronglyMeasurable.add hg.aestronglyMeasurable, hf.add' hg⟩

theorem integrable_finset_sum' {ι} (s : Finset ι) {f : ι → α → β}
    (hf : ∀ i ∈ s, Integrable (f i) μ) : Integrable (∑ i ∈ s, f i) μ :=
  Finset.sum_induction f (fun g => Integrable g μ) (fun _ _ => Integrable.add)
    (integrable_zero _ _ _) hf

theorem integrable_finset_sum {ι} (s : Finset ι) {f : ι → α → β}
    (hf : ∀ i ∈ s, Integrable (f i) μ) : Integrable (fun a => ∑ i ∈ s, f i a) μ := by
  simpa only [← Finset.sum_apply] using integrable_finset_sum' s hf

/-- If `f` is integrable, then so is `-f`.
See `Integrable.neg'` for the same statement, but formulated with `x ↦ - f x` instead of `-f`. -/
theorem Integrable.neg {f : α → β} (hf : Integrable f μ) : Integrable (-f) μ :=
  ⟨hf.aestronglyMeasurable.neg, hf.hasFiniteIntegral.neg⟩

/-- If `f` is integrable, then so is `fun x ↦ - f x`.
See `Integrable.neg` for the same statement, but formulated with `-f` instead of `fun x ↦ - f x`. -/
theorem Integrable.neg' {f : α → β} (hf : Integrable f μ) : Integrable (fun x ↦ - f x) μ :=
  ⟨hf.aestronglyMeasurable.neg, hf.hasFiniteIntegral.neg⟩

@[simp]
theorem integrable_neg_iff {f : α → β} : Integrable (-f) μ ↔ Integrable f μ :=
  ⟨fun h => neg_neg f ▸ h.neg, Integrable.neg⟩

/-- if `f` is integrable, then `f + g` is integrable iff `g` is.
See `integrable_add_iff_integrable_right'` for the same statement with `fun x ↦ f x + g x` instead
of `f + g`. -/
@[simp]
lemma integrable_add_iff_integrable_right {f g : α → β} (hf : Integrable f μ) :
    Integrable (f + g) μ ↔ Integrable g μ :=
  ⟨fun h ↦ show g = f + g + (-f) by simp only [add_neg_cancel_comm] ▸ h.add hf.neg,
    fun h ↦ hf.add h⟩

/-- if `f` is integrable, then `fun x ↦ f x + g x` is integrable iff `g` is.
See `integrable_add_iff_integrable_right` for the same statement with `f + g` instead
of `fun x ↦ f x + g x`. -/
@[simp]
lemma integrable_add_iff_integrable_right' {f g : α → β} (hf : Integrable f μ) :
    Integrable (fun x ↦ f x + g x) μ ↔ Integrable g μ :=
  integrable_add_iff_integrable_right hf

/-- if `f` is integrable, then `g + f` is integrable iff `g` is.
See `integrable_add_iff_integrable_left'` for the same statement with `fun x ↦ g x + f x` instead
of `g + f`. -/
@[simp]
lemma integrable_add_iff_integrable_left {f g : α → β} (hf : Integrable f μ) :
    Integrable (g + f) μ ↔ Integrable g μ := by
  rw [add_comm, integrable_add_iff_integrable_right hf]

/-- if `f` is integrable, then `fun x ↦ g x + f x` is integrable iff `g` is.
See `integrable_add_iff_integrable_left'` for the same statement with `g + f` instead
of `fun x ↦ g x + f x`. -/
@[simp]
lemma integrable_add_iff_integrable_left' {f g : α → β} (hf : Integrable f μ) :
    Integrable (fun x ↦ g x + f x) μ ↔ Integrable g μ :=
  integrable_add_iff_integrable_left hf

lemma integrable_left_of_integrable_add_of_nonneg {f g : α → ℝ}
    (h_meas : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g)
    (h_int : Integrable (f + g) μ) : Integrable f μ := by
  refine h_int.mono' h_meas ?_
  filter_upwards [hf, hg] with a haf hag
  exact (Real.norm_of_nonneg haf).symm ▸ le_add_of_nonneg_right hag

lemma integrable_right_of_integrable_add_of_nonneg {f g : α → ℝ}
    (h_meas : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g)
    (h_int : Integrable (f + g) μ) : Integrable g μ :=
  integrable_left_of_integrable_add_of_nonneg
    ((AEStronglyMeasurable.add_iff_right h_meas).mp h_int.aestronglyMeasurable)
      hg hf (add_comm f g ▸ h_int)

lemma integrable_add_iff_of_nonneg {f g : α → ℝ} (h_meas : AEStronglyMeasurable f μ)
    (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g) :
    Integrable (f + g) μ ↔ Integrable f μ ∧ Integrable g μ :=
  ⟨fun h ↦ ⟨integrable_left_of_integrable_add_of_nonneg h_meas hf hg h,
    integrable_right_of_integrable_add_of_nonneg h_meas hf hg h⟩, fun ⟨hf, hg⟩ ↦ hf.add hg⟩

lemma integrable_add_iff_of_nonpos {f g : α → ℝ} (h_meas : AEStronglyMeasurable f μ)
    (hf : f ≤ᵐ[μ] 0) (hg : g ≤ᵐ[μ] 0) :
    Integrable (f + g) μ ↔ Integrable f μ ∧ Integrable g μ := by
  rw [← integrable_neg_iff, ← integrable_neg_iff (f := f), ← integrable_neg_iff (f := g), neg_add]
  exact integrable_add_iff_of_nonneg h_meas.neg (hf.mono (fun _ ↦ neg_nonneg_of_nonpos))
    (hg.mono (fun _ ↦ neg_nonneg_of_nonpos))

lemma integrable_add_const_iff [IsFiniteMeasure μ] {f : α → β} {c : β} :
    Integrable (fun x ↦ f x + c) μ ↔ Integrable f μ :=
  integrable_add_iff_integrable_left (integrable_const _)

lemma integrable_const_add_iff [IsFiniteMeasure μ] {f : α → β} {c : β} :
    Integrable (fun x ↦ c + f x) μ ↔ Integrable f μ :=
  integrable_add_iff_integrable_right (integrable_const _)

theorem Integrable.sub {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (f - g) μ := by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem Integrable.norm {f : α → β} (hf : Integrable f μ) : Integrable (fun a => ‖f a‖) μ :=
  ⟨hf.aestronglyMeasurable.norm, hf.hasFiniteIntegral.norm⟩

theorem Integrable.inf {β} [NormedLatticeAddCommGroup β] {f g : α → β} (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (f ⊓ g) μ := by
  rw [← memℒp_one_iff_integrable] at hf hg ⊢
  exact hf.inf hg

theorem Integrable.sup {β} [NormedLatticeAddCommGroup β] {f g : α → β} (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (f ⊔ g) μ := by
  rw [← memℒp_one_iff_integrable] at hf hg ⊢
  exact hf.sup hg

theorem Integrable.abs {β} [NormedLatticeAddCommGroup β] {f : α → β} (hf : Integrable f μ) :
    Integrable (fun a => |f a|) μ := by
  rw [← memℒp_one_iff_integrable] at hf ⊢
  exact hf.abs

theorem Integrable.bdd_mul {F : Type*} [NormedDivisionRing F] {f g : α → F} (hint : Integrable g μ)
    (hm : AEStronglyMeasurable f μ) (hfbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => f x * g x) μ := by
  cases' isEmpty_or_nonempty α with hα hα
  · rw [μ.eq_zero_of_isEmpty]
    exact integrable_zero_measure
  · refine ⟨hm.mul hint.1, ?_⟩
    obtain ⟨C, hC⟩ := hfbdd
    have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC hα.some)
    have : (fun x => ‖f x * g x‖₊) ≤ fun x => ⟨C, hCnonneg⟩ * ‖g x‖₊ := by
      intro x
      simp only [nnnorm_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (zero_le _)
    refine lt_of_le_of_lt (lintegral_mono_nnreal this) ?_
    simp only [ENNReal.coe_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hint.2

/-- **Hölder's inequality for integrable functions**: the scalar multiplication of an integrable
vector-valued function by a scalar function with finite essential supremum is integrable. -/
theorem Integrable.essSup_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 β] {f : α → β}
    (hf : Integrable f μ) {g : α → 𝕜} (g_aestronglyMeasurable : AEStronglyMeasurable g μ)
    (ess_sup_g : essSup (fun x => (‖g x‖₊ : ℝ≥0∞)) μ ≠ ∞) :
    Integrable (fun x : α => g x • f x) μ := by
  rw [← memℒp_one_iff_integrable] at *
  refine ⟨g_aestronglyMeasurable.smul hf.1, ?_⟩
  have h : (1 : ℝ≥0∞) / 1 = 1 / ∞ + 1 / 1 := by norm_num
  have hg' : eLpNorm g ∞ μ ≠ ∞ := by rwa [eLpNorm_exponent_top]
  calc
    eLpNorm (fun x : α => g x • f x) 1 μ ≤ _ := by
      simpa using MeasureTheory.eLpNorm_smul_le_mul_eLpNorm hf.1 g_aestronglyMeasurable h
    _ < ∞ := ENNReal.mul_lt_top hg'.lt_top hf.2

/-- Hölder's inequality for integrable functions: the scalar multiplication of an integrable
scalar-valued function by a vector-value function with finite essential supremum is integrable. -/
theorem Integrable.smul_essSup {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 β] [BoundedSMul 𝕜 β]
    {f : α → 𝕜} (hf : Integrable f μ) {g : α → β}
    (g_aestronglyMeasurable : AEStronglyMeasurable g μ)
    (ess_sup_g : essSup (fun x => (‖g x‖₊ : ℝ≥0∞)) μ ≠ ∞) :
    Integrable (fun x : α => f x • g x) μ := by
  rw [← memℒp_one_iff_integrable] at *
  refine ⟨hf.1.smul g_aestronglyMeasurable, ?_⟩
  have h : (1 : ℝ≥0∞) / 1 = 1 / 1 + 1 / ∞ := by norm_num
  have hg' : eLpNorm g ∞ μ ≠ ∞ := by rwa [eLpNorm_exponent_top]
  calc
    eLpNorm (fun x : α => f x • g x) 1 μ ≤ _ := by
      simpa using MeasureTheory.eLpNorm_smul_le_mul_eLpNorm g_aestronglyMeasurable hf.1 h
    _ < ∞ := ENNReal.mul_lt_top hf.2 hg'.lt_top

theorem integrable_norm_iff {f : α → β} (hf : AEStronglyMeasurable f μ) :
    Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ := by
  simp_rw [Integrable, and_iff_right hf, and_iff_right hf.norm, hasFiniteIntegral_norm_iff]

theorem integrable_of_norm_sub_le {f₀ f₁ : α → β} {g : α → ℝ} (hf₁_m : AEStronglyMeasurable f₁ μ)
    (hf₀_i : Integrable f₀ μ) (hg_i : Integrable g μ) (h : ∀ᵐ a ∂μ, ‖f₀ a - f₁ a‖ ≤ g a) :
    Integrable f₁ μ :=
  haveI : ∀ᵐ a ∂μ, ‖f₁ a‖ ≤ ‖f₀ a‖ + g a := by
    apply h.mono
    intro a ha
    calc
      ‖f₁ a‖ ≤ ‖f₀ a‖ + ‖f₀ a - f₁ a‖ := norm_le_insert _ _
      _ ≤ ‖f₀ a‖ + g a := add_le_add_left ha _
  Integrable.mono' (hf₀_i.norm.add hg_i) hf₁_m this

lemma integrable_of_le_of_le {f g₁ g₂ : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (h_le₁ : g₁ ≤ᵐ[μ] f) (h_le₂ : f ≤ᵐ[μ] g₂)
    (h_int₁ : Integrable g₁ μ) (h_int₂ : Integrable g₂ μ) :
    Integrable f μ := by
  have : ∀ᵐ x ∂μ, ‖f x‖ ≤ max ‖g₁ x‖ ‖g₂ x‖ := by
    filter_upwards [h_le₁, h_le₂] with x hx1 hx2
    simp only [Real.norm_eq_abs]
    exact abs_le_max_abs_abs hx1 hx2
  have h_le_add : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖‖g₁ x‖ + ‖g₂ x‖‖ := by
    filter_upwards [this] with x hx
    refine hx.trans ?_
    conv_rhs => rw [Real.norm_of_nonneg (by positivity)]
    exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
  exact Integrable.mono (h_int₁.norm.add h_int₂.norm) hf h_le_add

theorem Integrable.prod_mk {f : α → β} {g : α → γ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => (f x, g x)) μ :=
  ⟨hf.aestronglyMeasurable.prod_mk hg.aestronglyMeasurable,
    (hf.norm.add' hg.norm).mono <|
      Eventually.of_forall fun x =>
        calc
          max ‖f x‖ ‖g x‖ ≤ ‖f x‖ + ‖g x‖ := max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
          _ ≤ ‖‖f x‖ + ‖g x‖‖ := le_abs_self _⟩

theorem Memℒp.integrable {q : ℝ≥0∞} (hq1 : 1 ≤ q) {f : α → β} [IsFiniteMeasure μ]
    (hfq : Memℒp f q μ) : Integrable f μ :=
  memℒp_one_iff_integrable.mp (hfq.mono_exponent hq1)

/-- A non-quantitative version of Markov inequality for integrable functions: the measure of points
where `‖f x‖ ≥ ε` is finite for all positive `ε`. -/
theorem Integrable.measure_norm_ge_lt_top {f : α → β} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    μ { x | ε ≤ ‖f x‖ } < ∞ := by
  rw [show { x | ε ≤ ‖f x‖ } = { x | ENNReal.ofReal ε ≤ ‖f x‖₊ } by
      simp only [ENNReal.ofReal, Real.toNNReal_le_iff_le_coe, ENNReal.coe_le_coe, coe_nnnorm]]
  refine (meas_ge_le_mul_pow_eLpNorm μ one_ne_zero ENNReal.one_ne_top hf.1 ?_).trans_lt ?_
  · simpa only [Ne, ENNReal.ofReal_eq_zero, not_le] using hε
  apply ENNReal.mul_lt_top
  · simpa only [ENNReal.one_toReal, ENNReal.rpow_one, ENNReal.inv_lt_top, ENNReal.ofReal_pos]
      using hε
  · simpa only [ENNReal.one_toReal, ENNReal.rpow_one] using
      (memℒp_one_iff_integrable.2 hf).eLpNorm_lt_top

/-- A non-quantitative version of Markov inequality for integrable functions: the measure of points
where `‖f x‖ > ε` is finite for all positive `ε`. -/
lemma Integrable.measure_norm_gt_lt_top {f : α → β} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    μ {x | ε < ‖f x‖} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ h ↦ (Set.mem_setOf_eq ▸ h).le)) (hf.measure_norm_ge_lt_top hε)

/-- If `f` is `ℝ`-valued and integrable, then for any `c > 0` the set `{x | f x ≥ c}` has finite
measure. -/
lemma Integrable.measure_ge_lt_top {f : α → ℝ} (hf : Integrable f μ) {ε : ℝ} (ε_pos : 0 < ε) :
    μ {a : α | ε ≤ f a} < ∞ := by
  refine lt_of_le_of_lt (measure_mono ?_) (hf.measure_norm_ge_lt_top ε_pos)
  intro x hx
  simp only [Real.norm_eq_abs, Set.mem_setOf_eq] at hx ⊢
  exact hx.trans (le_abs_self _)

/-- If `f` is `ℝ`-valued and integrable, then for any `c < 0` the set `{x | f x ≤ c}` has finite
measure. -/
lemma Integrable.measure_le_lt_top {f : α → ℝ} (hf : Integrable f μ) {c : ℝ} (c_neg : c < 0) :
    μ {a : α | f a ≤ c} < ∞ := by
  refine lt_of_le_of_lt (measure_mono ?_) (hf.measure_norm_ge_lt_top (show 0 < -c by linarith))
  intro x hx
  simp only [Real.norm_eq_abs, Set.mem_setOf_eq] at hx ⊢
  exact (show -c ≤ - f x by linarith).trans (neg_le_abs _)

/-- If `f` is `ℝ`-valued and integrable, then for any `c > 0` the set `{x | f x > c}` has finite
measure. -/
lemma Integrable.measure_gt_lt_top {f : α → ℝ} (hf : Integrable f μ) {ε : ℝ} (ε_pos : 0 < ε) :
    μ {a : α | ε < f a} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ hx ↦ (Set.mem_setOf_eq ▸ hx).le))
    (Integrable.measure_ge_lt_top hf ε_pos)

/-- If `f` is `ℝ`-valued and integrable, then for any `c < 0` the set `{x | f x < c}` has finite
measure. -/
lemma Integrable.measure_lt_lt_top {f : α → ℝ} (hf : Integrable f μ) {c : ℝ} (c_neg : c < 0) :
    μ {a : α | f a < c} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ hx ↦ (Set.mem_setOf_eq ▸ hx).le))
    (Integrable.measure_le_lt_top hf c_neg)

theorem LipschitzWith.integrable_comp_iff_of_antilipschitz {K K'} {f : α → β} {g : β → γ}
    (hg : LipschitzWith K g) (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) :
    Integrable (g ∘ f) μ ↔ Integrable f μ := by
  simp [← memℒp_one_iff_integrable, hg.memℒp_comp_iff_of_antilipschitz hg' g0]

theorem Integrable.real_toNNReal {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => ((f x).toNNReal : ℝ)) μ := by
  refine
    ⟨hf.aestronglyMeasurable.aemeasurable.real_toNNReal.coe_nnreal_real.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_le_of_lt ?_ ((hasFiniteIntegral_iff_norm _).1 hf.hasFiniteIntegral)
  apply lintegral_mono
  intro x
  simp [ENNReal.ofReal_le_ofReal, abs_le, le_abs_self]

theorem ofReal_toReal_ae_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x < ∞) :
    (fun x => ENNReal.ofReal (f x).toReal) =ᵐ[μ] f := by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, ofReal_toReal, Ne, not_false_iff]

theorem coe_toNNReal_ae_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x < ∞) :
    (fun x => ((f x).toNNReal : ℝ≥0∞)) =ᵐ[μ] f := by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, Ne, not_false_iff, coe_toNNReal]

section count

variable [MeasurableSingletonClass α] {f : α → β}

/-- A function has finite integral for the counting measure iff its norm is summable. -/
lemma hasFiniteIntegral_count_iff :
    HasFiniteIntegral f Measure.count ↔ Summable (‖f ·‖) := by
  simp only [hasFiniteIntegral_iff_nnnorm, lintegral_count, lt_top_iff_ne_top,
    ENNReal.tsum_coe_ne_top_iff_summable,  ← NNReal.summable_coe, coe_nnnorm]

/-- A function is integrable for the counting measure iff its norm is summable. -/
lemma integrable_count_iff :
    Integrable f Measure.count ↔ Summable (‖f ·‖) := by
  -- Note: this proof would be much easier if we assumed `SecondCountableTopology G`. Without
  -- this we have to justify the claim that `f` lands a.e. in a separable subset, which is true
  -- (because summable functions have countable range) but slightly tedious to check.
  rw [Integrable, hasFiniteIntegral_count_iff, and_iff_right_iff_imp]
  intro hs
  have hs' : (Function.support f).Countable := by
    simpa only [Ne, Pi.zero_apply, eq_comm, Function.support, norm_eq_zero]
      using hs.countable_support
  letI : MeasurableSpace β := borel β
  haveI : BorelSpace β := ⟨rfl⟩
  refine aestronglyMeasurable_iff_aemeasurable_separable.mpr ⟨?_, ?_⟩
  · refine (measurable_zero.measurable_of_countable_ne ?_).aemeasurable
    simpa only [Ne, Pi.zero_apply, eq_comm, Function.support] using hs'
  · refine ⟨f '' univ, ?_, ae_of_all _ fun a ↦ ⟨a, ⟨mem_univ _, rfl⟩⟩⟩
    suffices f '' univ ⊆ (f '' f.support) ∪ {0} from
      (((hs'.image f).union (countable_singleton 0)).mono this).isSeparable
    intro g hg
    rcases eq_or_ne g 0 with rfl | hg'
    · exact Or.inr (mem_singleton _)
    · obtain ⟨x, -, rfl⟩ := (mem_image ..).mp hg
      exact Or.inl ⟨x, hg', rfl⟩

end count

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integrable_withDensity_iff_integrable_coe_smul {f : α → ℝ≥0} (hf : Measurable f)
    {g : α → E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => (f x : ℝ) • g x) μ := by
  by_cases H : AEStronglyMeasurable (fun x : α => (f x : ℝ) • g x) μ
  · simp only [Integrable, aestronglyMeasurable_withDensity_iff hf, hasFiniteIntegral_iff_nnnorm, H]
    rw [lintegral_withDensity_eq_lintegral_mul₀' hf.coe_nnreal_ennreal.aemeasurable]
    · rw [iff_iff_eq]
      congr
      ext1 x
      simp only [nnnorm_smul, NNReal.nnnorm_eq, coe_mul, Pi.mul_apply]
    · rw [aemeasurable_withDensity_ennreal_iff hf]
      convert H.ennnorm using 1
      ext1 x
      simp only [nnnorm_smul, NNReal.nnnorm_eq, coe_mul]
  · simp only [Integrable, aestronglyMeasurable_withDensity_iff hf, H, false_and]

theorem integrable_withDensity_iff_integrable_smul {f : α → ℝ≥0} (hf : Measurable f) {g : α → E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => f x • g x) μ :=
  integrable_withDensity_iff_integrable_coe_smul hf

theorem integrable_withDensity_iff_integrable_smul' {f : α → ℝ≥0∞} (hf : Measurable f)
    (hflt : ∀ᵐ x ∂μ, f x < ∞) {g : α → E} :
    Integrable g (μ.withDensity f) ↔ Integrable (fun x => (f x).toReal • g x) μ := by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt),
    integrable_withDensity_iff_integrable_smul]
  · simp_rw [NNReal.smul_def, ENNReal.toReal]
  · exact hf.ennreal_toNNReal

theorem integrable_withDensity_iff_integrable_coe_smul₀ {f : α → ℝ≥0} (hf : AEMeasurable f μ)
    {g : α → E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => (f x : ℝ) • g x) μ :=
  calc
    Integrable g (μ.withDensity fun x => f x) ↔
        Integrable g (μ.withDensity fun x => (hf.mk f x : ℝ≥0)) := by
      suffices (fun x => (f x : ℝ≥0∞)) =ᵐ[μ] (fun x => (hf.mk f x : ℝ≥0)) by
        rw [withDensity_congr_ae this]
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]
    _ ↔ Integrable (fun x => ((hf.mk f x : ℝ≥0) : ℝ) • g x) μ :=
      integrable_withDensity_iff_integrable_coe_smul hf.measurable_mk
    _ ↔ Integrable (fun x => (f x : ℝ) • g x) μ := by
      apply integrable_congr
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]

theorem integrable_withDensity_iff_integrable_smul₀ {f : α → ℝ≥0} (hf : AEMeasurable f μ)
    {g : α → E} : Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => f x • g x) μ :=
  integrable_withDensity_iff_integrable_coe_smul₀ hf

end

theorem integrable_withDensity_iff {f : α → ℝ≥0∞} (hf : Measurable f) (hflt : ∀ᵐ x ∂μ, f x < ∞)
    {g : α → ℝ} : Integrable g (μ.withDensity f) ↔ Integrable (fun x => g x * (f x).toReal) μ := by
  have : (fun x => g x * (f x).toReal) = fun x => (f x).toReal • g x := by simp [mul_comm]
  rw [this]
  exact integrable_withDensity_iff_integrable_smul' hf hflt

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem memℒ1_smul_of_L1_withDensity {f : α → ℝ≥0} (f_meas : Measurable f)
    (u : Lp E 1 (μ.withDensity fun x => f x)) : Memℒp (fun x => f x • u x) 1 μ :=
  memℒp_one_iff_integrable.2 <|
    (integrable_withDensity_iff_integrable_smul f_meas).1 <| memℒp_one_iff_integrable.1 (Lp.memℒp u)

variable (μ)

/-- The map `u ↦ f • u` is an isometry between the `L^1` spaces for `μ.withDensity f` and `μ`. -/
noncomputable def withDensitySMulLI {f : α → ℝ≥0} (f_meas : Measurable f) :
    Lp E 1 (μ.withDensity fun x => f x) →ₗᵢ[ℝ] Lp E 1 μ where
  toFun u := (memℒ1_smul_of_L1_withDensity f_meas u).toLp _
  map_add' := by
    intro u v
    ext1
    filter_upwards [(memℒ1_smul_of_L1_withDensity f_meas u).coeFn_toLp,
      (memℒ1_smul_of_L1_withDensity f_meas v).coeFn_toLp,
      (memℒ1_smul_of_L1_withDensity f_meas (u + v)).coeFn_toLp,
      Lp.coeFn_add ((memℒ1_smul_of_L1_withDensity f_meas u).toLp _)
        ((memℒ1_smul_of_L1_withDensity f_meas v).toLp _),
      (ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 (Lp.coeFn_add u v)]
    intro x hu hv huv h' h''
    rw [huv, h', Pi.add_apply, hu, hv]
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, add_zero]
    · rw [h'' _, Pi.add_apply, smul_add]
      simpa only [Ne, ENNReal.coe_eq_zero] using hx
  map_smul' := by
    intro r u
    ext1
    filter_upwards [(ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 (Lp.coeFn_smul r u),
      (memℒ1_smul_of_L1_withDensity f_meas (r • u)).coeFn_toLp,
      Lp.coeFn_smul r ((memℒ1_smul_of_L1_withDensity f_meas u).toLp _),
      (memℒ1_smul_of_L1_withDensity f_meas u).coeFn_toLp]
    intro x h h' h'' h'''
    rw [RingHom.id_apply, h', h'', Pi.smul_apply, h''']
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, smul_zero]
    · rw [h _, smul_comm, Pi.smul_apply]
      simpa only [Ne, ENNReal.coe_eq_zero] using hx
  norm_map' := by
    intro u
    -- Porting note: Lean can't infer types of `AddHom.coe_mk`.
    simp only [eLpNorm, LinearMap.coe_mk,
      AddHom.coe_mk (M := Lp E 1 (μ.withDensity fun x => f x)) (N := Lp E 1 μ), Lp.norm_toLp,
      one_ne_zero, ENNReal.one_ne_top, ENNReal.one_toReal, if_false, eLpNorm', ENNReal.rpow_one,
      _root_.div_one, Lp.norm_def]
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ f_meas.coe_nnreal_ennreal
        (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top)]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [(memℒ1_smul_of_L1_withDensity f_meas u).coeFn_toLp] with x hx
    rw [hx, Pi.mul_apply]
    change (‖(f x : ℝ) • u x‖₊ : ℝ≥0∞) = (f x : ℝ≥0∞) * (‖u x‖₊ : ℝ≥0∞)
    simp only [nnnorm_smul, NNReal.nnnorm_eq, ENNReal.coe_mul]

@[simp]
theorem withDensitySMulLI_apply {f : α → ℝ≥0} (f_meas : Measurable f)
    (u : Lp E 1 (μ.withDensity fun x => f x)) :
    withDensitySMulLI μ (E := E) f_meas u =
      (memℒ1_smul_of_L1_withDensity f_meas u).toLp fun x => f x • u x :=
  rfl

end

section ENNReal

theorem mem_ℒ1_toReal_of_lintegral_ne_top {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) : Memℒp (fun x ↦ (f x).toReal) 1 μ := by
  rw [Memℒp, eLpNorm_one_eq_lintegral_nnnorm]
  exact ⟨(AEMeasurable.ennreal_toReal hfm).aestronglyMeasurable,
    hasFiniteIntegral_toReal_of_lintegral_ne_top hfi⟩

theorem integrable_toReal_of_lintegral_ne_top {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) : Integrable (fun x ↦ (f x).toReal) μ :=
  memℒp_one_iff_integrable.1 <| mem_ℒ1_toReal_of_lintegral_ne_top hfm hfi

lemma integrable_toReal_iff {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    Integrable (fun x ↦ (f x).toReal) μ ↔ ∫⁻ x, f x ∂μ ≠ ∞ := by
  rw [Integrable, hasFiniteIntegral_toReal_iff hf_ne_top]
  simp only [hf.ennreal_toReal.aestronglyMeasurable, ne_eq, true_and]

lemma lintegral_ofReal_ne_top_iff_integrable {f : α → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) :
    ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≠ ∞ ↔ Integrable f μ := by
  rw [Integrable, hasFiniteIntegral_iff_ofReal hf]
  simp [hfm]

end ENNReal

section PosPart

/-! ### Lemmas used for defining the positive part of an `L¹` function -/


theorem Integrable.pos_part {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun a => max (f a) 0) μ :=
  ⟨(hf.aestronglyMeasurable.aemeasurable.max aemeasurable_const).aestronglyMeasurable,
    hf.hasFiniteIntegral.max_zero⟩

theorem Integrable.neg_part {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun a => max (-f a) 0) μ :=
  hf.neg.pos_part

end PosPart

section BoundedSMul

variable {𝕜 : Type*}

theorem Integrable.smul [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 β] [BoundedSMul 𝕜 β] (c : 𝕜)
    {f : α → β} (hf : Integrable f μ) : Integrable (c • f) μ :=
  ⟨hf.aestronglyMeasurable.const_smul c, hf.hasFiniteIntegral.smul c⟩

theorem _root_.IsUnit.integrable_smul_iff [NormedRing 𝕜] [Module 𝕜 β] [BoundedSMul 𝕜 β] {c : 𝕜}
    (hc : IsUnit c) (f : α → β) : Integrable (c • f) μ ↔ Integrable f μ :=
  and_congr hc.aestronglyMeasurable_const_smul_iff (hasFiniteIntegral_smul_iff hc f)

theorem integrable_smul_iff [NormedDivisionRing 𝕜] [Module 𝕜 β] [BoundedSMul 𝕜 β] {c : 𝕜}
    (hc : c ≠ 0) (f : α → β) : Integrable (c • f) μ ↔ Integrable f μ :=
  (IsUnit.mk0 _ hc).integrable_smul_iff f

variable [NormedRing 𝕜] [Module 𝕜 β] [BoundedSMul 𝕜 β]

theorem Integrable.smul_of_top_right {f : α → β} {φ : α → 𝕜} (hf : Integrable f μ)
    (hφ : Memℒp φ ∞ μ) : Integrable (φ • f) μ := by
  rw [← memℒp_one_iff_integrable] at hf ⊢
  exact Memℒp.smul_of_top_right hf hφ

theorem Integrable.smul_of_top_left {f : α → β} {φ : α → 𝕜} (hφ : Integrable φ μ)
    (hf : Memℒp f ∞ μ) : Integrable (φ • f) μ := by
  rw [← memℒp_one_iff_integrable] at hφ ⊢
  exact Memℒp.smul_of_top_left hf hφ

theorem Integrable.smul_const {f : α → 𝕜} (hf : Integrable f μ) (c : β) :
    Integrable (fun x => f x • c) μ :=
  hf.smul_of_top_left (memℒp_top_const c)

end BoundedSMul

section NormedSpaceOverCompleteField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem integrable_smul_const {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
    Integrable (fun x => f x • c) μ ↔ Integrable f μ := by
  simp_rw [Integrable, aestronglyMeasurable_smul_const_iff (f := f) hc, and_congr_right_iff,
    hasFiniteIntegral_iff_nnnorm, nnnorm_smul, ENNReal.coe_mul]
  intro _; rw [lintegral_mul_const' _ _ ENNReal.coe_ne_top, ENNReal.mul_lt_top_iff]
  have : ∀ x : ℝ≥0∞, x = 0 → x < ∞ := by simp
  simp [hc, or_iff_left_of_imp (this _)]

end NormedSpaceOverCompleteField

section NormedRing

variable {𝕜 : Type*} [NormedRing 𝕜] {f : α → 𝕜}

theorem Integrable.const_mul {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (fun x => c * f x) μ :=
  h.smul c

theorem Integrable.const_mul' {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable ((fun _ : α => c) * f) μ :=
  Integrable.const_mul h c

theorem Integrable.mul_const {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (fun x => f x * c) μ :=
  h.smul (MulOpposite.op c)

theorem Integrable.mul_const' {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (f * fun _ : α => c) μ :=
  Integrable.mul_const h c

theorem integrable_const_mul_iff {c : 𝕜} (hc : IsUnit c) (f : α → 𝕜) :
    Integrable (fun x => c * f x) μ ↔ Integrable f μ :=
  hc.integrable_smul_iff f

theorem integrable_mul_const_iff {c : 𝕜} (hc : IsUnit c) (f : α → 𝕜) :
    Integrable (fun x => f x * c) μ ↔ Integrable f μ :=
  hc.op.integrable_smul_iff f

theorem Integrable.bdd_mul' {f g : α → 𝕜} {c : ℝ} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    Integrable (fun x => f x * g x) μ := by
  refine Integrable.mono' (hg.norm.smul c) (hf.mul hg.1) ?_
  filter_upwards [hf_bound] with x hx
  rw [Pi.smul_apply, smul_eq_mul]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

theorem Integrable.mul_of_top_right {f : α → 𝕜} {φ : α → 𝕜} (hf : Integrable f μ)
    (hφ : Memℒp φ ∞ μ) : Integrable (φ * f) μ :=
  hf.smul_of_top_right hφ

theorem Integrable.mul_of_top_left {f : α → 𝕜} {φ : α → 𝕜} (hφ : Integrable φ μ)
    (hf : Memℒp f ∞ μ) : Integrable (φ * f) μ :=
  hφ.smul_of_top_left hf

end NormedRing

section NormedDivisionRing

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] {f : α → 𝕜}

theorem Integrable.div_const {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (fun x => f x / c) μ := by simp_rw [div_eq_mul_inv, h.mul_const]

end NormedDivisionRing

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜}

theorem Integrable.ofReal {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => (f x : 𝕜)) μ := by
  rw [← memℒp_one_iff_integrable] at hf ⊢
  exact hf.ofReal

theorem Integrable.re_im_iff :
    Integrable (fun x => RCLike.re (f x)) μ ∧ Integrable (fun x => RCLike.im (f x)) μ ↔
      Integrable f μ := by
  simp_rw [← memℒp_one_iff_integrable]
  exact memℒp_re_im_iff

theorem Integrable.re (hf : Integrable f μ) : Integrable (fun x => RCLike.re (f x)) μ := by
  rw [← memℒp_one_iff_integrable] at hf ⊢
  exact hf.re

theorem Integrable.im (hf : Integrable f μ) : Integrable (fun x => RCLike.im (f x)) μ := by
  rw [← memℒp_one_iff_integrable] at hf ⊢
  exact hf.im

lemma Integrable.iff_ofReal {f : α → ℝ} : Integrable f μ ↔ Integrable (fun x ↦ (f x : ℂ)) μ :=
  ⟨fun hf ↦ hf.ofReal, fun hf ↦ hf.re⟩

end RCLike

section Trim

variable {H : Type*} [NormedAddCommGroup H] {m0 : MeasurableSpace α} {μ' : Measure α} {f : α → H}

theorem Integrable.trim (hm : m ≤ m0) (hf_int : Integrable f μ') (hf : StronglyMeasurable[m] f) :
    Integrable f (μ'.trim hm) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_trim hm _]
  · exact hf_int.2
  · exact @StronglyMeasurable.ennnorm _ m _ _ f hf

theorem integrable_of_integrable_trim (hm : m ≤ m0) (hf_int : Integrable f (μ'.trim hm)) :
    Integrable f μ' := by
  obtain ⟨hf_meas_ae, hf⟩ := hf_int
  refine ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim hm hf_meas_ae, ?_⟩
  rw [HasFiniteIntegral] at hf ⊢
  rwa [lintegral_trim_ae hm _] at hf
  exact AEStronglyMeasurable.ennnorm hf_meas_ae

end Trim

section SigmaFinite

variable {E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E]

theorem integrable_of_forall_fin_meas_le' {μ : Measure α} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (C : ℝ≥0∞) (hC : C < ∞) {f : α → E} (hf_meas : AEStronglyMeasurable f μ)
    (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → (∫⁻ x in s, ‖f x‖₊ ∂μ) ≤ C) : Integrable f μ :=
  ⟨hf_meas, (lintegral_le_of_forall_fin_meas_trim_le hm C hf).trans_lt hC⟩

theorem integrable_of_forall_fin_meas_le [SigmaFinite μ] (C : ℝ≥0∞) (hC : C < ∞) {f : α → E}
    (hf_meas : AEStronglyMeasurable f μ)
    (hf : ∀ s : Set α, MeasurableSet[m] s → μ s ≠ ∞ → (∫⁻ x in s, ‖f x‖₊ ∂μ) ≤ C) :
    Integrable f μ :=
  have : SigmaFinite (μ.trim le_rfl) := by rwa [@trim_eq_self _ m]
  integrable_of_forall_fin_meas_le' le_rfl C hC hf_meas hf

end SigmaFinite

/-! ### The predicate `Integrable` on measurable functions modulo a.e.-equality -/


namespace AEEqFun

section

/-- A class of almost everywhere equal functions is `Integrable` if its function representative
is integrable. -/
def Integrable (f : α →ₘ[μ] β) : Prop :=
  MeasureTheory.Integrable f μ

theorem integrable_mk {f : α → β} (hf : AEStronglyMeasurable f μ) :
    Integrable (mk f hf : α →ₘ[μ] β) ↔ MeasureTheory.Integrable f μ := by
  simp only [Integrable]
  apply integrable_congr
  exact coeFn_mk f hf

theorem integrable_coeFn {f : α →ₘ[μ] β} : MeasureTheory.Integrable f μ ↔ Integrable f := by
  rw [← integrable_mk, mk_coeFn]

theorem integrable_zero : Integrable (0 : α →ₘ[μ] β) :=
  (MeasureTheory.integrable_zero α β μ).congr (coeFn_mk _ _).symm

end

section

theorem Integrable.neg {f : α →ₘ[μ] β} : Integrable f → Integrable (-f) :=
  induction_on f fun _f hfm hfi => (integrable_mk _).2 ((integrable_mk hfm).1 hfi).neg

section

theorem integrable_iff_mem_L1 {f : α →ₘ[μ] β} : Integrable f ↔ f ∈ (α →₁[μ] β) := by
  rw [← integrable_coeFn, ← memℒp_one_iff_integrable, Lp.mem_Lp_iff_memℒp]

theorem Integrable.add {f g : α →ₘ[μ] β} : Integrable f → Integrable g → Integrable (f + g) := by
  refine induction_on₂ f g fun f hf g hg hfi hgi => ?_
  simp only [integrable_mk, mk_add_mk] at hfi hgi ⊢
  exact hfi.add hgi

theorem Integrable.sub {f g : α →ₘ[μ] β} (hf : Integrable f) (hg : Integrable g) :
    Integrable (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

end

section BoundedSMul

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 β] [BoundedSMul 𝕜 β]

theorem Integrable.smul {c : 𝕜} {f : α →ₘ[μ] β} : Integrable f → Integrable (c • f) :=
  induction_on f fun _f hfm hfi => (integrable_mk _).2 <|
    by simpa using ((integrable_mk hfm).1 hfi).smul c

end BoundedSMul

end

end AEEqFun

namespace L1


theorem integrable_coeFn (f : α →₁[μ] β) : Integrable f μ := by
  rw [← memℒp_one_iff_integrable]
  exact Lp.memℒp f

theorem hasFiniteIntegral_coeFn (f : α →₁[μ] β) : HasFiniteIntegral f μ :=
  (integrable_coeFn f).hasFiniteIntegral

theorem stronglyMeasurable_coeFn (f : α →₁[μ] β) : StronglyMeasurable f :=
  Lp.stronglyMeasurable f

theorem measurable_coeFn [MeasurableSpace β] [BorelSpace β] (f : α →₁[μ] β) : Measurable f :=
  (Lp.stronglyMeasurable f).measurable

theorem aestronglyMeasurable_coeFn (f : α →₁[μ] β) : AEStronglyMeasurable f μ :=
  Lp.aestronglyMeasurable f

theorem aemeasurable_coeFn [MeasurableSpace β] [BorelSpace β] (f : α →₁[μ] β) : AEMeasurable f μ :=
  (Lp.stronglyMeasurable f).measurable.aemeasurable

theorem edist_def (f g : α →₁[μ] β) : edist f g = ∫⁻ a, edist (f a) (g a) ∂μ := by
  simp only [Lp.edist_def, eLpNorm, one_ne_zero, eLpNorm'_eq_lintegral_nnnorm, Pi.sub_apply,
    one_toReal, ENNReal.rpow_one, ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_coe_nnnorm_sub]

theorem dist_def (f g : α →₁[μ] β) : dist f g = (∫⁻ a, edist (f a) (g a) ∂μ).toReal := by
  simp_rw [dist_edist, edist_def]

theorem norm_def (f : α →₁[μ] β) : ‖f‖ = (∫⁻ a, ‖f a‖₊ ∂μ).toReal := by
  simp [Lp.norm_def, eLpNorm, eLpNorm'_eq_lintegral_nnnorm]

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `norm_def` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
theorem norm_sub_eq_lintegral (f g : α →₁[μ] β) :
    ‖f - g‖ = (∫⁻ x, (‖f x - g x‖₊ : ℝ≥0∞) ∂μ).toReal := by
  rw [norm_def]
  congr 1
  rw [lintegral_congr_ae]
  filter_upwards [Lp.coeFn_sub f g] with _ ha
  simp only [ha, Pi.sub_apply]

theorem ofReal_norm_eq_lintegral (f : α →₁[μ] β) :
    ENNReal.ofReal ‖f‖ = ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ∂μ := by
  rw [norm_def, ENNReal.ofReal_toReal]
  exact ne_of_lt (hasFiniteIntegral_coeFn f)

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `ofReal_norm_eq_lintegral` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
theorem ofReal_norm_sub_eq_lintegral (f g : α →₁[μ] β) :
    ENNReal.ofReal ‖f - g‖ = ∫⁻ x, (‖f x - g x‖₊ : ℝ≥0∞) ∂μ := by
  simp_rw [ofReal_norm_eq_lintegral, ← edist_eq_coe_nnnorm]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with _ ha
  simp only [ha, Pi.sub_apply]

end L1

namespace Integrable


/-- Construct the equivalence class `[f]` of an integrable function `f`, as a member of the
space `L1 β 1 μ`. -/
def toL1 (f : α → β) (hf : Integrable f μ) : α →₁[μ] β :=
  (memℒp_one_iff_integrable.2 hf).toLp f

@[simp]
theorem toL1_coeFn (f : α →₁[μ] β) (hf : Integrable f μ) : hf.toL1 f = f := by
  simp [Integrable.toL1]

theorem coeFn_toL1 {f : α → β} (hf : Integrable f μ) : hf.toL1 f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk _ _

@[simp]
theorem toL1_zero (h : Integrable (0 : α → β) μ) : h.toL1 0 = 0 :=
  rfl

@[simp]
theorem toL1_eq_mk (f : α → β) (hf : Integrable f μ) :
    (hf.toL1 f : α →ₘ[μ] β) = AEEqFun.mk f hf.aestronglyMeasurable :=
  rfl

@[simp]
theorem toL1_eq_toL1_iff (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 f hf = toL1 g hg ↔ f =ᵐ[μ] g :=
  Memℒp.toLp_eq_toLp_iff _ _

theorem toL1_add (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 (f + g) (hf.add hg) = toL1 f hf + toL1 g hg :=
  rfl

theorem toL1_neg (f : α → β) (hf : Integrable f μ) : toL1 (-f) (Integrable.neg hf) = -toL1 f hf :=
  rfl

theorem toL1_sub (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 (f - g) (hf.sub hg) = toL1 f hf - toL1 g hg :=
  rfl

theorem norm_toL1 (f : α → β) (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = ENNReal.toReal (∫⁻ a, edist (f a) 0 ∂μ) := by
  simp only [toL1, Lp.norm_toLp, eLpNorm, one_ne_zero, eLpNorm'_eq_lintegral_nnnorm, one_toReal,
    ENNReal.rpow_one, ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_coe_nnnorm]

theorem nnnorm_toL1 {f : α → β} (hf : Integrable f μ) :
    (‖hf.toL1 f‖₊ : ℝ≥0∞) = ∫⁻ a, ‖f a‖₊ ∂μ := by
  simpa [Integrable.toL1, eLpNorm, eLpNorm'] using ENNReal.coe_toNNReal hf.2.ne

theorem norm_toL1_eq_lintegral_norm (f : α → β) (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) := by
  rw [norm_toL1, lintegral_norm_eq_lintegral_edist]

@[simp]
theorem edist_toL1_toL1 (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    edist (hf.toL1 f) (hg.toL1 g) = ∫⁻ a, edist (f a) (g a) ∂μ := by
  simp only [toL1, Lp.edist_toLp_toLp, eLpNorm, one_ne_zero, eLpNorm'_eq_lintegral_nnnorm,
    Pi.sub_apply, one_toReal, ENNReal.rpow_one, ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_coe_nnnorm_sub]

theorem edist_toL1_zero (f : α → β) (hf : Integrable f μ) :
    edist (hf.toL1 f) 0 = ∫⁻ a, edist (f a) 0 ∂μ := by
  simp only [edist_zero_right, Lp.nnnorm_coe_ennreal, toL1_eq_mk, eLpNorm_aeeqFun]
  apply eLpNorm_one_eq_lintegral_nnnorm

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 β] [BoundedSMul 𝕜 β]

theorem toL1_smul (f : α → β) (hf : Integrable f μ) (k : 𝕜) :
    toL1 (fun a => k • f a) (hf.smul k) = k • toL1 f hf :=
  rfl

theorem toL1_smul' (f : α → β) (hf : Integrable f μ) (k : 𝕜) :
    toL1 (k • f) (hf.smul k) = k • toL1 f hf :=
  rfl

end Integrable

section restrict

variable {E : Type*} [NormedAddCommGroup E] {f : α → E}

lemma HasFiniteIntegral.restrict (h : HasFiniteIntegral f μ) {s : Set α} :
    HasFiniteIntegral f (μ.restrict s) := by
  refine lt_of_le_of_lt ?_ h
  convert lintegral_mono_set (μ := μ) (s := s) (t := univ) (f := fun x ↦ ↑‖f x‖₊) (subset_univ s)
  exact Measure.restrict_univ.symm

/-- One should usually use `MeasureTheory.Integrable.IntegrableOn` instead. -/
lemma Integrable.restrict (hf : Integrable f μ) {s : Set α} : Integrable f (μ.restrict s) :=
  hf.mono_measure Measure.restrict_le_self

end restrict

end MeasureTheory

section ContinuousLinearMap

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedSpace 𝕜 E] {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

theorem ContinuousLinearMap.integrable_comp {φ : α → H} (L : H →L[𝕜] E) (φ_int : Integrable φ μ) :
    Integrable (fun a : α => L (φ a)) μ :=
  ((Integrable.norm φ_int).const_mul ‖L‖).mono'
    (L.continuous.comp_aestronglyMeasurable φ_int.aestronglyMeasurable)
    (Eventually.of_forall fun a => L.le_opNorm (φ a))

@[simp]
theorem ContinuousLinearEquiv.integrable_comp_iff {φ : α → H} (L : H ≃L[𝕜] E) :
    Integrable (fun a : α ↦ L (φ a)) μ ↔ Integrable φ μ :=
  ⟨fun h ↦ by simpa using ContinuousLinearMap.integrable_comp (L.symm : E →L[𝕜] H) h,
  fun h ↦ ContinuousLinearMap.integrable_comp (L : H →L[𝕜] E) h⟩

@[simp]
theorem LinearIsometryEquiv.integrable_comp_iff {φ : α → H} (L : H ≃ₗᵢ[𝕜] E) :
    Integrable (fun a : α ↦ L (φ a)) μ ↔ Integrable φ μ :=
  ContinuousLinearEquiv.integrable_comp_iff (L : H ≃L[𝕜] E)

theorem MeasureTheory.Integrable.apply_continuousLinearMap {φ : α → H →L[𝕜] E}
    (φ_int : Integrable φ μ) (v : H) : Integrable (fun a => φ a v) μ :=
  (ContinuousLinearMap.apply 𝕜 _ v).integrable_comp φ_int

end ContinuousLinearMap

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma Integrable.fst {f : α → E × F} (hf : Integrable f μ) : Integrable (fun x ↦ (f x).1) μ :=
  (ContinuousLinearMap.fst ℝ E F).integrable_comp hf

lemma Integrable.snd {f : α → E × F} (hf : Integrable f μ) : Integrable (fun x ↦ (f x).2) μ :=
  (ContinuousLinearMap.snd ℝ E F).integrable_comp hf

lemma integrable_prod {f : α → E × F} :
    Integrable f μ ↔ Integrable (fun x ↦ (f x).1) μ ∧ Integrable (fun x ↦ (f x).2) μ :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prod_mk h.2⟩

end MeasureTheory

set_option linter.style.longFile 1700
