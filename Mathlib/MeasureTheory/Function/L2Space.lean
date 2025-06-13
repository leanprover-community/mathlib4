/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # `L^2` space

If `E` is an inner product space over `𝕜` (`ℝ` or `ℂ`), then `Lp E 2 μ`
(defined in `Mathlib/MeasureTheory/Function/LpSpace.lean`)
is also an inner product space, with inner product defined as `inner f g := ∫ a, ⟪f a, g a⟫ ∂μ`.

### Main results

* `mem_L1_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `fun x ↦ ⟪f x, g x⟫`
  belongs to `Lp 𝕜 1 μ`.
* `integrable_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product
  `fun x ↦ ⟪f x, g x⟫` is integrable.
* `L2.innerProductSpace` : `Lp E 2 μ` is an inner product space.
-/

noncomputable section

open TopologicalSpace MeasureTheory MeasureTheory.Lp Filter

open scoped NNReal ENNReal MeasureTheory

namespace MeasureTheory

section

variable {α F : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup F]

theorem MemLp.integrable_sq {f : α → ℝ} (h : MemLp f 2 μ) : Integrable (fun x => f x ^ 2) μ := by
  simpa [← memLp_one_iff_integrable] using h.norm_rpow two_ne_zero ENNReal.ofNat_ne_top

@[deprecated (since := "2025-02-21")]
alias Memℒp.integrable_sq := MemLp.integrable_sq

theorem memLp_two_iff_integrable_sq_norm {f : α → F} (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ Integrable (fun x => ‖f x‖ ^ 2) μ := by
  rw [← memLp_one_iff_integrable]
  convert (memLp_norm_rpow_iff hf two_ne_zero ENNReal.ofNat_ne_top).symm
  · simp
  · rw [div_eq_mul_inv, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

@[deprecated (since := "2025-02-21")]
alias memℒp_two_iff_integrable_sq_norm := memLp_two_iff_integrable_sq_norm

theorem memLp_two_iff_integrable_sq {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ Integrable (fun x => f x ^ 2) μ := by
  convert memLp_two_iff_integrable_sq_norm hf using 3
  simp

@[deprecated (since := "2025-02-21")]
alias memℒp_two_iff_integrable_sq := memLp_two_iff_integrable_sq

end

section InnerProductSpace

variable {α : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
variable {E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem MemLp.const_inner (c : E) {f : α → E} (hf : MemLp f p μ) : MemLp (fun a => ⟪c, f a⟫) p μ :=
  hf.of_le_mul (AEStronglyMeasurable.inner aestronglyMeasurable_const hf.1)
    (Eventually.of_forall fun _ => norm_inner_le_norm _ _)

@[deprecated (since := "2025-02-21")]
alias Memℒp.const_inner := MemLp.const_inner

theorem MemLp.inner_const {f : α → E} (hf : MemLp f p μ) (c : E) : MemLp (fun a => ⟪f a, c⟫) p μ :=
  hf.of_le_mul (c := ‖c‖) (AEStronglyMeasurable.inner hf.1 aestronglyMeasurable_const)
    (Eventually.of_forall fun x => by rw [mul_comm]; exact norm_inner_le_norm _ _)

@[deprecated (since := "2025-02-21")]
alias Memℒp.inner_const := MemLp.inner_const

variable {f : α → E}

@[fun_prop]
theorem Integrable.const_inner (c : E) (hf : Integrable f μ) :
    Integrable (fun x => ⟪c, f x⟫) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢; exact hf.const_inner c

@[fun_prop]
theorem Integrable.inner_const (hf : Integrable f μ) (c : E) :
    Integrable (fun x => ⟪f x, c⟫) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢; exact hf.inner_const c

variable [CompleteSpace E] [NormedSpace ℝ E]

theorem _root_.integral_inner {f : α → E} (hf : Integrable f μ) (c : E) :
    ∫ x, ⟪c, f x⟫ ∂μ = ⟪c, ∫ x, f x ∂μ⟫ :=
  ((innerSL 𝕜 c).restrictScalars ℝ).integral_comp_comm hf

variable (𝕜)

theorem _root_.integral_eq_zero_of_forall_integral_inner_eq_zero (f : α → E) (hf : Integrable f μ)
    (hf_int : ∀ c : E, ∫ x, ⟪c, f x⟫ ∂μ = 0) : ∫ x, f x ∂μ = 0 := by
  specialize hf_int (∫ x, f x ∂μ); rwa [integral_inner hf, inner_self_eq_zero] at hf_int

end InnerProductSpace

namespace L2

variable {α E F 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem eLpNorm_rpow_two_norm_lt_top (f : Lp F 2 μ) :
    eLpNorm (fun x => ‖f x‖ ^ (2 : ℝ)) 1 μ < ∞ := by
  have h_two : ENNReal.ofReal (2 : ℝ) = 2 := by simp [zero_le_one]
  rw [eLpNorm_norm_rpow f zero_lt_two, one_mul, h_two]
  exact ENNReal.rpow_lt_top_of_nonneg zero_le_two (Lp.eLpNorm_ne_top f)

theorem eLpNorm_inner_lt_top (f g : α →₂[μ] E) : eLpNorm (fun x : α => ⟪f x, g x⟫) 1 μ < ∞ := by
  have h : ∀ x, ‖⟪f x, g x⟫‖ ≤ ‖‖f x‖ ^ (2 : ℝ) + ‖g x‖ ^ (2 : ℝ)‖ := by
    intro x
    rw [← @Nat.cast_two ℝ, Real.rpow_natCast, Real.rpow_natCast]
    calc
      ‖⟪f x, g x⟫‖ ≤ ‖f x‖ * ‖g x‖ := norm_inner_le_norm _ _
      _ ≤ 2 * ‖f x‖ * ‖g x‖ :=
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (norm_nonneg _) one_le_two)
          (norm_nonneg _))
      -- TODO(kmill): the type ascription is getting around an elaboration error
      _ ≤ ‖(‖f x‖ ^ 2 + ‖g x‖ ^ 2 : ℝ)‖ := (two_mul_le_add_sq _ _).trans (le_abs_self _)
  refine (eLpNorm_mono_ae (ae_of_all _ h)).trans_lt ((eLpNorm_add_le ?_ ?_ le_rfl).trans_lt ?_)
  · exact ((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const _).aestronglyMeasurable
  · exact ((Lp.aestronglyMeasurable g).norm.aemeasurable.pow_const _).aestronglyMeasurable
  rw [ENNReal.add_lt_top]
  exact ⟨eLpNorm_rpow_two_norm_lt_top f, eLpNorm_rpow_two_norm_lt_top g⟩

section InnerProductSpace

open scoped ComplexConjugate

instance : Inner 𝕜 (α →₂[μ] E) :=
  ⟨fun f g => ∫ a, ⟪f a, g a⟫ ∂μ⟩

theorem inner_def (f g : α →₂[μ] E) : ⟪f, g⟫ = ∫ a : α, ⟪f a, g a⟫ ∂μ :=
  rfl

theorem integral_inner_eq_sq_eLpNorm (f : α →₂[μ] E) :
    ∫ a, ⟪f a, f a⟫ ∂μ = ENNReal.toReal (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂μ) := by
  simp_rw [inner_self_eq_norm_sq_to_K]
  norm_cast
  rw [integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _
  · exact ((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const _).aestronglyMeasurable
  congr
  ext1 x
  have h_two : (2 : ℝ) = ((2 : ℕ) : ℝ) := by simp
  rw [← Real.rpow_natCast _ 2, ← h_two, ←
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two, ofReal_norm_eq_enorm]
  norm_cast

private theorem norm_sq_eq_re_inner (f : α →₂[μ] E) : ‖f‖ ^ 2 = RCLike.re ⟪f, f⟫ := by
  have h_two : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [inner_def, integral_inner_eq_sq_eLpNorm, norm_def, ← ENNReal.toReal_pow, RCLike.ofReal_re,
    ENNReal.toReal_eq_toReal (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)) _]
  · rw [← ENNReal.rpow_natCast, eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top, eLpNorm', ←
      ENNReal.rpow_mul, one_div, h_two]
    simp [enorm_eq_nnnorm]
  · refine (lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top zero_lt_two (ε := E) ?_).ne
    rw [← h_two, ← eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top]
    exact Lp.eLpNorm_lt_top f

@[deprecated (since := "2025-04-22")] alias norm_sq_eq_inner' := norm_sq_eq_re_inner

theorem mem_L1_inner (f g : α →₂[μ] E) :
    AEEqFun.mk (fun x => ⟪f x, g x⟫)
        ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable g)) ∈
      Lp 𝕜 1 μ := by
  simp_rw [mem_Lp_iff_eLpNorm_lt_top, eLpNorm_aeeqFun]; exact eLpNorm_inner_lt_top f g

theorem integrable_inner (f g : α →₂[μ] E) : Integrable (fun x : α => ⟪f x, g x⟫) μ :=
  (integrable_congr
        (AEEqFun.coeFn_mk (fun x => ⟪f x, g x⟫)
          ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable g)))).mp
    (AEEqFun.integrable_iff_mem_L1.mpr (mem_L1_inner f g))

private theorem add_left' (f f' g : α →₂[μ] E) : ⟪f + f', g⟫ = ⟪f, g⟫ + ⟪f', g⟫ := by
  simp_rw [inner_def, ← integral_add (integrable_inner (𝕜 := 𝕜) f g) (integrable_inner f' g),
    ← inner_add_left]
  refine integral_congr_ae ((coeFn_add f f').mono fun x hx => ?_)
  simp only [hx, Pi.add_apply]

private theorem smul_left' (f g : α →₂[μ] E) (r : 𝕜) : ⟪r • f, g⟫ = conj r * ⟪f, g⟫ := by
  rw [inner_def, inner_def, ← smul_eq_mul, ← integral_smul]
  refine integral_congr_ae ((coeFn_smul r f).mono fun x hx => ?_)
  simp only
  rw [smul_eq_mul, ← inner_smul_left, hx, Pi.smul_apply]

instance innerProductSpace : InnerProductSpace 𝕜 (α →₂[μ] E) where
  norm_sq_eq_re_inner := norm_sq_eq_re_inner
  conj_inner_symm _ _ := by simp_rw [inner_def, ← integral_conj, inner_conj_symm]
  add_left := add_left'
  smul_left := smul_left'

end InnerProductSpace

section IndicatorConstLp

variable (𝕜) {s : Set α}

/-- The inner product in `L2` of the indicator of a set `indicatorConstLp 2 hs hμs c` and `f` is
equal to the integral of the inner product over `s`: `∫ x in s, ⟪c, f x⟫ ∂μ`. -/
theorem inner_indicatorConstLp_eq_setIntegral_inner (f : Lp E 2 μ) (hs : MeasurableSet s) (c : E)
    (hμs : μ s ≠ ∞) : (⟪indicatorConstLp 2 hs hμs c, f⟫ : 𝕜) = ∫ x in s, ⟪c, f x⟫ ∂μ := by
  rw [inner_def, ← integral_add_compl hs (L2.integrable_inner _ f)]
  have h_left : (∫ x in s, ⟪(indicatorConstLp 2 hs hμs c) x, f x⟫ ∂μ) = ∫ x in s, ⟪c, f x⟫ ∂μ := by
    suffices h_ae_eq : ∀ᵐ x ∂μ, x ∈ s → ⟪indicatorConstLp 2 hs hμs c x, f x⟫ = ⟪c, f x⟫ from
      setIntegral_congr_ae hs h_ae_eq
    have h_indicator : ∀ᵐ x : α ∂μ, x ∈ s → indicatorConstLp 2 hs hμs c x = c :=
      indicatorConstLp_coeFn_mem
    refine h_indicator.mono fun x hx hxs => ?_
    congr
    exact hx hxs
  have h_right : (∫ x in sᶜ, ⟪(indicatorConstLp 2 hs hμs c) x, f x⟫ ∂μ) = 0 := by
    suffices h_ae_eq : ∀ᵐ x ∂μ, x ∉ s → ⟪indicatorConstLp 2 hs hμs c x, f x⟫ = 0 by
      simp_rw [← Set.mem_compl_iff] at h_ae_eq
      suffices h_int_zero :
          (∫ x in sᶜ, ⟪indicatorConstLp 2 hs hμs c x, f x⟫ ∂μ) = ∫ _ in sᶜ, 0 ∂μ by
        rw [h_int_zero]
        simp
      exact setIntegral_congr_ae hs.compl h_ae_eq
    have h_indicator : ∀ᵐ x : α ∂μ, x ∉ s → indicatorConstLp 2 hs hμs c x = 0 :=
      indicatorConstLp_coeFn_notMem
    refine h_indicator.mono fun x hx hxs => ?_
    rw [hx hxs]
    exact inner_zero_left _
  rw [h_left, h_right, add_zero]

/-- The inner product in `L2` of the indicator of a set `indicatorConstLp 2 hs hμs c` and `f` is
equal to the inner product of the constant `c` and the integral of `f` over `s`. -/
theorem inner_indicatorConstLp_eq_inner_setIntegral [CompleteSpace E] [NormedSpace ℝ E]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) (f : Lp E 2 μ) :
    (⟪indicatorConstLp 2 hs hμs c, f⟫ : 𝕜) = ⟪c, ∫ x in s, f x ∂μ⟫ := by
  rw [← integral_inner (integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs),
    L2.inner_indicatorConstLp_eq_setIntegral_inner]

variable {𝕜}

/-- The inner product in `L2` of the indicator of a set `indicatorConstLp 2 hs hμs (1 : 𝕜)` and
a real or complex function `f` is equal to the integral of `f` over `s`. -/
theorem inner_indicatorConstLp_one (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (f : Lp 𝕜 2 μ) :
    ⟪indicatorConstLp 2 hs hμs (1 : 𝕜), f⟫ = ∫ x in s, f x ∂μ := by
  rw [L2.inner_indicatorConstLp_eq_inner_setIntegral 𝕜 hs hμs (1 : 𝕜) f]; simp

end IndicatorConstLp

end L2

section InnerContinuous

variable {α 𝕜 : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [RCLike 𝕜]
variable (μ : Measure α) [IsFiniteMeasure μ]

open scoped BoundedContinuousFunction ComplexConjugate

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- For bounded continuous functions `f`, `g` on a finite-measure topological space `α`, the L^2
inner product is the integral of their pointwise inner product. -/
theorem BoundedContinuousFunction.inner_toLp (f g : α →ᵇ 𝕜) :
    ⟪BoundedContinuousFunction.toLp 2 μ 𝕜 f,
        BoundedContinuousFunction.toLp 2 μ 𝕜 g⟫ =
      ∫ x, g x * conj (f x) ∂μ := by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp 2 μ 𝕜
  have hg_ae := g.coeFn_toLp 2 μ 𝕜
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf, hg]
  simp

variable [CompactSpace α]

/-- For continuous functions `f`, `g` on a compact, finite-measure topological space `α`, the L^2
inner product is the integral of their pointwise inner product. -/
theorem ContinuousMap.inner_toLp (f g : C(α, 𝕜)) :
    ⟪ContinuousMap.toLp 2 μ 𝕜 f, ContinuousMap.toLp 2 μ 𝕜 g⟫ =
      ∫ x, g x * conj (f x) ∂μ := by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp (p := 2) (𝕜 := 𝕜) μ
  have hg_ae := g.coeFn_toLp (p := 2) (𝕜 := 𝕜) μ
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf, hg]
  simp

end InnerContinuous

end MeasureTheory
