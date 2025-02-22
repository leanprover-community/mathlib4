/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzDense
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformExtra
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Fourier transform on Schwartz functions

This file constructs the Fourier transform as a continuous linear map acting on Schwartz
functions, in `fourierTransformCLM`. It is also given as a continuous linear equiv, in
`fourierTransformCLE`.
-/

open Real MeasureTheory Filter
open scoped FourierTransform ENNReal InnerProductSpace SchwartzMap


namespace SchwartzMap

open MeasureTheory.Measure

variable
  (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform on a real inner product space, as a continuous linear map on the
Schwartz space. -/
noncomputable def fourierTransformCLM : 𝓢(V, E) →L[𝕜] 𝓢(V, E) := by
  refine mkCLM (fun (f : V → E) ↦ 𝓕 f) ?_ ?_ ?_ ?_
  · intro f g x
    simp only [fourierIntegral_eq, Pi.add_apply, smul_add]
    rw [integral_add]
    · exact (fourierIntegral_convergent_iff _).2 f.integrable
    · exact (fourierIntegral_convergent_iff _).2 g.integrable
  · intro c f x
    simp only [fourierIntegral_eq, Pi.smul_apply, RingHom.id_apply, smul_comm _ c, integral_smul]
  · intro f
    exact Real.contDiff_fourierIntegral (fun n _ ↦ integrable_pow_mul volume f n)
  · rintro ⟨k, n⟩
    refine ⟨Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1),
       (2 * π) ^ n * (2 * ↑n + 2) ^ k * (Finset.range (n + 1) ×ˢ Finset.range (k + 1)).card
         * 2 ^ integrablePower (volume : Measure V) *
         (∫ (x : V), (1 + ‖x‖) ^ (- (integrablePower (volume : Measure V) : ℝ))) * 2,
       ⟨by positivity, fun f x ↦ ?_⟩⟩
    apply (pow_mul_norm_iteratedFDeriv_fourierIntegral_le (f.smooth ⊤)
      (fun k n _hk _hn ↦ integrable_pow_mul_iteratedFDeriv _ f k n) le_top le_top x).trans
    simp only [mul_assoc]
    gcongr
    calc
    ∑ p ∈ Finset.range (n + 1) ×ˢ Finset.range (k + 1),
        ∫ (v : V), ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (⇑f) v‖
      ≤ ∑ p ∈ Finset.range (n + 1) ×ˢ Finset.range (k + 1),
        2 ^ integrablePower (volume : Measure V) *
        (∫ (x : V), (1 + ‖x‖) ^ (- (integrablePower (volume : Measure V) : ℝ))) * 2 *
        ((Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1)).sup
          (schwartzSeminormFamily 𝕜 V E)) f := by
      apply Finset.sum_le_sum (fun p hp ↦ ?_)
      simp only [Finset.mem_product, Finset.mem_range] at hp
      apply (f.integral_pow_mul_iteratedFDeriv_le 𝕜 _ _ _).trans
      simp only [mul_assoc]
      rw [two_mul]
      gcongr
      · apply Seminorm.le_def.1
        have : (0, p.2) ∈ (Finset.range (n + integrablePower (volume : Measure V) + 1)
            ×ˢ Finset.range (k + 1)) := by simp [hp.2]
        apply Finset.le_sup this (f := fun p ↦ SchwartzMap.seminorm 𝕜 p.1 p.2 (E := V) (F := E))
      · apply Seminorm.le_def.1
        have : (p.1 + integrablePower (volume : Measure V), p.2) ∈ (Finset.range
            (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1)) := by
          simp [hp.2]
          omega
        apply Finset.le_sup this (f := fun p ↦ SchwartzMap.seminorm 𝕜 p.1 p.2 (E := V) (F := E))
    _ = _ := by simp [mul_assoc]

@[simp] lemma fourierTransformCLM_apply (f : 𝓢(V, E)) :
    fourierTransformCLM 𝕜 f = 𝓕 f := rfl

variable [CompleteSpace E]

/-- The Fourier transform on a real inner product space, as a continuous linear equiv on the
Schwartz space. -/
noncomputable def fourierTransformCLE : 𝓢(V, E) ≃L[𝕜] 𝓢(V, E) where
  __ := fourierTransformCLM 𝕜
  invFun := (compCLMOfContinuousLinearEquiv 𝕜 (LinearIsometryEquiv.neg ℝ (E := V)))
      ∘L (fourierTransformCLM 𝕜)
  left_inv := by
    intro f
    ext x
    change 𝓕 (𝓕 f) (-x) = f x
    rw [← fourierIntegralInv_eq_fourierIntegral_neg, Continuous.fourier_inversion f.continuous
      f.integrable (fourierTransformCLM 𝕜 f).integrable]
  right_inv := by
    intro f
    ext x
    change 𝓕 (fun x ↦ (𝓕 f) (-x)) x = f x
    simp_rw [← fourierIntegralInv_eq_fourierIntegral_neg, Continuous.fourier_inversion_inv
      f.continuous f.integrable (fourierTransformCLM 𝕜 f).integrable]
  continuous_invFun := ContinuousLinearMap.continuous _

@[simp] lemma fourierTransformCLE_apply (f : 𝓢(V, E)) :
    fourierTransformCLE 𝕜 f = 𝓕 f := rfl

@[simp] lemma fourierTransformCLE_symm_apply (f : 𝓢(V, E)) :
    (fourierTransformCLE 𝕜).symm f = 𝓕⁻ f := by
  ext x
  exact (fourierIntegralInv_eq_fourierIntegral_neg f x).symm

-- TODO: Is it ugly to provide these definitions?

theorem continuous_fourierIntegral (f : 𝓢(V, E)) : Continuous (𝓕 f) :=
  (fourierTransformCLE ℂ f).continuous

theorem integrable_fourierIntegral (f : 𝓢(V, E)) : Integrable (𝓕 f) :=
  (fourierTransformCLE ℂ f).integrable

theorem memℒp_fourierIntegral (f : 𝓢(V, E)) (p : ℝ≥0∞)
    (μ : Measure V := by volume_tac) [μ.HasTemperateGrowth] : Memℒp (𝓕 f) p μ :=
  (fourierTransformCLE ℂ f).memℒp p μ

theorem eLpNorm_fourierIntegral_lt_top (f : 𝓢(V, E)) (p : ℝ≥0∞)
    (μ : Measure V := by volume_tac) [μ.HasTemperateGrowth] : eLpNorm (𝓕 f) p μ < ⊤ :=
  (fourierTransformCLE ℂ f).eLpNorm_lt_top p μ

/-- Plancherel's theorem: The Fourier transform preserves the `L^2` inner product. -/
theorem integral_inner_fourier_eq_integral_inner (f g : 𝓢(V, F)) :
    ∫ ξ, ⟪𝓕 f ξ, 𝓕 g ξ⟫_ℂ = ∫ x, ⟪f x, g x⟫_ℂ :=
  Real.integral_inner_fourier_eq_integral_inner f.continuous f.integrable
    f.integrable_fourierIntegral g.integrable

/-- Plancherel's theorem: The Fourier transform preserves the `L^2` norm. -/
theorem integral_norm_sq_fourier_eq_integral_norm_sq (f : 𝓢(V, F)) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 :=
  Real.integral_norm_sq_fourier_eq_integral_norm_sq f.continuous f.integrable
    f.integrable_fourierIntegral

/-- Plancherel's theorem, `eLpNorm` version. -/
theorem eLpNorm_fourier_two_eq_eLpNorm_two (f : 𝓢(V, F)) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume :=
  Real.eLpNorm_fourier_two_eq_eLpNorm_two f.continuous f.integrable (f.memℒp 2 _)
    f.integrable_fourierIntegral (f.memℒp_fourierIntegral 2 _)

end SchwartzMap


variable {𝕜 α V E F : Type*}

/-! ## Fourier transform on L1 -/

section L1

namespace MeasureTheory

variable [NormedAddCommGroup V] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

variable [NormedSpace ℂ E] [NormedSpace ℂ F]

variable [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]

-- TODO: Prove `eq`?
theorem L1.eLpNorm_fourierIntegral_top_le_eLpNorm_one (f : Lp E 1 (volume : Measure V)) :
    eLpNorm (𝓕 f) ⊤ volume ≤ eLpNorm f 1 volume := by
  -- TODO: Already using L1 norm here.
  calc eLpNorm (𝓕 f) ⊤ volume
  _ ≤ ENNReal.ofReal (∫ x, ‖f x‖) := by
    refine eLpNormEssSup_le_of_ae_bound (.of_forall fun ξ ↦ ?_)
    refine (norm_integral_le_integral_norm _).trans (integral_mono ?_ ?_ ?_)
    · simpa using (L1.integrable_coeFn f).norm
    · exact (L1.integrable_coeFn f).norm
    · simp
  _ = eLpNorm f 1 volume := by
    symm
    simpa using (Lp.memℒp f).eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top

-- theorem L1.eLpNorm_fourierIntegral_top_eq_eLpNorm_one (f : Lp E 1 (volume : Measure V)) :
--     eLpNorm (𝓕 f) ⊤ volume = eLpNorm f 1 volume := by
--   -- TODO: Already using L1 norm here.
--   calc eLpNorm (𝓕 f) ⊤ volume
--   _ = ENNReal.ofReal (∫ x, ‖f x‖) := by
--     rw [eLpNorm_exponent_top]
--     rw [eLpNormEssSup_eq_essSup_enorm]

--     refine eLpNormEssSup_le_of_ae_bound (.of_forall fun ξ ↦ ?_)
--     refine (norm_integral_le_integral_norm _).trans (integral_mono ?_ ?_ ?_)
--     · simpa using (L1.integrable_coeFn f).norm
--     · exact (L1.integrable_coeFn f).norm
--     · simp
--   _ = eLpNorm f 1 volume := by
--     symm
--     simpa using (Lp.memℒp f).eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top

theorem L1.eLpNorm_fourierIntegral_top_lt_top (f : Lp E 1 (volume : Measure V)) :
    eLpNorm (𝓕 f) ⊤ volume < ⊤ :=
  (eLpNorm_fourierIntegral_top_le_eLpNorm_one f).trans_lt (Lp.eLpNorm_lt_top f)

/-- The Fourier transform of an `L^1` function is continuous. -/
theorem L1.continuous_fourierIntegral (f : Lp E 1 (volume : Measure V)) : Continuous (𝓕 f) :=
  Real.fourierIntegral_continuous (integrable_coeFn f)

/-- The Fourier transform of an `L^1` function is an `L^∞` function. -/
theorem L1.memℒp_fourierIntegral_top (f : Lp E 1 (volume : Measure V)) : Memℒp (𝓕 f) ⊤ :=
  ⟨(continuous_fourierIntegral f).aestronglyMeasurable, eLpNorm_fourierIntegral_top_lt_top f⟩

variable (𝕜 V E) in
noncomputable def L1.fourierTransformLM :
    Lp E 1 (volume : Measure V) →ₗ[𝕜] Lp E ⊤ (volume : Measure V) where
  toFun f := (memℒp_fourierIntegral_top f).toLp
  map_add' f g := by
    simp_rw [Real.fourierIntegral_congr_ae (Lp.coeFn_add f g)]
    simp_rw [Real.fourierIntegral_add (integrable_coeFn f) (integrable_coeFn g)]
    exact Memℒp.toLp_add _ _
  map_smul' c f := by
    simp_rw [Real.fourierIntegral_congr_ae (Lp.coeFn_smul c f), Real.fourierIntegral_const_smul]
    exact Memℒp.toLp_const_smul _ _

-- theorem L1.coeFn_fourierTransformLM (f : Lp E 1 (volume : Measure V)) :
--     ⇑(fourierTransformLM 𝕜 V E f) =ᵐ[volume] 𝓕 f := (memℒp_fourierIntegral_top f).coeFn_toLp

variable (𝕜 V E) in
/-- The Fourier transform as a continuous linear map from `L^1` to `L^∞`. -/
noncomputable def L1.fourierTransformCLM :
    Lp E 1 (volume : Measure V) →L[𝕜] Lp E ⊤ (volume : Measure V) :=
  (fourierTransformLM 𝕜 V E).mkContinuous 1 fun f ↦ by
    suffices ‖fourierTransformLM 𝕜 V E f‖ₑ ≤ ‖f‖ₑ by simpa [enorm_eq_nnnorm] using this
    calc ‖(fourierTransformLM 𝕜 V E) f‖ₑ
    _ = eLpNorm ((fourierTransformLM 𝕜 V E) f) ⊤ volume := Lp.enorm_def _
    _ = eLpNorm (𝓕 f) ⊤ volume := eLpNorm_congr_ae (memℒp_fourierIntegral_top f).coeFn_toLp
    _ ≤ eLpNorm f 1 volume := eLpNorm_fourierIntegral_top_le_eLpNorm_one f
    _ = ‖f‖ₑ := (Lp.enorm_def f).symm

theorem L1.fourierTransformCLM_norm_le : ‖fourierTransformCLM 𝕜 V E‖ ≤ 1 :=
  (fourierTransformLM 𝕜 V E).mkContinuous_norm_le zero_le_one _

variable (𝕜) in
theorem L1.coeFn_fourierTransformCLM (f : Lp E 1 (volume : Measure V)) :
    ⇑(fourierTransformCLM 𝕜 V E f) =ᵐ[volume] 𝓕 f :=
  (memℒp_fourierIntegral_top f).coeFn_toLp

end MeasureTheory

end L1


/-! ## Fourier transform for Schwartz L^p functions -/

-- TDOO: Move
namespace MeasureTheory

variable [MeasurableSpace α] [NormedAddCommGroup E] [NormedField 𝕜] [NormedSpace 𝕜 E]

@[simp] theorem Lp.coe_smul {p : ℝ≥0∞} {μ : Measure α} (c : 𝕜) (f : Lp E p μ) :
    (c • f).val = c • f.val :=
  (LpSubmodule E p μ 𝕜).coe_smul c f

@[simp] theorem Lp.inf_coe_smul {p q : ℝ≥0∞} {μ : Measure α} (c : 𝕜)
    (f : ↥(Lp E p μ ⊓ Lp E q μ)) :
    (c • f).val = c • f.val :=
  (Lp.LpSubmodule E p μ 𝕜 ⊓ Lp.LpSubmodule E q μ 𝕜).coe_smul c f

end MeasureTheory

section LpSchwartz

namespace SchwartzMap

section AEEqSchwartz

variable [MeasurableSpace α] [NormedAddCommGroup α] [NormedSpace ℝ α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]

-- TODO: Is there not a general version of this somewhere?
theorem inductionOn_ae_eq {f : α → E} {μ : Measure α} (hf : ∃ g : 𝓢(α, E), g =ᵐ[μ] f)
    {P : (α → E) → Prop} (h_congr : ∀ {f g : α → E}, f =ᵐ[μ] g → (P f ↔ P g))
    (h_ind : ∀ g : 𝓢(α, E), P g) : P f := by
  rcases hf with ⟨g, hg⟩
  exact (h_congr hg).mp (h_ind g)

variable [OpensMeasurableSpace α] [SecondCountableTopologyEither α E]

theorem inductionOn_range_toAEEqFun {μ : Measure α} (f : LinearMap.range (toAEEqFun 𝕜 E μ))
    {P : (α → E) → Prop} (h_congr : ∀ {f g : α → E}, f =ᵐ[μ] g → (P f ↔ P g))
    (h_ind : ∀ g : 𝓢(α, E), P g) : P f :=
  inductionOn_ae_eq (mem_range_toAEEqFun_iff.mp f.2) h_congr h_ind

end AEEqSchwartz


-- Now try to define Fourier transform for both `L^p` and `L^p ∩ L^q`.
-- Later specialize to CLM for `L^2 → L^2` and `L^1 ∩ L^2 → L^2 ∩ L^∞`.

section Fourier

section Lp

variable [MeasurableSpace α] [NormedAddCommGroup E] [NormedField 𝕜] [NormedSpace 𝕜 E]

-- TODO: Move
variable (𝕜 E) in
/-- A linear map to the underlying `AEEqFun`. -/
def _root_.MeasureTheory.Lp.subtype (p : ℝ≥0∞) (μ : Measure α) : Lp E p μ →ₗ[𝕜] α →ₘ[μ] E :=
  (Lp.LpSubmodule E p μ 𝕜).subtype

-- TODO: Move
variable (𝕜 E) in
/-- A linear map to the underlying `AEEqFun`. -/
def _root_.MeasureTheory.Lp.inf_subtype (p q : ℝ≥0∞) (μ : Measure α) :
    ↑(Lp E p μ ⊓ Lp E q μ) →ₗ[𝕜] α →ₘ[μ] E :=
  (Lp.LpSubmodule E p μ 𝕜 ⊓ Lp.LpSubmodule E q μ 𝕜).subtype

end Lp

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  -- These depend on `Real.fourierIntegral_const_smul`
  -- (differs from `VectorFourier.fourierIntegral_const_smul`).
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  -- [NormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]

theorem aeeqFun_fourierIntegral_add {f g : V →ₘ[volume] E}
    (hf : ∃ f₀ : 𝓢(V, E), f₀ =ᵐ[volume] f) (hg : ∃ g₀ : 𝓢(V, E), g₀ =ᵐ[volume] g) :
    𝓕 (f + g) = 𝓕 f + 𝓕 g :=
  (fourierIntegral_congr_ae (AEEqFun.coeFn_add f g)).trans <| fourierIntegral_add
    (inductionOn_ae_eq hf integrable_congr integrable)
    (inductionOn_ae_eq hg integrable_congr integrable)

-- TODO: This doesn't actually care about Schwartz...
theorem aeeqFun_fourierIntegral_const_smul (c : 𝕜) (f : V →ₘ[volume] E) : 𝓕 (c • f) = c • 𝓕 f :=
  (fourierIntegral_congr_ae (AEEqFun.coeFn_smul c f)).trans (fourierIntegral_const_smul c f)

theorem fourier_inductionOn_ae_eq {f : V → E} (hf : ∃ g : 𝓢(V, E), g =ᵐ[volume] f)
    {P : (V → E) → Prop} (h_ind : ∀ g : 𝓢(V, E), P (𝓕 g)) : P (𝓕 f) := by
  rcases hf with ⟨g, hg⟩
  exact fourierIntegral_congr_ae hg ▸ h_ind g

theorem fourier_inductionOn_range_toAEEqFun
    (f : LinearMap.range (toAEEqFun 𝕜 E (volume : Measure V))) {P : (V → E) → Prop}
    (h_ind : ∀ g : 𝓢(V, E), P (𝓕 g)) : P (𝓕 f) :=
  fourier_inductionOn_ae_eq (mem_range_toAEEqFun_iff.mp f.2) (P := P) h_ind

variable (𝕜 V E) in
/-- Linear map from aeeq Schwartz functions to functions. -/
noncomputable def fourierTransformLM_aeeq_to_fun :
    LinearMap.range (toAEEqFun 𝕜 E (volume : Measure V)) →ₗ[𝕜] V → E where
  toFun f := 𝓕 f
  map_add' f g :=
    (fourierIntegral_congr_ae (AEEqFun.coeFn_add f.1 g.1)).trans <| fourierIntegral_add
      (inductionOn_range_toAEEqFun f integrable_congr integrable)
      (inductionOn_range_toAEEqFun g integrable_congr integrable)
    -- simp only [Submodule.coe_add, fourierIntegral_congr_ae (AEEqFun.coeFn_add f.1 g.1)]
    -- exact fourierIntegral_add
    --   (inductionOn_range_toAEEqFun f integrable_congr integrable)
    --   (inductionOn_range_toAEEqFun g integrable_congr integrable)
  map_smul' c f :=
    (fourierIntegral_congr_ae (AEEqFun.coeFn_smul c f.1)).trans (fourierIntegral_const_smul c f.1)
    -- simp only [SetLike.val_smul, fourierIntegral_congr_ae (AEEqFun.coeFn_smul c f.1)]
    -- exact fourierIntegral_const_smul c f.1

theorem fourierTransformLM_aeeq_to_fun_apply
    (f : LinearMap.range (toAEEqFun 𝕜 E (volume : Measure V))) :
    fourierTransformLM_aeeq_to_fun 𝕜 V E f = 𝓕 f := rfl

variable [CompleteSpace E]

variable (𝕜 V E) in
/-- Linear map from aeeq Schwartz functions to aeeq functions. -/
noncomputable def fourierTransformLM_aeeq_to_aeeq :
    LinearMap.range (toAEEqFun 𝕜 E (volume : Measure V)) →ₗ[𝕜] V →ₘ[volume] E where
  toFun f := AEEqFun.mk (fourierTransformLM_aeeq_to_fun 𝕜 V E f)
    (fourier_inductionOn_range_toAEEqFun f (P := fun f ↦ AEStronglyMeasurable f volume)
      fun f ↦ f.integrable_fourierIntegral.aestronglyMeasurable)
  map_add' f g := by
    simp only [AEEqFun.mk_add_mk]
    congr
    exact LinearMap.map_add _ f g
  map_smul' c f := by
    simp only [AEEqFun.smul_mk]
    congr
    exact LinearMap.map_smul _ c f

variable (𝕜 V E) in
noncomputable def fourierTransformLM_aeeq_to_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    LinearMap.range (toAEEqFun 𝕜 E (volume : Measure V)) →ₗ[𝕜] Lp E p (volume : Measure V) where
  toFun f := Memℒp.toLp (fourierTransformLM_aeeq_to_fun 𝕜 V E f) (by
    exact fourier_inductionOn_range_toAEEqFun f (P := (Memℒp · p volume))
      (memℒp_fourierIntegral · p volume))
  map_add' f g := by
    simp only [map_add]
    rfl
  map_smul' c f := by
    simp only [_root_.map_smul]
    rfl

-- `Fact (1 ≤ p)` comes from `toLpCLM`; but `toLp` would suffice.
variable (𝕜 V E) in
noncomputable def fourierTransformLM_Lp (p q : ℝ≥0∞) [Fact (1 ≤ p)] :
    LinearMap.range (toLpCLM 𝕜 E p (volume : Measure V)) →ₗ[𝕜] Lp E q (volume : Measure V) where
  toFun f := Memℒp.toLp (𝓕 f)
    (fourier_inductionOn_ae_eq (mem_range_toLpCLM_iff.mp f.2) (P := (Memℒp · q volume))
      (memℒp_fourierIntegral · q volume))
  map_add' f g := by
    simp only [Submodule.coe_add, AddSubgroup.coe_add, aeeqFun_fourierIntegral_add
      (mem_range_toLpCLM_iff.mp f.2) (mem_range_toLpCLM_iff.mp g.2)]
    rfl  -- exact Memℒp.toLp_add _ _
  map_smul' c f := by
    simp only [SetLike.val_smul, Lp.coe_smul, aeeqFun_fourierIntegral_const_smul c f.1.1]
    rfl  -- exact Memℒp.toLp_const_smul _ _
    -- simp only
    -- refine .trans ?_ (Memℒp.toLp_const_smul _ _)
    -- congr
    -- exact aeeqFun_fourierIntegral_const_smul c f.1.1

variable (𝕜 V E) in
noncomputable def fourierTransformLM_LpInf (p₁ p₂ q₁ q₂ : ℝ≥0∞) :
    LinearMap.range (toLpInfLM 𝕜 E p₁ p₂ (volume : Measure V)) →ₗ[𝕜]
      (Lp E q₁ _ ⊓ Lp E q₂ _ : AddSubgroup (V →ₘ[volume] E)) where
  toFun f := ⟨AEEqFun.mk (𝓕 f) _, Lp.mk_mem_inf_of_eLpNorm_lt_top _
    (Continuous.aestronglyMeasurable <|
      fourier_inductionOn_ae_eq (mem_range_toLpInfLM_iff.mp f.2) continuous_fourierIntegral)
    (fourier_inductionOn_ae_eq (mem_range_toLpInfLM_iff.mp f.2) (P := (eLpNorm · q₁ volume < ⊤))
      (fun f ↦ f.eLpNorm_fourierIntegral_lt_top q₁ volume))
    (fourier_inductionOn_ae_eq (mem_range_toLpInfLM_iff.mp f.2) (P := (eLpNorm · q₂ volume < ⊤))
      (fun f ↦ f.eLpNorm_fourierIntegral_lt_top q₂ volume))⟩
  map_add' f g := by
    simp_rw [Submodule.coe_add, AddSubgroup.coe_add, aeeqFun_fourierIntegral_add
      (mem_range_toLpInfLM_iff.mp f.2) (mem_range_toLpInfLM_iff.mp g.2)]
    rfl
  map_smul' c f := by
    simp_rw [SetLike.val_smul, Lp.inf_coe_smul, aeeqFun_fourierIntegral_const_smul c f.1.1]
    rfl

theorem fourierTransformLM_Lp_apply {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : LinearMap.range (toLpCLM 𝕜 E p (volume : Measure V))) :
    fourierTransformLM_Lp 𝕜 V E p q f = Memℒp.toLp (𝓕 f)
      (fourier_inductionOn_ae_eq (mem_range_toLpCLM_iff.mp f.2) (P := (Memℒp · q volume))
        (memℒp_fourierIntegral · q volume)) :=
  rfl

theorem coeFn_fourierTransformLM_Lp {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : LinearMap.range (toLpCLM 𝕜 E p (volume : Measure V))) :
    fourierTransformLM_Lp 𝕜 V E p q f =ᵐ[volume] 𝓕 f :=
  -- simp only [fourierTransformLM_Lp, LinearMap.coe_mk, AddHom.coe_mk]
  -- exact Memℒp.coeFn_toLp _
  AEEqFun.coeFn_mk _ _

theorem coeFn_fourierTransformLM_LpInf {p₁ p₂ q₁ q₂ : ℝ≥0∞}
    (f : LinearMap.range (toLpInfLM 𝕜 E p₁ p₂ (volume : Measure V))) :
    fourierTransformLM_LpInf 𝕜 V E _ _ q₁ q₂ f =ᵐ[volume] 𝓕 f :=
  AEEqFun.coeFn_mk _ _


variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]

noncomputable def fourierTransformCLM_L2 [CompleteSpace F] :
    LinearMap.range (toLpCLM 𝕜 F 2 (volume : Measure V)) →L[𝕜] Lp F 2 (volume : Measure V) :=
  LinearMap.mkContinuous (fourierTransformLM_Lp 𝕜 V F 2 2) 1
    (fun f ↦ le_of_eq <| by
      simp only [AddSubgroupClass.coe_norm, Lp.norm_def, one_mul]
      refine congrArg _ ?_
      rw [eLpNorm_congr_ae (coeFn_fourierTransformLM_Lp _)]
      exact inductionOn_ae_eq (mem_range_toLpCLM_iff.mp f.2)
        (P := fun f ↦ eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume)
        (fun h ↦ by simp_rw [Real.fourierIntegral_congr_ae h, eLpNorm_congr_ae h])
        eLpNorm_fourier_two_eq_eLpNorm_two)

noncomputable def fourierTransformCLM_L1L2 [CompleteSpace F] :
    LinearMap.range (toLpInfLM 𝕜 F 1 2 (volume : Measure V)) →L[𝕜]
      (Lp F ∞ _ ⊓ Lp F 2 _ : AddSubgroup (V →ₘ[volume] F)) :=
  LinearMap.mkContinuous (fourierTransformLM_LpInf 𝕜 V F 1 2 ∞ 2) 1
    (fun f ↦ by
      simp only [AddSubgroupClass.coe_norm, Lp.norm_inf_def, one_mul, Lp.norm_def]
      gcongr
      · exact Lp.eLpNorm_ne_top (AddSubgroup.inf_fst f.1)
      · simp only [AddSubgroup.inf_fst_val]
        rw [eLpNorm_congr_ae (coeFn_fourierTransformLM_LpInf _)]
        simp_rw [← AddSubgroup.inf_fst_val]
        exact L1.eLpNorm_fourierIntegral_top_le_eLpNorm_one _
      · exact Lp.eLpNorm_ne_top (AddSubgroup.inf_snd f.1)
      · simp only [AddSubgroup.inf_snd_val]
        rw [eLpNorm_congr_ae (coeFn_fourierTransformLM_LpInf _)]
        refine le_of_eq ?_
        exact inductionOn_ae_eq (mem_range_toLpInfLM_iff.mp f.2)
          (P := fun f ↦ eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume)
          (fun h ↦ by simp_rw [Real.fourierIntegral_congr_ae h, eLpNorm_congr_ae h])
          eLpNorm_fourier_two_eq_eLpNorm_two)

end Fourier

end SchwartzMap

end LpSchwartz
