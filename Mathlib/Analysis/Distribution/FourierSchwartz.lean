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

/-!
# Fourier transform on Schwartz functions

This file constructs the Fourier transform as a continuous linear map acting on Schwartz
functions, in `fourierTransformCLM`. It is also given as a continuous linear equiv, in
`fourierTransformCLE`.
-/

open Real MeasureTheory MeasureTheory.Measure Filter
open scoped FourierTransform ENNReal InnerProductSpace

namespace SchwartzMap

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

theorem continuous_fourier (f : 𝓢(V, E)) : Continuous (𝓕 f) :=
  (fourierTransformCLE ℂ f).continuous

theorem integrable_fourier (f : 𝓢(V, E)) : Integrable (𝓕 f) :=
  (fourierTransformCLE ℂ f).integrable

theorem memℒp_fourier (f : 𝓢(V, E)) (p : ℝ≥0∞)
    (μ : Measure V := by volume_tac) [μ.HasTemperateGrowth] : Memℒp (𝓕 f) p μ :=
  (fourierTransformCLE ℂ f).memℒp p μ

/-- Plancherel's theorem: The Fourier transform preserves the `L^2` inner product. -/
theorem integral_inner_fourier_eq_integral_inner (f g : 𝓢(V, F)) :
    ∫ ξ, ⟪𝓕 f ξ, 𝓕 g ξ⟫_ℂ = ∫ x, ⟪f x, g x⟫_ℂ :=
  Real.integral_inner_fourier_eq_integral_inner f.continuous f.integrable f.integrable_fourier
    g.integrable

/-- Plancherel's theorem: The Fourier transform preserves the `L^2` norm. -/
theorem integral_norm_sq_fourier_eq_integral_norm_sq (f : 𝓢(V, F)) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 :=
  Real.integral_norm_sq_fourier_eq_integral_norm_sq f.continuous f.integrable f.integrable_fourier

/-- Plancherel's theorem, `eLpNorm` version. -/
theorem eLpNorm_fourier_two_eq_eLpNorm_two (f : 𝓢(V, F)) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume :=
  Real.eLpNorm_fourier_two_eq_eLpNorm_two f.continuous f.integrable (f.memℒp 2 _)
    f.integrable_fourier (f.memℒp_fourier 2 _)

end SchwartzMap

/-! ## Extension to `Lp` using density -/

namespace MeasureTheory

open scoped SchwartzMap

variable {𝕜 V E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup V]
  [NormedSpace ℂ E] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- The Fourier transform of a function in `L^p` which has a Schwartz representative is also a
function in `L^q` with a Schwartz representative, with `q` arbitrary. -/
theorem Lp.LpSchwartzMap.memℒp_fourierIntegral {p : ℝ≥0∞}
    (f : LpSchwartzMap E p (volume : Measure V)) (q : ℝ≥0∞) : Memℒp (𝓕 f) q volume :=
  induction_on f (fun g ↦ Memℒp (𝓕 g) q volume)
    (fun _ hfg ↦ Eq.subst (motive := fun (f : V → E) ↦ Memℒp f q volume)
      (Real.fourierIntegral_congr_ae hfg).symm)
    (fun g ↦ g.memℒp_fourier q volume)

/-- The Fourier transform as a map from `LpSchwartzMap` to `LpSchwartzMap`. -/
noncomputable def Lp.LpSchwartzMap.fourierTransform {p : ℝ≥0∞} (q : ℝ≥0∞)
    (f : LpSchwartzMap E p (volume : Measure V)) :
    LpSchwartzMap E q (volume : Measure V) where
  val := (memℒp_fourierIntegral f q).toLp
  property := by
    rcases f with ⟨f, hf⟩
    rw [mem_iff_ae] at hf ⊢
    revert hf
    refine Exists.imp' (SchwartzMap.fourierTransformCLE ℂ) fun f₀ hf₀ ↦ ?_
    simpa [Real.fourierIntegral_congr_ae hf₀] using Memℒp.coeFn_toLp _

theorem Lp.LpSchwartzMap.coeFn_fourierTransform {p : ℝ≥0∞} (q : ℝ≥0∞)
    (f : LpSchwartzMap E p (volume : Measure V)) :
    ⇑(fourierTransform q f) =ᵐ[volume] 𝓕 f := by
  simpa [fourierTransform] using Memℒp.coeFn_toLp _

/-- The Fourier transform is uniform continuous as a map `L^1 → L^∞`. -/
theorem Lp.LpSchwartzMap.uniformContinuous_fourierTransform_one_top :
    UniformContinuous (fun f : LpSchwartzMap E 1 (volume : Measure V) ↦ fourierTransform ⊤ f) := by
  refine EMetric.uniformContinuous_iff.mpr ?_
  simp only [Subtype.edist_eq, edist_def]
  intro ε hε
  use ε, hε
  intro a b h
  calc eLpNorm (⇑(fourierTransform ⊤ a) - ⇑(fourierTransform ⊤ b)) ⊤ volume
  _ = eLpNorm (𝓕 a - 𝓕 b) ⊤ volume := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [coeFn_fourierTransform ⊤ a, coeFn_fourierTransform ⊤ b] with x h₁ h₂
    simp [h₁, h₂]
  _ = eLpNorm (𝓕 (a - b)) ⊤ volume := by
    refine congrArg (eLpNorm · ⊤ volume) ?_
    calc 𝓕 a - 𝓕 b
    _ = 𝓕 (⇑a - ⇑b) := by
      refine induction_on₂ a b (fun a b ↦ 𝓕 a - 𝓕 b = 𝓕 (a - b)) ?_ ?_
      · intro f' g' hf hg h
        simp only [Pi.sub_def]
        rw [Real.fourierIntegral_congr_ae hf, Real.fourierIntegral_congr_ae hg]
        rw [Real.fourierIntegral_congr_ae (hf.sub hg)]
        exact h
      intro f₀ g₀
      change _ = 𝓕 (f₀ - g₀)
      simp only [← SchwartzMap.fourierTransformCLM_apply ℂ]  -- TODO: Ok to specify `ℂ` here?
      ext ξ
      simp
    _ = 𝓕 (a - b) := by
      refine Real.fourierIntegral_congr_ae ?_
      filter_upwards [coeFn_sub a.val b.val] with x h
      simpa using h.symm
  _ ≤ ENNReal.ofReal (eLpNorm (⇑(a - b)) 1 volume).toReal := by
    simp only [eLpNorm_exponent_top]
    refine eLpNormEssSup_le_of_ae_nnnorm_bound ?_
    simp only [ENNReal.toNNReal_toReal_eq]
    refine ae_of_all _ fun x ↦ ?_
    refine ENNReal.le_toNNReal_of_coe_le ?_ (eLpNorm_ne_top (a - b).val)
    simp only [Real.fourierIntegral_eq]
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_mono_fn fun ξ ↦ ?_
    -- Switch to real-valued norm in order to use `Circle.norm_smul`.
    simp [enorm_eq_nnnorm, ← NNReal.coe_le_coe]
  _ ≤ eLpNorm (a - b) 1 volume := ENNReal.ofReal_toReal_le
  _ = eLpNorm (⇑a - ⇑b) 1 volume := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [coeFn_sub a.val b.val] with x h  -- TODO: Define `coe`?
    simpa using h
  _ < ε := h

theorem Lp.LpSchwartzMap.norm_fourier_two_eq_norm_two (f : LpSchwartzMap F 2 (volume : Measure V)) :
    ‖fourierTransform 2 f‖ = ‖f‖ := by
  suffices ‖(fourierTransform 2 f).val‖ₑ = ‖f.val‖ₑ by
    simpa [enorm_eq_nnnorm, ← NNReal.coe_inj] using this
  calc ‖(fourierTransform 2 f).val‖ₑ
  _ = eLpNorm (fourierTransform 2 f) 2 volume := enorm_def _
  _ = eLpNorm (𝓕 f) 2 volume := eLpNorm_congr_ae (coeFn_fourierTransform 2 f)
  _ = eLpNorm f 2 volume := by
    refine induction_on f (fun f ↦ eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume)
      ?_ SchwartzMap.eLpNorm_fourier_two_eq_eLpNorm_two
    intro f' hf h
    rw [Real.fourierIntegral_congr_ae hf, eLpNorm_congr_ae hf]
    exact h
  _ = ‖f.val‖ₑ := .symm <| enorm_def _

-- TODO: Would this be easier to prove using `fourierTransformLM`?
-- TODO: Use `‖fourierTransform 2 f‖ = ‖f‖` from above?

/-- The Fourier transform is uniform continuous under the `L^2` norm. -/
theorem Lp.LpSchwartzMap.uniformContinuous_fourierTransform_two_two :
    UniformContinuous (fun f : LpSchwartzMap F 2 (volume : Measure V) ↦ fourierTransform 2 f) := by
  refine EMetric.uniformContinuous_iff.mpr ?_
  simp only [Subtype.edist_eq, edist_def]
  intro ε hε
  use ε, hε
  intro f g h
  -- simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, coeFn_fourierTransformLM]
  calc eLpNorm (⇑(fourierTransform 2 f) - ⇑(fourierTransform 2 g)) 2 volume
  _ = eLpNorm (𝓕 f - 𝓕 g) 2 volume := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [coeFn_fourierTransform 2 f, coeFn_fourierTransform 2 g] with x h₁ h₂
    simp [h₁, h₂]
  _ = eLpNorm (𝓕 (⇑f - ⇑g)) 2 volume := by
    refine congrArg (eLpNorm · 2 volume) ?_
    refine induction_on₂ f g (fun f g ↦ 𝓕 f - 𝓕 g = 𝓕 (f - g)) ?_ ?_
    · intro f' g' hf hg h
      simp only [Pi.sub_def]
      rw [Real.fourierIntegral_congr_ae hf, Real.fourierIntegral_congr_ae hg]
      rw [Real.fourierIntegral_congr_ae (hf.sub hg)]
      exact h
    intro f₀ g₀
    change _ = 𝓕 (f₀ - g₀)
    simp only [← SchwartzMap.fourierTransformCLM_apply ℂ]  -- TODO: Ok to specify `ℂ` here?
    ext ξ
    simp
  _ = eLpNorm (𝓕 (f - g)) 2 volume := by
    refine congrArg (eLpNorm · 2 volume) ?_
    refine Real.fourierIntegral_congr_ae ?_
    filter_upwards [coeFn_sub f.val g.val] with x h
    simpa using h.symm
  _ = eLpNorm (f - g) 2 volume := by
    refine induction_on (f - g) (fun r ↦ eLpNorm (𝓕 r) 2 volume = eLpNorm r 2 volume) ?_
      SchwartzMap.eLpNorm_fourier_two_eq_eLpNorm_two
    intro r hr h
    rw [Real.fourierIntegral_congr_ae hr, eLpNorm_congr_ae hr]
    exact h
  _ = eLpNorm (⇑f - ⇑g) 2 volume := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [coeFn_sub f.val g.val] with x h
    simpa using h
  _ < ε := h

section LinearMap

variable [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E] [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]

theorem Lp.LpSchwartzMap.fourierTransform_add {p : ℝ≥0∞} (q : ℝ≥0∞)
    (f g : LpSchwartzMap E p (volume : Measure V)) :
    fourierTransform q (f + g) = fourierTransform q f + fourierTransform q g := by
  ext
  filter_upwards [coeFn_fourierTransform q f, coeFn_fourierTransform q g,
    coeFn_fourierTransform q (f + g),
    AEEqFun.coeFn_add (fourierTransform q f).val.val (fourierTransform q g).val.val]
    with ξ hf hg hfg hfg'
  calc fourierTransform q (f + g) ξ
  _ = 𝓕 (f + g) ξ := hfg
  _ = (𝓕 f + 𝓕 g) ξ := by
    refine congrFun ?_ ξ
    calc 𝓕 (f + g)
    _ = 𝓕 (⇑f + ⇑g) := by
      refine Real.fourierIntegral_congr_ae ?_
      filter_upwards [AEEqFun.coeFn_add f.val.val g.val.val] with x h
      simpa using h
    _ = 𝓕 f + 𝓕 g := by
      refine induction_on₂ f g (fun f g ↦ 𝓕 (f + g) = 𝓕 f + 𝓕 g) ?_ ?_
      · intro f' g' hf' hg' h
        simp only [Pi.add_def]
        rw [Real.fourierIntegral_congr_ae hf', Real.fourierIntegral_congr_ae hg']
        rw [Real.fourierIntegral_congr_ae (.add hf' hg')]
        exact h
      · intro f₀ g₀
        change 𝓕 ⇑(f₀ + g₀) = _
        simp only [← SchwartzMap.fourierTransformCLM_apply ℂ]  -- TODO: Remove need to specify `ℂ`
        ext ξ
        simp
  _ = (fourierTransform q f + fourierTransform q g) ξ := by simp [hfg', hf, hg]

theorem Lp.LpSchwartzMap.fourierTransform_smul {p : ℝ≥0∞} (q : ℝ≥0∞) (c : 𝕜)
    (f : LpSchwartzMap E p (volume : Measure V)) :
    fourierTransform q (c • f) = c • fourierTransform q f := by
  ext
  filter_upwards [coeFn_fourierTransform q f, coeFn_fourierTransform q (c • f),
    coeFn_smul c (fourierTransform q f : Lp E q volume)]
    with ξ hf hcf hcf'
  calc fourierTransform q (c • f) ξ
  _ = 𝓕 (c • f) ξ := hcf
  _ = (c • 𝓕 f) ξ := by
    refine congrFun ?_ ξ
    calc 𝓕 ⇑(c • f)
    _ = 𝓕 (c • ⇑f) := by
      refine Real.fourierIntegral_congr_ae ?_
      filter_upwards [coeFn_smul c (f : Lp E p volume)] with x h
      simpa using h
    _ = c • 𝓕 f := by
      refine induction_on f (fun f ↦ 𝓕 (c • f) = c • 𝓕 f) ?_ ?_
      · intro f₀ hf₀ h
        simp only [Pi.smul_def]
        rw [Real.fourierIntegral_congr_ae hf₀, Real.fourierIntegral_congr_ae (hf₀.const_smul c)]
        exact h
      · intro f₀
        change 𝓕 ⇑(c • f₀) = _
        simp only [← SchwartzMap.fourierTransformCLM_apply 𝕜]
        ext ξ
        simp
  _ = (c • fourierTransform q f) ξ := by simp [coe_smul, hcf', hf]

variable (𝕜 V E) in
/-- The Fourier transform as a linear map from Schwartz maps in `L^p` to Schwartz maps in `L^q`. -/
noncomputable def Lp.LpSchwartzMap.fourierTransformLM (p q : ℝ≥0∞) :
    LpSchwartzMap E p (volume : Measure V) →ₗ[𝕜] LpSchwartzMap E q (volume : Measure V) where
  toFun := fourierTransform q
  map_add' f g := fourierTransform_add q f g
  map_smul' c f := fourierTransform_smul q c f

theorem Lp.LpSchwartzMap.coeFn_fourierTransformLM {p q : ℝ≥0∞} :
    ⇑(fourierTransformLM 𝕜 V E p q) = fourierTransform q := rfl

variable (𝕜 V E) in
/-- Auxiliary to the definition of `Lp.fourierTransformCLM_one_top`. The Fourier transform as a
continuous linear map from the Schwartz subset of `L^1` to the Schwartz subset of `L^∞`. -/
noncomputable def Lp.LpSchwartzMap.fourierTransformCLM_one_top :
    LpSchwartzMap E 1 (volume : Measure V) →L[𝕜] LpSchwartzMap E ⊤ (volume : Measure V) :=
  { fourierTransformLM 𝕜 V E 1 ⊤ with
    cont := uniformContinuous_fourierTransform_one_top.continuous }

variable (𝕜 V F) in
/-- Auxiliary to the definition of `Lp.fourierTransformCLM_two_two`. The Fourier transform as a
continuous linear map from the Schwartz subset of `L^2` to the Schwartz subset of `L^2`. -/
noncomputable def Lp.LpSchwartzMap.fourierTransformCLM_two_two :
    LpSchwartzMap F 2 (volume : Measure V) →L[𝕜] LpSchwartzMap F 2 (volume : Measure V) :=
  { fourierTransformLM 𝕜 V F 2 2 with
    cont := uniformContinuous_fourierTransform_two_two.continuous }

theorem Lp.LpSchwartzMap.fourierTransformCLM_two_two_apply
    (f : LpSchwartzMap F 2 (volume : Measure V)) :
    LpSchwartzMap.fourierTransformCLM_two_two 𝕜 V F f = fourierTransform 2 f := rfl

variable (𝕜 V E) in
/-- The Fourier transform as a continuous linear map from `L^1` to `L^∞`. -/
noncomputable def Lp.fourierTransformCLM_one_top :
    Lp E 1 (volume : Measure V) →L[𝕜] Lp E ⊤ (volume : Measure V) :=
  .extend (LpSchwartzMap.subtypeL 𝕜 E ⊤ volume ∘L LpSchwartzMap.fourierTransformCLM_one_top 𝕜 V E)
    (LpSchwartzMap.subtypeL 𝕜 E 1 volume)
    (LpSchwartzMap.dense E ENNReal.one_ne_top volume).denseRange_val (isUniformInducing_val _)

variable (𝕜 V F) in
/-- The Fourier transform as a continuous linear map from `L^2` to `L^2`. -/
noncomputable def Lp.fourierTransformCLM_two_two :
    Lp F 2 (volume : Measure V) →L[𝕜] Lp F 2 (volume : Measure V) :=
  .extend (LpSchwartzMap.subtypeL 𝕜 F 2 volume ∘L LpSchwartzMap.fourierTransformCLM_two_two 𝕜 V F)
    (LpSchwartzMap.subtypeL 𝕜 F 2 volume)
    (LpSchwartzMap.dense F ENNReal.two_ne_top volume).denseRange_val (isUniformInducing_val _)

theorem Lp.fourierTransformCLM_two_two_apply_coe (f : LpSchwartzMap F 2 (volume : Measure V)) :
    fourierTransformCLM_two_two 𝕜 V F (f : Lp F 2 volume) = LpSchwartzMap.fourierTransform 2 f :=
  ContinuousLinearMap.extend_eq _ _ _ _ f

/-- Plancherel's theorem: The Fourier transform preserves the `L^2` norm. -/
theorem Lp.norm_fourierTransformCLM_two_two_apply (f : Lp F 2 (volume : Measure V)) :
    ‖fourierTransformCLM_two_two 𝕜 V F f‖ = ‖f‖ := by
  -- TODO: How does this manage to avoid specifying `P`?
  refine Dense.induction (LpSchwartzMap.dense F ENNReal.two_ne_top (volume : Measure V)) ?_
    (isClosed_eq (ContinuousLinearMap.continuous _).norm continuous_norm) f
  suffices ∀ f : LpSchwartzMap F 2 (volume : Measure V),
      ‖fourierTransformCLM_two_two 𝕜 V F f.val‖ = ‖f.val‖ by simpa using this
  intro f
  rw [fourierTransformCLM_two_two_apply_coe]
  simpa using LpSchwartzMap.norm_fourier_two_eq_norm_two f

-- TODO: Define `LinearIsometry(Equiv)`?

end LinearMap

end MeasureTheory
