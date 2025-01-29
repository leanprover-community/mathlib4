/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier transform on Schwartz functions

This file constructs the Fourier transform as a continuous linear map acting on Schwartz
functions, in `fourierTransformCLM`. It is also given as a continuous linear equiv, in
`fourierTransformCLE`.
-/

open Real MeasureTheory MeasureTheory.Measure Filter
open scoped FourierTransform ENNReal

namespace SchwartzMap

variable
  (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
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

end SchwartzMap


section Lp

open scoped SchwartzMap

variable {𝕜 𝕜' V E : Type*}

variable [NormedAddCommGroup E] [NormedAddCommGroup V] [NormedSpace ℂ E]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

-- TODO: Move to `Mathlib/Analysis/Fourier/FourierTransform.lean`?
-- TODO: Add to `simp`?
theorem Real.conj_fourierChar (x : ℝ) : starRingEnd ℂ (𝐞 x) = 𝐞 (-x) := by
  simp only [fourierChar, AddChar.coe_mk, mul_neg, Circle.exp_neg]
  exact (Circle.coe_inv_eq_conj _).symm

-- TODO: Rewrite for `VectorFourier.fourierIntegral`?
-- TODO: Move.
-- TODO: Is this useful?
-- Will it just require a lot of definitions if we try to avoid dropping down to integral?
theorem Real.fourierIntegral_congr_ae {f g : V → E} (h : f =ᵐ[volume] g) : 𝓕 f = 𝓕 g := by
  ext ξ
  refine integral_congr_ae ?_
  filter_upwards [h] with x h
  rw [h]

-- TODO: Move.
-- TODO: Adjust typeclasses?
theorem Real.star_fourierIntegral (f : V → ℂ) (ξ : V) :
    starRingEnd ℂ (𝓕 f ξ) = 𝓕 (fun x ↦ starRingEnd ℂ (f x)) (-ξ) := by
  simp only [fourierIntegral_eq]
  refine Eq.trans integral_conj.symm ?_
  simp [Circle.smul_def, conj_fourierChar]

theorem Real.fourierIntegral_star (f : V → ℂ) (ξ : V) :
    𝓕 (fun x ↦ starRingEnd ℂ (f x)) ξ = starRingEnd ℂ (𝓕 f (-ξ)) := by
  simp only [fourierIntegral_eq]
  refine Eq.trans ?_ integral_conj
  simp [Circle.smul_def, conj_fourierChar]

-- TODO: Move into `Mathlib/Analysis/Fourier/FourierTransform.lean`?
-- TODO: Check type classes for `V`.
-- TODO: Generalize to bilinear `L`?
theorem Real.integral_fourierTransform_mul_eq_integral_mul_fourierTransform {f g : V → ℂ}
    (hf_cont : Continuous f) (hf_int : Integrable f)
    (hg_cont : Continuous g) (hg_int : Integrable g) :
    ∫ w, 𝓕 f w * g w = ∫ w, f w * 𝓕 g w := by
  calc ∫ w, 𝓕 f w * g w
  _ = ∫ w, ∫ v, 𝐞 (-inner v w) • f v * g w := by simp [fourierIntegral_eq, integral_mul_right]
  _ = ∫ w, ∫ v, 𝐞 (-inner v w) • (f v * g w) := by
    simp only [Circle.smul_def, smul_eq_mul]
    refine congrArg (integral _) (funext fun w ↦ ?_)
    refine congrArg (integral _) (funext fun v ↦ ?_)
    ring
  _ = ∫ v, ∫ w, 𝐞 (-inner v w) • (f v * g w) := by
    symm
    refine integral_integral_swap ?_
    simp only [Function.uncurry_def]
    rw [← integrable_norm_iff]
    swap
    · refine Continuous.aestronglyMeasurable (.smul ?_ ?_)
      · exact .comp continuous_fourierChar continuous_inner.neg
      · exact .mul (hf_cont.comp continuous_fst) (hg_cont.comp continuous_snd)
    simp only [Circle.norm_smul, norm_mul]
    exact .prod_mul hf_int.norm hg_int.norm
  _ = ∫ v, ∫ w, f v * (𝐞 (-inner v w)) • g w := by
    simp only [Circle.smul_def, smul_eq_mul]
    refine congrArg (integral _) (funext fun w ↦ ?_)
    refine congrArg (integral _) (funext fun v ↦ ?_)
    ring
  _ = ∫ v, f v * ∫ w, 𝐞 (-inner v w) • g w := by simp [integral_mul_left]
  _ = ∫ (w : V), f w * 𝓕 g w := by simp [real_inner_comm, fourierIntegral_eq]

-- TODO: Generalize to `RCLike.innerProductSpace : InnerProductSpace 𝕜 𝕜`?
-- TODO: Generalize beyond `ℂ`?
/-- The Fourier transform preserves the L^2 norm. -/
theorem Real.integral_conj_mul_fourierIntegral_eq_integral_conj_mul {f g : V → ℂ}
    (hf_cont : Continuous f) (hf_int : Integrable f)
    (hf_cont_fourier : Continuous (𝓕 f)) (hf_int_fourier : Integrable (𝓕 f))
    (hg_cont : Continuous g) (hg_int : Integrable g) :
    ∫ ξ, starRingEnd ℂ (𝓕 f ξ) * 𝓕 g ξ = ∫ x, starRingEnd ℂ (f x) * g x := by
  -- Consider `∫ x, 𝓕 f x * g x` with `g x = starRingEnd ℂ (𝓕 f x)`.
  rw [← integral_fourierTransform_mul_eq_integral_mul_fourierTransform _ _ hg_cont hg_int]
  rotate_left
  · exact Complex.continuous_conj.comp hf_cont_fourier
  · exact (LinearIsometryEquiv.integrable_comp_iff Complex.conjLIE).mpr hf_int_fourier
  refine congrArg (integral _) (funext fun x ↦ ?_)
  rw [fourierIntegral_star]
  rw [← fourierIntegralInv_eq_fourierIntegral_neg]
  rw [Continuous.fourier_inversion hf_cont hf_int hf_int_fourier]

-- TODO: Is it useful to have this variant?
/-- The Fourier transform preserves the L^2 inner product. -/
theorem Real.integral_conj_mul_fourierIntegral_eq_integral_conj_mul' {f g : V → ℂ}
    (hf_cont : Continuous f) (hf_int : Integrable f)
    (hg_cont : Continuous g) (hg_int : Integrable g)
    (hg_cont_fourier : Continuous (𝓕 g)) (hg_int_fourier : Integrable (𝓕 g)) :
    ∫ ξ, starRingEnd ℂ (𝓕 f ξ) * 𝓕 g ξ = ∫ x, starRingEnd ℂ (f x) * g x := by
  -- Take conjugate of both sides.
  rw [← Complex.conjLIE.map_eq_iff]
  simp only [Complex.conjLIE_apply, ← integral_conj, map_mul, Complex.conj_conj]
  simp only [← mul_comm (starRingEnd ℂ _)]
  exact integral_conj_mul_fourierIntegral_eq_integral_conj_mul hg_cont hg_int hg_cont_fourier
    hg_int_fourier hf_cont hf_int

-- TODO: Possible to generalize beyond `ℂ`?
-- TODO: Provide eLpNorm version? Requires `Memℒp f 2`?
/-- Parseval's theorem: The Fourier transform preserves the L^2 norm. -/
theorem Real.integral_normSq_fourierIntegral_eq_integral_normSq {f : V → ℂ}
    (hf_cont : Continuous f) (hf_int : Integrable f)
    (hf_cont_fourier : Continuous (𝓕 f)) (hf_int_fourier : Integrable (𝓕 f)) :
    ∫ ξ, Complex.normSq (𝓕 f ξ) = ∫ x, Complex.normSq (f x) := by
  -- Switch to integral taking values in `ℂ`.
  rw [← Complex.ofRealLI.map_eq_iff]
  simp only [← LinearIsometry.integral_comp_comm]
  change ∫ ξ, (Complex.normSq (𝓕 f ξ) : ℂ) = ∫ x, (Complex.normSq (f x) : ℂ)
  simp only [Complex.normSq_eq_conj_mul_self]
  exact integral_conj_mul_fourierIntegral_eq_integral_conj_mul' hf_cont hf_int hf_cont hf_int
    hf_cont_fourier hf_int_fourier

-- TODO: Provide version using `eLpNorm _ 2`. Requires `Memℒp f 2`? `Memℒp (𝓕 f) 2`?
-- Wait until we know what we need it for.

-- TODO: Make more general? Don't require Continuous?
/-- Parseval's theorem for continuous functions in L^1 ∩ L^2. -/
theorem Real.eLpNorm_fourier_two_eq_eLpNorm_two {f : V → ℂ}
    (hf_cont : Continuous f) (hf_int : Integrable f) (hf_int2 : Memℒp f 2 volume)
    (hf_cont_fourier : Continuous (𝓕 f)) (hf_int_fourier : Integrable (𝓕 f))
    (hf_int2_fourier : Memℒp (𝓕 f) 2 volume) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  rw [Memℒp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.two_ne_top hf_int2,
    Memℒp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.two_ne_top hf_int2_fourier]
  refine congrArg (fun x ↦ ENNReal.ofReal (x ^ _)) ?_
  simp only [ENNReal.toReal_ofNat, rpow_two, ← Complex.normSq_eq_norm_sq]
  exact integral_normSq_fourierIntegral_eq_integral_normSq hf_cont hf_int hf_cont_fourier
      hf_int_fourier

theorem SchwartzMap.integral_normSq_fourierIntegral_eq_integral_normSq (f : 𝓢(V, ℂ)) :
    ∫ ξ, Complex.normSq (𝓕 f ξ) = ∫ x, Complex.normSq (f x) :=
  Real.integral_normSq_fourierIntegral_eq_integral_normSq f.continuous f.integrable
    f.continuous_fourier f.integrable_fourier

/-- Parseval's theorem for Schwartz functions. -/
theorem SchwartzMap.eLpNorm_fourier_two_eq_eLpNorm_two (f : 𝓢(V, ℂ)) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume :=
  Real.eLpNorm_fourier_two_eq_eLpNorm_two f.continuous f.integrable (f.memℒp 2 _)
    f.continuous_fourier f.integrable_fourier (f.memℒp_fourier 2 _)


-- TODO: Move.
noncomputable instance MeasureTheory.Lp.LpSchwartzMap.instCoeFun {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {μ : Measure V} : CoeFun (LpSchwartzMap E p μ) (fun _ ↦ V → E) where
  coe f := (((f : Lp E p μ) : V →ₘ[μ] E) : V → E)

/-- The Fourier transform of a function in `L^p` which has a representative in the Schwartz space is
a function in `L^q`. -/
theorem MeasureTheory.Lp.LpSchwartzMap.memℒp_fourierIntegral [CompleteSpace E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (q : ℝ≥0∞) [Fact (1 ≤ q)] (f : LpSchwartzMap (E := V) E p) :
    Memℒp (𝓕 f) q volume :=
  induction_on f (fun g ↦ Memℒp (𝓕 g) q volume)
    (fun g hfg h ↦ by
      simp only at h ⊢
      rw [Real.fourierIntegral_congr_ae hfg]  -- TODO: Check order.
      exact h)
    (fun g ↦ g.memℒp_fourier q volume)

section Fourier

variable [CompleteSpace E]

noncomputable def MeasureTheory.Lp.LpSchwartzMap.fourierTransform
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : LpSchwartzMap E p (volume : Measure V)) :
    LpSchwartzMap E q (volume : Measure V) where
  val := (memℒp_fourierIntegral q f).toLp
  property := by
    rcases f with ⟨f, hf⟩
    rw [mem_iff_ae] at hf ⊢
    revert hf
    refine Exists.imp' (SchwartzMap.fourierTransformCLE ℂ) fun f₀ hf₀ ↦ ?_
    simpa [Real.fourierIntegral_congr_ae hf₀] using Memℒp.coeFn_toLp _

theorem MeasureTheory.Lp.LpSchwartzMap.coeFn_fourierTransform
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : LpSchwartzMap E p (volume : Measure V)) :
    ⇑(fourierTransform q f) =ᵐ[volume] 𝓕 f := by
  simpa [fourierTransform] using Memℒp.coeFn_toLp _

theorem MeasureTheory.Lp.LpSchwartzMap.fourierTransform_add
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f g : LpSchwartzMap E p (volume : Measure V)) :
    fourierTransform q (f + g) = fourierTransform q f + fourierTransform q g := by
  ext
  filter_upwards [coeFn_fourierTransform q (f + g), coeFn_fourierTransform q f,
    coeFn_fourierTransform q g,
    AEEqFun.coeFn_add (α := V) (γ := E) (fourierTransform q f) (fourierTransform q g)]
    with ξ hfg hf hg hfg'
  calc fourierTransform q (f + g) ξ
  _ = 𝓕 (f + g) ξ := hfg
  _ = (𝓕 f + 𝓕 g) ξ := by
    refine congrFun ?_ ξ
    calc 𝓕 (f + g)
    _ = 𝓕 (⇑f + ⇑g) := by
      refine Real.fourierIntegral_congr_ae ?_
      filter_upwards [AEEqFun.coeFn_add (α := V) (γ := E) f g] with x h
      simpa using h
    _ = 𝓕 f + 𝓕 g := by
      refine induction_on₂ f g (fun f g ↦ 𝓕 (f + g) = 𝓕 f + 𝓕 g) ?_ ?_
      · intro f₀ g₀ hf₀ hg₀ h
        simp only [Pi.add_def]
        rw [Real.fourierIntegral_congr_ae hf₀, Real.fourierIntegral_congr_ae hg₀]
        rw [Real.fourierIntegral_congr_ae (.add hf₀ hg₀)]
        exact h
      · intro f₀ g₀
        change 𝓕 ⇑(f₀ + g₀) = _
        simp only [← SchwartzMap.fourierTransformCLM_apply ℂ]  -- TODO: Remove need to specify `ℂ`
        ext ξ
        simp
  _ = (fourierTransform q f + fourierTransform q g) ξ := by simp [hfg', hf, hg]

-- TODO: Eliminate `𝕜'`? `RCLike 𝕜'` comes from `SchwartzMap.fourierTransformCLM`.
variable [NormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]
  [RCLike 𝕜'] [NormedSpace 𝕜' E] [SMulCommClass ℂ 𝕜' E]

theorem MeasureTheory.Lp.LpSchwartzMap.fourierTransform_smul
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (c : 𝕜') (f : LpSchwartzMap E p (volume : Measure V)) :
    fourierTransform q (c • f) = c • fourierTransform q f := by
  ext
  filter_upwards [coeFn_fourierTransform q (c • f), coeFn_fourierTransform q f,
    coeFn_smul c (fourierTransform q f : Lp E q volume)]
    with ξ hcf hf hcf'
  calc fourierTransform q (c • f) ξ
  _ = 𝓕 (c • f) ξ := hcf
  _ = (c • 𝓕 f) ξ := by
    refine congrFun ?_ ξ
    calc 𝓕 ⇑(c • f)
    _ = 𝓕 (c • ⇑f) := by
      refine Real.fourierIntegral_congr_ae ?_
      filter_upwards [coeFn_smul c (f : Lp E p volume)] with x h
      simpa [coe_smul] using h
    _ = c • 𝓕 f := by
      refine induction_on f (fun f ↦ 𝓕 (c • f) = c • 𝓕 f) ?_ ?_
      · intro f₀ hf₀ h
        simp only [Pi.smul_def]
        rw [Real.fourierIntegral_congr_ae hf₀, Real.fourierIntegral_congr_ae (hf₀.const_smul c)]
        exact h
      · intro f₀
        change 𝓕 ⇑(c • f₀) = _
        simp only [← SchwartzMap.fourierTransformCLM_apply 𝕜']
        ext ξ
        simp
  _ = (c • fourierTransform q f) ξ := by simp [coe_smul, hcf', hf]

variable (𝕜' V E) in
/-- Fourier transform as a linear map from Schwartz maps in `L^p` to Schwartz maps in `L^q`. -/
noncomputable def MeasureTheory.Lp.LpSchwartzMap.fourierTransformLM
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    LpSchwartzMap E p (volume : Measure V) →ₗ[𝕜'] LpSchwartzMap E q (volume : Measure V) where
  toFun := fourierTransform q
  map_add' f g := fourierTransform_add q f g
  map_smul' c f := fourierTransform_smul q c f

theorem MeasureTheory.Lp.LpSchwartzMap.coeFn_fourierTransformLM
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ⇑(fourierTransformLM 𝕜' V E p q) = fourierTransform q := rfl

-- TODO: Generalize CLM to `L^p` and `L^q` with `1 ≤ p ≤ 2`.

theorem MeasureTheory.Lp.LpSchwartzMap.uniformContinuous_fourierTransform_one_top :
    UniformContinuous (fun f : LpSchwartzMap (E := V) E 1 ↦ fourierTransform ⊤ f) := by
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
      · intro f₀ g₀ hf hg h
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

theorem MeasureTheory.Lp.LpSchwartzMap.uniformContinuous_fourierTransform_two_two :
    UniformContinuous (fun f : LpSchwartzMap (E := V) E 2 ↦ fourierTransform 2 f) := by
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
    · intro f₀ g₀ hf hg h
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
    filter_upwards [AEEqFun.coeFn_sub (α := V) (γ := E) f g] with x h
    simpa using h.symm
  _ = eLpNorm (f - g) 2 volume := by
    refine induction_on (f - g) (fun r ↦ eLpNorm (𝓕 r) 2 volume = eLpNorm r 2 volume) ?_ ?_
    · intro r hr h
      rw [Real.fourierIntegral_congr_ae hr, eLpNorm_congr_ae hr]
      exact h
    -- TODO: Just need to generalize beyond `ℂ`?
    sorry
    -- exact SchwartzMap.eLpNorm_fourier_two_eq_eLpNorm_two
    -- intro r
    -- exact r.eLpNorm_fourier_two_eq_eLpNorm_two
  _ = eLpNorm (⇑f - ⇑g) 2 volume := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [AEEqFun.coeFn_sub (α := V) (γ := E) f g] with x h
    simpa using h
  _ < ε := h

noncomputable def MeasureTheory.Lp.LpSchwartzMap.fourierTransformCLM_one_top :
    LpSchwartzMap E 1 (volume : Measure V) →L[𝕜'] LpSchwartzMap E ⊤ (volume : Measure V) :=
  { fourierTransformLM 𝕜' V E 1 ⊤ with
    cont := by
      simpa [coeFn_fourierTransformLM] using uniformContinuous_fourierTransform_one_top.continuous
  }

noncomputable def MeasureTheory.Lp.LpSchwartzMap.fourierTransformCLM_two_two :
    LpSchwartzMap E 2 (volume : Measure V) →L[𝕜'] LpSchwartzMap E 2 (volume : Measure V) :=
  { fourierTransformLM 𝕜' V E 2 2 with
    cont := by
      simpa [coeFn_fourierTransformLM] using uniformContinuous_fourierTransform_two_two.continuous
  }

end Fourier

section Extend

-- TODO: Eliminate `𝕜'`? `RCLike 𝕜'` comes from `SchwartzMap.fourierTransformCLM`.
variable [NormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]
  [RCLike 𝕜'] [NormedSpace 𝕜' E] [SMulCommClass ℂ 𝕜' E]

variable (𝕜 E) in
def MeasureTheory.Lp.LpSchwartzMap.subtypeL (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure V) :
    LpSchwartzMap E p μ →L[𝕜] Lp E p μ where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_subtype_val

@[simp]
theorem MeasureTheory.Lp.LpSchwartzMap.coeFn_subtypeL (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure V) :
    ⇑(subtypeL 𝕜 E p μ) = Subtype.val := rfl

variable [CompleteSpace E]

noncomputable def MeasureTheory.Lp.fourierTransformCLM_one_top :
    Lp E 1 (volume : Measure V) →L[𝕜'] Lp E ⊤ (volume : Measure V) :=
  .extend
    (LpSchwartzMap.subtypeL 𝕜' E ⊤ volume ∘L
      LpSchwartzMap.fourierTransformCLM_one_top (𝕜' := 𝕜') (V := V) (E := E))
    (LpSchwartzMap.subtypeL 𝕜' E 1 volume)
    (by
      simp only [LpSchwartzMap.coeFn_subtypeL, denseRange_subtype_val, SetLike.setOf_mem_eq]
      exact LpSchwartzMap.dense E ENNReal.one_ne_top volume)
    ((isUniformInducing_iff Subtype.val).mpr rfl)

noncomputable def MeasureTheory.Lp.fourierTransformCLM_two_two :
    Lp E 2 (volume : Measure V) →L[𝕜'] Lp E 2 (volume : Measure V) :=
  .extend
    (LpSchwartzMap.subtypeL 𝕜' E 2 volume ∘L
      LpSchwartzMap.fourierTransformCLM_two_two (𝕜' := 𝕜') (V := V) (E := E))
    (LpSchwartzMap.subtypeL 𝕜' E 2 volume)
    (by
      simp only [LpSchwartzMap.coeFn_subtypeL, denseRange_subtype_val, SetLike.setOf_mem_eq]
      exact LpSchwartzMap.dense E ENNReal.two_ne_top volume)
    ((isUniformInducing_iff Subtype.val).mpr rfl)

end Extend

end Lp
