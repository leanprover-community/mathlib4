/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
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

-- TODO: Move to `Mathlib/Analysis/Fourier/FourierTransform.lean`?
-- TODO: Add to `simp`?
theorem _root_.Real.conj_fourierChar (x : ℝ) : starRingEnd ℂ (𝐞 x) = 𝐞 (-x) := by
  simp only [Real.fourierChar, AddChar.coe_mk, mul_neg, Circle.exp_neg]
  exact (Circle.coe_inv_eq_conj _).symm

-- TODO: Move.
-- TODO: Adjust typeclasses?
theorem _root_.Real.star_fourierIntegral (f : V → ℂ) (ξ : V) :
    starRingEnd ℂ (𝓕 f ξ) = 𝓕 (fun x ↦ starRingEnd ℂ (f x)) (-ξ) := by
  simp only [fourierIntegral_eq]
  refine Eq.trans integral_conj.symm ?_
  simp [Circle.smul_def, Real.conj_fourierChar]

theorem _root_.Real.fourierIntegral_star (f : V → ℂ) (ξ : V) :
    𝓕 (fun x ↦ starRingEnd ℂ (f x)) ξ = starRingEnd ℂ (𝓕 f (-ξ)) := by
  simp only [fourierIntegral_eq]
  refine Eq.trans ?_ integral_conj
  simp [Circle.smul_def, Real.conj_fourierChar]

-- TODO: Move into `Mathlib/Analysis/Fourier/FourierTransform.lean`?
-- TODO: Check type classes for `V`.
-- TODO: Generalize to bilinear `L`?
theorem _root_.Real.integral_fourierTransform_mul_eq_integral_mul_fourierTransform {f g : V → ℂ}
    (hf_cont : Continuous f) (hf_int : Integrable f)
    (hg_cont : Continuous g) (hg_int : Integrable g) :
    ∫ w, 𝓕 f w * g w = ∫ w, f w * 𝓕 g w := by
  calc ∫ w, 𝓕 f w * g w
  _ = ∫ w, ∫ v, 𝐞 (-inner v w) • f v * g w := by simp [Real.fourierIntegral_eq, integral_mul_right]
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
      · exact .comp Real.continuous_fourierChar continuous_inner.neg
      · exact .mul (hf_cont.comp continuous_fst) (hg_cont.comp continuous_snd)
    simp only [Circle.norm_smul, norm_mul]
    exact .prod_mul hf_int.norm hg_int.norm
  _ = ∫ v, ∫ w, f v * (𝐞 (-inner v w)) • g w := by
    simp only [Circle.smul_def, smul_eq_mul]
    refine congrArg (integral _) (funext fun w ↦ ?_)
    refine congrArg (integral _) (funext fun v ↦ ?_)
    ring
  _ = ∫ v, f v * ∫ w, 𝐞 (-inner v w) • g w := by simp [integral_mul_left]
  _ = ∫ (w : V), f w * 𝓕 g w := by simp [real_inner_comm, Real.fourierIntegral_eq]

-- TODO: Generalize to `RCLike.innerProductSpace : InnerProductSpace 𝕜 𝕜`?
-- TODO: Generalize beyond `ℂ`?
/-- The Fourier transform preserves the L^2 norm. -/
theorem _root_.Real.integral_conj_mul_fourierIntegral_eq_integral_conj_mul {f g : V → ℂ}
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
  rw [Real.fourierIntegral_star]
  rw [← Real.fourierIntegralInv_eq_fourierIntegral_neg]
  rw [Continuous.fourier_inversion hf_cont hf_int hf_int_fourier]

-- TODO: Is it useful to have this variant?
/-- The Fourier transform preserves the L^2 inner product. -/
theorem _root_.Real.integral_conj_mul_fourierIntegral_eq_integral_conj_mul' {f g : V → ℂ}
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
theorem _root_.Real.integral_normSq_fourierIntegral_eq_integral_normSq {f : V → ℂ}
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

theorem integral_normSq_fourierIntegral_eq_integral_normSq (f : 𝓢(V, ℂ)) :
    ∫ ξ, Complex.normSq (𝓕 f ξ) = ∫ x, Complex.normSq (f x) :=
  Real.integral_normSq_fourierIntegral_eq_integral_normSq f.continuous f.integrable
    f.continuous_fourier f.integrable_fourier

-- TODO: Provide version using `eLpNorm _ 2`. Requires `Memℒp f 2`? `Memℒp (𝓕 f) 2`?
-- Wait until we know what we need it for.

-- TODO: Make more general? Don't require Continuous?
/-- Parseval's theorem for continuous functions in L^1 ∩ L^2. -/
theorem _root_.Real.eLpNorm_fourier_two_eq_eLpNorm_two {f : V → ℂ}
    (hf_cont : Continuous f) (hf_int : Integrable f) (hf_mem : Memℒp f 2 volume)
    (hf_cont_fourier : Continuous (𝓕 f)) (hf_int_fourier : Integrable (𝓕 f))
    (hf_mem_fourier : Memℒp (𝓕 f) 2 volume) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  rw [Memℒp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.two_ne_top hf_mem,
    Memℒp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.two_ne_top hf_mem_fourier]
  refine congrArg (fun x ↦ ENNReal.ofReal (x ^ _)) ?_
  simp only [ENNReal.toReal_ofNat, rpow_two, ← Complex.normSq_eq_norm_sq]
  exact Real.integral_normSq_fourierIntegral_eq_integral_normSq hf_cont hf_int hf_cont_fourier
      hf_int_fourier

/-- Parseval's theorem for Schwartz functions. -/
theorem eLpNorm_fourier_two_eq_eLpNorm_two (f : 𝓢(V, ℂ)) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume :=
  Real.eLpNorm_fourier_two_eq_eLpNorm_two f.continuous f.integrable (f.memℒp 2 _)
    f.continuous_fourier f.integrable_fourier (f.memℒp_fourier 2 _)

/-- Parseval's theorem for Schwartz functions: The Fourier transform preserves the L^2 norm. -/
theorem eLpNorm_fourier_two_lt_top (f : 𝓢(V, ℂ)) : eLpNorm (𝓕 f) 2 volume < ⊤ :=
  (memℒp_fourier f 2 volume).eLpNorm_lt_top

/-- Parseval's theorem for Schwartz functions: The Fourier transform preserves the L^2 norm. -/
theorem eLpNorm_two_lt_top (f : 𝓢(V, ℂ)) : eLpNorm f 2 volume < ⊤ :=
  (memℒp f 2 volume).eLpNorm_lt_top

-- TODO: Move.
-- TODO: Typeclasses.
omit [CompleteSpace E]
theorem _root_.Real.fourierIntegral_congr_ae {f g : V → E} (h : f =ᵐ[volume] g) : 𝓕 f = 𝓕 g := by
  ext ξ
  refine integral_congr_ae ?_
  filter_upwards [h] with x h
  rw [h]

-- TODO: Move.
noncomputable instance _root_.MeasureTheory.Lp.LpSchwartzMap.instCoeFun {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {μ : Measure V} : CoeFun (MeasureTheory.Lp.LpSchwartzMap E p μ) (fun _ ↦ V → E) where
  coe f := (((f : Lp E p μ) : V →ₘ[μ] E) : V → E)

/-- The Fourier transform of a function in L^p that has a representative in the Schwartz space is a
function in L^q. -/
theorem _root_.MeasureTheory.Lp.LpSchwartzMap.memℒp_fourierTransform [CompleteSpace E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (q : ℝ≥0∞) [Fact (1 ≤ q)] (f : Lp.LpSchwartzMap (E := V) E p) :
    Memℒp (𝓕 f) q volume :=
  Lp.LpSchwartzMap.induction_on f (fun f ↦ Memℒp (𝓕 f) q volume)
    (fun g h ↦ by simpa [Real.fourierIntegral_congr_ae h] using g.memℒp_fourier q _)

/-- The Fourier transform of a function in L^p that has a representative in the Schwartz space is a
function in L^q. -/
theorem _root_.MeasureTheory.Lp.LpSchwartzMap.fourierTransform_mem_LpSchwartzMap [CompleteSpace E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : Lp.LpSchwartzMap E p (volume : Measure V)) :
    (Lp.LpSchwartzMap.memℒp_fourierTransform q f).toLp ∈ Lp.LpSchwartzMap E q volume := by
  -- TODO: Use `Lp.LpSchwartzMap.induction_on`? Need `Lp.LpSchwartzMap.induction_memℒp`?
  obtain ⟨f, hf⟩ := f
  rw [Lp.LpSchwartzMap.mem_iff_ae] at hf ⊢
  obtain ⟨g, hg⟩ := hf
  use SchwartzMap.fourierTransformCLE ℂ g
  simp only [fourierTransformCLE_apply]
  rw [Real.fourierIntegral_congr_ae hg]
  symm
  exact Memℒp.coeFn_toLp _

noncomputable def _root_.MeasureTheory.Lp.LpSchwartzMap.fourierTransform [CompleteSpace E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : Lp.LpSchwartzMap E p (volume : Measure V)) : Lp.LpSchwartzMap E q (volume : Measure V) :=
  ⟨_, Lp.LpSchwartzMap.fourierTransform_mem_LpSchwartzMap q f⟩

theorem _root_.MeasureTheory.Lp.LpSchwartzMap.coeFn_fourierTransform [CompleteSpace E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : Lp.LpSchwartzMap E p (volume : Measure V)) :
    ⇑(Lp.LpSchwartzMap.fourierTransform q f) =ᵐ[volume] 𝓕 f := by
  simpa [Lp.LpSchwartzMap.fourierTransform] using Memℒp.coeFn_toLp _

theorem _root_.MeasureTheory.Lp.LpSchwartzMap.uniformContinuous_fourierTransform_two :
    UniformContinuous (Lp.LpSchwartzMap.fourierTransform 2 :
      Lp.LpSchwartzMap ℂ 2 (volume : Measure V) → Lp.LpSchwartzMap ℂ 2 (volume : Measure V)) := by
  rw [EMetric.uniformContinuous_iff]
  intro ε hε
  simp only [Subtype.edist_eq, Lp.edist_def]
  use ε, hε
  intro f g h
  calc
  _ = eLpNorm (𝓕 f - 𝓕 g) 2 volume := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.LpSchwartzMap.coeFn_fourierTransform 2 f,
      Lp.LpSchwartzMap.coeFn_fourierTransform 2 g] with x h₁ h₂
    simp [h₁, h₂]
  _ = eLpNorm (𝓕 (⇑f - ⇑g)) 2 volume := by
    refine congrArg (eLpNorm · 2 volume) ?_
    refine Lp.LpSchwartzMap.induction_on₂ f g (fun f g ↦ 𝓕 f - 𝓕 g = 𝓕 (f - g)) ?_
    intro f₀ g₀ hf hg
    ext x
    simp only [Pi.sub_apply]
    rw [Real.fourierIntegral_congr_ae hf, Real.fourierIntegral_congr_ae hg]
    have : SchwartzMap.fourierTransformCLE ℂ f₀ x - SchwartzMap.fourierTransformCLE ℂ g₀ x =
        SchwartzMap.fourierTransformCLE ℂ (f₀ - g₀) x := by simp
    simp only [fourierTransformCLE_apply] at this
    refine Eq.trans this ?_
    refine congrFun ?_ x
    refine Real.fourierIntegral_congr_ae ?_
    filter_upwards [hf, hg] with x h₁ h₂
    simp [h₁, h₂]
  _ = eLpNorm (𝓕 (f - g)) 2 volume := by
    refine congrArg (eLpNorm · 2 volume) ?_
    refine Real.fourierIntegral_congr_ae ?_
    filter_upwards [AEEqFun.coeFn_sub (f : V →ₘ[volume] ℂ) g] with x h
    simp [h]
  _ = eLpNorm (f - g) 2 volume := by
    refine Lp.LpSchwartzMap.induction_on (f - g)
      (fun r ↦ eLpNorm (𝓕 r) 2 volume = eLpNorm r 2 volume) ?_
    intro r hr
    rw [Real.fourierIntegral_congr_ae hr, eLpNorm_congr_ae hr]
    exact r.eLpNorm_fourier_two_eq_eLpNorm_two
  _ = eLpNorm (⇑f - ⇑g) 2 volume := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [AEEqFun.coeFn_sub (f : V →ₘ[volume] ℂ) g] with x h
    simp [h]
  _ < ε := h

end SchwartzMap
