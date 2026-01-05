/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier transform on Schwartz functions

This file constructs the Fourier transform as a continuous linear map acting on Schwartz
functions, in `fourierTransformCLM`. It is also given as a continuous linear equiv, in
`fourierTransformCLE`.
-/

@[expose] public section

open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace

noncomputable section

namespace SchwartzMap

variable
  (𝕜 : Type*) [RCLike 𝕜]
  {W : Type*} [NormedAddCommGroup W]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section definition

/-- The Fourier transform on a real inner product space, as a continuous linear map on the
Schwartz space. -/
def fourierTransformCLM : 𝓢(V, E) →L[𝕜] 𝓢(V, E) := by
  refine mkCLM ((𝓕 : (V → E) → (V → E)) ·) ?_ ?_ ?_ ?_
  · intro f g x
    simp only [fourier_eq, add_apply, smul_add]
    rw [integral_add]
    · exact (fourierIntegral_convergent_iff _).2 f.integrable
    · exact (fourierIntegral_convergent_iff _).2 g.integrable
  · intro c f x
    simp only [fourier_eq, smul_apply, smul_comm _ c, integral_smul, RingHom.id_apply]
  · intro f
    exact Real.contDiff_fourier (fun n _ ↦ integrable_pow_mul volume f n)
  · rintro ⟨k, n⟩
    refine ⟨Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1),
       (2 * π) ^ n * (2 * ↑n + 2) ^ k * (Finset.range (n + 1) ×ˢ Finset.range (k + 1)).card
         * 2 ^ integrablePower (volume : Measure V) *
         (∫ (x : V), (1 + ‖x‖) ^ (- (integrablePower (volume : Measure V) : ℝ))) * 2,
       ⟨by positivity, fun f x ↦ ?_⟩⟩
    apply (pow_mul_norm_iteratedFDeriv_fourier_le (f.smooth ⊤)
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
      gcongr with p hp
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
          lia
        apply Finset.le_sup this (f := fun p ↦ SchwartzMap.seminorm 𝕜 p.1 p.2 (E := V) (F := E))
    _ = _ := by simp [mul_assoc]

instance instFourierTransform : FourierTransform 𝓢(V, E) 𝓢(V, E) where
  fourier f := fourierTransformCLM ℂ f

lemma fourier_coe (f : 𝓢(V, E)) : 𝓕 f = 𝓕 (f : V → E) := rfl

instance instFourierModule : FourierModule 𝕜 𝓢(V, E) 𝓢(V, E) where
  fourier_add := ContinuousLinearMap.map_add _
  fourier_smul := (fourierTransformCLM 𝕜).map_smul

@[simp]
theorem fourierTransformCLM_apply (f : 𝓢(V, E)) :
    fourierTransformCLM 𝕜 f = 𝓕 f := rfl

instance instFourierTransformInv : FourierTransformInv 𝓢(V, E) 𝓢(V, E) where
  fourierInv := (compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := V)))
      ∘L (fourierTransformCLM ℂ)

lemma fourierInv_coe (f : 𝓢(V, E)) :
    𝓕⁻ f = 𝓕⁻ (f : V → E) := by
  ext x
  exact (fourierInv_eq_fourier_neg f x).symm

instance instFourierInvModule : FourierInvModule 𝕜 𝓢(V, E) 𝓢(V, E) where
  fourierInv_add := ContinuousLinearMap.map_add _
  fourierInv_smul := ((compCLMOfContinuousLinearEquiv 𝕜 (D := V) (E := V) (F := E)
    (LinearIsometryEquiv.neg ℝ (E := V))) ∘L (fourierTransformCLM 𝕜)).map_smul

variable [CompleteSpace E]

instance instFourierPair : FourierPair 𝓢(V, E) 𝓢(V, E) where
  fourierInv_fourier_eq := by
    intro f
    ext x
    rw [fourierInv_coe, fourier_coe, f.continuous.fourierInv_fourier_eq f.integrable
      (𝓕 f).integrable]

instance instFourierInvPair : FourierInvPair 𝓢(V, E) 𝓢(V, E) where
  fourier_fourierInv_eq := by
    intro f
    ext x
    rw [fourier_coe, fourierInv_coe, f.continuous.fourier_fourierInv_eq f.integrable
      (𝓕 f).integrable]

@[deprecated (since := "2025-11-13")]
alias fourier_inversion := FourierTransform.fourierInv_fourier_eq

@[deprecated (since := "2025-11-13")]
alias fourier_inversion_inv := FourierTransform.fourier_fourierInv_eq

/-- The Fourier transform on a real inner product space, as a continuous linear equiv on the
Schwartz space. -/
def fourierTransformCLE : 𝓢(V, E) ≃L[𝕜] 𝓢(V, E) where
  __ := FourierTransform.fourierEquiv 𝕜 𝓢(V, E) 𝓢(V, E)
  continuous_toFun := (fourierTransformCLM 𝕜).continuous
  continuous_invFun := ContinuousLinearMap.continuous _

@[simp]
lemma fourierTransformCLE_apply (f : 𝓢(V, E)) : fourierTransformCLE 𝕜 f = 𝓕 f := rfl

@[simp]
lemma fourierTransformCLE_symm_apply (f : 𝓢(V, E)) : (fourierTransformCLE 𝕜).symm f = 𝓕⁻ f := rfl

end definition

section eval

variable {𝕜' : Type*} [NormedField 𝕜']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace 𝕜' G] [SMulCommClass ℝ 𝕜' G]

variable (𝕜') in
theorem fourier_evalCLM_eq (f : 𝓢(V, F →L[ℝ] G)) (m : F) :
    𝓕 (SchwartzMap.evalCLM 𝕜' F G m f) = SchwartzMap.evalCLM 𝕜' F G m (𝓕 f) := by
  ext x
  exact (fourier_continuousLinearMap_apply f.integrable).symm

end eval

section fubini

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

variable [CompleteSpace E] [CompleteSpace F]

/-- The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint.

Version where the multiplication is replaced by a general bilinear form `M`. -/
theorem integral_bilin_fourier_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (g ξ) = ∫ x, M (f x) (𝓕 g x) := by
  simpa using VectorFourier.integral_bilin_fourierIntegral_eq_flip M (L := innerₗ V)
    continuous_fourierChar continuous_inner f.integrable g.integrable

@[deprecated (since := "2025-11-16")]
alias integral_bilin_fourierIntegral_eq := integral_bilin_fourier_eq

/-- The Fourier transform satisfies `∫ 𝓕 f • g = ∫ f • 𝓕 g`, i.e., it is self-adjoint. -/
theorem integral_fourier_smul_eq (f : 𝓢(V, ℂ)) (g : 𝓢(V, F)) :
    ∫ ξ, 𝓕 f ξ • g ξ = ∫ x, f x • 𝓕 g x :=
  integral_bilin_fourier_eq f g (ContinuousLinearMap.lsmul ℂ ℂ)

/-- The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint. -/
theorem integral_fourier_mul_eq (f : 𝓢(V, ℂ)) (g : 𝓢(V, ℂ)) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x :=
  integral_bilin_fourier_eq f g (ContinuousLinearMap.mul ℂ ℂ)

/-- The inverse Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint.

Version where the multiplication is replaced by a general bilinear form `M`. -/
theorem integral_bilin_fourierInv_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕⁻ f ξ) (g ξ) = ∫ x, M (f x) (𝓕⁻ g x) := by
  convert (integral_bilin_fourier_eq (𝓕⁻ f) (𝓕⁻ g) M).symm
  · exact (FourierTransform.fourier_fourierInv_eq g).symm
  · exact (FourierTransform.fourier_fourierInv_eq f).symm

/-- The inverse Fourier transform satisfies `∫ 𝓕 f • g = ∫ f • 𝓕 g`, i.e., it is self-adjoint. -/
theorem integral_fourierInv_smul_eq (f : 𝓢(V, ℂ)) (g : 𝓢(V, F)) :
    ∫ ξ, 𝓕⁻ f ξ • g ξ = ∫ x, f x • 𝓕⁻ g x :=
  integral_bilin_fourierInv_eq f g (ContinuousLinearMap.lsmul ℂ ℂ)

/-- The inverse Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint. -/
theorem integral_fourierInv_mul_eq (f : 𝓢(V, ℂ)) (g : 𝓢(V, ℂ)) :
    ∫ ξ, 𝓕⁻ f ξ * g ξ = ∫ x, f x * 𝓕⁻ g x :=
  integral_bilin_fourierInv_eq f g (ContinuousLinearMap.mul ℂ ℂ)

theorem integral_sesq_fourier_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L⋆[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (g ξ) = ∫ x, M (f x) (𝓕⁻ g x) := by
  simpa [fourierInv_coe] using VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip M
    (L := innerₗ V) continuous_fourierChar continuous_inner f.integrable g.integrable

@[deprecated (since := "2025-11-16")]
alias integral_sesq_fourierIntegral_eq := integral_sesq_fourier_eq

/-- Plancherel's theorem for Schwartz functions.

Version where the multiplication is replaced by a general bilinear form `M`. -/
theorem integral_sesq_fourier_fourier (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L⋆[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (𝓕 g ξ) = ∫ x, M (f x) (g x) := by
  simpa using integral_sesq_fourier_eq f (𝓕 g) M

end fubini

section deriv

open ContinuousLinearMap
open scoped ContDiff

variable [NormedSpace ℝ W] (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E)

def fourierSMulRightCLM : 𝓢(V, E) →L[ℂ] 𝓢(V, W →L[ℝ] E) :=
  mkCLM (VectorFourier.fourierSMulRight L ·) (by intros; ext; simp) (by
    intro c g x
    ext v
    simp only [VectorFourier.fourierSMulRight_apply, smul_apply, neg_smul, RingHom.id_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_neg, neg_inj]
    calc
      _ = (L x) v • (2 * π * Complex.I) • c • g x := by rw [smul_comm]
      _ = (L x) v • c • (2 * π * Complex.I) • g x := by congr 1; rw [smul_comm]
      _ = c • (L x) v • (2 * π * Complex.I) • g x := by rw [smul_comm]
      _ = _ := by congr 1; rw [smul_comm]) (by
    intro f
    unfold VectorFourier.fourierSMulRight
    fun_prop) (by
    intro ⟨k, n⟩
    use {(k + 1, n), (k, n - 1)}, 4 * π * ‖L‖ * (max 1 n), by positivity
    intro f x
    calc
      _ = ‖x‖ ^ k * (2 * π * ‖iteratedFDeriv ℝ n (fun x ↦ (L x).smulRight (f x)) x‖) := by
        congr 1
        unfold VectorFourier.fourierSMulRight
        have : ContDiffAt ℝ n f x := f.contDiffAt n
        rw [iteratedFDeriv_const_smul_apply' (by fun_prop), norm_smul]
        have : 0 ≤ π := by positivity
        simp [this]
      _ = 2 * π * ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x ↦ (L x).smulRight (f x)) x‖ := by grind
      _ ≤ 2 * π * ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i) *
          ‖iteratedFDeriv ℝ i L x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
        gcongr 1
        exact norm_iteratedFDeriv_le_of_bilinear_of_le_one (smulRightL ℝ W E)
          (by fun_prop) (f.smooth ⊤) x (ENat.LEInfty.out) norm_smulRightL_le
      _ ≤ 2 * π * ‖x‖ ^ k *
          (‖L x‖ * ‖iteratedFDeriv ℝ n f x‖ + n * ‖L‖ * ‖iteratedFDeriv ℝ (n - 1) f x‖) := by
        gcongr 1
        rw [Finset.sum_range_succ', add_comm]
        simp only [Nat.choose_zero_right, Nat.cast_one, norm_iteratedFDeriv_zero, one_mul,
          Nat.sub_zero, add_le_add_iff_left]
        by_cases! h : n = 0
        · simp only [h, Finset.range_zero, Nat.choose_zero_succ, CharP.cast_eq_zero, zero_mul,
          Finset.sum_const_zero]
          positivity
        · obtain ⟨n', hn'⟩ : ∃ n', n' + 1 = n := by simpa using Nat.zero_lt_of_ne_zero h
          have : ∑ k ∈ Finset.range n',
              (((n' + 1).choose (k + 1 + 1)) : ℝ) * ‖iteratedFDeriv ℝ (k + 1 + 1) L x‖ *
              ‖iteratedFDeriv ℝ (n' + 1 - (k + 1 + 1)) f x‖ = 0 := by
            apply Finset.sum_eq_zero
            intro n₂ hn₂
            simp only [mul_eq_zero, Nat.cast_eq_zero, norm_eq_zero]
            left; right
            simp [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_const]
          rw [← hn', Finset.sum_range_succ', this]
          simp only [zero_add, Nat.choose_one_right, Nat.cast_add, Nat.cast_one, Nat.reduceAdd,
            Nat.add_one_sub_one, ge_iff_le]
          gcongr
          sorry
      _ = 2 * π * ‖x‖ ^ k * ‖L x‖ * ‖iteratedFDeriv ℝ n (⇑f) x‖ +
            2 * π * ‖x‖ ^ k * ↑n * ‖L‖ * ‖iteratedFDeriv ℝ (n - 1) (⇑f) x‖ := by ring
      _ ≤ 2 * π * ‖L‖ * 1 * (SchwartzMap.seminorm ℂ (k + 1) n) f +
            2 * π * ‖L‖ * n * (SchwartzMap.seminorm ℂ k (n - 1) f) := by
        apply add_le_add
        · grw [le_opNorm]
          simp only [mul_one]
          move_mul [2, π, ‖L‖, ‖L‖]
          gcongr
          have : ‖x‖ ^ k * ‖x‖ = ‖x‖ ^ (k + 1) := by ring
          rw [this]
          exact le_seminorm ℂ (k + 1) n f x
        · move_mul [2, π, (n : ℝ), ‖L‖]
          gcongr
          exact le_seminorm ℂ k (n - 1) f x
      _ ≤ 2 * π * ‖L‖ * max 1 n *
          max ((SchwartzMap.seminorm ℂ (k + 1) n) f) ((SchwartzMap.seminorm ℂ k (n - 1)) f) +
          2 * π * ‖L‖ * max 1 n *
          max ((SchwartzMap.seminorm ℂ (k + 1) n) f) ((SchwartzMap.seminorm ℂ k (n - 1)) f) := by
        apply add_le_add
        all_goals {gcongr; all_goals simp}
      _ = _ := by
        simp only [Finset.sup_insert, schwartzSeminormFamily_apply, Finset.sup_singleton,
          Seminorm.coe_sup, Pi.sup_apply]
        ring)

@[simp]
theorem fourierSMulRightCLM_apply_apply (f : 𝓢(V, E)) (x : V) :
    fourierSMulRightCLM L f x = -(2 * π * Complex.I) • (L x).smulRight (f x) := rfl

theorem fderivCLM_fourier_eq (f : 𝓢(V, E)) :
    fderivCLM 𝕜 V E (𝓕 f) = 𝓕 (fourierSMulRightCLM (innerSL ℝ) f) := by
  ext1 x
  calc
    _ = fderiv ℝ (𝓕 (f : V → E)) x := by simp [fourier_coe]
    _ = 𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) (f : V → E)) x := by
      rw [Real.fderiv_fourier f.integrable]
      convert f.integrable_pow_mul volume 1
      simp

theorem fourier_fderivCLM_eq (f : 𝓢(V, E)) :
    𝓕 (fderivCLM 𝕜 V E f) = fourierSMulRightCLM (-innerSL ℝ) (𝓕 f) := by
  ext1 x
  change 𝓕 (fderiv ℝ (f : V → E)) x = VectorFourier.fourierSMulRight (-innerSL ℝ) (𝓕 (f : V → E)) x
  rw [Real.fourier_fderiv f.integrable f.differentiable (fderivCLM ℝ V E f).integrable]

open LineDeriv

theorem lineDerivOp_fourier_eq (f : 𝓢(V, E)) (m : V) :
    ∂_{m} (𝓕 f) = 𝓕 (-(2 * π * Complex.I) • smulLeftCLM E (inner ℝ · m) f) := calc
  _ = SchwartzMap.evalCLM ℝ V E m (fderivCLM ℝ V E (𝓕 f)) := rfl
  _ = SchwartzMap.evalCLM ℝ V E m (𝓕 (fourierSMulRightCLM (innerSL ℝ) f)) := by
    rw [fderivCLM_fourier_eq]
  _ = 𝓕 (SchwartzMap.evalCLM ℝ V E m (fourierSMulRightCLM (innerSL ℝ) f)) := by
    rw [fourier_evalCLM_eq ℝ (fourierSMulRightCLM (innerSL ℝ) f) m]
  _ = _ := by
    congr
    ext x
    have : (inner ℝ · m).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
    simp [this, innerSL_apply_apply ℝ]

theorem fourier_lineDerivOp_eq (f : 𝓢(V, E)) (m : V) :
    𝓕 (∂_{m} f) = (2 * π * Complex.I) • smulLeftCLM E (inner ℝ · m) (𝓕 f) := calc
  _ = 𝓕 (SchwartzMap.evalCLM ℝ V E m (fderivCLM ℝ V E f)) := rfl
  _ = SchwartzMap.evalCLM ℝ V E m (𝓕 (fderivCLM ℝ V E f)) := by
    rw [fourier_evalCLM_eq ℝ]
  _ = SchwartzMap.evalCLM ℝ V E m (fourierSMulRightCLM (-innerSL ℝ) (𝓕 f)) := by
    rw [fourier_fderivCLM_eq]
  _ = _ := by
    ext x
    have : (inner ℝ · m).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
    simp [this, innerSL_apply_apply ℝ]

variable [CompleteSpace E]

theorem lineDerivOp_fourierInv_eq (f : 𝓢(V, E)) (m : V) :
    ∂_{m} (𝓕⁻ f) = 𝓕⁻ ((2 * π * Complex.I) • smulLeftCLM E (inner ℝ · m) f) := calc
  _ = 𝓕⁻ (𝓕 (∂_{m} (𝓕⁻ f))) := by simp
  _ = 𝓕⁻ ((2 * π * Complex.I) • smulLeftCLM E (inner ℝ · m) (𝓕 (𝓕⁻ f))) := by
    rw [fourier_lineDerivOp_eq]
  _ = _ := by simp

theorem fourierInv_lineDerivOp_eq (f : 𝓢(V, E)) (m : V) :
    𝓕⁻ (∂_{m} f) = -(2 * π * Complex.I) • smulLeftCLM E (inner ℝ · m) (𝓕⁻ f) := calc
  _ = 𝓕⁻ (∂_{m} (𝓕 (𝓕⁻ f))) := by simp
  _ = 𝓕⁻ (𝓕 (-(2 * π * Complex.I) • smulLeftCLM E (inner ℝ · m) (𝓕⁻ f))) := by
    rw [lineDerivOp_fourier_eq]
  _ = _ := by simp

end deriv

section L2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Plancherel's theorem for Schwartz functions. -/
@[simp] theorem integral_inner_fourier_fourier (f g : 𝓢(V, H)) :
    ∫ ξ, ⟪𝓕 f ξ, 𝓕 g ξ⟫ = ∫ x, ⟪f x, g x⟫ :=
  integral_sesq_fourier_fourier f g (innerSL ℂ)

theorem integral_norm_sq_fourier (f : 𝓢(V, H)) :
    ∫ ξ, ‖𝓕 f ξ‖^2 = ∫ x, ‖f x‖^2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    integral_inner_fourier_fourier f f

theorem inner_fourier_toL2_eq (f g : 𝓢(V, H)) :
    ⟪(𝓕 f).toLp 2, (𝓕 g).toLp 2⟫ = ⟪f.toLp 2, g.toLp 2⟫ := by simp

@[deprecated (since := "2025-11-13")]
alias inner_fourierTransformCLM_toL2_eq := inner_fourier_toL2_eq

@[simp] theorem norm_fourier_toL2_eq (f : 𝓢(V, H)) :
    ‖(𝓕 f).toLp 2‖ = ‖f.toLp 2‖ := by
  simp_rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_fourier_toL2_eq]

@[deprecated (since := "2025-11-13")]
alias norm_fourierTransformCLM_toL2_eq := norm_fourier_toL2_eq

end L2

end SchwartzMap
