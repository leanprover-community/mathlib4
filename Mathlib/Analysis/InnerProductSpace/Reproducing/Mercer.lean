/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.InnerProductSpace.Reproducing
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Mercer's theorem
This file implements Mercer's theorem, i.e. under an integrability condition the kernel has a
spectral representation.

## Main definitions
 - `mercerForm`: the bilinear map
    `(f,g) ↦ ∫ p : X × X, ⟪K p.1 p.2 (f p.2), (g p.1)⟫_𝕜 ∂ (μ.prod μ)`.

## Implementation notes
In Mercer's theorem, the spectral representation of the kernel is derived from the Hilbert-Schmidt
operator `T f x = ∫ y : X, K x y (f y) ∂ μ`. This file implements that operator as Riesz
represention of the bilinear map `(f,g) ↦ ∫ p : X × X, ⟪K p.1 p.2 (f p.2), (g p.1)⟫_𝕜 ∂ (μ.prod μ)`
evaluated at `f`. The implementing this way versus a direct formalization limits the number of
times Fubini-Totelli uses.

## Todo:
 - Implement the integral operator `T f x = ∫ y : X, K x y (f y) ∂ μ` as Riesz representer of
   the `mercerForm`.

-/

public noncomputable section

open InnerProductSpace MeasureTheory

namespace RKHS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [MeasurableSpace V]
  [BorelSpace V] [MeasurableSpace (V →L[𝕜] V)] [BorelSpace (V →L[𝕜] V)]
variable {μ : Measure X} [SFinite μ]
variable {K : Matrix X X (V →L[𝕜] V)}

private lemma lintegral_norm_inner_le (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ))
    (f g : Lp V 2 μ) : ∫⁻  (p : X × X), ‖⟪(K p.1 p.2) (f p.2), g p.1⟫_𝕜‖ₑ ∂μ.prod μ ≤
      (eLpNorm (fun p ↦ K p.1 p.2) 2 (μ.prod μ)) * ‖f‖ₑ * ‖g‖ₑ := by
  calc
    ∫⁻ (p : X × X), ‖⟪(K p.1 p.2) (f p.2), g p.1⟫_𝕜‖ₑ ∂μ.prod μ ≤
        ∫⁻ (p : X × X), ‖K p.1 p.2‖ₑ * (‖f p.2‖ₑ * ‖g p.1‖ₑ) ∂μ.prod μ := by
      grw [eNorm_inner_le_eNorm, ContinuousLinearMap.le_opENorm]
      simp [mul_assoc]
    _ ≤ (∫⁻ (a : X × X), ‖K a.1 a.2‖ₑ ^ 2 ∂μ.prod μ) ^ (2:ℝ)⁻¹ *
          (∫⁻ (a : X × X), ‖f a.2‖ₑ ^ 2 * ‖g a.1‖ₑ ^ 2 ∂μ.prod μ) ^ (2:ℝ)⁻¹ := by
      refine (ENNReal.lintegral_mul_le_Lp_mul_Lq _ .two_two
        hK.aemeasurable.eNorm (((f : X →ₘ[μ] V).aemeasurable.comp_snd.eNorm.mul
          ((g : X →ₘ[μ] V).aemeasurable.comp_fst.eNorm)))).trans_eq ?_
      simp [mul_pow]
    _ = (∫⁻ (a : X × X), ‖K a.1 a.2‖ₑ ^ 2 ∂μ.prod μ) ^ (2:ℝ)⁻¹ * ((∫⁻ (x : X), ‖f x‖ₑ ^ 2 ∂μ) *
          ∫⁻ (y : X), ‖g y‖ₑ ^ 2 ∂μ) ^ (2:ℝ)⁻¹ := by
      congr
      exact (lintegral_prod_swap _).trans (lintegral_prod_mul
        ((f : X →ₘ[μ] V).aemeasurable.eNorm.pow_const 2)
        ((g : X →ₘ[μ] V).aemeasurable.eNorm.pow_const 2))
    _ ≤ (eLpNorm (fun p ↦ K p.1 p.2) 2 (μ.prod μ)) * ‖f‖ₑ * ‖g‖ₑ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp)]
      simp [Lp.eNorm_def, mul_assoc, hK.aestronglyMeasurable, Lp.aestronglyMeasurable,
        eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top]

private lemma mercerForm_integrable (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ))
    (f g : Lp V 2 μ) : Integrable (fun p ↦ ⟪(K p.1 p.2) (f p.2), g p.1⟫_𝕜) (μ.prod μ) := by
  constructor
  · have h1 : AEStronglyMeasurable (fun p : X × X ↦ (K p.1 p.2) (f p.2 : V)) (μ.prod μ) :=
      isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        (hK.aestronglyMeasurable.prodMk (f : X →ₘ[μ] V).aestronglyMeasurable.comp_snd)
    have h2 : AEStronglyMeasurable (fun p : X × X ↦ (g p.1 : V)) (μ.prod μ) :=
      (g : X →ₘ[μ] V).aestronglyMeasurable.comp_fst
    exact continuous_inner.comp_aestronglyMeasurable (h1.prodMk h2)
  · grw [hasFiniteIntegral_def, lintegral_norm_inner_le hK f g]
    finiteness

omit [SFinite μ] in
private lemma integral_congr_fst {U : Type*} {φ ψ : X → U} (h : φ =ᵐ[μ] ψ) (F : X × X → U → 𝕜) :
    ∫ p : X × X, F p (φ p.1) ∂ μ.prod μ = ∫ p : X × X, F p (ψ p.1) ∂ μ.prod μ := by
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h] with p hp
  rw [hp]

omit [SFinite μ] in
private lemma integral_congr_snd {U : Type*} {φ ψ : X → U} (h : φ =ᵐ[μ] ψ) (F : X × X → U → 𝕜) :
    ∫ p : X × X, F p (φ p.2) ∂ μ.prod μ = ∫ p : X × X, F p (ψ p.2) ∂ μ.prod μ := by
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae h] with p hp
  rw [hp]

/-- The bilinear map `(f,g) ↦ ∫ p : X × X, ⟪K p.1 p.2 (f p.2), (g p.1)⟫_𝕜 ∂ (μ.prod μ)`. -/
def mercerForm (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) :
    Lp V 2 μ →L⋆[𝕜] Lp V 2 μ →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd 𝕜) (RingHom.id 𝕜)
      (fun f g ↦ ∫ p : X × X, ⟪K p.1 p.2 (f p.2), (g p.1)⟫_𝕜 ∂ (μ.prod μ))
      ?_ ?_ ?_ ?_)
    (eLpNorm (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)).toReal ?_
where finally
  · intro f₁ f₂ g
    simp_rw [integral_congr_snd (Lp.coeFn_add f₁ f₂) (fun p v ↦ ⟪K p.1 p.2 v, (g p.1)⟫_𝕜)]
    simp [integral_add (mercerForm_integrable hK f₁ g) (mercerForm_integrable hK f₂ g),
      inner_add_left]
  · intro c f g
    simp [integral_congr_snd (Lp.coeFn_smul c f) (fun p v ↦ ⟪K p.1 p.2 v, (g p.1)⟫_𝕜),
      inner_smul_left, integral_const_mul]
  · intro f g₁ g₂
    simp_rw [integral_congr_fst (Lp.coeFn_add g₁ g₂) (fun p v ↦ ⟪K p.1 p.2 (f p.2), v⟫_𝕜)]
    simp [integral_add (mercerForm_integrable hK f g₁) (mercerForm_integrable hK f g₂),
      inner_add_right]
  · intro c f g
    simp [integral_congr_fst (Lp.coeFn_smul c g) (fun p v ↦ ⟪K p.1 p.2 (f p.2), v⟫_𝕜),
      inner_smul_right, integral_const_mul]
  · intro f g
    grw [LinearMap.mk₂'ₛₗ_apply, norm_integral_le_lintegral_norm]
    simp_rw [ofReal_norm]
    grw [lintegral_norm_inner_le hK f g]
    · simp
    finiteness

variable (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ))

@[simp]
lemma mercerForm_apply (f g : Lp V 2 μ) :
    mercerForm hK f g = ∫ p : X × X, ⟪K p.1 p.2 (f p.2), (g p.1)⟫_𝕜 ∂ (μ.prod μ) := by
  rfl

theorem mercerForm_conj_symm [CompleteSpace V] (hK' : K.IsHermitian)
    (f g : Lp V 2 μ) : starRingEnd 𝕜 (mercerForm hK f g) = mercerForm hK g f := by
  simp [← integral_conj, ← integral_prod_swap (fun p : X × X ↦ ⟪K p.1 p.2 (g p.2), f p.1⟫_𝕜),
    ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    hK'.apply]

variable [CompleteSpace V]

/-- The integral operator `f ↦ ∫ (y : X), K · y (f y) ∂μ` defined through the Riesz representer
associated to the bilinear form `mercerForm`. -/
def integralOperator : Lp V 2 μ →L[𝕜] Lp V 2 μ :=
  InnerProductSpace.continuousLinearMapOfBilin (mercerForm hK)

@[simp]
lemma integralOperator_apply (f : Lp V 2 μ) :
    integralOperator hK f = (InnerProductSpace.toDual 𝕜 (Lp V 2 μ)).symm (mercerForm hK f) := by
  rfl

theorem integralOperator_inner (f g : Lp V 2 μ) :
    ⟪integralOperator hK f, g⟫_𝕜 = mercerForm hK f g := by
  simp [mercerForm, integralOperator]

theorem inner_integralOperator (f g : Lp V 2 μ) :
    ⟪f, integralOperator hK g⟫_𝕜 = starRingEnd 𝕜 (mercerForm hK g f) := by
  rw [← inner_conj_symm, integralOperator_inner]

theorem isSymmetric_integralOperator (hK' : K.IsHermitian) :
    (integralOperator hK).IsSymmetric := fun f g ↦ by
  rw [ContinuousLinearMap.coe_coe, integralOperator_inner, inner_integralOperator,
    mercerForm_conj_symm hK hK']

theorem isSelfAdjoint_integralOperator (hK' : K.IsHermitian) :
    IsSelfAdjoint (integralOperator hK) :=
  (isSymmetric_integralOperator hK hK').isSelfAdjoint

end RKHS
