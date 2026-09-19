/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.InnerProductSpace.Reproducing

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
      grw [enorm_inner_le_enorm, ContinuousLinearMap.le_opENorm]
      simp [mul_assoc]
    _ ≤ (∫⁻ (a : X × X), ‖K a.1 a.2‖ₑ ^ 2 ∂μ.prod μ) ^ (2:ℝ)⁻¹ *
          (∫⁻ (a : X × X), ‖f a.2‖ₑ ^ 2 * ‖g a.1‖ₑ ^ 2 ∂μ.prod μ) ^ (2:ℝ)⁻¹ := by
      have := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.prod μ) Real.HolderConjugate.two_two
        hK.aemeasurable.enorm (((f : X →ₘ[μ] V).measurable.comp measurable_snd).enorm.mul
          ((g : X →ₘ[μ] V).measurable.comp measurable_fst).enorm).aemeasurable
      simp only [Function.comp_apply, Pi.mul_apply, ENNReal.rpow_ofNat, one_div] at this
      grw [this]
      simp [mul_pow]
    _ ≤ (∫⁻ (a : X × X), ‖K a.1 a.2‖ₑ ^ 2 ∂μ.prod μ) ^ (2:ℝ)⁻¹ * ((∫⁻ (x : X), ‖f x‖ₑ ^ 2 ∂μ) *
          ∫⁻ (y : X), ‖g y‖ₑ ^ 2 ∂μ) ^ (2:ℝ)⁻¹ := by
      simp_rw [mul_comm (‖f _‖ₑ ^ 2)]
      grw [lintegral_prod_mul ((g : X →ₘ[μ] V).aemeasurable.enorm.pow_const 2)
        ((f : X →ₘ[μ] V).aemeasurable.enorm.pow_const 2)]
      simp [mul_comm]
    _ ≤ (eLpNorm (fun p ↦ K p.1 p.2) 2 (μ.prod μ)) * ‖f‖ₑ * ‖g‖ₑ := by
      rw [ENNReal.mul_rpow_of_nonneg (∫⁻ (x : X), ‖f x‖ₑ ^ 2 ∂μ) (∫⁻ (y : X), ‖g y‖ₑ ^ 2 ∂μ)
        (by simp)]
      simp [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (Ne.symm (NeZero.ne' 2))
        (ENNReal.ofNat_ne_top), mul_assoc]

private lemma mercerForm_integrable (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ))
    (f g : Lp V 2 μ) : Integrable (fun p ↦ ⟪(K p.1 p.2) (f p.2), g p.1⟫_𝕜) (μ.prod μ) := by
  constructor
  · have h1 : AEStronglyMeasurable (fun p : X × X ↦ (K p.1 p.2) (f p.2 : V)) (μ.prod μ) :=
      isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        (hK.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable f).comp_snd)
    have h2 : AEStronglyMeasurable (fun p : X × X ↦ (g p.1 : V)) (μ.prod μ) :=
      (Lp.aestronglyMeasurable g).comp_fst
    exact continuous_inner.comp_aestronglyMeasurable (h1.prodMk h2)
  · grw [hasFiniteIntegral_def, lintegral_norm_inner_le hK f g]
    refine ENNReal.mul_lt_top ?_ enorm_lt_top
    refine ENNReal.mul_lt_top hK.eLpNorm_lt_top enorm_lt_top

private lemma integral_congr_fst {U : Type*} {φ ψ : X → U} (h : φ =ᵐ[μ] ψ) (F : X × X → U → 𝕜) :
    ∫ p : X × X, F p (φ p.1) ∂ μ.prod μ = ∫ p : X × X, F p (ψ p.1) ∂ μ.prod μ := by
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h] with p hp
  rw [hp]

private lemma integral_congr_snd {U : Type*} {φ ψ : X → U} (h : φ =ᵐ[μ] ψ) (F : X × X → U → 𝕜) :
    ∫ p : X × X, F p (φ p.2) ∂ μ.prod μ = ∫ p : X × X, F p (ψ p.2) ∂ μ.prod μ := by
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae h] with p hp
  rw [hp]

/-- The bilinear map `(f,g) ↦ ∫ p : X × X, ⟪K p.1 p.2 (f p.2), (g p.1)⟫_𝕜 ∂ (μ.prod μ)`. -/
def mercerForm (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) :
    Lp V 2 μ →L⋆[𝕜] Lp V 2 μ →L[𝕜] 𝕜 := LinearMap.mkContinuous₂
  (LinearMap.mk₂'ₛₗ (starRingEnd 𝕜) (RingHom.id 𝕜)
    (fun (f : Lp V 2 μ) (g : Lp V 2 μ) ↦ ∫ p : X × X, ⟪K p.1 p.2 (f p.2), (g p.1)⟫_𝕜 ∂ (μ.prod μ))
    (fun f₁ f₂ g ↦ by
      simp_rw [← integral_add (mercerForm_integrable hK f₁ g) (mercerForm_integrable hK f₂ g),
        ← inner_add_left,
        integral_congr_snd (Lp.coeFn_add f₁ f₂) (fun p v ↦ ⟪K p.1 p.2 v, (g p.1)⟫_𝕜)]
      simp
    )
    (fun c f g ↦ by
      simp_rw [← integral_smul, ← inner_smul_left_eq_star_smul,
        integral_congr_snd (Lp.coeFn_smul c f) (fun p v ↦ ⟪K p.1 p.2 v, (g p.1)⟫_𝕜)]
      simp
    )
    (fun f g₁ g₂ ↦ by
      simp_rw [← integral_add (mercerForm_integrable hK f g₁) (mercerForm_integrable hK f g₂),
        ← inner_add_right,
        integral_congr_fst (Lp.coeFn_add g₁ g₂) (fun p v ↦ ⟪K p.1 p.2 (f p.2), v⟫_𝕜)]
      simp
    )
    (fun c f g ↦ by
      simp_rw [← integral_smul, ← inner_smul_right_eq_smul, RingHom.id_apply,
        integral_congr_fst (Lp.coeFn_smul c g) (fun p v ↦ ⟪K p.1 p.2 (f p.2), v⟫_𝕜)]
      simp
    )
  )
  (eLpNorm (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)).toReal
  (fun f g ↦ by
    grw [LinearMap.mk₂'ₛₗ_apply, norm_integral_le_lintegral_norm]
    simp_rw [ofReal_norm]
    grw [lintegral_norm_inner_le hK f g]
    · simp
    rw [← lt_top_iff_ne_top]
    refine ENNReal.mul_lt_top ?_ enorm_lt_top
    refine ENNReal.mul_lt_top hK.eLpNorm_lt_top enorm_lt_top
    )

variable (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ))

@[simp]
lemma mercerForm_apply (f g : Lp V 2 μ) :
    mercerForm hK f g = ∫ p : X × X, ⟪K p.1 p.2 (f p.2), (g p.1)⟫_𝕜 ∂ (μ.prod μ) := by
  rfl

theorem mercerForm_conj_symm [CompleteSpace V] [Fact K.PosSemidef]
    (f g : Lp V 2 μ) : starRingEnd 𝕜 (mercerForm hK f g) = mercerForm hK g f := by
  simp_rw [mercerForm_apply]
  rw [← integral_conj, ← integral_prod_swap]
  congr with _
  rw [← ContinuousLinearMap.adjoint_inner_right, ← conj_inner_symm,
    ← ContinuousLinearMap.star_eq_adjoint,
    Matrix.IsHermitian.ext_iff.mp (Fact.out : K.PosSemidef).1]
  simp

end RKHS
