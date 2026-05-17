/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # The Fourier transform of the convolution

In this file we calculate the Fourier transform of a convolution.

## Main definitions
* `SchwartzMap.convolution`: The convolution on Schwartz functions is defined via the Fourier
  transform.

## Main statements
* `Real.fourier_bilin_convolution_eq`: The Fourier transform of a convolution is the bilinear map
  applied to the Fourier transform of the functions.
* `Real.fourier_smul_convolution_eq`: Variant for scalar multiplication.
* `Real.fourier_mul_convolution_eq`: Variant for multiplication.
* `SchwartzMap.fourier_convolution`: The Fourier transform of the Schwartz convolution is given by
  the pairing of the Fourier transformed Schwartz functions.
* `SchwartzMap.convolution_apply`: The Schwartz function convolution coincides with the convolution
  for functions.

-/

@[expose] public section

variable {𝕜 R E F F₁ F₂ F₃ : Type*}

namespace Real

open MeasureTheory Convolution

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F₁] [NormedAddCommGroup F₂] [NormedAddCommGroup F₃]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace 𝕜 F₁] [NormedSpace 𝕜 F₂] [NormedSpace 𝕜 F₃]

/- The norm of the integrant of the convolution is integrable if the functions are integrable
and continuous. -/
theorem integrable_prod_sub (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {f₁ : E → F₁} {f₂ : E → F₂}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (hf₁' : Continuous f₁) (hf₂' : Continuous f₂) :
    Integrable (fun (p : E × E) ↦ ‖B‖ * (‖f₁ (p.1 - p.2)‖ * ‖f₂ p.2‖)) (volume.prod volume) := by
  apply Integrable.const_mul
  rw [integrable_prod_iff' (by fun_prop)]
  constructor
  · filter_upwards with x
    exact (hf₁.comp_sub_right x).norm.mul_const _
  have : Integrable (fun x ↦ ((∫ y, ‖f₁ y‖) * ‖f₂ x‖)) := by
    apply hf₂.norm.bdd_mul (by fun_prop) (c := ‖(∫ y, ‖f₁ y‖)‖)
    filter_upwards with; rfl
  convert this using 1
  ext x
  simp_rw [norm_mul, norm_norm]
  rw [integral_mul_const]
  congr 1
  convert integral_sub_right_eq_self _ x (μ := volume)
  rfl

open FourierTransform

variable [NormedSpace ℂ F₃]

/-- Calculate the Fourier transform of the convolution as a symmetric integral. -/
theorem fourier_bilin_convolution_eq_integral (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {f₁ : E → F₁} {f₂ : E → F₂}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (hf₁' : Continuous f₁) (hf₂' : Continuous f₂)
    (ξ : E) :
    𝓕 (f₁ ⋆[B] f₂) ξ = ∫ y, ∫ x, 𝐞 (-inner ℝ (y + x) ξ) • B (f₁ x) (f₂ y) := calc
  _ = 𝓕 (f₂ ⋆[B.flip] f₁) ξ := by
    rw [convolution_flip]
  _ = ∫ x, 𝐞 (-inner ℝ x ξ) • ∫ y, B (f₁ (x - y)) (f₂ y) := by rfl
  _ = ∫ x, ∫ y, 𝐞 (-inner ℝ x ξ) • B (f₁ (x - y)) (f₂ y) := by
    congr
    ext x
    simp_rw [Circle.smul_def, integral_smul]
  _ = ∫ y, ∫ x, 𝐞 (-inner ℝ x ξ) • B (f₁ (x - y)) (f₂ y) := by
    refine integral_integral_swap ?_
    apply (integrable_prod_sub B hf₁ hf₂ hf₁' hf₂').mono (by measurability)
    filter_upwards with ⟨y, x⟩
    have : ‖(B (f₁ (y - x))) (f₂ x)‖ ≤ ‖B‖ * (‖f₁ (y - x)‖ * ‖f₂ x‖) := by
      grw [B.le_opNorm₂ (f₁ (y - x)) (f₂ x), mul_assoc]
    simpa
  _ = ∫ y, ∫ x, 𝐞 (-inner ℝ (y + x) ξ) • B (f₁ x) (f₂ y) := by
    congr
    ext y
    -- Linear change of variables
    convert integral_sub_right_eq_self _ y (μ := volume)
    congr
    simp

variable [CompleteSpace F₁] [CompleteSpace F₂] [CompleteSpace F₃]
  [NormedSpace ℂ F₁] [NormedSpace ℂ F₂]

open ContinuousLinearMap

/-- The Fourier transform of the convolution is given by the bilinear map applied to the Fourier
transform of the individual functions. -/
theorem fourier_bilin_convolution_eq (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) {f₁ : E → F₁} {f₂ : E → F₂}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (hf₁' : Continuous f₁) (hf₂' : Continuous f₂)
    (ξ : E) :
    𝓕 (f₁ ⋆[B] f₂) ξ = B (𝓕 f₁ ξ) (𝓕 f₂ ξ) := calc
  _ = ∫ y, ∫ x, 𝐞 (-inner ℝ (y + x) ξ) • B (f₁ x) (f₂ y) :=
    fourier_bilin_convolution_eq_integral B hf₁ hf₂ hf₁' hf₂' _
  _ = ∫ y, ∫ x, 𝐞 (-inner ℝ y ξ) • 𝐞 (-inner ℝ x ξ) • B (f₁ x) (f₂ y) := by
    congr
    ext y
    congr
    ext x
    rw [smul_smul, ← AddChar.map_add_eq_mul, inner_add_left]
    congr
    grind
  _ = ∫ y, (∫ x, B (𝐞 (-inner ℝ x ξ) • f₁ x)) (𝐞 (-inner ℝ y ξ) • f₂ y) := by
    congr
    ext y
    simp_rw [Circle.smul_def, map_smul, MeasureTheory.integral_smul]
    congr
    rw [integral_apply ?_ (f₂ y)]
    · simp
    have : MeasureTheory.Integrable (fun x ↦ ‖B‖ * ‖f₁ x‖) MeasureTheory.volume :=
      hf₁.norm.const_mul _
    apply this.mono (by fun_prop)
    filter_upwards with x
    simpa [← Circle.smul_def] using le_opNorm B (f₁ x)
  _ = B (∫ x, 𝐞 (-inner ℝ x ξ) • f₁ x) (∫ y, 𝐞 (-inner ℝ y ξ) • f₂ y) := by
    rw [← integral_comp_comm _ (by simpa using hf₂), ← integral_comp_comm _ (by simpa using hf₁)]

/-- The Fourier transform of the convolution is given by the multiplication of the Fourier transform
of the individual functions.

Version for scalar multiplication. -/
theorem fourier_smul_convolution_eq {f₁ : E → ℂ} {f₂ : E → F₁}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (hf₁' : Continuous f₁) (hf₂' : Continuous f₂)
    (ξ : E) :
    𝓕 (f₁ ⋆[lsmul ℂ ℂ] f₂) ξ = (𝓕 f₁ ξ) • (𝓕 f₂ ξ) :=
  fourier_bilin_convolution_eq (lsmul ℂ ℂ) hf₁ hf₂ hf₁' hf₂' ξ

variable [NormedRing R] [NormedSpace ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
  [CompleteSpace R]

/-- The Fourier transform of the convolution is given by the multiplication of the Fourier transform
of the individual functions.

Version for multiplication. -/
theorem fourier_mul_convolution_eq {f₁ : E → R} {f₂ : E → R}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (hf₁' : Continuous f₁) (hf₂' : Continuous f₂)
    (ξ : E) :
    𝓕 (f₁ ⋆[mul ℂ R] f₂) ξ = (𝓕 f₁ ξ) * (𝓕 f₂ ξ) :=
  fourier_bilin_convolution_eq (mul ℂ R) hf₁ hf₂ hf₁' hf₂' ξ

end Real

namespace SchwartzMap

variable [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [NormedSpace 𝕜 F₁] [SMulCommClass ℂ 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [NormedSpace 𝕜 F₂] [SMulCommClass ℂ 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℂ F₃] [NormedSpace 𝕜 F₃] [SMulCommClass ℂ 𝕜 F₃]

open FourierTransform Convolution

/-- The bilinear convolution of Schwartz functions.

The continuity in the left argument is provided in `SchwartzMap.convolution_continuous_left`. -/
noncomputable
def convolution (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) : 𝓢(E, F₁) →ₗ[𝕜] 𝓢(E, F₂) →L[𝕜] 𝓢(E, F₃) where
  toFun f := fourierInvCLM 𝕜 𝓢(E, F₃) ∘L pairing B (𝓕 f) ∘L fourierCLM 𝕜 𝓢(E, F₂)
  map_add' := by simp [FourierTransform.fourier_add]
  map_smul' := by simp [FourierTransform.fourier_smul]

@[simp]
theorem convolution_flip (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) :
    convolution B.flip g f = convolution B f g := rfl

/-- The convolution is continuous in the left argument.

Note that since `𝓢(E, F)` is not a normed space, uncurried and curried continuity do not
coincide. -/
@[fun_prop]
theorem convolution_continuous_left (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) (g : 𝓢(E, F₂)) :
    Continuous (convolution B · g) := (convolution B.flip g).continuous

variable [CompleteSpace F₃]

theorem fourier_convolution (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) :
    𝓕 (convolution B f g) = pairing B (𝓕 f) (𝓕 g) := by simp [convolution]

variable [CompleteSpace F₁] [CompleteSpace F₂]

open MeasureTheory

theorem fourier_convolution_apply (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (x : E) :
    𝓕 (convolution B f g) x = 𝓕 (f ⋆[B] g) x := by
  simp [fourier_convolution, fourier_coe,
    Real.fourier_bilin_convolution_eq B f.integrable g.integrable f.continuous g.continuous]

/-- The convolution on Schwartz functions is equal to the convolution on functions. -/
theorem convolution_apply (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (x : E) :
    convolution B f g x = (f ⋆[B] g) x := calc
  _ = 𝓕⁻ (𝓕 (convolution B f g)) x := by simp
  _ = 𝓕⁻ (fun y ↦ 𝓕 (f ⋆[B] g) y) x := by
    rw [fourierInv_coe]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [fourier_convolution_apply]
  _ = _ := by
    rw [Continuous.fourierInv_fourier_eq]
    · refine BddAbove.continuous_convolution_right_of_integrable B ?_ f.integrable g.continuous
      exact ⟨SchwartzMap.seminorm ℝ 0 0 g, fun x ⟨y, hy⟩ ↦ hy ▸ norm_le_seminorm ℝ g y⟩
    · exact f.integrable.integrable_convolution B g.integrable
    · have : Integrable (fun ξ ↦ B (𝓕 f ξ) (𝓕 g ξ)) volume := (pairing B (𝓕 f) (𝓕 g)).integrable
      convert this
      rw [← fourier_convolution_apply B f g, fourier_convolution, pairing_apply_apply]


end SchwartzMap
