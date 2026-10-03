/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Seewoo Lee
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Normed.Radial

/-!
# Radial Schwartz functions

This file defines the submodule of the Schwartz space `𝓢(E, F)` consisting of the radial functions.
Since the Fourier transform of a radial function is again radial, this submodule is preserved by
the Fourier transform. Moreover, a radial function is even, so on this submodule the Fourier
transform agrees with its inverse and is therefore an involution. Consequently the space of radial
Schwartz functions is a `StarModule ℝ` with the Fourier transform as star operation, and the
decomposition into self-adjoint and skew-adjoint parts writes a radial Schwartz function as a sum
of eigenfunctions of the Fourier transform with eigenvalues `1` and `-1`.

## Main definitions

* `RadialSchwartzMap`: the submodule of `𝓢(E, F)` consisting of the radial Schwartz functions.
* `RadialSchwartzMap.fourierTransformCLM`: the Fourier transform as a continuous linear
  endomorphism of the space of radial Schwartz functions.

## Main statements

* `Function.IsRadial.fourier`: the Fourier transform of a radial function is radial.
* `RadialSchwartzMap.fourier_apply_apply`: the Fourier transform is an involution on radial
  Schwartz functions.
* `RadialSchwartzMap.selfAdjointPart_eq` and `RadialSchwartzMap.skewAdjointPart_eq`: with respect
  to the star operation given by the Fourier transform, the self-adjoint and skew-adjoint parts of
  a radial Schwartz function `f` are `(f + 𝓕 f) / 2` and `(f - 𝓕 f) / 2`.

## Notation

* `𝓢₀[𝕜](E, F)`: the submodule `RadialSchwartzMap 𝕜 E F` of radial Schwartz functions, localized
  in the `RadialSchwartzMap` namespace.

## References

This file was written as part of the
[Sphere Packing Project](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean).

## Tags

Schwartz space, radial function, Fourier transform
-/

@[expose] public section

open Function SchwartzMap

/-- The submodule of radial Schwartz functions inside the Schwartz space `𝓢(E, F)`. -/
@[simps]
def RadialSchwartzMap (𝕜 E F : Type*) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] :
    Submodule 𝕜 𝓢(E, F) where
  carrier := {f | IsRadial f}
  add_mem' := by grind [isRadial_def]
  zero_mem' := by simp [isRadial_def]
  smul_mem' := by grind [isRadial_def]

@[inherit_doc]
scoped[RadialSchwartzMap] notation "𝓢₀[" 𝕜 "](" E ", " F ")" => RadialSchwartzMap 𝕜 E F

namespace RadialSchwartzMap

variable {𝕜 E F : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- Create a `RadialSchwartzMap` -/
def mk [NormedSpace ℝ E] (f : 𝓢(E, F)) (hf : IsRadial f) : 𝓢₀[𝕜](E, F) := ⟨f, hf⟩

section NormedSpace

variable [NormedSpace ℝ E]

instance instFunLike : FunLike (𝓢₀[𝕜](E, F)) E F where
  coe f := f.1
  coe_injective := DFunLike.coe_injective.comp Subtype.val_injective

@[simp, norm_cast]
lemma coe_coe (f : 𝓢₀[𝕜](E, F)) : ⇑(f : 𝓢(E, F)) = f := rfl

@[simp]
lemma zero_apply (x : E) : (0 : 𝓢₀[𝕜](E, F)) x = 0 := rfl

@[simp]
lemma add_apply (f g : 𝓢₀[𝕜](E, F)) (x : E) : (f + g) x = f x + g x := rfl

@[simp]
lemma neg_apply (f : 𝓢₀[𝕜](E, F)) (x : E) : (-f) x = -f x := rfl

@[simp]
lemma sub_apply (f g : 𝓢₀[𝕜](E, F)) (x : E) : (f - g) x = f x - g x := rfl

@[simp]
lemma smul_apply (c : 𝕜) (f : 𝓢₀[𝕜](E, F)) (x : E) : (c • f) x = c • f x := rfl

lemma isRadial (f : 𝓢₀[𝕜](E, F)) : IsRadial f := f.2

lemma _root_.SchwartzMap.mem_radialSchwartzMap_iff_isRadial (f : 𝓢(E, F)) :
    f ∈ 𝓢₀[𝕜](E, F) ↔ IsRadial f := .rfl

end NormedSpace

lemma _root_.SchwartzMap.mem_radialSchwartzMap_iff_comp_linearIsometryEquiv
    [InnerProductSpace ℝ E] (f : 𝓢(E, F)) :
    f ∈ 𝓢₀[𝕜](E, F) ↔ ∀ g : E ≃ₗᵢ[ℝ] E, ⇑f ∘ g = ⇑f :=
  isRadial_iff_comp_linearIsometryEquiv _

end RadialSchwartzMap

noncomputable section Fourier

open Real FourierTransform RadialSchwartzMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]

/-- The Fourier transform of a radial function is radial. -/
lemma Function.IsRadial.fourier {f : E → F} (hf : f.IsRadial) : (𝓕 f).IsRadial := by
  rw [isRadial_iff_comp_linearIsometryEquiv] at hf ⊢
  intro g
  ext x
  rw [Function.comp_apply, ← Real.fourier_comp_linearIsometry g f x, hf g]

variable (𝕜) in
lemma SchwartzMap.fourier_mem_radialSchwartzMap_of_mem_radialSchwartzMap {f : 𝓢(E, F)}
    (hf : f ∈ 𝓢₀[𝕜](E, F)) : 𝓕 f ∈ 𝓢₀[𝕜](E, F) := by
  rw [SchwartzMap.mem_radialSchwartzMap_iff_isRadial] at hf ⊢
  exact SchwartzMap.fourier_coe f ▸ hf.fourier

namespace RadialSchwartzMap

variable (𝕜 E F)

lemma map_fourierTransformCLM_le : (𝓢₀[𝕜](E, F)).map
    (SchwartzMap.fourierTransformCLM 𝕜 (V := E) (E := F)).toLinearMap ≤ 𝓢₀[𝕜](E, F) :=
  Submodule.map_le_iff_le_comap.mpr fun _ ↦ fourier_mem_radialSchwartzMap_of_mem_radialSchwartzMap 𝕜

/-- The Fourier transform as a continuous linear map on radial Schwartz functions. -/
def fourierTransformCLM : 𝓢₀[𝕜](E, F) →L[𝕜] 𝓢₀[𝕜](E, F) :=
  (SchwartzMap.fourierTransformCLM 𝕜).restrict fun _ ↦
    fourier_mem_radialSchwartzMap_of_mem_radialSchwartzMap 𝕜

instance instFourierTransform :
    FourierTransform (𝓢₀[𝕜](E, F)) (𝓢₀[𝕜](E, F)) where
  fourier := fourierTransformCLM 𝕜 E F

variable {𝕜 E F}

@[simp]
lemma fourierTransformCLM_apply (f : 𝓢₀[𝕜](E, F)) :
    fourierTransformCLM 𝕜 E F f = 𝓕 f := rfl

@[simp, norm_cast]
lemma coe_fourier (f : 𝓢₀[𝕜](E, F)) :
    ((𝓕 f : 𝓢₀[𝕜](E, F)) : 𝓢(E, F)) = 𝓕 (f : 𝓢(E, F)) := rfl

@[simp, norm_cast]
lemma fourier_coe (f : 𝓢₀[𝕜](E, F)) :
    ((𝓕 f : 𝓢₀[𝕜](E, F)) : E → F) = 𝓕 (f : E → F) := rfl

section inverse

lemma _root_.Function.Even.fourierInv {f : E → F} (hf : (𝓕 f).Even) {w : E} :
    𝓕⁻ f w = 𝓕 f w := by
  rw [fourierInv_eq_fourier_neg]
  exact hf w

variable (𝕜) in
lemma _root_.SchwartzMap.fourier_eq_fourierInv_of_mem_radialSchwartzMap {f : 𝓢(E, F)}
    (hf : f ∈ 𝓢₀[𝕜](E, F)) : 𝓕⁻ f = 𝓕 f := by
  ext x
  rw [fourierInv_coe, SchwartzMap.fourier_coe]
  exact Function.Even.fourierInv <| IsRadial.even (hf.fourier)

lemma _root_.SchwartzMap.eqOn_fourier_fourierInv_radialSchwartzMap :
    Set.EqOn (𝓕⁻ : 𝓢(E, F) → 𝓢(E, F)) (𝓕 : 𝓢(E, F) → 𝓢(E, F)) (𝓢₀[𝕜](E, F)) :=
  fun _ hf ↦ SchwartzMap.fourier_eq_fourierInv_of_mem_radialSchwartzMap 𝕜 hf

instance instFourierInv :
    FourierTransformInv (𝓢₀[𝕜](E, F)) (𝓢₀[𝕜](E, F)) where
  fourierInv := fourierTransformCLM 𝕜 E F

lemma fourierInv_eq_fourier : (𝓕⁻ : 𝓢₀[𝕜](E, F) → 𝓢₀[𝕜](E, F)) = 𝓕 := rfl

lemma coe_fourierInv (f : 𝓢₀[𝕜](E, F)) : 𝓕⁻ f = 𝓕⁻ (f : 𝓢(E, F)) := by
  rw [fourierInv_eq_fourier, coe_fourier f]
  exact (SchwartzMap.fourier_eq_fourierInv_of_mem_radialSchwartzMap 𝕜 (Submodule.coe_mem f)).symm

variable [CompleteSpace F]

instance instFourierPair : FourierPair (𝓢₀[𝕜](E, F)) (𝓢₀[𝕜](E, F)) where
  fourierInv_fourier_eq := by
    intro f
    rw [← Subtype.val_inj, coe_fourierInv, coe_fourier]
    exact SchwartzMap.instFourierPair.fourierInv_fourier_eq (f : 𝓢(E, F))

variable {f : 𝓢₀[𝕜](E, F)}

/-- The Fourier transform is an involution on radial Schwartz functions. -/
@[simp]
lemma fourier_apply_apply : 𝓕 (𝓕 f) = f := by
  rw [← fourierInv_eq_fourier]
  exact instFourierPair.fourierInv_fourier_eq f

/-- The inverse Fourier transform is an involution on radial Schwartz functions. -/
@[simp]
lemma fourierInv_apply_apply : 𝓕⁻ (𝓕⁻ f) = f := by
  rw [fourierInv_eq_fourier]
  exact fourier_apply_apply

instance instFourierInvPair :
    FourierInvPair (𝓢₀[𝕜](E, F)) (𝓢₀[𝕜](E, F)) where
  fourier_fourierInv_eq := by
    intro f
    rw [fourierInv_eq_fourier]
    exact fourierInv_apply_apply

end inverse

section MoreFourierInstances

instance instFourierAdd : FourierAdd (𝓢₀[𝕜](E, F)) (𝓢₀[𝕜](E, F)) where
  fourier_add := fun _ _ ↦ by simp [← Subtype.val_inj]

instance instFourierInvAdd : FourierInvAdd (𝓢₀[𝕜](E, F)) (𝓢₀[𝕜](E, F)) where
  fourierInv_add := instFourierAdd.fourier_add

instance instFourierSMul : FourierSMul 𝕜 (𝓢₀[𝕜](E, F)) (𝓢₀[𝕜](E, F)) where
  fourier_smul := fun _ _ ↦ by simp [← Subtype.val_inj]

instance instFourierInvSMul :
    FourierInvSMul 𝕜 (𝓢₀[𝕜](E, F)) (𝓢₀[𝕜](E, F)) where
  fourierInv_smul := instFourierSMul.fourier_smul

instance instContinuousFourier :
    ContinuousFourier (𝓢₀[𝕜](E, F)) (𝓢₀[𝕜](E, F)) where
  continuous_fourier := ContinuousLinearMap.continuous _

instance instContinuousFourierInv :
    ContinuousFourierInv (𝓢₀[𝕜](E, F)) (𝓢₀[𝕜](E, F)) where
  continuous_fourierInv := instContinuousFourier.continuous_fourier

end MoreFourierInstances

end RadialSchwartzMap

end Fourier

noncomputable section Star

open FourierTransform

namespace RadialSchwartzMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]

variable [CompleteSpace F]

instance instStarAddMonoid : StarAddMonoid (𝓢₀[𝕜](E, F)) where
  star := 𝓕
  star_involutive := fun _ ↦ fourier_apply_apply
  star_add := instFourierAdd.fourier_add

instance instStarModule : StarModule ℝ (𝓢₀[𝕜](E, F)) where
  star_smul := by
    intro r f
    change 𝓕 (r • f) = star r • 𝓕 f
    rw [star_trivial]
    aesop

variable {f : 𝓢₀[𝕜](E, F)}

lemma mem_selfAdjoint_iff : f ∈ selfAdjoint (𝓢₀[𝕜](E, F)) ↔ 𝓕 f = f := by rfl

lemma mem_skewAdjoint_iff : f ∈ skewAdjoint (𝓢₀[𝕜](E, F)) ↔ 𝓕 f = -f := by rfl

lemma selfAdjointPart_eq : selfAdjointPart ℝ f = (1 / 2 : ℝ) • (f + 𝓕 f) := by aesop

lemma skewAdjointPart_eq : skewAdjointPart ℝ f = (1 / 2 : ℝ) • (f - 𝓕 f) := by aesop

end RadialSchwartzMap

end Star
