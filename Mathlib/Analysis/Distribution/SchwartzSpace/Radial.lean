/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Seewoo Lee
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # Radial Schwartz Functions

This file defines the notion of a radial function, and uses it to define the submodule the Schwartz
space consisting of radial functions. It proves that the Fourier transform is an involution on this
submodule. It proves `FourierTransform`, `FourierPair`, `ContinuousFourier`, `FourierAdd` and
`FourierSMul` instances (and the corresponding instances for 𝓕⁻) and `StarAddMonoid` and
`StarModule` instances (where the module structure is over ℝ).

This file was written as part of the [Sphere Packing Project](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean).
-/

@[expose] public section

namespace Function

variable {D E F : Type*}

/-- A function on a space with a norm is *radial* if factors through the norm. -/
def IsRadial [Norm E] (f : E → F) : Prop := f.FactorsThrough (‖·‖ : E → ℝ)

lemma isRadial_def [Norm E] (f : E → F) :
    f.IsRadial ↔ ∀ {x y : E}, ‖x‖ = ‖y‖ → f x = f y := by
  simp [IsRadial, Function.FactorsThrough]

/-- The radial part of a function. If f is a radial function, then `f = f.radialPart ∘ ‖·‖`. -/
noncomputable def radialPart [Norm E] [hF : Nonempty F] (f : E → F) : ℝ → F :=
  Function.extend (‖·‖ : E → ℝ) f <| fun _ ↦ Classical.choice hF

namespace IsRadial

lemma eq_radialPart_comp_norm [Norm E] [Nonempty F] {f : E → F} (hf : f.IsRadial) :
    f = f.radialPart ∘ (‖·‖ : E → ℝ) := by
  ext x
  rw [radialPart]
  exact (hf.extend_apply _ _).symm

lemma even [SeminormedAddGroup E] {f : E → F} (hf : f.IsRadial) : f.Even := fun x ↦ hf (norm_neg x)

lemma comp_right [Norm D] {f : D → E} {g : E → F} (hf : f.IsRadial) :
  (g ∘ f).IsRadial := by grind [isRadial_def]

end IsRadial
section Norm

open IsRadial

lemma RCLike.normSq_radial {K : Type*} [RCLike K] : IsRadial (RCLike.normSq (K := K)) := by
  intro _ _ _
  simpa [RCLike.normSq_eq_def']

lemma Complex.normSq_radial : IsRadial (Complex.normSq) := RCLike.normSq_radial

variable [Norm E]

variable (E) in
lemma _root_.Norm.isRadial : (‖·‖ : E → ℝ).IsRadial := by grind [isRadial_def]

lemma comp_norm (g : ℝ → F) : (g ∘ (‖·‖ : E → ℝ)).IsRadial := by
  simp [IsRadial.comp_right, Norm.isRadial]

variable (E) in
lemma isRadial_norm_sq : IsRadial (‖·‖ ^ 2 : E → ℝ) := by grind [isRadial_def]

end Norm

section Isometries

lemma IsRadial.comp_isometry [SeminormedAddGroup E] {f : E → F} (hf : f.IsRadial) {g : E → E}
    (hg : Isometry g) (hg₀ : g 0 = 0) : f ∘ g = f :=
  funext fun x ↦ hf <| hg.norm_map_of_map_zero hg₀ x

lemma isRadial_iff_comp_linearIsometryEquiv [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → F) : f.IsRadial ↔ ∀ g : E ≃ₗᵢ[ℝ] E, f ∘ g = f := by
  refine ⟨fun hf g ↦ hf.comp_isometry g.isometry (by simp), fun h x y hxy ↦ ?_⟩
  specialize h (ℝ ∙ (x - y))ᗮ.reflection
  rw [← Submodule.reflection_sub hxy, ← f.comp_apply (g := (ℝ ∙ (x - y))ᗮ.reflection), h]

end Isometries

end Function

section RadialSchwartz

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

namespace RadialSchwartzMap

variable {𝕜 E F : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- Create a `RadialSchwartzMap` -/
def mk [NormedSpace ℝ E] (f : 𝓢(E, F)) (hf : IsRadial f) : RadialSchwartzMap 𝕜 E F := ⟨f, hf⟩

section NormedSpace

variable [NormedSpace ℝ E]

instance instFunLike : FunLike (RadialSchwartzMap 𝕜 E F) E F where
  coe f := f.1
  coe_injective := DFunLike.coe_injective.comp Subtype.val_injective

@[simp, norm_cast]
lemma coe_coe (f : RadialSchwartzMap 𝕜 E F) : ⇑(f : 𝓢(E, F)) = f := rfl

@[simp]
lemma zero_apply (x : E) : (0 : RadialSchwartzMap 𝕜 E F) x = 0 := rfl

@[simp]
lemma add_apply (f g : RadialSchwartzMap 𝕜 E F) (x : E) : (f + g) x = f x + g x := rfl

@[simp]
lemma neg_apply (f : RadialSchwartzMap 𝕜 E F) (x : E) : (-f) x = -f x := rfl

@[simp]
lemma sub_apply (f g : RadialSchwartzMap 𝕜 E F) (x : E) : (f - g) x = f x - g x := rfl

@[simp]
lemma smul_apply (c : 𝕜) (f : RadialSchwartzMap 𝕜 E F) (x : E) : (c • f) x = c • f x := rfl

lemma isRadial (f : RadialSchwartzMap 𝕜 E F) : IsRadial f := f.2

lemma _root_.SchwartzMap.mem_radialSchwartzMap_iff_isRadial (f : 𝓢(E, F)) :
    f ∈ RadialSchwartzMap 𝕜 E F ↔ IsRadial f := .rfl

end NormedSpace

lemma _root_.SchwartzMap.mem_radialSchwartzMap_iff_comp_linearIsometryEquiv
    [InnerProductSpace ℝ E] (f : 𝓢(E, F)) :
    f ∈ RadialSchwartzMap 𝕜 E F ↔ ∀ g : E ≃ₗᵢ[ℝ] E, ⇑f ∘ g = ⇑f :=
  isRadial_iff_comp_linearIsometryEquiv _

end RadialSchwartzMap

noncomputable section Fourier

open Real FourierTransform

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
    (hf : f ∈ RadialSchwartzMap 𝕜 E F) : 𝓕 f ∈ RadialSchwartzMap 𝕜 E F := by
  rw [SchwartzMap.mem_radialSchwartzMap_iff_isRadial] at hf ⊢
  exact SchwartzMap.fourier_coe f ▸ hf.fourier

namespace RadialSchwartzMap

variable (𝕜 E F)

lemma map_fourierTransformCLM_le : (RadialSchwartzMap 𝕜 E F).map
    (SchwartzMap.fourierTransformCLM 𝕜 (V := E) (E := F)).toLinearMap ≤ RadialSchwartzMap 𝕜 E F :=
  Submodule.map_le_iff_le_comap.mpr fun _ ↦ fourier_mem_radialSchwartzMap_of_mem_radialSchwartzMap 𝕜

/-- The Fourier transform as a continuous linear map on radial Schwartz functions. -/
def fourierTransformCLM : RadialSchwartzMap 𝕜 E F →L[𝕜] RadialSchwartzMap 𝕜 E F :=
  (SchwartzMap.fourierTransformCLM 𝕜).restrict fun _ ↦
    fourier_mem_radialSchwartzMap_of_mem_radialSchwartzMap 𝕜

instance instFourierTransform :
    FourierTransform (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) where
  fourier := fourierTransformCLM 𝕜 E F

variable {𝕜 E F}

@[simp]
lemma fourierTransformCLM_apply (f : RadialSchwartzMap 𝕜 E F) :
    fourierTransformCLM 𝕜 E F f = 𝓕 f := rfl

@[simp, norm_cast]
lemma coe_fourier (f : RadialSchwartzMap 𝕜 E F) :
    ((𝓕 f : RadialSchwartzMap 𝕜 E F) : 𝓢(E, F)) = 𝓕 (f : 𝓢(E, F)) := rfl

@[simp, norm_cast]
lemma fourier_coe (f : RadialSchwartzMap 𝕜 E F) :
    ((𝓕 f : RadialSchwartzMap 𝕜 E F) : E → F) = 𝓕 (f : E → F) := rfl

section inverse

lemma _root_.Function.Even.fourierInv {f : E → F} (hf : (𝓕 f).Even) {w : E} :
    𝓕⁻ f w = 𝓕 f w := by
  rw [fourierInv_eq_fourier_neg]
  exact hf w

variable (𝕜) in
lemma _root_.SchwartzMap.fourier_eq_fourierInv_of_mem_radialSchwartzMap {f : 𝓢(E, F)}
    (hf : f ∈ RadialSchwartzMap 𝕜 E F) : 𝓕⁻ f = 𝓕 f := by
  ext x
  rw [fourierInv_coe, SchwartzMap.fourier_coe]
  exact Function.Even.fourierInv <| IsRadial.even (hf.fourier)

lemma _root_.SchwartzMap.eqOn_fourier_fourierInv_radialSchwartzMap :
    Set.EqOn (𝓕⁻ : 𝓢(E, F) → 𝓢(E, F)) (𝓕 : 𝓢(E, F) → 𝓢(E, F)) (RadialSchwartzMap 𝕜 E F) :=
  fun _ hf ↦ SchwartzMap.fourier_eq_fourierInv_of_mem_radialSchwartzMap 𝕜 hf

instance instFourierInv :
    FourierTransformInv (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) where
  fourierInv := fourierTransformCLM 𝕜 E F

lemma fourierInv_eq_fourier : (𝓕⁻ : RadialSchwartzMap 𝕜 E F → RadialSchwartzMap 𝕜 E F) = 𝓕 := rfl

lemma coe_fourierInv (f : RadialSchwartzMap 𝕜 E F) : 𝓕⁻ f = 𝓕⁻ (f : 𝓢(E, F)) := by
  rw [fourierInv_eq_fourier, coe_fourier f]
  exact (SchwartzMap.fourier_eq_fourierInv_of_mem_radialSchwartzMap 𝕜 (Submodule.coe_mem f)).symm

variable [CompleteSpace F]

instance instFourierPair : FourierPair (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) where
  fourierInv_fourier_eq := by
    intro f
    rw [← Subtype.val_inj, coe_fourierInv, coe_fourier]
    exact SchwartzMap.instFourierPair.fourierInv_fourier_eq (f : 𝓢(E, F))

variable {f : RadialSchwartzMap 𝕜 E F}

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
    FourierInvPair (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) where
  fourier_fourierInv_eq := by
    intro f
    rw [fourierInv_eq_fourier]
    exact fourierInv_apply_apply

end inverse

section MoreFourierInstances

instance instFourierAdd : FourierAdd (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) where
  fourier_add := fun _ _ ↦ by simp [← Subtype.val_inj]

instance instFourierInvAdd : FourierInvAdd (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) where
  fourierInv_add := instFourierAdd.fourier_add

instance instFourierSMul : FourierSMul 𝕜 (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) where
  fourier_smul := fun _ _ ↦ by simp [← Subtype.val_inj]

instance instFourierInvSMul :
    FourierInvSMul 𝕜 (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) where
  fourierInv_smul := instFourierSMul.fourier_smul

instance instContinuousFourier :
    ContinuousFourier (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) where
  continuous_fourier := ContinuousLinearMap.continuous _

instance instContinuousFourierInv :
    ContinuousFourierInv (RadialSchwartzMap 𝕜 E F) (RadialSchwartzMap 𝕜 E F) where
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

instance instStarAddMonoid : StarAddMonoid (RadialSchwartzMap 𝕜 E F) where
  star := 𝓕
  star_involutive := fun _ ↦ fourier_apply_apply
  star_add := instFourierAdd.fourier_add

instance instStarModule : StarModule ℝ (RadialSchwartzMap 𝕜 E F) where
  star_smul := by
    intro r f
    change 𝓕 (r • f) = star r • 𝓕 f
    rw [star_trivial]
    aesop

variable {f : RadialSchwartzMap 𝕜 E F}

lemma mem_selfAdjoint_iff : f ∈ selfAdjoint (RadialSchwartzMap 𝕜 E F) ↔ 𝓕 f = f := by rfl

lemma mem_skewAdjoint_iff : f ∈ skewAdjoint (RadialSchwartzMap 𝕜 E F) ↔ 𝓕 f = -f := by rfl

lemma selfAdjointPart_eq : selfAdjointPart ℝ f = (1 / 2 : ℝ) • (f + 𝓕 f) := by aesop

lemma skewAdjointPart_eq : skewAdjointPart ℝ f = (1 / 2 : ℝ) • (f - 𝓕 f) := by aesop

end RadialSchwartzMap

end Star

end RadialSchwartz
