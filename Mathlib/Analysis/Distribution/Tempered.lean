/-
Copyright (c) 2024 Jack Valmadre. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Valmadre
-/
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.Distribution.Periodic
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.Topology.Algebra.Module.WeakDual

/-!
# Tempered distributions

## Main theorems

* `fourierTransform_delta_zero`
* `fourierTransform_one`
* `fourierTransform_exp_inner_mul_I`
* `fourierTransform_delta`
-/

open MeasureTheory
open scoped ContinuousLinearMap ENNReal SchwartzMap FourierTransform

variable {𝕜 D E F G V : Type*}
  [NormedAddCommGroup D] [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup V]

namespace SchwartzMap

section Basic

-- TODO: Review `SMulCommClass ℝ 𝕜 𝕜`. Could use `NormedAlgebra ℝ 𝕜`; less general?
variable [NormedField 𝕜] [NormedSpace ℝ 𝕜] [SMulCommClass ℝ 𝕜 𝕜] [MeasurableSpace D]
  [NormedSpace ℝ E]

variable (𝕜 E) in
/-- Type copy of `𝓢(E, 𝕜) →L[𝕜] 𝕜` endowed with the weak star topology.

Assumes test functions, linear functionals and linearity have same type `𝕜`.
-/
def Distribution := 𝓢(E, 𝕜) →L[𝕜] 𝕜  -- WeakDual 𝕜 𝓢(E, 𝕜)

-- TODO: Should we just use `WeakDual 𝕜 𝓢(E, 𝕜)` directly?
-- TODO: Should this be `𝓢′` (prime) rather than `𝓢'` (apostrophe)?
/-- Notation for the tempered distributions as the dual of the Schwartz space. -/
scoped[SchwartzMap] notation "𝓢'(" E ", " 𝕜 ")" => Distribution 𝕜 E

namespace Distribution

noncomputable instance instAddCommMonoid : AddCommMonoid (𝓢'(E, 𝕜)) := WeakDual.instAddCommMonoid

noncomputable instance instModule : Module 𝕜 (𝓢'(E, 𝕜)) := WeakDual.instModule

/-- Weak star topology as defined in `WeakDual`. -/
instance instTopologicalSpace : TopologicalSpace (𝓢'(E, 𝕜)) := WeakDual.instTopologicalSpace

instance instContinuousAdd : ContinuousAdd (𝓢'(E, 𝕜)) := WeakDual.instContinuousAdd

instance instFunLike : FunLike (𝓢'(E, 𝕜)) (𝓢(E, 𝕜)) 𝕜 :=
  WeakDual.instFunLike

instance instContinuousLinearMapClass : ContinuousLinearMapClass 𝓢'(E, 𝕜) 𝕜 𝓢(E, 𝕜) 𝕜 :=
  WeakDual.instContinuousLinearMapClass

-- TODO: Can this be added to `WeakDual`?
instance instNeg : Neg (𝓢'(E, 𝕜)) := ContinuousLinearMap.neg

section Monoid

variable (M : Type*) [Monoid M] [DistribMulAction M 𝕜]
  [SMulCommClass 𝕜 M 𝕜] [ContinuousConstSMul M 𝕜]

instance instMulAction : MulAction M 𝓢'(E, 𝕜) := WeakDual.instMulAction M

instance instDistribMulAction : DistribMulAction M 𝓢'(E, 𝕜) := WeakDual.instDistribMulAction M

instance instContinuousConstSMul : ContinuousConstSMul M 𝓢'(E, 𝕜) :=
  WeakDual.instContinuousConstSMul M

instance instContinuousSMul [TopologicalSpace M] [ContinuousSMul M 𝕜] : ContinuousSMul M 𝓢'(E, 𝕜) :=
  WeakDual.instContinuousSMul M

end Monoid

-- TODO: Cleaner to use `DFunLike.ext f g h`?
@[ext] theorem ext {f g : 𝓢'(E, 𝕜)} (h : ∀ φ, f φ = g φ) : f = g := ContinuousLinearMap.ext h

-- Note: Does not assume `RCLike 𝕜`.
variable (𝕜) in
/-- The Dirac delta as a tempered distribution. -/
def delta (x : E) : 𝓢'(E, 𝕜) :=
  SchwartzMap.mkCLMtoNormedSpace (· x) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    ⟨Finset.Iic 0, 1, zero_le_one, fun φ ↦ by
      simpa using one_add_le_sup_seminorm_apply (m := 0) (le_refl 0) (le_refl 0) φ x⟩

theorem delta_apply (x : E) (φ : 𝓢(E, 𝕜)) : delta 𝕜 x φ = φ x := rfl

/-- Pre-composition with a constant linear map `L` as a continuous linear map `f ↦ f.comp L`.

This is used to define the Fourier transform of a tempered distribution as a continuous linear map.

(We can't use `ContinuousLinearMap.compL` as it would require `SeminormedAddCommGroup` and
`NormedSpace 𝕜` for `SchwartzMap`.)
-/
def precomp (L : 𝓢(E, 𝕜) →L[𝕜] 𝓢(E, 𝕜)) : 𝓢'(E, 𝕜) →L[𝕜] 𝓢'(E, 𝕜) where
  toFun f := f ∘L L
  map_add' f g := ContinuousLinearMap.add_comp f g L
  map_smul' c f := ContinuousLinearMap.smul_comp c f L
  cont := WeakDual.continuous_of_continuous_eval fun φ ↦ WeakDual.eval_continuous (L φ)

@[simp]
theorem precomp_apply (L : 𝓢(E, 𝕜) →L[𝕜] 𝓢(E, 𝕜)) (f : 𝓢'(E, 𝕜)) : precomp L f = f ∘L L := rfl

theorem coeFn_precomp (L : 𝓢(E, 𝕜) →L[𝕜] 𝓢(E, 𝕜)) : ⇑(precomp L) = (· ∘L L) := rfl

-- TODO: Should `f, μ` be `outParam`?
/-- The condition that a tempered distribution is equal to an integral against a known function and
measure. -/
def IsIntegral [MeasurableSpace E] (F : 𝓢'(E, 𝕜)) (μ : Measure E) (f : E → 𝕜) : Prop :=
  ∀ φ, F φ = ∫ x, φ x * f x ∂μ

theorem isIntegral_iff [MeasurableSpace E] (F : 𝓢'(E, 𝕜)) (μ : Measure E) (f : E → 𝕜) :
    F.IsIntegral μ f ↔ ∀ φ, F φ = ∫ x, φ x * f x ∂μ := Iff.rfl

end Distribution

end Basic

namespace Distribution

section One

variable [RCLike 𝕜] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

/-- The constant function `1` as a tempered distribution. -/
noncomputable instance one : One 𝓢'(D, 𝕜) where
  one := SchwartzMap.integralCLM 𝕜 volume

@[simp]
theorem coeFn_one : ⇑(1 : 𝓢'(D, 𝕜)) = fun φ ↦ ∫ x, φ x := rfl

end One

section Lp

variable [RCLike 𝕜] [NormedSpace ℝ D] [MeasurableSpace D] [OpensMeasurableSpace D]

variable {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {μ : Measure D} [hμ : μ.HasTemperateGrowth]

instance : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.IsConjExponent.one_le <| .symm <| .conjExponent hp.out⟩

-- TODO: Is this less general than `ofLp`? Does it support `AEEqFun`?
/-- Define tempered distribution `φ ↦ ∫ x, φ x * f x ∂μ` from function in `L^p` on given measure. -/
noncomputable def ofMemℒp (f : D → 𝕜) (hf : Memℒp f p μ) : 𝓢'(D, 𝕜) :=
  L1.integralCLM' 𝕜
  ∘L .bilinearRightLpL 𝕜 (.flip <| .mul 𝕜 𝕜)
    (.trans (ENNReal.IsConjExponent.conjExponent hp.out).inv_add_inv_conj (@inv_one ENNReal).symm)
    (hf.toLp)
  ∘L SchwartzMap.toLpCLM 𝕜 𝕜 p.conjExponent μ

theorem coeFn_ofMemℒp {f : D → 𝕜} (hf : Memℒp f p μ) :
    ⇑(ofMemℒp f hf) = (∫ x, · x * f x ∂μ) := by
  ext φ
  rw [ofMemℒp]
  simp only [@ContinuousLinearMap.comp_apply _]
  change L1.integralCLM _ = _
  rw [← MeasureTheory.L1.integral_eq, L1.integral_eq_integral]
  refine integral_congr_ae ?_
  refine .trans (ContinuousLinearMap.coeFn_bilinearRightLpL _ _ _ _) ?_
  simpa using .mul SchwartzMap.coeFn_toLpCLM hf.coeFn_toLp

theorem ofMemℒp_isIntegral {f : D → 𝕜} (hf : Memℒp f p μ) : (ofMemℒp f hf).IsIntegral μ f :=
  congrFun (coeFn_ofMemℒp hf)

end Lp

section HasTemperateGrowth

variable [RCLike 𝕜] [NormedSpace ℝ D]

-- TODO: Remove this?
-- TODO: Define analogous method for L^p?
/-- Multiplication on the right by a `HasTemperateGrowth` function. -/
noncomputable def mulRight_hasTemperateGrowth (g : 𝓢'(D, 𝕜)) {f : D → 𝕜}
    (hf : Function.HasTemperateGrowth f) : 𝓢'(D, 𝕜) :=
  g.comp (SchwartzMap.bilinLeftCLM (.mul 𝕜 𝕜) hf)

variable [MeasurableSpace D] [BorelSpace D] [SecondCountableTopology D]

/-- Define tempered distribution `φ ↦ ∫ x, φ x * f x ∂μ` from function and measure with temperate
growth. -/
noncomputable def ofHasTemperateGrowth (f : D → 𝕜) (hf : f.HasTemperateGrowth)
    (μ : Measure D := by volume_tac) [hμ : μ.HasTemperateGrowth] : 𝓢'(D, 𝕜) :=
  SchwartzMap.integralCLM 𝕜 μ ∘L SchwartzMap.bilinLeftCLM (.mul 𝕜 𝕜) hf

theorem coeFn_ofHasTemperateGrowth {f : D → 𝕜} {hf : f.HasTemperateGrowth}
    {μ : Measure D} [hμ : μ.HasTemperateGrowth] :
    ⇑(ofHasTemperateGrowth f hf μ) = (∫ x, · x * f x ∂μ) := rfl

theorem ofHasTemperateGrowth_isIntegral {f : D → 𝕜} {hf : f.HasTemperateGrowth}
    {μ : Measure D} [hμ : μ.HasTemperateGrowth] : (ofHasTemperateGrowth f hf μ).IsIntegral μ f :=
  fun _ ↦ rfl

end HasTemperateGrowth

section Fourier

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

-- TODO: Could be generalized from `ℂ` to `𝕜` with `NormedSpace ℂ 𝕜`?
-- Currently require `RCLike 𝕜` and `NormedSpace ℂ 𝕜` from `SchwartzMap.fourierTransformCLM`.
variable (V) in
/-- Auxiliary function for the definition of `fourierTransformCLE`. -/
noncomputable def fourierTransformCLM : 𝓢'(V, ℂ) →L[ℂ] 𝓢'(V, ℂ) :=
  precomp <| SchwartzMap.fourierTransformCLM ℂ

theorem coeFn_fourierTransformCLM (f : 𝓢'(V, ℂ)) :
    fourierTransformCLM V f = fun φ ↦ f (SchwartzMap.fourierTransformCLE ℂ φ) := rfl

variable (V) in
/-- Auxiliary function for the definition of `fourierTransformCLE`. -/
noncomputable def fourierTransformInvCLM : 𝓢'(V, ℂ) →L[ℂ] 𝓢'(V, ℂ) :=
  precomp (SchwartzMap.fourierTransformCLE ℂ).symm.toContinuousLinearMap

theorem coeFn_fourierTransformInvCLM (f : 𝓢'(V, ℂ)) :
    fourierTransformInvCLM V f = fun φ ↦ f ((SchwartzMap.fourierTransformCLE ℂ).symm φ) := rfl

theorem leftInverse_fourierTransformCLM :
    Function.LeftInverse (fourierTransformInvCLM V) (fourierTransformCLM V) :=
  fun f ↦ ext fun φ ↦ by simp [coeFn_fourierTransformCLM, coeFn_fourierTransformInvCLM]

theorem rightInverse_fourierTransformCLM :
    Function.RightInverse (fourierTransformInvCLM V) (fourierTransformCLM V) :=
  fun f ↦ ext fun φ ↦ by simp [coeFn_fourierTransformCLM, coeFn_fourierTransformInvCLM]

-- TODO: Should `fourierTransformInvCLM` be moved inside here to avoid accumulating definitions?
/-- The Fourier transform of a tempered distribution as a `ContinuousLinearEquiv`.
The inverse Fourier transform is represented by `(fourierTransformCLE V).symm`.
-/
noncomputable def fourierTransformCLE : 𝓢'(V, ℂ) ≃L[ℂ] 𝓢'(V, ℂ) :=
  { fourierTransformCLM V with
    invFun := fourierTransformInvCLM V
    left_inv := leftInverse_fourierTransformCLM
    right_inv := rightInverse_fourierTransformCLM }

theorem coeFn_fourierTransformCLE (f : 𝓢'(V, ℂ)) :
    fourierTransformCLE f = f ∘ SchwartzMap.fourierTransformCLE ℂ := rfl

theorem coeFn_fourierTransformCLE_symm (f : 𝓢'(V, ℂ)) :
    fourierTransformCLE.symm f = f ∘ (SchwartzMap.fourierTransformCLE ℂ).symm := rfl

/-- Notation for the Fourier transform of a Schwartz function. -/
notation "𝓕ₛ[" 𝕜 "]" => SchwartzMap.fourierTransformCLE 𝕜

/-- Notation for the Fourier transform of a tempered distribution. -/
notation "𝓕ₜ" => fourierTransformCLE

/-- The inverse Fourier transform is the mirror of the Fourier transform. -/
theorem fourierTransform_symm_eq_comp_fourierTransform_compNeg (f : 𝓢'(V, ℂ)) :
    (𝓕ₜ).symm f = 𝓕ₜ f ∘L SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (.neg ℝ) := by
  ext φ
  simp only [@coeFn_fourierTransformCLE _, coeFn_fourierTransformCLE_symm, Function.comp_apply,
    @ContinuousLinearMap.comp_apply _]
  refine congrArg f ?_
  -- TODO: Add `SchwartzMap.coeFn_fourierTransformCLE` (avoid `ext`).
  ext x
  simpa using congrFun (Real.fourierIntegralInv_eq_fourierIntegral_comp_neg φ) x

/-- The inverse Fourier transform is the Fourier transform of the mirror. -/
theorem fourierTransform_symm_eq_fourierTransform_comp_compNeg (f : 𝓢'(V, ℂ)) :
    (𝓕ₜ).symm f = 𝓕ₜ (f ∘L SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (.neg ℝ)) := by
  ext φ
  simp only [coeFn_fourierTransformCLE, coeFn_fourierTransformCLE_symm, Function.comp_apply,
    @ContinuousLinearMap.comp_apply _]
  refine congrArg f ?_
  ext x
  simpa using Real.fourierIntegralInv_eq_fourierIntegral_neg φ x

/-- Duality of the Fourier transform. -/
theorem fourierTransform_eq_of_fourierTransform_eq {g g' : 𝓢'(V, ℂ)} (h : 𝓕ₜ g = g') :
    𝓕ₜ g' = g ∘L compCLMOfContinuousLinearEquiv ℂ (.neg ℝ) := by
  have : compCLMOfContinuousLinearEquiv ℂ (.neg ℝ) ∘L compCLMOfContinuousLinearEquiv ℂ (.neg ℝ) =
      ContinuousLinearMap.id ℂ 𝓢(V, ℂ) := by ext; simp
  rw [← fourierTransformCLE.eq_symm_apply, fourierTransform_symm_eq_fourierTransform_comp_compNeg,
    ContinuousLinearMap.comp_assoc, this, ContinuousLinearMap.comp_id]
  exact h.symm

/-- Transfer results from `SchwartzMap` to `TemperedDistribution`.

Given a Fourier transform for Schwartz maps `𝓕ₛ[ℂ] (a φ) = b (𝓕ₛ[ℂ] φ)`, obtain the Fourier
transform of the distribution `g ∘L b`.
-/
theorem of_schwartzMapFourier_eq {a : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)} {b : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)}
    (h : ∀ φ : 𝓢(V, ℂ), 𝓕ₛ[ℂ] (a φ) = b (𝓕ₛ[ℂ] φ)) (g : 𝓢'(V, ℂ)) :
    𝓕ₜ (g ∘L b) = (𝓕ₜ g) ∘L a := by
  ext φ
  simpa [coeFn_fourierTransformCLE] using congrArg g (h φ).symm

variable (V) in
theorem fourierTransform_delta_zero : 𝓕ₜ (delta ℂ (0 : V)) = 1 := by
  ext φ
  simp [coeFn_fourierTransformCLE, delta_apply, Real.fourierIntegral_eq]

variable (V) in
theorem fourierTransform_one : 𝓕ₜ (1 : 𝓢'(V, ℂ)) = delta ℂ 0 := by
  rw [fourierTransform_eq_of_fourierTransform_eq (fourierTransform_delta_zero V)]
  ext φ
  simp [@ContinuousLinearMap.comp_apply _, @delta_apply _]

end Fourier

section Composition

variable [RCLike 𝕜] [NormedSpace ℝ D]

-- TODO: Instead write `compAffineEquivCLM` and eliminate this definition?
-- TODO: Later useful to write this as CLE `≃L[𝕜]`?
variable (𝕜) in
/-- Composition with addition on the right as a continuous linear map `φ ↦ φ ∘ (· + a)`. -/
def _root_.SchwartzMap.compAddRight (a : D) : 𝓢(D, 𝕜) →L[𝕜] 𝓢(D, 𝕜) :=
  compCLMOfAntilipschitz 𝕜 (g := (· + a)) (K := 1) (.add .id (.const a)) (fun _ _ ↦ by simp)

@[simp]
theorem _root_.SchwartzMap.coeFn_compAddRight (a : D) (φ : 𝓢(D, 𝕜)) :
    ⇑(SchwartzMap.compAddRight 𝕜 a φ) = φ ∘ (· + a) := rfl

end Composition

section ExpInner

open Complex
open scoped Real

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Statement of `VectorFourier.fourierIntegral_comp_add_right` for tempered distributions. -/
theorem fourierTransform_comp_mul_exp_inner_mul_I (G : 𝓢'(V, ℂ)) (a : V) :
    𝓕ₜ (G ∘L bilinLeftCLM (.mul ℂ ℂ) (g := fun x ↦ exp ((2 * π * inner a x : ℝ) * I))
      (.comp Complex.exp_ofReal_mul_I_hasTemperateGrowth
        (.mul (.const _) (innerSL ℝ a).hasTemperateGrowth))) =
    𝓕ₜ G ∘L compAddRight ℂ a := by
  symm  -- TODO: Should we flip the definition?
  ext φ
  simp only [@coeFn_fourierTransformCLE _, Function.comp_apply, @ContinuousLinearMap.comp_apply _]
  refine congrArg G ?_
  ext x
  simp only [fourierTransformCLE_apply, coeFn_compAddRight, coeFn_bilinLeftCLM,
    ContinuousLinearMap.mul_apply', Real.fourierIntegral]
  rw [VectorFourier.fourierIntegral_comp_add_right]
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, innerₗ_apply]
  ring

theorem one_comp_bilinLeftCLM_mul {f : V → ℂ} (hf : f.HasTemperateGrowth) :
    (1 : 𝓢'(V, ℂ)) ∘L bilinLeftCLM (.mul ℂ ℂ) hf = ofHasTemperateGrowth f hf := rfl

-- TODO: Check that the below works with `ofMemℒp`:
-- ofMemℒp (fun x ↦ exp ((inner a x : ℝ) * I)) (p := ⊤) (μ := volume)
--   (memℒp_top_of_bound (Continuous.aestronglyMeasurable <| .cexp <| .mul
--     (.comp ofRealCLM.continuous (innerSL ℝ a).continuous) continuous_const) 1 (by simp))

-- TODO: Use `fun x ↦ (𝐞 (inner a x) : ℂ)` (Real.fourierChar) instead?
-- TODO: Add two_pi to the name or use `delta ℂ ((2 * π)⁻¹ • a)`?

/-- The Fourier transform of `x ↦ exp (2 * π * inner a x * I)` is `δ a` -/
theorem fourierTransform_exp_inner_mul_I (a : V) :
    𝓕ₜ (ofHasTemperateGrowth (fun x ↦ exp ((2 * π * inner a x : ℝ) * I))
      (.comp Complex.exp_ofReal_mul_I_hasTemperateGrowth
        (.mul (.const _) (innerSL ℝ a).hasTemperateGrowth))) =
    delta ℂ a := by
  ext φ
  simpa [fourierTransform_one, @ContinuousLinearMap.comp_apply _, @delta_apply _] using
    DFunLike.congr_fun (fourierTransform_comp_mul_exp_inner_mul_I (1 : 𝓢'(V, ℂ)) a) φ

/-- The Fourier transform of `x ↦ exp (2 * π * inner a x * I)` is `δ a` -/
theorem fourierTransform_delta (a : V) :
    𝓕ₜ (delta ℂ a) = ofHasTemperateGrowth (fun x ↦ exp ((2 * π * -inner a x : ℝ) * I))
      (.comp Complex.exp_ofReal_mul_I_hasTemperateGrowth
        (.mul (.const _) (innerSL ℝ a).hasTemperateGrowth.neg)) := by
  rw [fourierTransform_eq_of_fourierTransform_eq (fourierTransform_exp_inner_mul_I a)]
  ext φ
  rw [ContinuousLinearMap.comp_apply]
  simp only [@coeFn_ofHasTemperateGrowth _]
  rw [← MeasureTheory.integral_neg_eq_self]
  simp

end ExpInner

end Distribution

end SchwartzMap
