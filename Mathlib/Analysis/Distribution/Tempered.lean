/-
Copyright (c) 2024 Jack Valmadre. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Valmadre
-/
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.Topology.Algebra.Module.WeakDual

/-!
# Tempered distributions
-/

open MeasureTheory
open scoped SchwartzMap ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] -- [DenselyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] -- [MeasurableSpace E]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] -- [MeasurableSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

-- Properties from `SchwartzMap.fourierTransformCLM`.
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

-- TODO: Preferable for `𝕜` to come after `V` like `𝓢(V, 𝕜)`? Use name like `𝕜' R C r`?
-- TODO: Better to define directly as type copy of `𝓢(E, 𝕜) →L[𝕜] 𝕜`?
variable (𝕜 E) in
/-- Type copy of `𝓢(E, 𝕜) →L[𝕜] 𝕜` endowed with the weak star topology.

Assumes test functions, linear functionals and linearity have same type `𝕜`.
-/
def TemperedDistribution := WeakDual 𝕜 𝓢(E, 𝕜)

-- TODO: Should this be `𝓢′` (prime) rather than `𝓢'` (apostrophe)?
/-- Notation for the tempered distributions as the dual of the Schwartz space. -/
scoped[TemperedDistribution] notation "𝓢'(" E ", " 𝕜 ")" => TemperedDistribution 𝕜 E

namespace TemperedDistribution

/-- Weak star topology as defined in `WeakDual`. -/
instance instTopologicalSpace : TopologicalSpace (𝓢'(E, 𝕜)) :=
  WeakDual.instTopologicalSpace

noncomputable instance instAddCommMonoid : AddCommMonoid (𝓢'(E, 𝕜)) :=
  WeakDual.instAddCommMonoid

noncomputable instance instModule : Module 𝕜 (𝓢'(E, 𝕜)) :=
  WeakDual.instModule

instance neg : Neg (𝓢'(E, 𝕜)) := ContinuousLinearMap.neg

instance instFunLike : FunLike (𝓢'(E, 𝕜)) (𝓢(E, 𝕜)) 𝕜 :=
  WeakDual.instFunLike

-- TODO: Cleaner to use `DFunLike.ext f g h`?
@[ext] theorem ext {f g : 𝓢'(E, 𝕜)} (h : ∀ φ, f φ = g φ) : f = g := ContinuousLinearMap.ext h

variable (𝕜) in
/-- The Dirac delta as a tempered distribution. -/
noncomputable def delta (x : E) : 𝓢'(E, 𝕜) := SchwartzMap.delta 𝕜 𝕜 x

variable (k V) in
/-- The constant function `1` as a tempered distribution. -/
noncomputable instance one : One 𝓢'(V, 𝕜) where
  one := SchwartzMap.integralCLM 𝕜 volume

-- TODO: Is it better to define this using `ofHasTemperateGrowth`?
variable (V) in
/-- The constant function as a tempered distribution. -/
noncomputable def const (c : 𝕜) : 𝓢'(V, 𝕜) := c • 1

theorem delta_apply {x : E} {φ : 𝓢(E, 𝕜)} : delta 𝕜 x φ = φ x := rfl

theorem one_apply {φ : 𝓢(V, ℂ)} : (1 : 𝓢'(V, ℂ)) φ = ∫ x, φ x := rfl

-- TODO: Remove this and just keep `fourierTransformCLM` to avoid accumulating definitions?
/-- The Fourier transform of a tempered distribution.

The Fourier transform of the continuous linear functional is the linear functional defined by the
the linear functional of the Fourier transform of the test function.
-/
noncomputable def fourierTransform (f : 𝓢'(V, ℂ)) : 𝓢'(V, ℂ) :=
  f ∘L SchwartzMap.fourierTransformCLM ℂ

-- TODO: simp?
theorem fourierTransform_apply {f : 𝓢'(V, ℂ)} :
    fourierTransform f = f ∘L SchwartzMap.fourierTransformCLM ℂ := rfl

-- TODO: simp?
theorem fourierTransform_apply_apply {f : 𝓢'(V, ℂ)} {φ : 𝓢(V, ℂ)} :
    f.fourierTransform φ = f (φ.fourierTransformCLM ℂ) := rfl

-- Can't use `compL (𝕜 := ℂ) (E := 𝓢(V, ℂ)) (Fₗ := 𝓢(V, ℂ)) (Gₗ := ℂ)` because
-- it requires `[SeminormedAddCommGroup E]`, `[NormedSpace 𝕜 E]`, etc.
-- #check ContinuousLinearMap.compL ℂ 𝓢(V, ℂ) 𝓢(V, ℂ) ℂ

/-- Pre-composition with a constant linear functional `L` as a continuous linear map `f ↦ f.comp L`.

Used to define the Fourier transform of a tempered distribution as a continuous linear map.
-/
def precompCLM (L : 𝓢(D, 𝕜) →L[𝕜] 𝓢(E, 𝕜)) : 𝓢'(E, 𝕜) →L[𝕜] 𝓢'(D, 𝕜) where
  toFun f := f ∘L L
  map_add' f g := ContinuousLinearMap.add_comp f g L
  map_smul' c f := ContinuousLinearMap.smul_comp c f L
  cont := WeakDual.continuous_of_continuous_eval fun φ ↦ WeakDual.eval_continuous (L φ)

@[simp]
theorem precompCLM_apply {L : 𝓢(D, 𝕜) →L[𝕜] 𝓢(E, 𝕜)} {f : 𝓢'(E, 𝕜)} : precompCLM L f = f ∘L L := rfl

variable (V) in
/-- Auxiliary function for the definition of `fourierTransformCLE`. -/
noncomputable def fourierTransformCLM : 𝓢'(V, ℂ) →L[ℂ] 𝓢'(V, ℂ) :=
  precompCLM <| SchwartzMap.fourierTransformCLM ℂ

-- TODO: Should this use `fourierTransformCLE` or `fourierTransformCLM`?
-- Using `fourierTransformCLE` makes it easier to prove inverse below.
theorem fourierTransformCLM_apply (f : 𝓢'(V, ℂ)) :
    fourierTransformCLM V f = f ∘L (SchwartzMap.fourierTransformCLE ℂ).toContinuousLinearMap := rfl

theorem fourierTransformCLM_apply_apply (f : 𝓢'(V, ℂ)) (φ : 𝓢(V, ℂ)) :
    fourierTransformCLM V f φ = f (SchwartzMap.fourierTransformCLE ℂ φ) := rfl

variable (V) in
/-- Auxiliary function for the definition of `fourierTransformCLE`. -/
noncomputable def fourierTransformInvCLM : 𝓢'(V, ℂ) →L[ℂ] 𝓢'(V, ℂ) :=
  precompCLM <| (SchwartzMap.fourierTransformCLE ℂ).symm.toContinuousLinearMap

theorem fourierTransformInvCLM_apply (f : 𝓢'(V, ℂ)) :
    fourierTransformInvCLM V f =
    f ∘L (SchwartzMap.fourierTransformCLE ℂ).symm.toContinuousLinearMap := rfl

theorem fourierTransformInvCLM_apply_apply (f : 𝓢'(V, ℂ)) (φ : 𝓢(V, ℂ)) :
    fourierTransformInvCLM V f φ = f ((SchwartzMap.fourierTransformCLE ℂ).symm φ) := rfl

theorem leftInverse_fourierTransformCLM :
    Function.LeftInverse (fourierTransformInvCLM V) (fourierTransformCLM V) :=
  fun f ↦ ext fun φ ↦ by simp [fourierTransformInvCLM_apply, fourierTransformCLM_apply,
    ContinuousLinearMap.comp_apply (R₁ := _)]

theorem rightInverse_fourierTransformCLM :
    Function.RightInverse (fourierTransformInvCLM V) (fourierTransformCLM V) :=
  fun f ↦ ext fun φ ↦ by simp [fourierTransformInvCLM_apply, fourierTransformCLM_apply,
    ContinuousLinearMap.comp_apply (R₁ := _)]


-- TODO: Should `fourierTransformInvCLM` be moved inside here to avoid accumulating definitions?
-- TODO: Generalize beyond `ℂ`?
variable (V) in
/-- The Fourier transform of a tempered distribution as a `ContinuousLinearEquiv`.

The inverse Fourier transform is represented by `(fourierTransformCLE V).symm`.
-/
noncomputable def fourierTransformCLE : 𝓢'(V, ℂ) ≃L[ℂ] 𝓢'(V, ℂ) where
  __ := fourierTransformCLM V
  invFun := fourierTransformInvCLM V
  left_inv := leftInverse_fourierTransformCLM
  right_inv := rightInverse_fourierTransformCLM

theorem fourierTransformCLE_apply {f : 𝓢'(V, ℂ)} :
    fourierTransformCLE V f = f ∘L (SchwartzMap.fourierTransformCLE ℂ).toContinuousLinearMap := rfl

theorem fourierTransformCLE_symm_apply {f : 𝓢'(V, ℂ)} :
    (fourierTransformCLE V).symm f =
    f ∘L (SchwartzMap.fourierTransformCLE ℂ).symm.toContinuousLinearMap := rfl

-- TODO: Define `_apply_coeFn` with `⇑` rather than `_apply_apply`?
theorem fourierTransformCLE_apply_apply {f : 𝓢'(V, ℂ)} {φ : 𝓢(V, ℂ)} :
    fourierTransformCLE V f φ = f (SchwartzMap.fourierTransformCLE ℂ φ) := rfl

theorem fourierTransformCLE_symm_apply_apply {f : 𝓢'(V, ℂ)} {φ : 𝓢(V, ℂ)} :
    (fourierTransformCLE V).symm f φ = f ((SchwartzMap.fourierTransformCLE ℂ).symm φ) := rfl

-- Note: Prefer use of `fourierTransformCLE` over `fourierTransformCLM` and `fourierTransform`.
-- TODO: Rename `fourierTransformCLE` to `fourierTransform` and remove others or make "aux"?

theorem fourierTransformCLE_symm_apply_eq_fourierTransformCLE_comp_compNeg {g : 𝓢'(V, ℂ)} :
    (fourierTransformCLE V).symm g =
    fourierTransformCLE V (g ∘L SchwartzMap.compNegCLM ℂ) := by
  ext φ
  simp only [fourierTransformCLE_apply_apply, fourierTransformCLE_symm_apply_apply,
    ContinuousLinearMap.comp_apply (R₁ := _)]
  refine congrArg g ?_
  ext x
  simp [Real.fourierIntegralInv_eq_fourierIntegral_neg]

theorem fourierTransform_apply_eq_fourierTransformInv_comp_compNeg {g : 𝓢'(V, ℂ)} :
    fourierTransformCLE V g =
    (fourierTransformCLE V).symm (g ∘L SchwartzMap.compNegCLM ℂ) := by
  ext φ
  simp only [fourierTransformCLE_apply_apply, fourierTransformCLE_symm_apply_apply,
    ContinuousLinearMap.comp_apply (R₁ := _)]
  refine congrArg g ?_
  ext x
  simp [Real.fourierIntegralInv_eq_fourierIntegral_neg]

/-- Duality property of the Fourier transform.

If the Fourier transform of `f(x)` is `g(ξ)`, then the Fourier transform of `g(x)` is `f(-ξ)`.
-/
theorem fourierTransform_eq_comp_compNeg_of_fourierTransform_eq {f : 𝓢'(V, ℂ)} {g : 𝓢'(V, ℂ)}
    (h : fourierTransformCLE V f = g) :
    fourierTransformCLE V g = f ∘L SchwartzMap.compNegCLM ℂ := by
  rw [fourierTransform_apply_eq_fourierTransformInv_comp_compNeg] at h
  simp [← h]

-- TODO: Does this definition make it unintuitive to do `rw`?
-- TODO: It feels like there may be a more natural way to express `∘L compNeg`?
/-- Even symmetry `f(-x) = f(x)` for tempered distributions. -/
def EvenSymm (f : 𝓢'(E, 𝕜)) : Prop := f ∘L SchwartzMap.compNegCLM 𝕜 = f

/-- Odd symmetry `f(-x) = -f(x)` for tempered distributions. -/
def OddSymm (f : 𝓢'(E, 𝕜)) : Prop := f ∘L SchwartzMap.compNegCLM 𝕜 = -f

theorem delta_evenSymm : EvenSymm (delta 𝕜 0 : 𝓢'(E, 𝕜)) := by
  ext φ
  simp [ContinuousLinearMap.comp_apply (R₁ := _), delta_apply (𝕜 := _)]

theorem one_evenSymm : EvenSymm (1 : 𝓢'(V, ℂ)) := ext (integral_neg_eq_self · volume)

theorem fourierTransformCLE_delta_eq_one : fourierTransformCLE V (delta ℂ 0) = 1 := by
  ext φ
  simp [fourierTransformCLE_apply_apply, delta_apply, one_apply, Real.fourierIntegral_eq]

theorem fourierTransformCLE_one_eq_delta :
    fourierTransformCLE V 1 = delta ℂ 0 := by
  rw [fourierTransform_eq_comp_compNeg_of_fourierTransform_eq
    fourierTransformCLE_delta_eq_one]
  rw [delta_evenSymm]

theorem fourierTransformCLE_const_eq_smul_delta {c : ℂ} :
    fourierTransformCLE V (const V c) = c • delta ℂ 0 := by
  rw [const, ContinuousLinearEquiv.map_smul, fourierTransformCLE_one_eq_delta]

section Mul

/-- Any smooth function with temperate growth defines a tempered distribution. -/
noncomputable def ofHasTemperateGrowth {f : V → 𝕜} (hf : Function.HasTemperateGrowth f) :
    𝓢'(V, 𝕜) := (1 : 𝓢'(V, 𝕜)).comp (SchwartzMap.bilinLeftCLM (.mul 𝕜 𝕜) hf)

theorem ofHasTemperateGrowth_apply {f : V → 𝕜} (hf : Function.HasTemperateGrowth f) (φ : 𝓢(V, 𝕜)) :
    ofHasTemperateGrowth hf φ = ∫ x, φ x * f x := rfl

/-- Any Schwartz function defines a tempered distribution. -/
noncomputable def ofSchwartzMap (f : 𝓢(V, 𝕜)) : 𝓢'(V, 𝕜) :=
  ofHasTemperateGrowth f.hasTemperateGrowth

theorem ofSchwartzMap_apply (f : 𝓢(V, 𝕜)) (φ : 𝓢(V, 𝕜)) : ofSchwartzMap f φ = ∫ x, φ x * f x := rfl

end Mul

end TemperedDistribution
