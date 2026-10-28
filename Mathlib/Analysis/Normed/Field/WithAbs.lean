/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Field.TransferInstance
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.MetricSpace.Completion

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.UniformField

/-!
# WithAbs for fields

This extends the `WithAbs` mechanism to fields, providing a type synonym for a field which depends
on an absolute value. This is useful when dealing with several absolute values on the same field.

In particular this allows us to define the completion of a field at a given absolute value.
-/

public section

open Topology

namespace WithAbs

variable {R S : Type*} [Semiring S] [PartialOrder S]

section Field

variable [Field R] {T : Type*} [Field T] (v : AbsoluteValue R S)

instance : Field (WithAbs v) := fast_instance% (equiv v).field

noncomputable instance normedField (v : AbsoluteValue R ℝ) : NormedField (WithAbs v) :=
  letI := v.toNormedField
  fast_instance% (equiv v).normedField

instance [Module R T] [FiniteDimensional R T] :
    FiniteDimensional (WithAbs v) T :=
  Module.Finite.of_restrictScalars_finite R (WithAbs v) T

instance [Module T R] [FiniteDimensional T R] :
    FiniteDimensional T (WithAbs v) :=
  Module.Finite.equiv (linearEquiv T v).symm

instance [Algebra R T] [Algebra.IsSeparable R T] :
    Algebra.IsSeparable (WithAbs v) T :=
  .of_equiv_equiv (equiv v).symm (.refl T) (by ext; simp [algebraMap_left_apply])

instance [Algebra T R] [Algebra.IsSeparable T R] :
    Algebra.IsSeparable T (WithAbs v) :=
  AlgEquiv.Algebra.isSeparable (algEquiv T v).symm

@[simp] lemma toAbs_div (x y : R) : toAbs v (x / y) = toAbs v x / toAbs v y := rfl
@[simp] lemma ofAbs_div (x y : WithAbs v) : ofAbs (x / y) = ofAbs x / ofAbs y := rfl

@[simp] lemma toAbs_inv (x : R) : toAbs v x⁻¹ = (toAbs v x)⁻¹ := rfl
@[simp] lemma ofAbs_inv (x : WithAbs v) : ofAbs (x⁻¹) = (ofAbs x)⁻¹ := rfl

/- Note that `AbsoluteValue.tendsto_div_one_add_pow_nhds_one` would follow from the below
result if `WithAbs v` had a topology for general value rings `S`. Currently `WithAbs v` only has
a topology when `S = ℝ`. -/
theorem tendsto_one_div_one_add_pow_nhds_one {v : AbsoluteValue R ℝ} {a : R} (ha : v a < 1) :
    Filter.atTop.Tendsto (fun n ↦ (equiv v).symm (1 / (1 + a ^ n))) (𝓝 1) := by
  simpa using! inv_one (G := WithAbs v) ▸ (tendsto_inv_iff₀ one_ne_zero).2
    (tendsto_iff_norm_sub_tendsto_zero.2 <| by simpa using! ha)

end Field

section CommRing

variable [CommRing R] {T : Type*} [Field T] [Algebra R T] (w : AbsoluteValue T ℝ)

instance : UniformContinuousConstSMul R (WithAbs w) where
  uniformContinuous_const_smul r := by
    simp_rw [Algebra.smul_def]
    exact (Ring.uniformContinuousConstSMul _).uniformContinuous_const_smul _

end CommRing

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : AbsoluteValue K ℝ)
  (w : AbsoluteValue L ℝ) [w.LiesOver v]

theorem isometry_map : Isometry (WithAbs.map v w (algebraMap K L)) := by
  rw [← AbsoluteValue.LiesOver.under_eq w v, AddMonoidHomClass.isometry_iff_norm]
  simp_rw [map_apply, norm_eq_apply_ofAbs]
  simp [AbsoluteValue.under_def]

end WithAbs

end

/-!
### The completion of a field at an absolute value.
-/

@[expose] public section

namespace AbsoluteValue

open WithAbs

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- The completion of a field with respect to a real absolute value, as a one-field structure
wrapping the uniform-space completion of `WithAbs v`. -/
structure Completion where
  /-- Wrap an element of the underlying completion `UniformSpace.Completion (WithAbs v)` into
  `v.Completion`. -/
  ofCompletion ::
  /-- The underlying element of the completion `UniformSpace.Completion (WithAbs v)`. -/
  toCompletion : UniformSpace.Completion (WithAbs v)

section Notation

open Lean.PrettyPrinter.Delaborator

/-- Prevents `ofCompletion v x` being printed as `{ toCompletion := x }`
by `delabStructureInstance`. -/
@[app_delab Completion.ofCompletion]
meta def Completion.delabOfCompletion : Delab := delabApp

end Notation

namespace Completion

/-- `Completion.toCompletion` and `Completion.ofCompletion` as an equivalence. -/
@[simps]
def equivCompletion : v.Completion ≃ UniformSpace.Completion (WithAbs v) where
  toFun := toCompletion
  invFun := ofCompletion
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : NormedField v.Completion := fast_instance% (equivCompletion v).normedField

/-- `Completion.toCompletion` as a ring isomorphism onto the underlying completion. -/
@[simps! apply]
def equiv : v.Completion ≃+* UniformSpace.Completion (WithAbs v) where
  toEquiv := equivCompletion v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp] lemma toCompletion_ofCompletion (x : UniformSpace.Completion (WithAbs v)) :
    toCompletion (ofCompletion x : v.Completion) = x := rfl
@[simp] lemma ofCompletion_toCompletion (x : v.Completion) :
    ofCompletion x.toCompletion = x := rfl

@[simp] lemma toCompletion_zero : (0 : v.Completion).toCompletion = 0 := rfl
@[simp] lemma toCompletion_one : (1 : v.Completion).toCompletion = 1 := rfl
@[simp] lemma toCompletion_add (x y : v.Completion) :
    (x + y).toCompletion = x.toCompletion + y.toCompletion := rfl
@[simp] lemma toCompletion_mul (x y : v.Completion) :
    (x * y).toCompletion = x.toCompletion * y.toCompletion := rfl

@[ext] theorem ext {v : AbsoluteValue K ℝ} {x y : v.Completion}
    (h : x.toCompletion = y.toCompletion) : x = y := by
  cases x; cases y; exact congrArg ofCompletion h

theorem toCompletion_surjective : Function.Surjective (toCompletion (v := v)) :=
  (equivCompletion v).surjective

theorem ofCompletion_surjective : Function.Surjective (ofCompletion (v := v)) :=
  (equivCompletion v).symm.surjective

@[simp] lemma norm_toCompletion (x : v.Completion) : ‖x.toCompletion‖ = ‖x‖ := rfl

@[simp] lemma norm_ofCompletion (x : UniformSpace.Completion (WithAbs v)) :
    ‖(ofCompletion x : v.Completion)‖ = ‖x‖ := rfl

theorem isometry_toCompletion : Isometry (toCompletion (v := v)) :=
  Isometry.of_dist_eq fun _ _ ↦ rfl

/-- `Completion.toCompletion` as an isometry equivalence onto the underlying completion. -/
noncomputable def isometryEquivCompletion :
    v.Completion ≃ᵢ UniformSpace.Completion (WithAbs v) where
  toEquiv := equivCompletion v
  isometry_toFun := isometry_toCompletion v

theorem continuous_toCompletion : Continuous (toCompletion (v := v)) :=
  (isometry_toCompletion v).continuous

theorem continuous_ofCompletion : Continuous (ofCompletion (v := v)) :=
  (isometryEquivCompletion v).symm.continuous

instance : CompleteSpace v.Completion :=
  ((isometry_toCompletion v).isUniformInducing.completeSpace_congr
    (toCompletion_surjective v)).mpr inferInstance

noncomputable instance : Inhabited v.Completion := ⟨0⟩

/-- Coercion of an element of `WithAbs v` into the completion. -/
noncomputable instance : Coe (WithAbs v) v.Completion where
  coe x := ofCompletion (x : UniformSpace.Completion (WithAbs v))

/-- Coercion of an element of `K` into the completion. -/
noncomputable instance : Coe K v.Completion where
  coe k := ofCompletion (toAbs v k : UniformSpace.Completion (WithAbs v))

@[simp] lemma coe_toCompletion (x : WithAbs v) :
    (x : v.Completion).toCompletion = (x : UniformSpace.Completion (WithAbs v)) := rfl

@[norm_cast] lemma coe_zero : ((0 : K) : v.Completion) = 0 := by ext; simp
@[norm_cast] lemma coe_one : ((1 : K) : v.Completion) = 1 := by ext; simp
@[norm_cast] lemma coe_add (x y : K) : ((x + y : K) : v.Completion) = ↑x + ↑y := by
  ext; simp [UniformSpace.Completion.coe_add]
@[norm_cast] lemma coe_mul (x y : K) : ((x * y : K) : v.Completion) = ↑x * ↑y := by
  ext; simp [UniformSpace.Completion.coe_mul]

lemma norm_coe (x : WithAbs v) : ‖(x : v.Completion)‖ = v x.ofAbs :=
  UniformSpace.Completion.norm_coe x

theorem continuous_coe : Continuous ((↑) : WithAbs v → v.Completion) :=
  (continuous_ofCompletion v).comp (UniformSpace.Completion.continuous_coe _)

theorem denseRange_coe : DenseRange ((↑) : WithAbs v → v.Completion) :=
  (ofCompletion_surjective v).denseRange.comp UniformSpace.Completion.denseRange_coe
    (continuous_ofCompletion v)

/-- Induction on the completion of a field at an absolute value: a closed property that
holds on the image of `K` holds everywhere. -/
@[elab_as_elim]
theorem induction_on {p : v.Completion → Prop} (x : v.Completion) (hp : IsClosed {x | p x})
    (ih : ∀ a : WithAbs v, p a) : p x :=
  UniformSpace.Completion.induction_on (p := fun y ↦ p (ofCompletion y)) x.toCompletion
    (hp.preimage (continuous_ofCompletion v)) ih

/-- Two continuous functions out of `v.Completion` into a Hausdorff space that agree on `K`
are equal. -/
theorem ext_of_continuous {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f g : v.Completion → Y}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ a : WithAbs v, f a = g a) : f = g :=
  (denseRange_coe v).equalizer hf hg (funext h)

section Algebra

variable (R : Type*) [CommSemiring R] [Algebra R (WithAbs v)]
  [UniformContinuousConstSMul R (WithAbs v)]

noncomputable instance : Algebra R v.Completion := fast_instance% (equivCompletion v).algebra R

theorem algebraMap_toCompletion (r : R) :
    (algebraMap R v.Completion r).toCompletion =
      algebraMap R (UniformSpace.Completion (WithAbs v)) r := rfl

end Algebra

@[simp] theorem algebraMap_apply (k : K) : algebraMap K v.Completion k = (k : v.Completion) := rfl

section LiesOver

variable {L : Type*} [Field L] [Algebra K L] (w : AbsoluteValue L ℝ) [w.LiesOver v]

/-- If `w` lies over `v`, then the ring homomorphism `v.Completion →+* w.Completion` induced by
`algebraMap K L`. -/
noncomputable def map : v.Completion →+* w.Completion :=
  ((equiv w).symm.toRingHom.comp <| UniformSpace.Completion.mapRingHom
    (WithAbs.map v w (algebraMap K L)) (WithAbs.isometry_map v w).continuous).comp
    (equiv v).toRingHom

theorem isometry_map : Isometry (map v w) :=
  (isometryEquivCompletion w).symm.isometry.comp <|
    (UniformSpace.Completion.isometry_mapRingHom (WithAbs.isometry_map v w)).comp
      (isometry_toCompletion v)

theorem continuous_map : Continuous (map v w) :=
  (isometry_map v w).continuous

@[simp]
theorem map_coe (x : WithAbs v) :
    map v w (x : v.Completion) = (WithAbs.map v w (algebraMap K L) x : w.Completion) :=
  ext <| UniformSpace.Completion.mapRingHom_coe _ x

/-- If `w` lies over `v` with completions `K_v` and `L_w`, then there is a unique `K_v`-algebra
structure on `L_w` satisfying both `IsScalarTower K K_v L_w` and `ContinuousSMul K_v L_w`,
see `AbsoluteValue.Completion.algebraMap_eq` and `AbsoluteValue.Completion.algebra_eq`. -/
@[instance_reducible]
noncomputable def algebraOfLiesOver : Algebra v.Completion w.Completion :=
  (map v w).toAlgebra

instance : letI := algebraOfLiesOver v w
    IsScalarTower K v.Completion w.Completion :=
  let := algebraOfLiesOver v w
  IsScalarTower.of_algebraMap_eq fun x ↦ (map_coe v w (toAbs v x)).symm

instance : letI := algebraOfLiesOver v w
    ContinuousSMul v.Completion w.Completion :=
  let := algebraOfLiesOver v w
  continuousSMul_of_algebraMap v.Completion w.Completion (continuous_map v w)

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]
  [ContinuousSMul v.Completion w.Completion]

theorem algebraMap_eq : algebraMap v.Completion w.Completion = map v w :=
  DFunLike.ext' <| ext_of_continuous v (continuous_algebraMap _ _) (continuous_map v w) fun x ↦
    (IsScalarTower.algebraMap_apply K v.Completion w.Completion x.ofAbs).symm.trans
      (map_coe v w x).symm

theorem algebraMap_of_liesOver_apply (x : v.Completion) :
    algebraMap v.Completion w.Completion x = map v w x := by
  rw [algebraMap_eq]

theorem algebra_eq : ‹_› = algebraOfLiesOver v w :=
  Algebra.algebra_ext _ _ (algebraMap_of_liesOver_apply v w)

end LiesOver

variable {L : Type*} [NormedField L] [CompleteSpace L] {f : WithAbs v →+* L} {v}

/-- If the absolute value of a normed field factors through an embedding into another normed field
that is locally compact, then the completion of the first normed field is also locally compact. -/
theorem locallyCompactSpace [LocallyCompactSpace L] (h : Isometry f) :
    LocallyCompactSpace v.Completion :=
  (h.completion_extension.comp (isometry_toCompletion v)).isClosedEmbedding.locallyCompactSpace

end AbsoluteValue.Completion
