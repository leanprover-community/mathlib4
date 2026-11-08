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

/-!
### The completion of a field at an absolute value.
-/

namespace AbsoluteValue

open WithAbs

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- The completion of a field with respect to a real absolute value, as a one-field structure
wrapping the uniform-space completion of `WithAbs v`. -/
@[nolint structureInType]
structure Completion where
  /-- Wrap an element of the underlying completion `UniformSpace.Completion (WithAbs v)` into
  `v.Completion`. -/
  private ofCompletion' ::
  /-- The underlying element of the completion `UniformSpace.Completion (WithAbs v)`. -/
  private toCompletion' : UniformSpace.Completion (WithAbs v)

namespace Completion

/-- `Completion.toCompletion` and `Completion.ofCompletion` as an equivalence. -/
private def equivAux : v.Completion ≃ UniformSpace.Completion (WithAbs v) where
  toFun := toCompletion'
  invFun := ofCompletion'
  left_inv _ := rfl
  right_inv _ := rfl

-- This instance exists to avoid a zsmul diamond.
@[no_expose]
noncomputable instance (R : Type*) [CommSemiring R] [Algebra R (WithAbs v)] :
    SMul R v.Completion where
  smul r x := ofCompletion' (r • x.toCompletion')

@[no_expose]
noncomputable instance : NormedField v.Completion := fast_instance% (equivAux v).normedField

/-- `Completion.toCompletion` and `Completion.ofCompletion` as an equivalence. -/
def equiv : v.Completion ≃+* UniformSpace.Completion (WithAbs v) where
  toEquiv := equivAux v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable {v}

/-- The ring homomorphism from `v.Completion` to `UniformSpace.Completion (WithAbs v)`. -/
noncomputable def toCompletion : v.Completion →+* UniformSpace.Completion (WithAbs v) :=
  equiv v

/-- The ring homomorphism from `UniformSpace.Completion (WithAbs v)` to `v.Completion`. -/
noncomputable def ofCompletion : UniformSpace.Completion (WithAbs v) →+* v.Completion :=
  (equiv v).symm

@[simp]
theorem equiv_apply (x : v.Completion) : equiv v x = x.toCompletion := by
  rfl

@[simp]
theorem equiv_symm_apply (x : UniformSpace.Completion (WithAbs v)) :
    (equiv v).symm x = .ofCompletion x := by
  rfl

@[simp]
theorem toCompletion_ofCompletion (x : UniformSpace.Completion (WithAbs v)) :
    toCompletion (ofCompletion x) = x := by
  rfl

@[simp]
theorem ofCompletion_toCompletion (x : v.Completion) : ofCompletion (toCompletion x) = x := by
  rfl

variable (v)

theorem toCompletion_injective : Function.Injective (toCompletion (v := v)) :=
  (equiv v).injective

theorem ofCompletion_injective : Function.Injective (ofCompletion (v := v)) :=
  (equiv v).symm.injective

theorem toCompletion_surjective : Function.Surjective (toCompletion (v := v)) :=
  (equiv v).surjective

theorem ofCompletion_surjective : Function.Surjective (ofCompletion (v := v)) :=
  (equiv v).symm.surjective

variable {v}

@[simp]
theorem toCompletion_inj {x y : v.Completion} : toCompletion x = toCompletion y ↔ x = y :=
  (toCompletion_injective v).eq_iff

@[simp]
theorem ofCompletion_inj {x y : UniformSpace.Completion (WithAbs v)} :
    ofCompletion x = ofCompletion y ↔ x = y :=
  (ofCompletion_injective v).eq_iff

@[simp]
theorem norm_toCompletion (x : v.Completion) : ‖toCompletion x‖ = ‖x‖ := by
  rfl

@[simp]
theorem norm_ofCompletion (x : UniformSpace.Completion (WithAbs v)) :
    ‖(ofCompletion x : v.Completion)‖ = ‖x‖ := by
  rfl

variable (v)

theorem isometry_toCompletion : Isometry (toCompletion (v := v)) :=
  Isometry.of_dist_eq fun _ _ ↦ rfl

theorem isometry_ofCompletion : Isometry (ofCompletion (v := v)) :=
  Isometry.of_dist_eq fun _ _ ↦ rfl

/-- `Completion.toCompletion` as an isometry equivalence onto the underlying completion. -/
@[simps!]
noncomputable def isometryEquiv : v.Completion ≃ᵢ UniformSpace.Completion (WithAbs v) where
  toEquiv := equiv v
  isometry_toFun := isometry_toCompletion v

theorem continuous_toCompletion : Continuous (toCompletion (v := v)) :=
  (isometry_toCompletion v).continuous

theorem continuous_ofCompletion : Continuous (ofCompletion (v := v)) :=
  (isometryEquiv v).symm.continuous

instance : CompleteSpace v.Completion :=
  ((isometry_toCompletion v).isUniformInducing.completeSpace_congr
    (toCompletion_surjective v)).mpr inferInstance

noncomputable instance : Inhabited v.Completion := ⟨0⟩

variable {v}

/-- The coercion from `WithAbs v` to `v.Completion`. -/
@[coe]
noncomputable def coe (x : WithAbs v) : v.Completion :=
  ofCompletion (x : UniformSpace.Completion (WithAbs v))

/-- Coercion of an element of `WithAbs v` into the completion. -/
noncomputable instance : Coe (WithAbs v) v.Completion where coe := coe

@[simp]
theorem toCompletion_coe (x : WithAbs v) :
    (x : v.Completion).toCompletion = (x : UniformSpace.Completion (WithAbs v)) := by
  rfl

@[simp]
theorem ofCompletion_coe (x : WithAbs v) :
    ofCompletion (x : UniformSpace.Completion (WithAbs v)) = (x : v.Completion) := by
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : WithAbs v) : v.Completion) = 0 :=
  toCompletion_injective v UniformSpace.Completion.coe_zero

@[simp, norm_cast]
theorem coe_one : ((1 : WithAbs v) : v.Completion) = 1 :=
  toCompletion_injective v <| UniformSpace.Completion.coe_one _

@[simp, norm_cast]
theorem coe_add (x y : WithAbs v) : ((x + y : WithAbs v) : v.Completion) = x + y :=
  toCompletion_injective v <| UniformSpace.Completion.coe_add x y

@[simp, norm_cast]
theorem coe_mul (x y : WithAbs v) : ((x * y : WithAbs v) : v.Completion) = x * y :=
  toCompletion_injective v <| UniformSpace.Completion.coe_mul x y

@[simp, norm_cast]
theorem coe_neg (x : WithAbs v) : ((-x : WithAbs v) : v.Completion) = -x :=
  toCompletion_injective v <| UniformSpace.Completion.coe_neg x

@[simp, norm_cast]
theorem coe_sub (x y : WithAbs v) : ((x - y : WithAbs v) : v.Completion) = x - y :=
  toCompletion_injective v <| UniformSpace.Completion.coe_sub x y

@[simp, norm_cast]
theorem coe_inv (x : WithAbs v) : ((x⁻¹ : WithAbs v) : v.Completion) = (↑x)⁻¹ :=
  toCompletion_injective v (UniformSpace.Completion.coe_inv x).symm

theorem norm_coe (x : WithAbs v) : ‖(x : v.Completion)‖ = v x.ofAbs :=
  UniformSpace.Completion.norm_coe x

variable (v)

theorem continuous_coe : Continuous ((↑) : WithAbs v → v.Completion) :=
  (continuous_ofCompletion v).comp (UniformSpace.Completion.continuous_coe _)

theorem denseRange_coe : DenseRange ((↑) : WithAbs v → v.Completion) :=
  (ofCompletion_surjective v).denseRange.comp UniformSpace.Completion.denseRange_coe
    (continuous_ofCompletion v)

variable {v}

/-- Induction on the completion of a field at an absolute value: a closed property that
holds on the image of `K` holds everywhere. -/
@[elab_as_elim]
theorem induction_on {p : v.Completion → Prop} (x : v.Completion) (hp : IsClosed {x | p x})
    (ih : ∀ a : WithAbs v, p a) : p x :=
  UniformSpace.Completion.induction_on (p := p ∘ ofCompletion) x.toCompletion
    (hp.preimage (continuous_ofCompletion v)) ih

/-- Two continuous functions out of `v.Completion` into a Hausdorff space that agree on `K`
are equal. -/
theorem ext {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f g : v.Completion → Y}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ a : WithAbs v, f a = g a) : f = g :=
  (denseRange_coe v).equalizer hf hg (funext h)

variable (v)

section Algebra

variable {R : Type*} [CommSemiring R] [Algebra R (WithAbs v)]
  [UniformContinuousConstSMul R (WithAbs v)]

@[no_expose]
noncomputable instance : Algebra R v.Completion := fast_instance% (equiv v).algebra R

theorem toCompletion_algebraMap (r : R) :
    (algebraMap R v.Completion r).toCompletion =
      algebraMap R (UniformSpace.Completion (WithAbs v)) r := by
  rfl

theorem ofCompletion_algebraMap (r : R) :
    ofCompletion (algebraMap R (UniformSpace.Completion (WithAbs v)) r) =
      algebraMap R v.Completion r := by
  rfl

theorem algebraMap_def (r : R) :
    algebraMap R v.Completion r = (algebraMap R (WithAbs v) r : v.Completion) := by
  rfl

end Algebra

section LiesOver

variable {L : Type*} [Field L] [Algebra K L] (w : AbsoluteValue L ℝ) [w.LiesOver v]

/-- If `w` lies over `v`, then the ring homomorphism `v.Completion →+* w.Completion` induced by
`algebraMap K L`. -/
noncomputable def map : v.Completion →+* w.Completion :=
  ((equiv w).symm.toRingHom.comp <| UniformSpace.Completion.mapRingHom
    (WithAbs.map v w (algebraMap K L)) (WithAbs.isometry_map v w).continuous).comp
    (equiv v).toRingHom

theorem isometry_map : Isometry (map v w) :=
  (isometryEquiv w).symm.isometry.comp <|
    (UniformSpace.Completion.isometry_mapRingHom (WithAbs.isometry_map v w)).comp
      (isometry_toCompletion v)

theorem continuous_map : Continuous (map v w) := (isometry_map v w).continuous

@[simp]
theorem map_coe (x : WithAbs v) : map v w (x : v.Completion) = WithAbs.map v w (algebraMap K L) x :=
  toCompletion_injective w <| UniformSpace.Completion.mapRingHom_coe
    (WithAbs.isometry_map v w).continuous x

/-- If `w` lies over `v` with completions `K_v` and `L_w`, then there is a unique `K_v`-algebra
structure on `L_w` satisfying both `IsScalarTower K K_v L_w` and `ContinuousSMul K_v L_w`,
see `AbsoluteValue.Completion.algebraMap_eq_of_liesOver` and
`AbsoluteValue.Completion.algebra_eq_of_liesOver`. -/
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

theorem algebraMap_eq_of_liesOver : algebraMap v.Completion w.Completion = map v w :=
  DFunLike.ext' <| ext (continuous_algebraMap _ _) (continuous_map v w) fun x ↦
    (IsScalarTower.algebraMap_apply K v.Completion w.Completion x.ofAbs).symm.trans
      (map_coe v w x).symm

@[deprecated (since := "2026-10-28")] alias algebraMap_eq := algebraMap_eq_of_liesOver

theorem algebraMap_apply_of_liesOver (x : v.Completion) :
    algebraMap v.Completion w.Completion x = map v w x := by
  rw [algebraMap_eq_of_liesOver]

theorem algebra_eq_of_liesOver : ‹_› = algebraOfLiesOver v w :=
  Algebra.algebra_ext _ _ (algebraMap_apply_of_liesOver v w)

@[deprecated (since := "2026-10-28")] alias algebraMap_apply := algebraMap_apply_of_liesOver
@[deprecated (since := "2026-10-28")] alias algebra_eq := algebra_eq_of_liesOver

end LiesOver

variable {L : Type*} [NormedField L] [CompleteSpace L] {f : WithAbs v →+* L} {v}

/-- If the absolute value of a normed field factors through an embedding into another normed field
that is locally compact, then the completion of the first normed field is also locally compact. -/
theorem locallyCompactSpace [LocallyCompactSpace L] (h : Isometry f) :
    LocallyCompactSpace v.Completion :=
  (h.completion_extension.comp (isometry_toCompletion v)).isClosedEmbedding.locallyCompactSpace

end AbsoluteValue.Completion
