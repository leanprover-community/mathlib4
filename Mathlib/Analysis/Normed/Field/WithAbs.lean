/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Field.TransferInstance
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.MetricSpace.Completion

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

/-- The completion of a field with respect to a real absolute value. -/
abbrev Completion := UniformSpace.Completion (WithAbs v)

namespace Completion

noncomputable instance : Coe K v.Completion where
  coe k : v.Completion := ↑(toAbs v k)

section Algebra

variable {L : Type*} [Field L] [Algebra K L] (w : AbsoluteValue L ℝ) [w.LiesOver v]

/-- If `w` lies over `v` with completions `K_v` and `L_w`, then there is a unique `K_v`-algebra
structure on `L_w` satisfying both `IsScalarTower K K_v L_w` and `ContinuousSMul K_v L_w`,
see `AbsoluteValue.Completion.algebraMap_eq` and `AbsoluteValue.Completion.algebra_eq`. -/
@[instance_reducible]
noncomputable def algebraOfLiesOver : Algebra v.Completion w.Completion :=
  (UniformSpace.Completion.mapRingHom (WithAbs.map v w (algebraMap K L))
    (WithAbs.isometry_map v w).continuous).toAlgebra

instance : letI := algebraOfLiesOver v w
    IsScalarTower K v.Completion w.Completion :=
  let := algebraOfLiesOver v w
  IsScalarTower.of_algebraMap_eq fun x ↦ (UniformSpace.Completion.mapRingHom_coe
    (WithAbs.isometry_map v w).continuous (WithAbs.toAbs v x)).symm

instance : letI := algebraOfLiesOver v w
    ContinuousSMul v.Completion w.Completion :=
  let := algebraOfLiesOver v w
  continuousSMul_of_algebraMap v.Completion w.Completion
    (UniformSpace.Completion.isometry_mapRingHom (WithAbs.isometry_map v w)).continuous

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]
  [ContinuousSMul v.Completion w.Completion]

open UniformSpace.Completion in
theorem algebraMap_eq : algebraMap v.Completion w.Completion =
    UniformSpace.Completion.mapRingHom (WithAbs.map v w (algebraMap K L))
      (WithAbs.isometry_map v w).continuous := by
  refine DFunLike.ext' (extension_unique ?_ ?_ ?_).symm
  · exact (uniformContinuous_coe (WithAbs w)).comp (isometry_map v w).uniformContinuous
  · exact uniformContinuous_addMonoidHom_of_continuous (continuous_algebraMap _ _)
  · exact fun _ ↦ IsScalarTower.algebraMap_apply ..

theorem algebraMap_apply (x : v.Completion) :
    algebraMap v.Completion w.Completion x = UniformSpace.Completion.mapRingHom
      (WithAbs.map v w (algebraMap K L)) (WithAbs.isometry_map v w).continuous x := by
  rw [algebraMap_eq]

theorem algebra_eq : ‹_› = algebraOfLiesOver v w :=
  Algebra.algebra_ext _ _ (algebraMap_apply v w)

end Algebra

variable {L : Type*} [NormedField L] [CompleteSpace L] {f : WithAbs v →+* L} {v}

/-- If the absolute value of a normed field factors through an embedding into another normed field
that is locally compact, then the completion of the first normed field is also locally compact. -/
theorem locallyCompactSpace [LocallyCompactSpace L] (h : Isometry f) :
    LocallyCompactSpace v.Completion :=
  h.completion_extension.isClosedEmbedding.locallyCompactSpace

end AbsoluteValue.Completion
