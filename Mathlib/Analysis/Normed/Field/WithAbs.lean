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

@[expose] public section

open Topology

namespace WithAbs

variable {R S : Type*} [Semiring S] [PartialOrder S]

section Field

variable [Field R] {T : Type*} [Field T] (v : AbsoluteValue R S)

instance : Field (WithAbs v) := (equiv v).field

noncomputable instance normedField (v : AbsoluteValue R ℝ) : NormedField (WithAbs v) :=
  letI := v.toNormedField
  (equiv v).normedField

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] moduleLeft in
instance [Module R T] [FiniteDimensional R T] :
    FiniteDimensional (WithAbs v) T :=
  Module.Finite.of_restrictScalars_finite R (WithAbs v) T

instance [Module T R] [FiniteDimensional T R] :
    FiniteDimensional T (WithAbs v) :=
  Module.Finite.equiv (linearEquiv T v).symm

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] algebraLeft in
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

set_option backward.isDefEq.respectTransparency false in
/- Note that `AbsoluteValue.tendsto_div_one_add_pow_nhds_one` would follow from the below
result if `WithAbs v` had a topology for general value rings `S`. Currently `WithAbs v` only has
a topology when `S = ℝ`. -/
theorem tendsto_one_div_one_add_pow_nhds_one {v : AbsoluteValue R ℝ} {a : R} (ha : v a < 1) :
    Filter.atTop.Tendsto (fun n ↦ (equiv v).symm (1 / (1 + a ^ n))) (𝓝 1) := by
  simpa using inv_one (G := WithAbs v) ▸ (tendsto_inv_iff₀ one_ne_zero).2
    (tendsto_iff_norm_sub_tendsto_zero.2 <| by simpa using ha)

end Field

section CommRing

variable [CommRing R] {T : Type*} [Field T] [Algebra R T] (w : AbsoluteValue T ℝ)

set_option backward.isDefEq.respectTransparency false in
instance : UniformContinuousConstSMul R (WithAbs w) where
  uniformContinuous_const_smul r := by
    simp_rw [Algebra.smul_def]
    exact (Ring.uniformContinuousConstSMul _).uniformContinuous_const_smul _

end CommRing

/-!
### The completion of a field at an absolute value.
-/

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ} {L : Type*} [NormedField L]
  {f : WithAbs v →+* L}

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
`f` is an isometry. -/
@[deprecated AddMonoidHomClass.isometry_of_norm (since := "2025-11-28")]
theorem isometry_of_comp (h : ∀ x, ‖f x‖ = v x.ofAbs) : Isometry f :=
  AddMonoidHomClass.isometry_of_norm _ h

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
the pseudometric space associated to the absolute value is the same as the pseudometric space
induced by `f`. -/
@[deprecated "Use `Isometry.dist_eq` in combination with `AddMonoidHomClass.isometry_of_norm`"
  (since := "2025-11-28")]
theorem pseudoMetricSpace_induced_of_comp (h : ∀ x, ‖f x‖ = v x.ofAbs) :
    PseudoMetricSpace.induced f inferInstance = (normedField v).toPseudoMetricSpace := by
  ext; exact AddMonoidHomClass.isometry_of_norm _ h |>.dist_eq _ _

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
the uniform structure associated to the absolute value is the same as the uniform structure
induced by `f`. -/
@[deprecated "Use `IsUniformInducing.comap_uniformSpace in combination` with
  AddMonoidHomClass.isometry_of_norm" (since := "2025-11-28")]
theorem uniformSpace_comap_eq_of_comp (h : ∀ x, ‖f x‖ = v x.ofAbs) :
    UniformSpace.comap f inferInstance = (normedField v).toUniformSpace :=
  IsUniformInducing.comap_uniformSpace
    (AddMonoidHomClass.isometry_of_norm _ h).isUniformInducing

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
`f` is uniform inducing. -/
@[deprecated "Use `Isometry.isUniformInducing` in combination with
  AddMonoidHomClass.isometry_of_norm" (since := "2025-11-28")]
theorem isUniformInducing_of_comp (h : ∀ x, ‖f x‖ = v x.ofAbs) : IsUniformInducing f :=
  (AddMonoidHomClass.isometry_of_norm _ h).isUniformInducing

end WithAbs

namespace AbsoluteValue

open WithAbs

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- The completion of a field with respect to a real absolute value. -/
abbrev Completion := UniformSpace.Completion (WithAbs v)

namespace Completion

noncomputable instance : Coe K v.Completion where
  coe k : v.Completion := ↑(toAbs v k)

variable {L : Type*} [NormedField L] [CompleteSpace L] {f : WithAbs v →+* L} {v}

set_option backward.isDefEq.respectTransparency false in
/-- If the absolute value of a normed field factors through an embedding into another normed field
`L`, then we can extend that embedding to an embedding on the completion `v.Completion →+* L`. -/
@[deprecated "Use `Isometry.extensionHom` in combination with `AddMonoidHomClass.isometry_of_norm`"
  (since := "2025-11-28")]
noncomputable abbrev extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x.ofAbs) :
    v.Completion →+* L := (AddMonoidHomClass.isometry_of_norm _ h).extensionHom

set_option backward.isDefEq.respectTransparency false in
@[deprecated "Use `Isometry.extensionHom_coe` in combination with
  `AddMonoidHomClass.isometry_of_norm`" (since := "2025-11-28")]
theorem extensionEmbedding_of_comp_coe (h : ∀ x, ‖f x‖ = v x.ofAbs) (x : K) :
    (AddMonoidHomClass.isometry_of_norm _ h).extensionHom x = f ((equiv v).symm x) :=
  AddMonoidHomClass.isometry_of_norm _ h |>.extensionHom_coe _

set_option backward.isDefEq.respectTransparency false in
/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.Completion →+* L` preserves distances. -/
@[deprecated "Use `Isometry.dist_eq` in combination with `AddMonoidHomClass.isometry_of_norm`"
  (since := "2025-11-28")]
theorem extensionEmbedding_dist_eq_of_comp (h : ∀ x, ‖f x‖ = v x.ofAbs) (x y : v.Completion) :
    let f := AddMonoidHomClass.isometry_of_norm _ h |>.extensionHom
    dist (f x) (f y) = dist x y :=
  AddMonoidHomClass.isometry_of_norm _ h |>.completion_extension.dist_eq _ _

set_option backward.isDefEq.respectTransparency false in
/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.Completion →+* L` is an isometry. -/
@[deprecated "Use `Isometry.completion_extension` in combination with
  `AddMonoidHomClass.isometry_of_norm`" (since := "2025-11-28")]
theorem isometry_extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x.ofAbs) :
    Isometry (AddMonoidHomClass.isometry_of_norm _ h |>.extensionHom) :=
  AddMonoidHomClass.isometry_of_norm _ h |>.completion_extension

set_option backward.isDefEq.respectTransparency false in
/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.Completion →+* L` is a closed embedding. -/
@[deprecated "Use `Isometry.isClosedEmbedding` in combination with `Isometry.completion_extension`
  and `AddMonoidHomClass.isometry_of_norm`" (since := "2025-11-28")]
theorem isClosedEmbedding_extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x.ofAbs) :
    IsClosedEmbedding (AddMonoidHomClass.isometry_of_norm _ h |>.extensionHom) :=
  (AddMonoidHomClass.isometry_of_norm _ h).completion_extension.isClosedEmbedding

/-- If the absolute value of a normed field factors through an embedding into another normed field
that is locally compact, then the completion of the first normed field is also locally compact. -/
theorem locallyCompactSpace [LocallyCompactSpace L] (h : Isometry f) :
    LocallyCompactSpace v.Completion :=
  h.completion_extension.isClosedEmbedding.locallyCompactSpace

end AbsoluteValue.Completion
