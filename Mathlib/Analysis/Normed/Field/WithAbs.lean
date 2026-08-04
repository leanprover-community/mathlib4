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

/-!
### The completion of a field at an absolute value.
-/

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ} {L : Type*} [NormedField L]
  {f : WithAbs v →+* L}

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

/-- If the absolute value of a normed field factors through an embedding into another normed field
that is locally compact, then the completion of the first normed field is also locally compact. -/
theorem locallyCompactSpace [LocallyCompactSpace L] (h : Isometry f) :
    LocallyCompactSpace v.Completion :=
  h.completion_extension.isClosedEmbedding.locallyCompactSpace

end AbsoluteValue.Completion
