/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Completion

/-!
# WithAbs

`WithAbs v` is a type synonym for a semiring `R` which depends on an absolute value. The point of
this is to allow the type class inference system to handle multiple sources of instances that
arise from absolute values. See `NumberTheory.NumberField.Completion` for an example of this
being used to define Archimedean completions of a number field.

## Main definitions
 - `WithAbs` : type synonym for a semiring which depends on an absolute value. This is
  a function that takes an absolute value on a semiring and returns the semiring. This can be used
  to assign and infer instances on a semiring that depend on absolute values.
 - `WithAbs.equiv v` : the canonical (type) equivalence between `WithAbs v` and `R`.
 - `WithAbs.ringEquiv v` : The canonical ring equivalence between `WithAbs v` and `R`.
 - `AbsoluteValue.completion` : the uniform space completion of a field `K` according to the
  uniform structure defined by the specified real absolute value.
-/

open Topology

noncomputable section

variable {R S K : Type*} [Semiring R] [OrderedSemiring S] [Field K]

/-- Type synonym for a semiring which depends on an absolute value. This is a function that takes
an absolute value on a semiring and returns the semiring. We use this to assign and infer instances
on a semiring that depend on absolute values. -/
@[nolint unusedArguments]
def WithAbs : AbsoluteValue R S → Type _ := fun _ => R

namespace WithAbs

variable (v : AbsoluteValue R ℝ)

/-- Canonical equivalence between `WithAbs v` and `R`. -/
def equiv : WithAbs v ≃ R := Equiv.refl (WithAbs v)

instance instNonTrivial [Nontrivial R] : Nontrivial (WithAbs v) := inferInstanceAs (Nontrivial R)

instance instUnique [Unique R] : Unique (WithAbs v) := inferInstanceAs (Unique R)

instance instSemiring : Semiring (WithAbs v) := inferInstanceAs (Semiring R)

instance instRing [Ring R] : Ring (WithAbs v) := inferInstanceAs (Ring R)

instance instInhabited : Inhabited (WithAbs v) := ⟨0⟩

instance normedRing {R : Type*} [Ring R] (v : AbsoluteValue R ℝ) : NormedRing (WithAbs v) :=
  v.toNormedRing

instance normedField (v : AbsoluteValue K ℝ) : NormedField (WithAbs v) :=
  v.toNormedField

/-! `WithAbs.equiv` preserves the ring structure. -/

variable (x y : WithAbs v) (r s : R)
@[simp]
theorem equiv_zero : WithAbs.equiv v 0 = 0 := rfl

@[simp]
theorem equiv_symm_zero : (WithAbs.equiv v).symm 0 = 0 := rfl

@[simp]
theorem equiv_add : WithAbs.equiv v (x + y) = WithAbs.equiv v x + WithAbs.equiv v y := rfl

@[simp]
theorem equiv_symm_add :
    (WithAbs.equiv v).symm (r + s) = (WithAbs.equiv v).symm r + (WithAbs.equiv v).symm s :=
  rfl

@[simp]
theorem equiv_sub [Ring R] : WithAbs.equiv v (x - y) = WithAbs.equiv v x - WithAbs.equiv v y := rfl

@[simp]
theorem equiv_symm_sub [Ring R] :
    (WithAbs.equiv v).symm (r - s) = (WithAbs.equiv v).symm r - (WithAbs.equiv v).symm s :=
  rfl

@[simp]
theorem equiv_neg [Ring R] : WithAbs.equiv v (-x) = - WithAbs.equiv v x := rfl

@[simp]
theorem equiv_symm_neg [Ring R] : (WithAbs.equiv v).symm (-r) = - (WithAbs.equiv v).symm r := rfl

@[simp]
theorem equiv_mul : WithAbs.equiv v (x * y) = WithAbs.equiv v x * WithAbs.equiv v y := rfl

@[simp]
theorem equiv_symm_mul :
    (WithAbs.equiv v).symm (x * y) = (WithAbs.equiv v).symm x * (WithAbs.equiv v).symm y :=
  rfl

/-- `WithAbs.equiv` as a ring equivalence. -/
def ringEquiv : WithAbs v ≃+* R := RingEquiv.refl _

/-! The completion of a field at an absolute value. -/

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [NormedField L] {f : WithAbs v →+* L}

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
`f` is an isometry. -/
theorem isometry_of_comp (h : ∀ x, ‖f x‖ = v x) : Isometry f :=
  Isometry.of_dist_eq <| fun x y => by simp only [‹NormedField L›.dist_eq, ← f.map_sub, h]; rfl

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
the pseudo metric space associated to the absolute value is the same as the pseudo metric space
induced by `f`. -/
theorem pseudoMetricSpace_induced_of_comp (h : ∀ x, ‖f x‖ = v x) :
    PseudoMetricSpace.induced f inferInstance = (normedField v).toPseudoMetricSpace := by
  ext; exact isometry_of_comp h |>.dist_eq _ _

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
the uniform structure associated to the absolute value is the same as the uniform structure
induced by `f`. -/
theorem uniformSpace_comap_eq_of_comp (h : ∀ x, ‖f x‖ = v x) :
    UniformSpace.comap f inferInstance = (normedField v).toUniformSpace := by
  simp only [← pseudoMetricSpace_induced_of_comp h, PseudoMetricSpace.toUniformSpace]

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
`f` is uniform inducing. -/
theorem isUniformInducing_of_comp (h : ∀ x, ‖f x‖ = v x) : IsUniformInducing f :=
  isUniformInducing_iff_uniformSpace.2 <| uniformSpace_comap_eq_of_comp h

end WithAbs

namespace AbsoluteValue

open WithAbs

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- The completion of a field with respect to a real absolute value. -/
abbrev completion := UniformSpace.Completion (WithAbs v)

namespace Completion

instance : Coe K v.completion :=
  inferInstanceAs <| Coe (WithAbs v) (UniformSpace.Completion (WithAbs v))

variable {L : Type*} [NormedField L] [CompleteSpace L] {f : WithAbs v →+* L} {v}

/-- If the absolute value of a normed field factors through an embedding into another normed field
`L`, then we can extend that embedding to an embedding on the completion `v.completion →+* L`. -/
abbrev extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) : v.completion →+* L :=
  UniformSpace.Completion.extensionHom _
    (WithAbs.isUniformInducing_of_comp h).uniformContinuous.continuous

theorem extensionEmbedding_of_comp_coe (h : ∀ x, ‖f x‖ = v x) (x : K) :
    extensionEmbedding_of_comp h x = f x := by
  rw [← UniformSpace.Completion.extensionHom_coe f
    (WithAbs.isUniformInducing_of_comp h).uniformContinuous.continuous]

/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.completion →+* L` preserves distances. -/
theorem extensionEmbedding_dist_eq_of_comp (h : ∀ x, ‖f x‖ = v x) (x y : v.completion) :
    dist (extensionEmbedding_of_comp h x) (extensionEmbedding_of_comp h y) =
      dist x y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ (fun x y => ?_)
  · refine isClosed_eq ?_ continuous_dist
    exact continuous_iff_continuous_dist.1 UniformSpace.Completion.continuous_extension
  · simp only [extensionEmbedding_of_comp_coe]
    exact UniformSpace.Completion.dist_eq x y ▸ (WithAbs.isometry_of_comp h).dist_eq _ _

/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.completion →+* L` is an isometry. -/
theorem isometry_extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) :
    Isometry (extensionEmbedding_of_comp h) :=
  Isometry.of_dist_eq <| extensionEmbedding_dist_eq_of_comp h

/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.completion →+* L` is a closed embedding. -/
theorem isClosedEmbedding_extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) :
    IsClosedEmbedding (extensionEmbedding_of_comp h) :=
  (isometry_extensionEmbedding_of_comp h).isClosedEmbedding

/-- If the absolute value of a normed field factors through an embedding into another normed field
that is locally compact, then the completion of the first normed field is also locally compact. -/
theorem locallyCompactSpace [LocallyCompactSpace L] (h : ∀ x, ‖f x‖ = v x)  :
    LocallyCompactSpace (v.completion) :=
  (isClosedEmbedding_extensionEmbedding_of_comp h).locallyCompactSpace

end AbsoluteValue.Completion
