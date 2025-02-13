/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
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
 - `AbsoluteValue.Completion` : the uniform space completion of a field `K` according to the
  uniform structure defined by the specified real absolute value.
-/

open Topology

noncomputable section

variable {R S : Type*} [OrderedSemiring S]

/-- Type synonym for a semiring which depends on an absolute value. This is a function that takes
an absolute value on a semiring and returns the semiring. We use this to assign and infer instances
on a semiring that depend on absolute values.

This is also helpful when dealing with several absolute values on the same semiring. -/
@[nolint unusedArguments]
def WithAbs [Semiring R] : AbsoluteValue R S → Type _ := fun _ => R

namespace WithAbs

section semiring

variable [Semiring R] (v : AbsoluteValue R S)

instance instNontrivial [Nontrivial R] : Nontrivial (WithAbs v) := inferInstanceAs (Nontrivial R)

instance instUnique [Unique R] : Unique (WithAbs v) := inferInstanceAs (Unique R)

instance instSemiring : Semiring (WithAbs v) := inferInstanceAs (Semiring R)

instance instInhabited : Inhabited (WithAbs v) := ⟨0⟩

/-- The canonical (semiring) equivalence between `WithAbs v` and `R`. -/
def equiv : WithAbs v ≃+* R := RingEquiv.refl _

/-- `WithAbs.equiv` as a ring equivalence. -/
@[deprecated equiv (since := "2025-01-13")]
def ringEquiv : WithAbs v ≃+* R := RingEquiv.refl _

end semiring

section more_instances

instance instCommSemiring [CommSemiring R] (v : AbsoluteValue R S) : CommSemiring (WithAbs v) :=
  inferInstanceAs (CommSemiring R)

instance instRing [Ring R] (v : AbsoluteValue R S) : Ring (WithAbs v) := inferInstanceAs (Ring R)

instance instCommRing [CommRing R] (v : AbsoluteValue R S) : CommRing (WithAbs v) :=
  inferInstanceAs (CommRing R)

instance normedRing [Ring R] (v : AbsoluteValue R ℝ) : NormedRing (WithAbs v) :=
  v.toNormedRing

lemma norm_eq_abv [Ring R] (v : AbsoluteValue R ℝ) (x : WithAbs v) :
    ‖x‖ = v (WithAbs.equiv v x) := rfl

instance normedField [Field R] (v : AbsoluteValue R ℝ) : NormedField (WithAbs v) :=
  v.toNormedField

end more_instances

section module

variable {R' : Type*} [Semiring R]

instance instModule_left [AddCommGroup R'] [Module R R'] (v : AbsoluteValue R S) :
    Module (WithAbs v) R' :=
  inferInstanceAs <| Module R R'

instance instModule_right [Semiring R'] [Module R R'] (v : AbsoluteValue R' S) :
    Module R (WithAbs v) :=
  inferInstanceAs <| Module R R'

end module

section algebra

variable {R' : Type*} [CommSemiring R] [Semiring R'] [Algebra R R']

instance instAlgebra_left (v : AbsoluteValue R S) : Algebra (WithAbs v) R' :=
  inferInstanceAs <| Algebra R R'

instance instAlgebra_right (v : AbsoluteValue R' S) : Algebra R (WithAbs v) :=
  inferInstanceAs <| Algebra R R'

/-- The canonical algebra isomorphism from an `R`-algebra `R'` with an absolute value `v`
to `R'`. -/
def algEquiv (v : AbsoluteValue R' S) : (WithAbs v) ≃ₐ[R] R' := AlgEquiv.refl (A₁ := R')

end algebra

/-!
### `WithAbs.equiv` preserves the ring structure.

These are deprecated as they are special cases of the generic `map_zero` etc. lemmas
after `WithAbs.equiv` is defined to be a ring equivalence.
-/

section equiv_semiring

variable [Semiring R] (v : AbsoluteValue R S) (x y : WithAbs v) (r s : R)

@[deprecated map_zero (since := "2025-01-13"), simp]
theorem equiv_zero : equiv v 0 = 0 := rfl

@[deprecated map_zero (since := "2025-01-13"), simp]
theorem equiv_symm_zero : (equiv v).symm 0 = 0 := rfl

@[deprecated map_add (since := "2025-01-13"), simp]
theorem equiv_add : equiv v (x + y) = equiv v x + equiv v y := rfl

@[deprecated map_add (since := "2025-01-13"), simp]
theorem equiv_symm_add : (equiv v).symm (r + s) = (equiv v).symm r + (equiv v).symm s := rfl

@[deprecated map_mul (since := "2025-01-13"), simp]
theorem equiv_mul : equiv v (x * y) = equiv v x * equiv v y := rfl

@[deprecated map_mul (since := "2025-01-13"), simp]
theorem equiv_symm_mul : (equiv v).symm (x * y) = (equiv v).symm x * (equiv v).symm y := rfl

end equiv_semiring

section equiv_ring

variable [Ring R] (v : AbsoluteValue R S) (x y : WithAbs v) (r s : R)

@[deprecated map_sub (since := "2025-01-13"), simp]
theorem equiv_sub : equiv v (x - y) = equiv v x - equiv v y := rfl

@[deprecated map_sub (since := "2025-01-13"), simp]
theorem equiv_symm_sub : (equiv v).symm (r - s) = (equiv v).symm r - (equiv v).symm s := rfl

@[deprecated map_neg (since := "2025-01-13"), simp]
theorem equiv_neg : equiv v (-x) = - equiv v x := rfl

@[deprecated map_neg (since := "2025-01-13"), simp]
theorem equiv_symm_neg : (equiv v).symm (-r) = - (equiv v).symm r := rfl

end equiv_ring

/-!
### The completion of a field at an absolute value.
-/

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
abbrev Completion := UniformSpace.Completion (WithAbs v)

@[deprecated (since := "2024-12-01")] alias completion := Completion

namespace Completion

instance : Coe K v.Completion :=
  inferInstanceAs <| Coe (WithAbs v) (UniformSpace.Completion (WithAbs v))

variable {L : Type*} [NormedField L] [CompleteSpace L] {f : WithAbs v →+* L} {v}

/-- If the absolute value of a normed field factors through an embedding into another normed field
`L`, then we can extend that embedding to an embedding on the completion `v.Completion →+* L`. -/
abbrev extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) : v.Completion →+* L :=
  UniformSpace.Completion.extensionHom _
    (WithAbs.isUniformInducing_of_comp h).uniformContinuous.continuous

theorem extensionEmbedding_of_comp_coe (h : ∀ x, ‖f x‖ = v x) (x : K) :
    extensionEmbedding_of_comp h x = f x := by
  rw [← UniformSpace.Completion.extensionHom_coe f
    (WithAbs.isUniformInducing_of_comp h).uniformContinuous.continuous]

/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.Completion →+* L` preserves distances. -/
theorem extensionEmbedding_dist_eq_of_comp (h : ∀ x, ‖f x‖ = v x) (x y : v.Completion) :
    dist (extensionEmbedding_of_comp h x) (extensionEmbedding_of_comp h y) =
      dist x y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ (fun x y => ?_)
  · refine isClosed_eq ?_ continuous_dist
    exact continuous_iff_continuous_dist.1 UniformSpace.Completion.continuous_extension
  · simp only [extensionEmbedding_of_comp_coe]
    exact UniformSpace.Completion.dist_eq x y ▸ (WithAbs.isometry_of_comp h).dist_eq _ _

/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.Completion →+* L` is an isometry. -/
theorem isometry_extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) :
    Isometry (extensionEmbedding_of_comp h) :=
  Isometry.of_dist_eq <| extensionEmbedding_dist_eq_of_comp h

/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.Completion →+* L` is a closed embedding. -/
theorem isClosedEmbedding_extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) :
    IsClosedEmbedding (extensionEmbedding_of_comp h) :=
  (isometry_extensionEmbedding_of_comp h).isClosedEmbedding

/-- If the absolute value of a normed field factors through an embedding into another normed field
that is locally compact, then the completion of the first normed field is also locally compact. -/
theorem locallyCompactSpace [LocallyCompactSpace L] (h : ∀ x, ‖f x‖ = v x)  :
    LocallyCompactSpace (v.Completion) :=
  (isClosedEmbedding_extensionEmbedding_of_comp h).locallyCompactSpace

end AbsoluteValue.Completion
