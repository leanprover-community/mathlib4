/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Analysis.Normed.Field.Basic

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
-/
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

end WithAbs
