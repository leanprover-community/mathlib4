/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# WithAbs

`WithAbs v` is a type synonym for a semiring `R` which depends on an absolute value. The point of
this is to allow the type class inference system to handle multiple sources of instances that
arise from absolute values.

## Main definitions
- `WithAbs` : type synonym for a semiring which depends on an absolute value. This is
  a function that takes an absolute value on a semiring and returns the semiring. This can be used
  to assign and infer instances on a semiring that depend on absolute values.
- `WithAbs.equiv v` : the canonical (type) equivalence between `WithAbs v` and `R`.
- `WithAbs.ringEquiv v` : The canonical ring equivalence between `WithAbs v` and `R`.
-/

open Topology

noncomputable section

variable {R S : Type*} [Semiring S] [PartialOrder S]

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

end WithAbs
