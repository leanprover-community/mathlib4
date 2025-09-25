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

theorem algebraMap_left_apply (v : AbsoluteValue R S) (x : WithAbs v) :
    algebraMap (WithAbs v) R' x = algebraMap R R' (WithAbs.equiv v x) := rfl

instance instAlgebra_right (v : AbsoluteValue R' S) : Algebra R (WithAbs v) :=
  inferInstanceAs <| Algebra R R'

theorem algebraMap_right_apply (v : AbsoluteValue R' S) (x : R) :
    algebraMap R (WithAbs v) x = WithAbs.equiv v (algebraMap R R' x) := rfl

theorem equiv_algebraMap_apply (v : AbsoluteValue R S) (w : AbsoluteValue R' S) (x : WithAbs v) :
    equiv w (algebraMap (WithAbs v) (WithAbs w) x) = algebraMap R R' (equiv v x) := rfl

/-- The canonical algebra isomorphism from an `R`-algebra `R'` with an absolute value `v`
to `R'`. -/
def algEquiv (v : AbsoluteValue R' S) : (WithAbs v) ≃ₐ[R] R' := AlgEquiv.refl (A₁ := R')

end algebra

end WithAbs
