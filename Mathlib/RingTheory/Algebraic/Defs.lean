/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Algebraic elements and algebraic extensions

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.

## Main definitions

* `IsAlgebraic`: algebraic elements of an algebra.
* `Transcendental`: transcendental elements of an algebra are those that are not algebraic.
* `Subalgebra.IsAlgebraic`: a subalgebra is algebraic if all its elements are algebraic.
* `Algebra.IsAlgebraic`: an algebra is algebraic if all its elements are algebraic.
* `Algebra.Transcendental`: an algebra is transcendental if some element is transcendental.

## Main results

* `transcendental_iff`: an element `x : A` is transcendental over `R` iff out of `R[X]`
  only the zero polynomial evaluates to 0 at `x`.
* `Subalgebra.isAlgebraic_iff`: a subalgebra is algebraic iff it is algebraic as an algebra.
-/

assert_not_exists IsIntegralClosure LinearIndependent LocalRing MvPolynomial

universe u v w
open Polynomial

section

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- An element of an R-algebra is algebraic over R if it is a root of a nonzero polynomial
with coefficients in R. -/
@[stacks 09GC "Algebraic elements"]
def IsAlgebraic (x : A) : Prop :=
  ∃ p : R[X], p ≠ 0 ∧ aeval x p = 0

/-- An element of an R-algebra is transcendental over R if it is not algebraic over R. -/
def Transcendental (x : A) : Prop :=
  ¬IsAlgebraic R x

variable {R}

/-- An element `x` is transcendental over `R` if and only if for any polynomial `p`,
`Polynomial.aeval x p = 0` implies `p = 0`. This is similar to `algebraicIndependent_iff`. -/
theorem transcendental_iff {x : A} :
    Transcendental R x ↔ ∀ p : R[X], aeval x p = 0 → p = 0 := by
  rw [Transcendental, IsAlgebraic, not_exists]
  congr! 1; tauto

/-- A subalgebra is algebraic if all its elements are algebraic. -/
protected def Subalgebra.IsAlgebraic (S : Subalgebra R A) : Prop :=
  ∀ x ∈ S, IsAlgebraic R x

variable (R A)

/-- An algebra is algebraic if all its elements are algebraic. -/
@[stacks 09GC "Algebraic extensions"]
protected class Algebra.IsAlgebraic : Prop where
  isAlgebraic : ∀ x : A, IsAlgebraic R x

/-- An algebra is transcendental if some element is transcendental. -/
protected class Algebra.Transcendental : Prop where
  transcendental : ∃ x : A, Transcendental R x

variable {R A}

lemma Algebra.isAlgebraic_def : Algebra.IsAlgebraic R A ↔ ∀ x : A, IsAlgebraic R x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma Algebra.transcendental_def : Algebra.Transcendental R A ↔ ∃ x : A, Transcendental R x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

theorem Algebra.transcendental_iff_not_isAlgebraic :
    Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A := by
  simp [isAlgebraic_def, transcendental_def, Transcendental]

/-- A subalgebra is algebraic if and only if it is algebraic as an algebra. -/
theorem Subalgebra.isAlgebraic_iff (S : Subalgebra R A) :
    S.IsAlgebraic ↔ Algebra.IsAlgebraic R S := by
  delta Subalgebra.IsAlgebraic
  rw [Subtype.forall', Algebra.isAlgebraic_def]
  refine forall_congr' fun x => exists_congr fun p => and_congr Iff.rfl ?_
  have h : Function.Injective S.val := Subtype.val_injective
  conv_rhs => rw [← h.eq_iff, map_zero]
  rw [← aeval_algHom_apply, S.val_apply]

/-- An algebra is algebraic if and only if it is algebraic as a subalgebra. -/
theorem Algebra.isAlgebraic_iff : Algebra.IsAlgebraic R A ↔ (⊤ : Subalgebra R A).IsAlgebraic := by
  delta Subalgebra.IsAlgebraic
  simp only [Algebra.isAlgebraic_def, Algebra.mem_top, forall_prop_of_true]

end
