/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
module

public import Mathlib.RingTheory.Adjoin.Polynomial
public import Mathlib.RingTheory.Polynomial.Tower
/-!
# Adjoin one single element

This file contains basic results on `Algebra.adjoin`, specifically on adjoining singletons.

## Tags

adjoin, algebra, ringhom

-/

@[expose] public section

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (b : B)

namespace Algebra

open Polynomial

/-- Ring homomorphism between `A[b]` and `A[↑b]`. -/
def RingHom.adjoinAlgebraMap :
    Algebra.adjoin A {b} →+* Algebra.adjoin A {(algebraMap B C) b} :=
  RingHom.codRestrict (((Algebra.ofId B C).restrictScalars A).comp
    (Subalgebra.val (Algebra.adjoin A {b}))) _
    (fun x ↦ by induction x using adjoin_singleton_induction with
      | f p => aesop (add norm [adjoin_singleton_eq_range_aeval, aeval_algebraMap_apply]))

@[simp]
theorem RingHom.adjoin_algebraMap_apply (x : Algebra.adjoin A {b}) :
    (RingHom.adjoinAlgebraMap b x (C := C) : C) = algebraMap B C x := rfl

theorem RingHom.adjoin_algebraMap_surjective :
    Function.Surjective (RingHom.adjoinAlgebraMap (A := A) b (C := C)) := by
  intro c
  obtain ⟨p, hp⟩ := adjoin_eq_exists_aeval A (algebraMap B C b) c
  aesop (add safe ((aeval_algebraMap_apply C b p).symm))

instance : Algebra (Algebra.adjoin A {b}) (Algebra.adjoin A {(algebraMap B C) b}) :=
  RingHom.toAlgebra (RingHom.adjoinAlgebraMap b)

instance : IsScalarTower (Algebra.adjoin A {b}) (Algebra.adjoin A {(algebraMap B C) b}) C :=
  IsScalarTower.of_algebraMap_eq' (by rfl)

/-- If the `algebraMap` injective then we have a Ring isomorphism between A[b] and A[↑b]. -/
noncomputable def RingHom.adjoinAlgebraMapEquiv [FaithfulSMul B C] :
    Algebra.adjoin A {b} ≃+* Algebra.adjoin A {(algebraMap B C) b} := by
  apply RingEquiv.ofBijective (RingHom.adjoinAlgebraMap b)
     ((Function.bijective_iff_existsUnique (adjoinAlgebraMap b)).mpr (fun y ↦ ?_))
  induction y using Algebra.adjoin_singleton_induction with | f p =>
  use ⟨p.aeval b, by simp⟩
  aesop (add norm [Polynomial.aeval_algebraMap_apply, Subtype.ext_iff])

end Algebra
