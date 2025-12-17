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
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (a : B)

namespace Algebra

open Polynomial

/-- Ring homomorphism between `A[a]` and `A[↑a]`. -/
def RingHom.adjoinAlgebraMap :
    Algebra.adjoin A {a} →+* Algebra.adjoin A {(algebraMap B C) a} :=
  RingHom.codRestrict (((Algebra.ofId B C).restrictScalars A).comp
    (Subalgebra.val (Algebra.adjoin A {a}))) _
    (fun x ↦ by induction x using adjoin_singleton_induction with
      | f p => aesop (add norm [adjoin_singleton_eq_range_aeval, aeval_algebraMap_apply]))

@[simp]
theorem RingHom.adjoin_algebraMap_apply (x : Algebra.adjoin A {a}) :
    (RingHom.adjoinAlgebraMap a x (C := C) : C) = algebraMap B C x := rfl

theorem RingHom.adjoin_algebraMap_surjective :
    Function.Surjective (RingHom.adjoinAlgebraMap (A := A) a (C := C)) := by
  intro b
  obtain ⟨p, hp⟩ := adjoin_eq_exists_aeval A (algebraMap B C a) b
  aesop (add safe ((aeval_algebraMap_apply C a p).symm))

instance : Algebra (Algebra.adjoin A {a}) (Algebra.adjoin A {(algebraMap B C) a}) :=
  RingHom.toAlgebra (RingHom.adjoinAlgebraMap a)

instance : IsScalarTower (Algebra.adjoin A {a}) (Algebra.adjoin A {(algebraMap B C) a}) C :=
  IsScalarTower.of_algebraMap_eq' (by rfl)

/-- If the `algebraMap` injective then we have a Ring isomorphism between A[a] and A[↑a]. -/
noncomputable def RingHom.adjoinAlgebraMapEquiv [FaithfulSMul B C] :
    Algebra.adjoin A {a} ≃+* Algebra.adjoin A {(algebraMap B C) a} := by
  apply RingEquiv.ofBijective (RingHom.adjoinAlgebraMap a)
     ((Function.bijective_iff_existsUnique (adjoinAlgebraMap a)).mpr (fun y ↦ ?_))
  induction y using Algebra.adjoin_singleton_induction with | f p =>
  use ⟨p.aeval a, by simp⟩
  aesop (add norm [Polynomial.aeval_algebraMap_apply, Subtype.ext_iff])

end Algebra
