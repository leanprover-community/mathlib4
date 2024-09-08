/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Star.NonUnitalSubalgebra

/-! # Classes of C⋆-algebras

This file defines classes for complex C⋆-algebras. These are (unital or non-unital, commutative or
noncommutative) Banach algebra over `ℂ` with an antimultiplicative conjugate-linear involution
(`star`) satisfying the C⋆-identity `∥star x * x∥ = ∥x∥ ^ 2`.

## Notes

These classes are not defined in `Mathlib.Analysis.CStarAlgebra.Basic` because they require
heavier imports.

-/

class NonUnitalCStarAlgebra (A : Type*) extends NonUnitalNormedRing A, StarRing A, CompleteSpace A,
    CStarRing A, NormedSpace ℂ A, IsScalarTower ℂ A A, SMulCommClass ℂ A A, StarModule ℂ A where

class NonUnitalCommCStarAlgebra (A : Type*) extends NonUnitalCStarAlgebra A where
  mul_comm : ∀ (a b : A), a * b = b * a

class CStarAlgebra (A : Type*) extends NormedRing A, StarRing A, CompleteSpace A, CStarRing A,
    NormedAlgebra ℂ A, StarModule ℂ A where

class CommCStarAlgebra (A : Type*) extends CStarAlgebra A where
  mul_comm : ∀ (a b : A), a * b = b * a

instance (priority := 100) CStarAlgebra.toNonUnitalCStarAlgebra (A : Type*) [CStarAlgebra A] :
    NonUnitalCStarAlgebra A where

instance (priority := 100) CommCStarAlgebra.toNonUnitalCommCStarAlgebra
    (A : Type*) [CommCStarAlgebra A] : NonUnitalCommCStarAlgebra A where
  mul_comm := mul_comm

instance (priority := 100) CommCStarAlgebra.toNormedCommRing
    (A : Type*) [CommCStarAlgebra A] : NormedCommRing A where
  mul_comm := mul_comm

instance (priority := 100) NonUnitalCommCStarAlgebra.toNonUnitalNormedCommRing
    (A : Type*) [NonUnitalCommCStarAlgebra A] : NonUnitalNormedCommRing A where
  mul_comm := mul_comm

-- missing instance: where should it go?
-- `Algebra.Ring.Subsemiring.Basic`
instance {S R : Type*} [Ring R] [SetLike S R] [SubsemiringClass S R] :
    NonUnitalSubsemiringClass S R where
  mul_mem := mul_mem

-- missing instance: where should it go?
instance {S R : Type*} [Ring R] [SetLike S R] [SubringClass S R] :
    NonUnitalSubringClass S R where

/-- This is not registered as an instance to avoid Lean searching for `IsClosed (s : Set A)`
instances frequently. -/
@[reducible]
noncomputable def StarSubalgebra.cstarAlgebra {S A : Type*} [CStarAlgebra A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]
    (s : S) (h_closed : IsClosed (s : Set A)) : CStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le

/-- This is not registered as an instance to avoid Lean searching for `IsClosed (s : Set A)`
instances frequently. -/
@[reducible]
noncomputable def StarSubalgebra.commCStarAlgebra {S A : Type*} [CommCStarAlgebra A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]
    (s : S) (h_closed : IsClosed (s : Set A)) : CommCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le
  mul_comm _ _ := Subtype.ext <| mul_comm _ _

/-- This is not registered as an instance to avoid Lean searching for `IsClosed (s : Set A)`
instances frequently. -/
@[reducible]
noncomputable def NonUnitalStarSubalgebra.nonUnitalCStarAlgebra {S A : Type*}
    [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] (s : S) (h_closed : IsClosed (s : Set A)) : NonUnitalCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le

/-- This is not registered as an instance to avoid Lean searching for `IsClosed (s : Set A)`
instances frequently. -/
@[reducible]
noncomputable def NonUnitalStarSubalgebra.nonUnitalCommCStarAlgebra {S A : Type*}
    [NonUnitalCommCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] (s : S) (h_closed : IsClosed (s : Set A)) : NonUnitalCommCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le
  mul_comm _ _ := Subtype.ext <| mul_comm _ _
