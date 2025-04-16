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

/-- The class of non-unital (complex) C⋆-algebras. -/
class NonUnitalCStarAlgebra (A : Type*) [NonUnitalRing A] extends
    NormedRing A, StarRing A, CompleteSpace A,
    CStarRing A, NormedSpace ℂ A, IsScalarTower ℂ A A, SMulCommClass ℂ A A, StarModule ℂ A where

/-- The class of non-unital commutative (complex) C⋆-algebras. -/
@[deprecated "Use `[NonUnitalCommRing α] [NonUnitalCommCStarAlgebra α]` instead."
  (since := "2025-04-14")]
structure NonUnitalCommCStarAlgebra (A : Type*) extends
    NonUnitalCommRing A, NormedRing A, NonUnitalCStarAlgebra A

attribute [nolint docBlame] NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra

/-- The class of unital (complex) C⋆-algebras. -/
class CStarAlgebra (A : Type*) [Ring A] extends
    NormedRing A, StarRing A, CompleteSpace A, CStarRing A,
    NormedAlgebra ℂ A, StarModule ℂ A where

/-- The class of unital commutative (complex) C⋆-algebras. -/
@[deprecated "Use `[CommRing α] [CommCStarAlgebra α]` instead."
  (since := "2025-04-14")]
structure CommCStarAlgebra (A : Type*) extends CommRing A, NormedRing A, CStarAlgebra A

attribute [nolint docBlame] CommCStarAlgebra.toCStarAlgebra

instance (priority := 100) CStarAlgebra.toNonUnitalCStarAlgebra (A : Type*)
    [Ring A] [CStarAlgebra A] :
    NonUnitalCStarAlgebra A where

noncomputable instance StarSubalgebra.cstarAlgebra {S A : Type*} [Ring A] [CStarAlgebra A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]
    (s : S) [h_closed : IsClosed (s : Set A)] : CStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le

noncomputable instance NonUnitalStarSubalgebra.nonUnitalCStarAlgebra {S A : Type*}
    [NonUnitalRing A] [NonUnitalCStarAlgebra A]
    [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] (s : S) [h_closed : IsClosed (s : Set A)] : NonUnitalCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le

noncomputable instance : CStarAlgebra ℂ where

section Pi

variable {ι : Type*} {A : ι → Type*} [Fintype ι]

instance [(i : ι) → NonUnitalRing (A i)] [(i : ι) → NonUnitalCStarAlgebra (A i)] :
    NonUnitalCStarAlgebra (Π i, A i) where

noncomputable instance [(i : ι) → Ring (A i)] [(i : ι) → CStarAlgebra (A i)] :
    CStarAlgebra (Π i, A i) where

end Pi

section Prod

variable {A B : Type*}

instance [NonUnitalRing A] [NonUnitalCStarAlgebra A] [NonUnitalRing B] [NonUnitalCStarAlgebra B] :
    NonUnitalCStarAlgebra (A × B) where

noncomputable instance [Ring A] [CStarAlgebra A] [Ring B] [CStarAlgebra B] :
    CStarAlgebra (A × B) where

end Prod

namespace MulOpposite

variable {A : Type*}

instance [NonUnitalRing A] [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra Aᵐᵒᵖ where

noncomputable instance [Ring A] [CStarAlgebra A] : CStarAlgebra Aᵐᵒᵖ where

end MulOpposite
