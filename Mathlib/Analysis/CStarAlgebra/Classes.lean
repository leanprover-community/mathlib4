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

These classes are not defined in `Mathlib/Analysis/CStarAlgebra/Basic.lean` because they require
heavier imports.

-/

/-- The class of non-unital (complex) C⋆-algebras. -/
class NonUnitalCStarAlgebra (A : Type*) extends NonUnitalNormedRing A, StarRing A, CompleteSpace A,
    CStarRing A, NormedSpace ℂ A, IsScalarTower ℂ A A, SMulCommClass ℂ A A, StarModule ℂ A where

/-- The class of non-unital commutative (complex) C⋆-algebras. -/
class NonUnitalCommCStarAlgebra (A : Type*) extends
    NonUnitalNormedCommRing A, NonUnitalCStarAlgebra A

/-- The class of unital (complex) C⋆-algebras. -/
class CStarAlgebra (A : Type*) extends NormedRing A, StarRing A, CompleteSpace A, CStarRing A,
    NormedAlgebra ℂ A, StarModule ℂ A where

/-- The class of unital commutative (complex) C⋆-algebras. -/
class CommCStarAlgebra (A : Type*) extends NormedCommRing A, CStarAlgebra A

#adaptation_note /-- 2025-03-29 for lean4#7717 had to add `norm_mul_self_le` field. -/
instance (priority := 100) CStarAlgebra.toNonUnitalCStarAlgebra (A : Type*) [CStarAlgebra A] :
    NonUnitalCStarAlgebra A where
  norm_mul_self_le := CStarRing.norm_mul_self_le

instance (priority := 100) CommCStarAlgebra.toNonUnitalCommCStarAlgebra (A : Type*)
    [CommCStarAlgebra A] : NonUnitalCommCStarAlgebra A where

noncomputable instance StarSubalgebra.cstarAlgebra {S A : Type*} [CStarAlgebra A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]
    (s : S) [h_closed : IsClosed (s : Set A)] : CStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le

noncomputable instance StarSubalgebra.commCStarAlgebra {S A : Type*} [CommCStarAlgebra A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]
    (s : S) [h_closed : IsClosed (s : Set A)] : CommCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le
  mul_comm _ _ := Subtype.ext <| mul_comm _ _

noncomputable instance NonUnitalStarSubalgebra.nonUnitalCStarAlgebra {S A : Type*}
    [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] (s : S) [h_closed : IsClosed (s : Set A)] : NonUnitalCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le

noncomputable instance NonUnitalStarSubalgebra.nonUnitalCommCStarAlgebra {S A : Type*}
    [NonUnitalCommCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] (s : S) [h_closed : IsClosed (s : Set A)] : NonUnitalCommCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le
  mul_comm _ _ := Subtype.ext <| mul_comm _ _

#adaptation_note /-- 2025-03-29 for lean4#7717 had to add `norm_mul_self_le` field. -/
noncomputable instance : CommCStarAlgebra ℂ where
  mul_comm := mul_comm
  norm_mul_self_le := CStarRing.norm_mul_self_le

section Pi

variable {ι : Type*} {A : ι → Type*} [Fintype ι]

#adaptation_note /-- 2025-03-29 for lean4#7717 had to add `norm_mul_self_le` field. -/
instance [(i : ι) → NonUnitalCStarAlgebra (A i)] : NonUnitalCStarAlgebra (Π i, A i) where
  norm_mul_self_le := CStarRing.norm_mul_self_le

instance [(i : ι) → NonUnitalCommCStarAlgebra (A i)] : NonUnitalCommCStarAlgebra (Π i, A i) where
  mul_comm := mul_comm

#adaptation_note /-- 2025-03-29 for lean4#7717 had to add `norm_mul_self_le` field. -/
noncomputable instance [(i : ι) → CStarAlgebra (A i)] : CStarAlgebra (Π i, A i) where
  norm_mul_self_le := CStarRing.norm_mul_self_le

noncomputable instance [(i : ι) → CommCStarAlgebra (A i)] : CommCStarAlgebra (Π i, A i) where
  mul_comm := mul_comm

end Pi

section Prod

variable {A B : Type*}

#adaptation_note /-- 2025-03-29 for lean4#7717 had to add `norm_mul_self_le` field. -/
instance [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] : NonUnitalCStarAlgebra (A × B) where
  norm_mul_self_le := CStarRing.norm_mul_self_le

instance [NonUnitalCommCStarAlgebra A] [NonUnitalCommCStarAlgebra B] :
    NonUnitalCommCStarAlgebra (A × B) where
  mul_comm := mul_comm

#adaptation_note /-- 2025-03-29 for lean4#7717 had to add `norm_mul_self_le` field. -/
noncomputable instance [CStarAlgebra A] [CStarAlgebra B] : CStarAlgebra (A × B) where
  norm_mul_self_le := CStarRing.norm_mul_self_le

noncomputable instance [CommCStarAlgebra A] [CommCStarAlgebra B] : CommCStarAlgebra (A × B) where
  mul_comm := mul_comm

end Prod

namespace MulOpposite

variable {A : Type*}

#adaptation_note /-- 2025-03-29 for lean4#7717 had to add `norm_mul_self_le` field. -/
instance [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra Aᵐᵒᵖ where
  norm_mul_self_le := CStarRing.norm_mul_self_le

instance [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra Aᵐᵒᵖ where

#adaptation_note /-- 2025-03-29 for lean4#7717 had to add `norm_mul_self_le` field. -/
noncomputable instance [CStarAlgebra A] : CStarAlgebra Aᵐᵒᵖ where
  norm_mul_self_le := CStarRing.norm_mul_self_le

noncomputable instance [CommCStarAlgebra A] : CommCStarAlgebra Aᵐᵒᵖ where

end MulOpposite
