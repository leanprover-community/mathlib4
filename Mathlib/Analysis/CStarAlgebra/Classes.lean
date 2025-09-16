/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Algebra.StarSubalgebra

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

instance (priority := 100) CStarAlgebra.toNonUnitalCStarAlgebra (A : Type*) [CStarAlgebra A] :
    NonUnitalCStarAlgebra A where

instance (priority := 100) CommCStarAlgebra.toNonUnitalCommCStarAlgebra (A : Type*)
    [CommCStarAlgebra A] : NonUnitalCommCStarAlgebra A where

instance StarSubalgebra.cstarAlgebra {S A : Type*} [CStarAlgebra A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]
    (s : S) [h_closed : IsClosed (s : Set A)] : CStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le

instance StarSubalgebra.commCStarAlgebra {S A : Type*} [CommCStarAlgebra A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]
    (s : S) [h_closed : IsClosed (s : Set A)] : CommCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le
  mul_comm _ _ := Subtype.ext <| mul_comm _ _

instance NonUnitalStarSubalgebra.nonUnitalCStarAlgebra {S A : Type*}
    [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] (s : S) [h_closed : IsClosed (s : Set A)] : NonUnitalCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le

instance NonUnitalStarSubalgebra.nonUnitalCommCStarAlgebra {S A : Type*}
    [NonUnitalCommCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] (s : S) [h_closed : IsClosed (s : Set A)] : NonUnitalCommCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le
  mul_comm _ _ := Subtype.ext <| mul_comm _ _

noncomputable instance : CommCStarAlgebra ℂ where

section Elemental

variable {A : Type*}

noncomputable instance [CStarAlgebra A] (x : A) :
    CStarAlgebra (StarAlgebra.elemental ℂ x) :=
  StarSubalgebra.cstarAlgebra _ (h_closed := StarAlgebra.elemental.isClosed ℂ x)

noncomputable instance [NonUnitalCStarAlgebra A] (x : A) :
    NonUnitalCStarAlgebra (NonUnitalStarAlgebra.elemental ℂ x) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra _
    (h_closed := NonUnitalStarAlgebra.elemental.isClosed ℂ x)

noncomputable instance [CStarAlgebra A] (x : A) [IsStarNormal x] :
    CommCStarAlgebra (StarAlgebra.elemental ℂ x) where

noncomputable instance [NonUnitalCStarAlgebra A] (x : A) [IsStarNormal x] :
    NonUnitalCommCStarAlgebra (NonUnitalStarAlgebra.elemental ℂ x) where

end Elemental

section Pi

variable {ι : Type*} {A : ι → Type*} [Fintype ι]

instance [(i : ι) → NonUnitalCStarAlgebra (A i)] : NonUnitalCStarAlgebra (Π i, A i) where

instance [(i : ι) → NonUnitalCommCStarAlgebra (A i)] : NonUnitalCommCStarAlgebra (Π i, A i) where

instance [(i : ι) → CStarAlgebra (A i)] : CStarAlgebra (Π i, A i) where

instance [(i : ι) → CommCStarAlgebra (A i)] : CommCStarAlgebra (Π i, A i) where

end Pi

section Prod

variable {A B : Type*}

instance [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] : NonUnitalCStarAlgebra (A × B) where

instance [NonUnitalCommCStarAlgebra A] [NonUnitalCommCStarAlgebra B] :
    NonUnitalCommCStarAlgebra (A × B) where

instance [CStarAlgebra A] [CStarAlgebra B] : CStarAlgebra (A × B) where

instance [CommCStarAlgebra A] [CommCStarAlgebra B] : CommCStarAlgebra (A × B) where

end Prod

namespace MulOpposite

variable {A : Type*}

instance [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra Aᵐᵒᵖ where

instance [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra Aᵐᵒᵖ where

instance [CStarAlgebra A] : CStarAlgebra Aᵐᵒᵖ where

instance [CommCStarAlgebra A] : CommCStarAlgebra Aᵐᵒᵖ where

end MulOpposite
