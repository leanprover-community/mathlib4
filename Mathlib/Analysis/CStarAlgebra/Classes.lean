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
@[class_abbrev]
structure NonUnitalCStarAlgebra (A : Type*) where
  [a : NonUnitalRing A]
  [b : WithNormedRing A]
  [c : StarRing A]
  [d : CompleteSpace A]
  [e : CStarRing A]
  [f : NormedSpace ℂ A]
  [g : IsScalarTower ℂ A A]
  [h : SMulCommClass ℂ A A]
  [i : StarModule ℂ A]

attribute [instance] NonUnitalCStarAlgebra.mk

/-- The class of non-unital commutative (complex) C⋆-algebras. -/
@[class_abbrev]
structure NonUnitalCommCStarAlgebra (A : Type*) where
  [a : NonUnitalRing A]
  [b : WithNormedRing A]
  [c : StarRing A]
  [d : CompleteSpace A]
  [e : CStarRing A]
  [f : NormedSpace ℂ A]
  [g : IsScalarTower ℂ A A]
  [h : SMulCommClass ℂ A A]
  [i : StarModule ℂ A]

attribute [instance] NonUnitalCommCStarAlgebra.mk

/-- The class of unital (complex) C⋆-algebras. -/
@[class_abbrev]
structure CStarAlgebra (A : Type*) where
  [a : Ring A]
  [b : WithNormedRing A]
  [c : StarRing A]
  [d : CompleteSpace A]
  [e : CStarRing A]
  [f : NormedAlgebra ℂ A]
  [g : StarModule ℂ A]

attribute [instance] CStarAlgebra.mk

/-- The class of unital commutative (complex) C⋆-algebras. -/
@[class_abbrev]
structure CommCStarAlgebra (A : Type*) where
  [a : CommRing A]
  [b : WithNormedRing A]
  [c : StarRing A]
  [d : CompleteSpace A]
  [e : CStarRing A]
  [f : NormedAlgebra ℂ A]
  [g : StarModule ℂ A]

attribute [instance] CommCStarAlgebra.mk

noncomputable example (A : Type*) [CStarAlgebra A] : NonUnitalCStarAlgebra A := by infer_instance

noncomputable example (A : Type*) [CommCStarAlgebra A] : NonUnitalCommCStarAlgebra A := by
  infer_instance

noncomputable instance StarSubalgebra.cstarRing {S A : Type*} [NonUnitalCStarAlgebra A]
    [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]
    (s : S) : CStarRing s where
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le

instance {α β : Type*} [UniformSpace α] [CompleteSpace α] [SetLike β α] {s : β}
    [IsClosed (s : Set α)] :
    CompleteSpace s := by
  change CompleteSpace (s : Set α)
  infer_instance

noncomputable example {S A : Type*} [CStarAlgebra A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]
    (s : S) [h_closed : IsClosed (s : Set A)] : CStarAlgebra s := by infer_instance

noncomputable example {S A : Type*} [CommCStarAlgebra A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]
    (s : S) [h_closed : IsClosed (s : Set A)] : CommCStarAlgebra s := by infer_instance

noncomputable example {S A : Type*}
    [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] (s : S) [h_closed : IsClosed (s : Set A)] : NonUnitalCStarAlgebra s := by
  infer_instance

noncomputable example {S A : Type*}
    [NonUnitalCommCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] (s : S) [h_closed : IsClosed (s : Set A)] : NonUnitalCommCStarAlgebra s := by
  infer_instance

noncomputable example : CommCStarAlgebra ℂ := by infer_instance

section Pi

variable {ι : Type*} {A : ι → Type*} [Fintype ι]

example [(i : ι) → NonUnitalCStarAlgebra (A i)] : NonUnitalCStarAlgebra (Π i, A i) := by
  infer_instance

example [(i : ι) → NonUnitalCommCStarAlgebra (A i)] : NonUnitalCommCStarAlgebra (Π i, A i) := by
  infer_instance

example [(i : ι) → CStarAlgebra (A i)] : CStarAlgebra (Π i, A i) := by
  infer_instance

example [(i : ι) → CommCStarAlgebra (A i)] : CommCStarAlgebra (Π i, A i) := by
  infer_instance

end Pi

section Prod

variable {A B : Type*}

noncomputable example [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NonUnitalCStarAlgebra (A × B) := by infer_instance

noncomputable example [NonUnitalCommCStarAlgebra A] [NonUnitalCommCStarAlgebra B] :
    NonUnitalCommCStarAlgebra (A × B) := by infer_instance

noncomputable example [CStarAlgebra A] [CStarAlgebra B] : CStarAlgebra (A × B) := by
  infer_instance

noncomputable example [CommCStarAlgebra A] [CommCStarAlgebra B] : CommCStarAlgebra (A × B) := by
  infer_instance

end Prod

namespace MulOpposite

variable {A : Type*}

noncomputable example [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra Aᵐᵒᵖ := by infer_instance

noncomputable example [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra Aᵐᵒᵖ := by
  infer_instance

noncomputable example [CStarAlgebra A] : CStarAlgebra Aᵐᵒᵖ := by infer_instance

noncomputable example [CommCStarAlgebra A] : CommCStarAlgebra Aᵐᵒᵖ := by infer_instance

end MulOpposite
