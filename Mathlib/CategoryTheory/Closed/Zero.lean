/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

#align_import category_theory.closed.zero from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# A cartesian closed category with zero object is trivial

A cartesian closed category with zero object is trivial: it is equivalent to the category with one
object and one morphism.

## References

* https://mathoverflow.net/a/136480

-/


universe w v u

noncomputable section

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]
variable [HasFiniteProducts C] [CartesianClosed C]

/-- If a cartesian closed category has an initial object which is isomorphic to the terminal object,
then each homset has exactly one element.
-/
def uniqueHomsetOfInitialIsoTerminal [HasInitial C] (i : ⊥_ C ≅ ⊤_ C) (X Y : C) : Unique (X ⟶ Y) :=
  Equiv.unique <|
    calc
      (X ⟶ Y) ≃ (X ⨯ ⊤_ C ⟶ Y) := Iso.homCongr (prod.rightUnitor _).symm (Iso.refl _)
      _ ≃ (X ⨯ ⊥_ C ⟶ Y) := (Iso.homCongr (prod.mapIso (Iso.refl _) i.symm) (Iso.refl _))
      _ ≃ (⊥_ C ⟶ Y ^^ X) := (exp.adjunction _).homEquiv _ _
#align category_theory.unique_homset_of_initial_iso_terminal CategoryTheory.uniqueHomsetOfInitialIsoTerminal

open scoped ZeroObject

/-- If a cartesian closed category has a zero object, each homset has exactly one element. -/
def uniqueHomsetOfZero [HasZeroObject C] (X Y : C) : Unique (X ⟶ Y) := by
  haveI : HasInitial C := HasZeroObject.hasInitial
  apply uniqueHomsetOfInitialIsoTerminal _ X Y
  refine ⟨default, (default : ⊤_ C ⟶ 0) ≫ default, ?_, ?_⟩ <;> simp [eq_iff_true_of_subsingleton]
#align category_theory.unique_homset_of_zero CategoryTheory.uniqueHomsetOfZero

attribute [local instance] uniqueHomsetOfZero

/-- A cartesian closed category with a zero object is equivalent to the category with one object and
one morphism.
-/
def equivPUnit [HasZeroObject C] : C ≌ Discrete PUnit.{w + 1} :=
  Equivalence.mk (Functor.star C) (Functor.fromPUnit 0)
    (NatIso.ofComponents
      (fun X =>
        { hom := default
          inv := default })
      fun f => Subsingleton.elim _ _)
    (Functor.punitExt _ _)
#align category_theory.equiv_punit CategoryTheory.equivPUnit

end CategoryTheory
