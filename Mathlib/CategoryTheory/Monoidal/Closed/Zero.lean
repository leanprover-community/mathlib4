/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# A Cartesian-closed category with zero object is trivial

A Cartesian-closed category with zero object is trivial: it is equivalent to the category with one
object and one morphism.

## References

* https://mathoverflow.net/a/136480

-/


universe w v u

noncomputable section

namespace CategoryTheory

open Category Limits MonoidalCategory

variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [CartesianClosed C]

/-- If a Cartesian-closed category has an initial object which is isomorphic to the terminal object,
then each homset has exactly one element.
-/
def uniqueHomsetOfInitialIsoUnit [HasInitial C] (i : ⊥_ C ≅ 𝟙_ C) (X Y : C) : Unique (X ⟶ Y) :=
  Equiv.unique <|
    calc
      (X ⟶ Y) ≃ (X ⊗ 𝟙_ C ⟶ Y) := Iso.homCongr (rightUnitor _).symm (Iso.refl _)
      _ ≃ (X ⊗ ⊥_ C ⟶ Y) := (Iso.homCongr ((Iso.refl _) ⊗ᵢ i.symm) (Iso.refl _))
      _ ≃ (⊥_ C ⟶ Y ^^ X) := (exp.adjunction _).homEquiv _ _

open scoped ZeroObject

/-- If a Cartesian-closed category has a zero object, each homset has exactly one element. -/
def uniqueHomsetOfZero [HasZeroObject C] (X Y : C) : Unique (X ⟶ Y) := by
  haveI : HasInitial C := HasZeroObject.hasInitial
  apply uniqueHomsetOfInitialIsoUnit _ X Y
  refine ⟨default, (default : 𝟙_ C ⟶ 0) ≫ default, ?_, ?_⟩ <;> simp [eq_iff_true_of_subsingleton]

attribute [local instance] uniqueHomsetOfZero

/-- A Cartesian-closed category with a zero object is equivalent to the category with one object and
one morphism.
-/
def equivPUnit [HasZeroObject C] : C ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star C
  inverse := Functor.fromPUnit 0
  unitIso := NatIso.ofComponents
      (fun X =>
        { hom := default
          inv := default })
      fun _ => Subsingleton.elim _ _
  counitIso := Functor.punitExt _ _

end CategoryTheory
