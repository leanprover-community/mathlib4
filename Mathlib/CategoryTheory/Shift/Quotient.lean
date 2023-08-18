/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.Induced
import Mathlib.CategoryTheory.Quotient

/-!
# Shift on a quotient category

Let `C` be a category equipped a shift by a monoid `A`. If we have a relation
on morphisms `r : HomRel C` that is compatible with the shift (i.e. if two
morphisms `f` and `g` are related, then `f⟦a⟧'` and `g⟦a⟧'` are also related
for all `a : A`), then the quotient category `Quotient r` is equipped with
a shift.

The condition `r.IsCompatibleWithShift A` on the relation `r` is a class so that
the shift can be automatically infered on the quotient category.

-/

universe v u

open CategoryTheory

variable {C : Type u} [Category.{v} C]
  (r : HomRel C) (A : Type _) [AddMonoid A] [HasShift C A]

namespace HomRel

class IsCompatibleWithShift : Prop :=
  translate : ∀ (a : A) ⦃X Y : C⦄ (f g : X ⟶ Y) (_ : r f g), r (f⟦a⟧') (g⟦a⟧')

end HomRel

namespace CategoryTheory

variable (s : A → Quotient r ⥤ Quotient r)
  (i : ∀ a, Quotient.functor r ⋙ s a ≅ shiftFunctor C a ⋙ Quotient.functor r)

lemma HasShift.quotient'_aux :
    Nonempty (Full ((whiskeringLeft C _ (Quotient r)).obj (Quotient.functor r))) ∧
        Faithful ((whiskeringLeft C _ (Quotient r)).obj (Quotient.functor r)) :=
  ⟨⟨inferInstance⟩, inferInstance⟩

noncomputable def HasShift.quotient' :
    HasShift (Quotient r) A :=
  HasShift.induced (Quotient.functor r) A s i (HasShift.quotient'_aux r)

noncomputable def Functor.CommShift.quotient' :
    letI : HasShift (Quotient r) A := HasShift.quotient' r A s i
    (Quotient.functor r).CommShift A :=
  Functor.CommShift.ofInduced _ _ _ _ _

variable {A}

def Quotient.shiftFunctor' [r.IsCompatibleWithShift A] (a : A) : Quotient r ⥤ Quotient r :=
  Quotient.lift r (CategoryTheory.shiftFunctor C a ⋙ Quotient.functor r)
    (fun _ _ _ _ hfg => Quotient.sound r (HomRel.IsCompatibleWithShift.translate _ _ _ hfg))

def Quotient.shiftFunctor'Factors [r.IsCompatibleWithShift A] (a : A) :
    Quotient.functor r ⋙ Quotient.shiftFunctor' r a ≅
      CategoryTheory.shiftFunctor C a ⋙ Quotient.functor r :=
  Quotient.lift.isLift _ _ _

variable (A)

noncomputable instance HasShift.quotient [r.IsCompatibleWithShift A] :
    HasShift (Quotient r) A :=
  HasShift.quotient' r A (Quotient.shiftFunctor' r) (Quotient.shiftFunctor'Factors r)

noncomputable instance Quotient.functor_commShift [r.IsCompatibleWithShift A] :
    (Quotient.functor r).CommShift A :=
  Functor.CommShift.quotient' _ _ _ _

-- the construction is made irreducible in order to prevent timeouts and abuse of defeq
attribute [irreducible] HasShift.quotient Quotient.functor_commShift

end CategoryTheory
