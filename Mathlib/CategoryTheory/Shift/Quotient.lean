import Mathlib.CategoryTheory.Shift.Induced
import Mathlib.CategoryTheory.Quotient

open CategoryTheory Category

variable {C : Type _} [Category C]
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
  Functor.CommShift.of_induced _ _ _ _ _

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

-- the construction is made irreducible in order to prevent timeouts
attribute [irreducible] HasShift.quotient Quotient.functor_commShift

noncomputable example [r.IsCompatibleWithShift A] :
    HasShift (Quotient r) A := inferInstance

noncomputable example [r.IsCompatibleWithShift A] :
    Functor.CommShift (Quotient.functor r) A := inferInstance

end CategoryTheory
