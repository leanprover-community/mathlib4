/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Monoidal.Pentagon
import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedBifunctorComp

/-!
# Derived monoidal category structure

-/

namespace CategoryTheory

open MonoidalCategory

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.ContainsIdentities]

def DerivedMonoidal (_ : C ⥤ D) (_ : MorphismProperty C) := D

instance : Category (DerivedMonoidal L W) := inferInstanceAs (Category D)

section

variable [(curriedTensor C ⋙ (whiskeringRight _ _ _).obj L).HasLeftDerivedFunctor₂ W W]

noncomputable nonrec def DerivedMonoidal.bifunctor :
    DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤ DerivedMonoidal L W :=
  (curriedTensor C ⋙ (whiskeringRight _ _ _).obj L).leftDerived₂ L L W W

def toDerivedMonoidal : C ⥤ DerivedMonoidal L W := L

instance : (toDerivedMonoidal L W).IsLocalization W := by assumption

noncomputable def DerivedMonoidal.counit :
    (((whiskeringLeft₂ D).obj L).obj L).obj (bifunctor L W) ⟶
    curriedTensor C ⋙ (whiskeringRight _ _ _).obj L :=
  (curriedTensor C ⋙ (whiskeringRight _ _ _).obj L).leftDerivedCounit₂ L L W W

instance :
    (DerivedMonoidal.bifunctor L W).IsLeftDerivedFunctor₂
      (DerivedMonoidal.counit L W) W W := by
  dsimp only [DerivedMonoidal.bifunctor, DerivedMonoidal.counit]
  infer_instance

end

-- needs more assumptions
class Functor.HasDerivedMonoidalCategory : Prop where
  hasLeftDerivedFunctor₂ :
    (curriedTensor C ⋙ (whiskeringRight _ _ _).obj L).HasLeftDerivedFunctor₂ W W
  bifunctorComp₁₂_isLeftDerivedFunctor :
    Functor.IsLeftDerivedFunctor₃ _ (bifunctorComp₁₂Counit (DerivedMonoidal.counit L W)
      (DerivedMonoidal.counit L W)) W W W
  bifunctorComp₂₃_isLeftDerivedFunctor :
    Functor.IsLeftDerivedFunctor₃ _ (bifunctorComp₂₃Counit (DerivedMonoidal.counit L W)
      (DerivedMonoidal.counit L W)) W W W

namespace Functor.HasDerivedMonoidalCategory

attribute [instance] hasLeftDerivedFunctor₂
  bifunctorComp₂₃_isLeftDerivedFunctor
  bifunctorComp₁₂_isLeftDerivedFunctor

end Functor.HasDerivedMonoidalCategory

namespace DerivedMonoidal

variable [L.HasDerivedMonoidalCategory W]

noncomputable def associator :
    bifunctorComp₁₂ (bifunctor L W) (bifunctor L W) ≅
      bifunctorComp₂₃ (bifunctor L W) (bifunctor L W) :=
  Functor.leftDerived₃NatIso _ _
    (bifunctorComp₁₂Counit (counit L W) (counit L W))
    (bifunctorComp₂₃Counit (counit L W) (counit L W)) W W W
    ((Functor.postcompose₃.obj L).mapIso (curriedAssociatorNatIso C))

--noncomputable instance : MonoidalCategory (DerivedMonoidal L W) :=
--  .ofBifunctor ((toDerivedMonoidal L W).obj (𝟙_ C)) (bifunctor L W) (associator L W)
--    sorry sorry sorry sorry

end DerivedMonoidal

end CategoryTheory
