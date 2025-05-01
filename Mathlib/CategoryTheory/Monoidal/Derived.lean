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

noncomputable nonrec def DerivedMonoidal.tensor :
    DerivedMonoidal L W ⥤ DerivedMonoidal L W ⥤ DerivedMonoidal L W :=
  (curriedTensor C ⋙ (whiskeringRight _ _ _).obj L).leftDerived₂ L L W W

def toDerivedMonoidal : C ⥤ DerivedMonoidal L W := L

instance : (toDerivedMonoidal L W).IsLocalization W := by assumption

noncomputable def DerivedMonoidal.counit :
    (((whiskeringLeft₂ D).obj L).obj L).obj (tensor L W) ⟶
    curriedTensor C ⋙ (whiskeringRight _ _ _).obj L :=
  (curriedTensor C ⋙ (whiskeringRight _ _ _).obj L).leftDerivedCounit₂ L L W W

instance :
    (DerivedMonoidal.tensor L W).IsLeftDerivedFunctor₂
      (DerivedMonoidal.counit L W) W W := by
  dsimp only [DerivedMonoidal.tensor, DerivedMonoidal.counit]
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

namespace DerivedMonoidal

end DerivedMonoidal

end CategoryTheory
