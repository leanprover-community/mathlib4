/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Trifunctor
import Mathlib.CategoryTheory.Whiskering

/-!
# Quatrifunctors obtained by composition

-/

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ C₁₂₃ C₂₃₄ C : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₁₂₃]
  [Category C₄] [Category C₂₃₄] [Category C]

@[simps!]
def trifunctorComp₁₂₃ (F₁₂₃ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₁₂₃) (G : C₁₂₃ ⥤ C₄ ⥤ C) :
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ C :=
  (Functor.postcompose₃.obj G).obj F₁₂₃

@[simps!]
def trifunctorComp₂₃₄ (F : C₁ ⥤ C₂₃₄ ⥤ C) (G₂₃₄ : C₂ ⥤ C₃ ⥤ C₄ ⥤ C₂₃₄) :
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ C :=
  (F ⋙ Functor.postcompose₃).flip.obj G₂₃₄

end CategoryTheory
