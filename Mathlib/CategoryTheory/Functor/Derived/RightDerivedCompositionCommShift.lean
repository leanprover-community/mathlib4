/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedComposition
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift

/-!
# Compatibility with shifts of the comparison morphism for the composition of right derived functors

```
     F₁₂  F₂₃
  C₁ ⥤ C₂ = C₃
L₁|  L₂|   L₃|
  v    v     v
  D₁ ⥤ D₂ ⥤ D₃
   RF₁₂   RF₂₃
```
In the situation above, when we have natural transformations
`α₁₂ : F₁₂ ⋙ L₂ ⟶ L₁ ⋙ RF₁₂`, `α₂₃ : F₂₃ ⋙ L₃ ⟶ L₂ ⋙ RF₂₃`,
an isomorphism `e : F₁₂ ⋙ F₂₃ ≅ F₁₃` where `F₁₃ : C₁ ⥤ C₃`,
and a natural transformation `α₁₃ : F₁₃ ⋙ L₃ ⟶ L₁ ⋙ RF₁₃`
which makes `RF₁₃` the derived functor of of `F₁₃ ⋙ L₃`
(with respect to `W₁ : MorphismProperty C₁`),
a comparison morphism `RF₁₃ ⟶ RF₁₂ ⋙ RF₂₃` for the composition
of right derived functors was defined in the file
`Mathlib.CategoryTheory.Functor.Derived.RightDerivedComposition`.
In this file, we show that if all the categories are equipped with
shifts by an abelian group `A`, all the involved functors and natural
transformations commute with these, then this natural transformation
`RF₁₃ ⟶ RF₁₂ ⋙ RF₂₃` also commutes with shifts.

-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category D₁] [Category D₂] [Category D₃]
  {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₁₃ : C₁ ⥤ C₃} (e : F₁₂ ⋙ F₂₃ ≅ F₁₃)
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃)
  (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  {RF₁₂ : D₁ ⥤ D₂} {RF₂₃ : D₂ ⥤ D₃} {RF₁₃ : D₁ ⥤ D₃}
  (α₁₂ : F₁₂ ⋙ L₂ ⟶ L₁ ⋙ RF₁₂)
  (α₂₃ : F₂₃ ⋙ L₃ ⟶ L₂ ⋙ RF₂₃)
  (α₁₃ : F₁₃ ⋙ L₃ ⟶ L₁ ⋙ RF₁₃) [RF₁₃.IsRightDerivedFunctor α₁₃ W₁]
  (A : Type*) [AddGroup A]
  [HasShift C₁ A] [HasShift C₂ A] [HasShift C₃ A]
  [HasShift D₁ A] [HasShift D₂ A] [HasShift D₃ A]
  [W₁.IsCompatibleWithShift A]
  [L₁.CommShift A] [L₂.CommShift A] [L₃.CommShift A]
  [F₁₂.CommShift A] [F₂₃.CommShift A] [F₁₃.CommShift A]
  [RF₁₂.CommShift A] [RF₂₃.CommShift A] [RF₁₃.CommShift A]
  [e.hom.CommShift A] [α₁₂.CommShift A] [α₂₃.CommShift A] [α₁₃.CommShift A]

instance : (natTransOfIsRightDerivedFunctorComp e L₁ L₂ L₃ W₁ α₁₂ α₂₃ α₁₃).CommShift A :=
  NatTrans.CommShift.of_isRightDerivedFunctor _ _ _ W₁
    (comp_whiskerLeft_natTransOfIsRightDerivedFunctorComp e L₁ L₂ L₃ W₁ α₁₂ α₂₃ α₁₃)

end Functor

end CategoryTheory
