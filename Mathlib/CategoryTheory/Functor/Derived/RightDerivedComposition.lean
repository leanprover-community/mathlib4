/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# Comparison morphism for the composition of right derived functors

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
we define a natural transformation `RF₁₃ ⟶ RF₁₂ ⋙ RF₂₃`
(see `Functor.natTransOfIsRightDerivedFunctorComp`).
We may say that this is the comparison morphism for the
composition of right derived functors, even though the
definition only assumes that `RF₁₃` is a right derived functor.
(In applications, both `RF₁₂` and `RF₂₃` would usually
be derived functors as well.)

-/

@[expose] public section

namespace CategoryTheory

open Category

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

/-- The comparison morphism for the composition of right derived functors. -/
@[no_expose]
noncomputable def natTransOfIsRightDerivedFunctorComp :
    RF₁₃ ⟶ RF₁₂ ⋙ RF₂₃ :=
  rightDerivedDesc RF₁₃ α₁₃ W₁ _ (whiskerRight e.inv _ ≫
    (associator _ _ _).hom ≫ whiskerLeft F₁₂ α₂₃ ≫ (associator _ _ _).inv ≫
      whiskerRight α₁₂ RF₂₃ ≫ (associator _ _ _).hom)

@[reassoc (attr := simp)]
lemma comp_whiskerLeft_natTransOfIsRightDerivedFunctorComp :
    α₁₃ ≫ whiskerLeft L₁ (natTransOfIsRightDerivedFunctorComp e L₁ L₂ L₃ W₁ α₁₂ α₂₃ α₁₃) =
      whiskerRight e.inv _ ≫
        (associator _ _ _).hom ≫ whiskerLeft F₁₂ α₂₃ ≫ (associator _ _ _).inv ≫
          whiskerRight α₁₂ RF₂₃ ≫ (associator _ _ _).hom := by
  simp [natTransOfIsRightDerivedFunctorComp]

@[reassoc (attr := simp)]
lemma comp_natTransOfIsRightDerivedFunctorComp_app (X : C₁) :
    α₁₃.app X ≫ (natTransOfIsRightDerivedFunctorComp e L₁ L₂ L₃ W₁ α₁₂ α₂₃ α₁₃).app (L₁.obj X) =
      L₃.map (e.inv.app X) ≫ α₂₃.app (F₁₂.obj X) ≫ RF₂₃.map (α₁₂.app X) := by
  simp [natTransOfIsRightDerivedFunctorComp]

lemma isIso_natTransOfIsRightDerivedFunctorComp_app (X : C₁)
    (h₁₂ : IsIso (α₁₃.app X) := by infer_instance)
    (h₁₂ : IsIso (α₁₂.app X) := by infer_instance)
    (h₂₃ : IsIso (α₂₃.app (F₁₂.obj X)) := by infer_instance) :
    IsIso ((natTransOfIsRightDerivedFunctorComp e L₁ L₂ L₃ W₁ α₁₂ α₂₃ α₁₃).app (L₁.obj X)) :=
  IsIso.of_isIso_fac_left
    (comp_natTransOfIsRightDerivedFunctorComp_app e L₁ L₂ L₃ W₁ α₁₂ α₂₃ α₁₃ X)

end Functor

end CategoryTheory
