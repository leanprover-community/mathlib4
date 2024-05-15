/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-
# The monoidal category structure induced by a monoidal functor

In this file, given a monoidal functor `F : MonoidalFunctor C D`, we define
a monoidal category structure on the category `InducedCategory D F.obj`,
which has the "same" objects as `C`, but the morphisms between `X` and `Y` identify to
`F.obj X ⟶ F.obj Y`.

-/

namespace CategoryTheory.InducedCategory

variable {C D : Type*} [Category D] {F : C → D}

abbrev mk (X : C) : InducedCategory D F := X

abbrev homMk {X Y : InducedCategory D F} (f : F X ⟶ F Y) : X ⟶ Y := f

@[simps]
def isoMk {X Y : InducedCategory D F} (e : F X ≅ F Y) : X ≅ Y where
  hom := homMk e.hom
  inv := homMk e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

end CategoryTheory.InducedCategory

namespace CategoryTheory.MonoidalCategory

open InducedCategory Category

variable {C D : Type*} [Category C] [Category D]
  [MonoidalCategory C] [MonoidalCategory D] (F : MonoidalFunctor C D)

noncomputable instance inducedCategoryMonoidal :
    MonoidalCategoryStruct (InducedCategory D F.obj) where
  tensorObj X Y := InducedCategory.mk (X ⊗ Y)
  tensorUnit := (tensorUnit : C)
  whiskerLeft X {Y₁ Y₂} g := InducedCategory.homMk ((F.μIso X Y₁).inv ≫
    F.obj X ◁ (inducedFunctor F.obj).map g ≫ (F.μIso X Y₂).hom)
  whiskerRight {X₁ X₂} f Y := InducedCategory.homMk
    ((F.μIso X₁ Y).inv ≫ (inducedFunctor F.obj).map f ▷ F.obj Y ≫ (F.μIso X₂ Y).hom)
  tensorHom {X₁ X₂ Y₁ Y₂} f g :=
    InducedCategory.homMk ((F.μIso X₁ Y₁).inv ≫
      ((inducedFunctor F.obj).map f ⊗ (inducedFunctor F.obj).map g) ≫ (F.μIso X₂ Y₂).hom)
  associator X Y Z := InducedCategory.isoMk (F.mapIso (associator (C := C) X Y Z))
  leftUnitor X := InducedCategory.isoMk (F.mapIso (leftUnitor (C := C) X))
  rightUnitor X := InducedCategory.isoMk (F.mapIso (rightUnitor (C := C) X))

-- very draft, this will be cleaned up when `InducedCategory`
-- is refactored using 1-field structures
noncomputable instance : MonoidalCategory (InducedCategory D F.obj) where
  tensor_id X Y := by
    dsimp [inducedCategoryMonoidal]
    erw [tensor_id]
    simp
    rfl
  tensor_comp := sorry
  tensorHom_def := sorry
  whiskerLeft_id X Y := by
    dsimp [inducedCategoryMonoidal]
    erw [whiskerLeft_id]
    simp
    rfl
  id_whiskerRight X Y := by
    dsimp [inducedCategoryMonoidal]
    erw [id_whiskerRight]
    simp
    rfl
  associator_naturality := sorry
  leftUnitor_naturality := sorry
  rightUnitor_naturality := sorry
  pentagon X Y Z T := by
    dsimp [inducedCategoryMonoidal, homMk]
    simp only [LaxMonoidalFunctor.μ_natural_left, MonoidalFunctor.μ_inv_hom_id_assoc,
      LaxMonoidalFunctor.μ_natural_right]
    erw [← F.map_comp, ← F.map_comp, ← F.map_comp]
    simp
  triangle X Y := by
    dsimp [inducedCategoryMonoidal, homMk]
    simp only [LaxMonoidalFunctor.μ_natural_right, MonoidalFunctor.μ_inv_hom_id_assoc,
      LaxMonoidalFunctor.μ_natural_left]
    erw [← F.map_comp]
    simp

def inducedMonoidalFunctor : MonoidalFunctor (InducedCategory D F.obj) D where
  toFunctor := inducedFunctor F.obj
  ε := F.ε
  μ := F.μ
  μ_natural_left := sorry
  μ_natural_right := sorry
  associativity := F.associativity
  left_unitality := F.left_unitality
  right_unitality := F.right_unitality

noncomputable def toInducedMonoidalFunctor : MonoidalFunctor C (InducedCategory D F.obj) where
  obj := id
  map := F.map
  ε := 𝟙 _
  μ _ _ := 𝟙 _
  ε_isIso := by dsimp; infer_instance
  μ_isIso := by dsimp; infer_instance
  μ_natural_left := sorry
  μ_natural_right := sorry
  associativity := sorry
  left_unitality := sorry
  right_unitality := sorry

noncomputable def toInducedCompInducedMonoidalFunctor :
    toInducedMonoidalFunctor F ⊗⋙ inducedMonoidalFunctor F ≅ F where
  -- needs a constructor for isomorphisms in the category of monoidal functors
  hom :=
    { app := fun X => 𝟙 _
      naturality := sorry
      unit := sorry
      tensor := sorry }
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

end CategoryTheory.MonoidalCategory
