/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.functor_category
! leanprover-community/mathlib commit 73dd4b5411ec8fafb18a9d77c9c826907730af80
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const

/-!
# Monoidal structure on `C ⥤ D` when `D` is monoidal.

When `C` is any category, and `D` is a monoidal category,
there is a natural "pointwise" monoidal structure on `C ⥤ D`.

The initial intended application is tensor product of presheaves.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Monoidal

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

namespace FunctorCategory

variable (F G F' G' : C ⥤ D)

/-- (An auxiliary definition for `functorCategoryMonoidal`.)
Tensor product of functors `C ⥤ D`, when `D` is monoidal.
 -/
@[simps]
def tensorObj : C ⥤ D where
  obj X := F.obj X ⊗ G.obj X
  map f := F.map f ⊗ G.map f
#align category_theory.monoidal.functor_category.tensor_obj CategoryTheory.Monoidal.FunctorCategory.tensorObj

variable {F G F' G'}

variable (α : F ⟶ G) (β : F' ⟶ G')

/-- (An auxiliary definition for `functorCategoryMonoidal`.)
Tensor product of natural transformations into `D`, when `D` is monoidal.
-/
@[simps]
def tensorHom : tensorObj F F' ⟶ tensorObj G G' where
  app X := α.app X ⊗ β.app X
  naturality X Y f := by dsimp; rw [← tensor_comp, α.naturality, β.naturality, tensor_comp]
#align category_theory.monoidal.functor_category.tensor_hom CategoryTheory.Monoidal.FunctorCategory.tensorHom

end FunctorCategory

open CategoryTheory.Monoidal.FunctorCategory

/-- When `C` is any category, and `D` is a monoidal category,
the functor category `C ⥤ D` has a natural pointwise monoidal structure,
where `(F ⊗ G).obj X = F.obj X ⊗ G.obj X`.
-/
instance functorCategoryMonoidal : MonoidalCategory (C ⥤ D) where
  tensorObj F G := tensorObj F G
  tensorHom α β := tensorHom α β
  tensor_id F G := by ext; dsimp; rw [tensor_id]
  tensor_comp α β γ δ := by ext; dsimp; rw [tensor_comp]
  tensorUnit' := (CategoryTheory.Functor.const C).obj (𝟙_ D)
  leftUnitor F := NatIso.ofComponents (fun X => λ_ (F.obj X))
    (fun f => by dsimp; rw [leftUnitor_naturality])
  rightUnitor F := NatIso.ofComponents (fun X => ρ_ (F.obj X))
    (fun f => by dsimp; rw [rightUnitor_naturality])
  associator F G H := NatIso.ofComponents (fun X => α_ (F.obj X) (G.obj X) (H.obj X))
    (fun f => by dsimp;rw [associator_naturality])
  leftUnitor_naturality α := by ext X; dsimp; rw [leftUnitor_naturality]
  rightUnitor_naturality α := by ext X; dsimp; rw [rightUnitor_naturality]
  associator_naturality α β γ := by ext X; dsimp; rw [associator_naturality]
  triangle F G := by ext X; dsimp; rw [triangle]
  pentagon F G H K := by ext X; dsimp; rw [pentagon]
#align category_theory.monoidal.functor_category_monoidal CategoryTheory.Monoidal.functorCategoryMonoidal

@[simp]
theorem tensorUnit_obj {X} : (𝟙_ (C ⥤ D)).obj X = 𝟙_ D :=
  rfl
#align category_theory.monoidal.tensor_unit_obj CategoryTheory.Monoidal.tensorUnit_obj

@[simp]
theorem tensorUnit_map {X Y} {f : X ⟶ Y} : (𝟙_ (C ⥤ D)).map f = 𝟙 (𝟙_ D) :=
  rfl
#align category_theory.monoidal.tensor_unit_map CategoryTheory.Monoidal.tensorUnit_map

@[simp]
theorem tensorObj_obj {F G : C ⥤ D} {X} : (F ⊗ G).obj X = F.obj X ⊗ G.obj X :=
  rfl
#align category_theory.monoidal.tensor_obj_obj CategoryTheory.Monoidal.tensorObj_obj

@[simp]
theorem tensorObj_map {F G : C ⥤ D} {X Y} {f : X ⟶ Y} : (F ⊗ G).map f = F.map f ⊗ G.map f :=
  rfl
#align category_theory.monoidal.tensor_obj_map CategoryTheory.Monoidal.tensorObj_map

@[simp]
theorem tensorHom_app {F G F' G' : C ⥤ D} {α : F ⟶ G} {β : F' ⟶ G'} {X} :
    (α ⊗ β).app X = α.app X ⊗ β.app X :=
  rfl
#align category_theory.monoidal.tensor_hom_app CategoryTheory.Monoidal.tensorHom_app

@[simp]
theorem leftUnitor_hom_app {F : C ⥤ D} {X} :
    ((λ_ F).hom : 𝟙_ _ ⊗ F ⟶ F).app X = (λ_ (F.obj X)).hom :=
  rfl
#align category_theory.monoidal.left_unitor_hom_app CategoryTheory.Monoidal.leftUnitor_hom_app

@[simp]
theorem leftUnitor_inv_app {F : C ⥤ D} {X} :
    ((λ_ F).inv : F ⟶ 𝟙_ _ ⊗ F).app X = (λ_ (F.obj X)).inv :=
  rfl
#align category_theory.monoidal.left_unitor_inv_app CategoryTheory.Monoidal.leftUnitor_inv_app

@[simp]
theorem rightUnitor_hom_app {F : C ⥤ D} {X} :
    ((ρ_ F).hom : F ⊗ 𝟙_ _ ⟶ F).app X = (ρ_ (F.obj X)).hom :=
  rfl
#align category_theory.monoidal.right_unitor_hom_app CategoryTheory.Monoidal.rightUnitor_hom_app

@[simp]
theorem rightUnitor_inv_app {F : C ⥤ D} {X} :
    ((ρ_ F).inv : F ⟶ F ⊗ 𝟙_ _).app X = (ρ_ (F.obj X)).inv :=
  rfl
#align category_theory.monoidal.right_unitor_inv_app CategoryTheory.Monoidal.rightUnitor_inv_app

@[simp]
theorem associator_hom_app {F G H : C ⥤ D} {X} :
    ((α_ F G H).hom : (F ⊗ G) ⊗ H ⟶ F ⊗ G ⊗ H).app X = (α_ (F.obj X) (G.obj X) (H.obj X)).hom :=
  rfl
#align category_theory.monoidal.associator_hom_app CategoryTheory.Monoidal.associator_hom_app

@[simp]
theorem associator_inv_app {F G H : C ⥤ D} {X} :
    ((α_ F G H).inv : F ⊗ G ⊗ H ⟶ (F ⊗ G) ⊗ H).app X = (α_ (F.obj X) (G.obj X) (H.obj X)).inv :=
  rfl
#align category_theory.monoidal.associator_inv_app CategoryTheory.Monoidal.associator_inv_app

section BraidedCategory

open CategoryTheory.BraidedCategory

variable [BraidedCategory.{v₂} D]

/-- When `C` is any category, and `D` is a braided monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also braided.
-/
instance functorCategoryBraided : BraidedCategory (C ⥤ D) where
  braiding F G := NatIso.ofComponents (fun X => β_ _ _) (by aesop_cat)
  hexagon_forward F G H := by ext X; apply hexagon_forward
  hexagon_reverse F G H := by ext X; apply hexagon_reverse
#align category_theory.monoidal.functor_category_braided CategoryTheory.Monoidal.functorCategoryBraided

example : BraidedCategory (C ⥤ D) :=
  CategoryTheory.Monoidal.functorCategoryBraided

end BraidedCategory

section SymmetricCategory

open CategoryTheory.SymmetricCategory

variable [SymmetricCategory.{v₂} D]

/-- When `C` is any category, and `D` is a symmetric monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also symmetric.
-/
instance functorCategorySymmetric : SymmetricCategory (C ⥤ D)
    where symmetry F G := by ext X; apply symmetry
#align category_theory.monoidal.functor_category_symmetric CategoryTheory.Monoidal.functorCategorySymmetric

end SymmetricCategory

end CategoryTheory.Monoidal
