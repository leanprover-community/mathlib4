/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.Const

/-!
# Monoidal structure on `C ⥤ D` when `D` is monoidal.

When `C` is any category, and `D` is a monoidal category,
there is a natural "pointwise" monoidal structure on `C ⥤ D`.

The initial intended application is tensor product of presheaves.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

namespace Monoidal

namespace FunctorCategory

variable (F G F' G' : C ⥤ D)

/-- (An auxiliary definition for `functorCategoryMonoidal`.)
Tensor product of functors `C ⥤ D`, when `D` is monoidal.
-/
@[simps]
def tensorObj : C ⥤ D where
  obj X := F.obj X ⊗ G.obj X
  map f := F.map f ⊗ₘ G.map f

variable {F G F' G'}
variable (α : F ⟶ G) (β : F' ⟶ G')

/-- (An auxiliary definition for `functorCategoryMonoidal`.)
Tensor product of natural transformations into `D`, when `D` is monoidal.
-/
@[simps]
def tensorHom : tensorObj F F' ⟶ tensorObj G G' where
  app X := α.app X ⊗ₘ β.app X
  naturality X Y f := by
    dsimp; rw [tensorHom_comp_tensorHom, α.naturality, β.naturality, ← tensorHom_comp_tensorHom]

/-- (An auxiliary definition for `functorCategoryMonoidal`.) -/
@[simps]
def whiskerLeft (F) (β : F' ⟶ G') : tensorObj F F' ⟶ tensorObj F G' where
  app X := F.obj X ◁ β.app X
  naturality X Y f := by
    simp only [← id_tensorHom]
    apply (tensorHom (𝟙 F) β).naturality

/-- (An auxiliary definition for `functorCategoryMonoidal`.) -/
@[simps]
def whiskerRight (F') : tensorObj F F' ⟶ tensorObj G F' where
  app X := α.app X ▷ F'.obj X
  naturality X Y f := by
    simp only [← tensorHom_id]
    apply (tensorHom α (𝟙 F')).naturality

end FunctorCategory

open CategoryTheory.Monoidal.FunctorCategory

/-- When `C` is any category, and `D` is a monoidal category,
the functor category `C ⥤ D` has a natural pointwise monoidal structure,
where `(F ⊗ G).obj X = F.obj X ⊗ G.obj X`.
-/
instance functorCategoryMonoidalStruct : MonoidalCategoryStruct (C ⥤ D) where
  tensorObj F G := tensorObj F G
  tensorHom α β := tensorHom α β
  whiskerLeft F _ _ α := FunctorCategory.whiskerLeft F α
  whiskerRight α F := FunctorCategory.whiskerRight α F
  tensorUnit := (CategoryTheory.Functor.const C).obj (𝟙_ D)
  leftUnitor F := NatIso.ofComponents fun X => λ_ (F.obj X)
  rightUnitor F := NatIso.ofComponents fun X => ρ_ (F.obj X)
  associator F G H := NatIso.ofComponents fun X => α_ (F.obj X) (G.obj X) (H.obj X)

@[simp]
theorem tensorUnit_obj {X} : (𝟙_ (C ⥤ D)).obj X = 𝟙_ D :=
  rfl

@[simp]
theorem tensorUnit_map {X Y} {f : X ⟶ Y} : (𝟙_ (C ⥤ D)).map f = 𝟙 (𝟙_ D) :=
  rfl

@[simp]
theorem tensorObj_obj {F G : C ⥤ D} {X} : (F ⊗ G).obj X = F.obj X ⊗ G.obj X :=
  rfl

@[simp]
theorem tensorObj_map {F G : C ⥤ D} {X Y} {f : X ⟶ Y} : (F ⊗ G).map f = F.map f ⊗ₘ G.map f :=
  rfl

@[simp]
theorem tensorHom_app {F G F' G' : C ⥤ D} {α : F ⟶ G} {β : F' ⟶ G'} {X} :
    (α ⊗ₘ β).app X = α.app X ⊗ₘ β.app X :=
  rfl

@[simp]
theorem whiskerLeft_app {F F' G' : C ⥤ D} {β : F' ⟶ G'} {X} :
    (F ◁ β).app X = F.obj X ◁ β.app X :=
  rfl

@[simp]
theorem whiskerRight_app {F G F' : C ⥤ D} {α : F ⟶ G} {X} :
    (α ▷ F').app X = α.app X ▷ F'.obj X :=
  rfl

@[simp]
theorem leftUnitor_hom_app {F : C ⥤ D} {X} :
    ((λ_ F).hom : 𝟙_ _ ⊗ F ⟶ F).app X = (λ_ (F.obj X)).hom :=
  rfl

@[simp]
theorem leftUnitor_inv_app {F : C ⥤ D} {X} :
    ((λ_ F).inv : F ⟶ 𝟙_ _ ⊗ F).app X = (λ_ (F.obj X)).inv :=
  rfl

@[simp]
theorem rightUnitor_hom_app {F : C ⥤ D} {X} :
    ((ρ_ F).hom : F ⊗ 𝟙_ _ ⟶ F).app X = (ρ_ (F.obj X)).hom :=
  rfl

@[simp]
theorem rightUnitor_inv_app {F : C ⥤ D} {X} :
    ((ρ_ F).inv : F ⟶ F ⊗ 𝟙_ _).app X = (ρ_ (F.obj X)).inv :=
  rfl

@[simp]
theorem associator_hom_app {F G H : C ⥤ D} {X} :
    ((α_ F G H).hom : (F ⊗ G) ⊗ H ⟶ F ⊗ G ⊗ H).app X = (α_ (F.obj X) (G.obj X) (H.obj X)).hom :=
  rfl

@[simp]
theorem associator_inv_app {F G H : C ⥤ D} {X} :
    ((α_ F G H).inv : F ⊗ G ⊗ H ⟶ (F ⊗ G) ⊗ H).app X = (α_ (F.obj X) (G.obj X) (H.obj X)).inv :=
  rfl

/-- When `C` is any category, and `D` is a monoidal category,
the functor category `C ⥤ D` has a natural pointwise monoidal structure,
where `(F ⊗ G).obj X = F.obj X ⊗ G.obj X`.
-/
instance functorCategoryMonoidal : MonoidalCategory (C ⥤ D) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  pentagon F G H K := by ext X; dsimp; rw [pentagon]

section BraidedCategory

open CategoryTheory.BraidedCategory

variable [BraidedCategory.{v₂} D]

/-- When `C` is any category, and `D` is a braided monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also braided.
-/
instance functorCategoryBraided : BraidedCategory (C ⥤ D) where
  braiding F G := NatIso.ofComponents fun _ => β_ _ _
  hexagon_forward F G H := by ext X; apply hexagon_forward
  hexagon_reverse F G H := by ext X; apply hexagon_reverse

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
instance functorCategorySymmetric : SymmetricCategory (C ⥤ D) where
  symmetry F G := by ext X; apply symmetry

end SymmetricCategory

end Monoidal

@[simps]
instance Functor.LaxMonoidal.whiskeringRight
    {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory D]
    [MonoidalCategory E] (L : D ⥤ E) [L.LaxMonoidal] :
    ((Functor.whiskeringRight C D E).obj L).LaxMonoidal where
  ε := { app X := Functor.LaxMonoidal.ε L }
  μ F G := { app X := Functor.LaxMonoidal.μ L (F.obj X) (G.obj X) }

@[simps]
instance Functor.OplaxMonoidal.whiskeringRight
    {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory D]
    [MonoidalCategory E] (L : D ⥤ E) [L.OplaxMonoidal] :
    ((Functor.whiskeringRight C D E).obj L).OplaxMonoidal where
  η := { app X := Functor.OplaxMonoidal.η L }
  δ F G := { app X := Functor.OplaxMonoidal.δ L (F.obj X) (G.obj X) }
  oplax_left_unitality := by aesop
  oplax_right_unitality := by aesop

instance {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory D]
    [MonoidalCategory E] (L : D ⥤ E) [L.Monoidal] :
    ((Functor.whiskeringRight C D E).obj L).Monoidal where

@[deprecated (since := "2025-11-06")] alias instLaxMonoidalFunctorObjWhiskeringRight :=
  Functor.LaxMonoidal.whiskeringRight
@[deprecated (since := "2025-11-06")] alias instOplaxMonoidalFunctorObjWhiskeringRight :=
  Functor.OplaxMonoidal.whiskeringRight
@[deprecated (since := "2025-11-06")] alias ε_app := Functor.LaxMonoidal.whiskeringRight_ε_app
@[deprecated (since := "2025-11-06")] alias μ_app := Functor.LaxMonoidal.whiskeringRight_μ_app
@[deprecated (since := "2025-11-06")] alias η_app := Functor.OplaxMonoidal.whiskeringRight_η_app
@[deprecated (since := "2025-11-06")] alias δ_app := Functor.OplaxMonoidal.whiskeringRight_δ_app

@[simps!]
instance Functor.Monoidal.whiskeringLeft
    (E : Type*) [Category* E] [MonoidalCategory E] (F : C ⥤ D) :
    ((whiskeringLeft _ _ E).obj F).Monoidal :=
  CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

instance (E : Type*) [Category* E] [MonoidalCategory E] (e : C ≌ D) :
    (e.congrLeft (E := E)).functor.Monoidal :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ E).obj e.inverse).Monoidal

instance (E : Type*) [Category* E] [MonoidalCategory E] (e : C ≌ D) :
    (e.congrLeft (E := E)).inverse.Monoidal :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ E).obj e.functor).Monoidal

set_option backward.isDefEq.respectTransparency false in
instance (E : Type*) [Category* E] [MonoidalCategory E] (e : C ≌ D) :
    (e.congrLeft (E := E)).IsMonoidal where
  leftAdjoint_μ X Y := by
    ext
    simp [← Functor.map_comp]

end CategoryTheory
