/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Category.Preord
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Thin

/-!
# Preorders as a reflective subcategory of categories

The functor `catToPreord` equips the objects of a small category with the preorder
`X ≤ Y ↔ Nonempty (X ⟶ Y)`. It is left adjoint to `preordToCat`, exhibiting `Preord`
as a reflective subcategory of `Cat`.
-/

@[expose] public section

universe v u

open CategoryTheory

/-- The preorder on the objects of a category given by the existence of a morphism. -/
@[implicit_reducible]
def Preord.ofCat (C : Type u) [Category.{v} C] : Preord.{u} where
  carrier := C
  str :=
    { le X Y := Nonempty (X ⟶ Y)
      le_refl X := ⟨𝟙 X⟩
      le_trans _ _ _ := Nonempty.map2 (· ≫ ·) }

/-- The functor sending a small category to its preorder of objects. -/
def catToPreord : Cat.{u, u} ⥤ Preord.{u} where
  obj C := Preord.ofCat C
  map {C D} F := Preord.ofHom (X := Preord.ofCat C) (Y := Preord.ofCat D)
    ⟨F.toFunctor.obj, fun _ _ h ↦ h.map F.toFunctor.map⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `catToPreord` is left adjoint to `preordToCat`. -/
def catToPreordAdjunction : catToPreord.{u} ⊣ preordToCat :=
  .mkOfHomEquiv
    { homEquiv C P :=
        { toFun f :=
            ({ obj := f.hom
               map g := homOfLE (f.hom.monotone ⟨g⟩)
               map_id _ := rfl
               map_comp _ _ := rfl } : C ⥤ P).toCatHom
          invFun F := Preord.ofHom (X := catToPreord.obj C) (Y := P)
            ⟨F.toFunctor.obj, fun _ _ h ↦ h.elim fun f ↦ leOfHom (F.toFunctor.map f)⟩
          left_inv _ := rfl
          right_inv _ := rfl }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

instance : Reflective preordToCat.{u} where
  L := catToPreord
  adj := catToPreordAdjunction

/-- A thin category is isomorphic to the category associated to its preorder of objects. -/
noncomputable def Preord.ofCatIso (C : Type u) [SmallCategory C] [Quiver.IsThin C] :
    preordToCat.obj (ofCat C) ≅ Cat.of C where
  hom :=
    ({ obj := id
       map f := (leOfHom f).some
       map_id _ := Subsingleton.elim _ _
       map_comp _ _ := Subsingleton.elim _ _ } :
      ofCat C ⥤ C).toCatHom
  inv := ({ obj := id
            map f := homOfLE ⟨f⟩
            map_id _ := rfl
            map_comp _ _ := rfl } : C ⥤ ofCat C).toCatHom
  hom_inv_id := rfl
  inv_hom_id := Cat.ext <| Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ Subsingleton.elim _ _
