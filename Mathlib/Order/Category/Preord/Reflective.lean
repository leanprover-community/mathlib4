/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Thin
public import Mathlib.Order.Category.Preord

/-!
# Preorders as a reflective subcategory of categories

The functor `catToPreord` equips the objects of a small category with the preorder
`X ≤ Y ↔ Nonempty (X ⟶ Y)`. It is left adjoint to `preordToCat`, exhibiting `Preord`
as a reflective subcategory of `Cat`.
-/

@[expose] public section

universe v u

open CategoryTheory

/-- A wrapper for turning a category `C` into its associated preorder of objects. -/
structure Preorder.OfCat (C : Type u) where
  obj : C

instance (C : Type u) [Category.{v} C] : Preorder (Preorder.OfCat C) where
  le X Y := Nonempty (X.obj ⟶ Y.obj)
  le_refl X := ⟨𝟙 X.obj⟩
  le_trans _ _ _ := Nonempty.map2 (· ≫ ·)

/-- The preorder on the objects of a category given by the existence of a morphism. -/
@[implicit_reducible]
def Preord.ofCat (C : Type u) [Category.{v} C] : Preord.{u} := .of (Preorder.OfCat C)

/-- The functor sending a small category to its preorder of objects. -/
@[implicit_reducible]
def catToPreord : Cat.{u, u} ⥤ Preord.{u} where
  obj C := .ofCat C
  map F := Preord.ofHom
    ⟨fun X ↦ ⟨F.toFunctor.obj X.obj⟩, fun _ _ h ↦ h.map F.toFunctor.map⟩

/-- `catToPreord` is left adjoint to `preordToCat`. -/
def catToPreordAdjunction : catToPreord.{u} ⊣ preordToCat :=
  .mkOfHomEquiv
    { homEquiv C P :=
        { toFun f :=
            Functor.toCatHom
              { obj X := f.hom ⟨X⟩
                map g := homOfLE (f.hom.monotone ⟨g⟩) }
          invFun F := Preord.ofHom ⟨fun X ↦ F.toFunctor.obj X.obj,
            fun _ _ h ↦ h.elim fun f ↦ leOfHom (F.toFunctor.map f)⟩ } }

instance : Reflective preordToCat.{u} where
  L := catToPreord
  adj := catToPreordAdjunction

/-- A thin category is isomorphic to the category associated to its preorder of objects. -/
noncomputable def Preord.ofCatIso (C : Type u) [SmallCategory C] [Quiver.IsThin C] :
    preordToCat.obj (ofCat C) ≅ .of C where
  hom := Functor.toCatHom { obj := Preorder.OfCat.obj, map f := (leOfHom f).some }
  inv := Functor.toCatHom { obj := .mk, map f := homOfLE ⟨f⟩ }
  inv_hom_id := Cat.ext <| Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ Subsingleton.elim _ _
