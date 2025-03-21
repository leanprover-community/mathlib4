/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Equivalence

/-!
# The category of equivalences of categories

In this file, we put a `Category` structure on equivalences of categories. By definition,
a morphism between two equivalences is a natural transformation between their respective functors.

This file merely contains the definition of the category structure and provides basic properties and
constructions, such as `functorFunctor : (C ≌ D) ⥤ (C ⥤ D)`, and `congrRightFunctor`.

to keep transitive imports as minimal as possible, we do not provide in this file the
"inverseFunctor" functor, as its most natural construction makes use of the calculus of mates from
`CategoryTheory.Adjuction.Mates`.
-/

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Equivalence

/-- A morphism between equivalences of categories is a natural transformation between their
functors. -/
def Hom : (C ≌ D) → (C ≌ D) → Type (max u₁ v₂) :=
  fun f g ↦ (f.functor ⟶ g.functor)

instance : Category.{max u₁ v₂} (C ≌ D) where
  Hom e f := Hom e f
  id e := 𝟙 e.functor
  comp {a b c} f g := ((f :) ≫ (g :) : a.functor ⟶ _)

/-- Promote a natural transformation `e.functor ⟶ f.functor` to a morphism in `C ≌ D`. -/
def mkHom {e f : C ≌ D} (η : e.functor ⟶ f.functor) : e ⟶ f := η

/-- Recover a natural transformation between `e.functor` and `f.functor` from the data of
a morphism `e ⟶ f`. -/
def asNatTrans {e f : C ≌ D} (η : e ⟶ f) : e.functor ⟶ f.functor := η

@[simp]
lemma mkHom_asNatTrans {e f : C ≌ D} (η : e.functor ⟶ f.functor) :
    mkHom (asNatTrans η) = η :=
  rfl

@[simp]
lemma asNatTrans_mkHom {e f : C ≌ D} (η : e ⟶ f) :
    asNatTrans (mkHom η) = η :=
  rfl

@[simp]
lemma id_asNatTrans {e : C ≌ D} : asNatTrans (𝟙 e) = 𝟙 _ := rfl

@[simp]
lemma id_asNatTrans' {e : C ≌ D} : asNatTrans (𝟙 e.functor) = 𝟙 _ := rfl

@[simp]
lemma comp_asNatTrans {e f g: C ≌ D} (α : e ⟶ f) (β : f ⟶ g) :
    asNatTrans (α ≫ β) = asNatTrans α ≫ asNatTrans β :=
  rfl

@[simp]
lemma mkHom_id_functor {e : C ≌ D} : mkHom (𝟙 e.functor) = 𝟙 e := rfl

@[simp]
lemma mkHom_id_inverse {e : C ≌ D} : mkHom (𝟙 e.inverse) = 𝟙 e.symm := rfl

@[simp]
lemma mkHom_comp {e f g: C ≌ D} (α : e.functor ⟶ f.functor) (β : f.functor ⟶ g.functor) :
    mkHom (α ≫ β) = (mkHom α) ≫ (mkHom β) :=
  rfl

@[ext]
lemma homExt {e f : C ≌ D} {α β : e ⟶ f} (h : asNatTrans α = asNatTrans β) : α = β := by
  apply NatTrans.ext
  exact NatTrans.ext_iff.mp h

/-- Construct an isomorphism in `C ≌ D` from a natural isomorphism between the functors
of the equivalences. -/
@[simps]
def mkIso {e f : C ≌ D} (η : e.functor ≅ f.functor) : e ≅ f where
  hom := mkHom η.hom
  inv := mkHom η.inv

/-- Obtain a natural isomorphism between the functors of two equivalences from
  an isomorphism in `C ≌ D`. -/
@[simps]
def asNatIso {e f : C ≌ D} (η : e ≅ f) : e.functor ≅ f.functor where
  hom := asNatTrans η.hom
  inv := asNatTrans η.inv
  hom_inv_id := by simp [← comp_asNatTrans]
  inv_hom_id := by simp [← comp_asNatTrans]

variable (C D)

/-- The `functor` functor that sends an equivalence of categories to its functor. -/
@[simps!]
def functorFunctor : (C ≌ D) ⥤ (C ⥤ D) where
  obj f := f.functor
  map α := asNatTrans α

/-- Promoting `Equivalence.congrRight` to a functor. -/
@[simps]
def congrRightFunctor (E : Type*) [Category E] : (C ≌ D) ⥤ ((E ⥤ C) ≌ (E ⥤ D)) where
  obj e := e.congrRight
  map {e f} α := mkHom <| (whiskeringRight _ _ _).map <| asNatTrans α

end Equivalence

end CategoryTheory
