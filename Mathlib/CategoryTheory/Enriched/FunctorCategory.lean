/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.Functor.FunctorHom
import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Functor categories are enriched over functors to type

Shows that the functor category `C ⥤ D` is enriched over `C ⥤ Type max v' v u`, for `C` a
category in `Type u` with morphisms in `Type v`, and `D` a category with morphisms in `Type v'`.
-/


universe w v' v u u'

open CategoryTheory MonoidalCategory Functor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (F G : C ⥤ D)

namespace CategoryTheory.Enriched.Functor

@[simp]
lemma natTransEquiv_app_app_apply (F G : C ⥤ D) (f : F ⟶ G)
    {X : C} {a : (𝟙_ (C ⥤ Type (max v' v u))).obj X} (Y : C) {φ : X ⟶ Y} :
    ((natTransEquiv f).app X a).app Y φ = f.app Y := rfl

@[simp]
lemma natTransEquiv_whiskerRight_functorHom_app (K L : C ⥤ D) (X : C) (f : K ⟶ K)
    (x : 𝟙_ _ ⊗ (K.functorHom L).obj X) :
    ((natTransEquiv f ▷ K.functorHom L).app X x) =
    (HomObj.ofNatTrans f, x.2) := rfl

@[simp]
lemma functorHom_whiskerLeft_natTransEquiv_app (K L : C ⥤ D) (X : C) (f : L ⟶ L)
    (x : (K.functorHom L).obj X ⊗ 𝟙_ _) :
    ((K.functorHom L ◁ natTransEquiv f).app X x) =
    (x.1, HomObj.ofNatTrans f) := rfl

@[simp]
lemma whiskerLeft_app_apply (K L M N : C ⥤ D)
    (g : L.functorHom M ⊗ M.functorHom N ⟶ L.functorHom N)
    {X : C} (a : (K.functorHom L ⊗ L.functorHom M ⊗ M.functorHom N).obj X) :
    (K.functorHom L ◁ g).app X a = ⟨a.1, g.app X a.2⟩ := rfl

@[simp]
lemma whiskerRight_app_apply (K L M N : C ⥤ D)
    (f : K.functorHom L ⊗ L.functorHom M ⟶ K.functorHom M)
    {X : C} (a : ((K.functorHom L ⊗ L.functorHom M) ⊗ M.functorHom N).obj X) :
    (f ▷  M.functorHom N).app X a = ⟨f.app X a.1, a.2⟩ := rfl

@[simp]
lemma associator_inv_apply (K L M N : C ⥤ D) {X : C}
    (x : ((K.functorHom L) ⊗ (L.functorHom M) ⊗ (M.functorHom N)).obj X) :
    (α_ ((K.functorHom L).obj X) ((L.functorHom M).obj X) ((M.functorHom N).obj X)).inv x =
    ⟨⟨x.1, x.2.1⟩, x.2.2⟩ := rfl

@[simp]
lemma associator_hom_apply (K L M N : C ⥤ D) {X : C}
    (x : ( ((K.functorHom L) ⊗ (L.functorHom M)) ⊗ (M.functorHom N)).obj X) :
    (α_ ((K.functorHom L).obj X) ((L.functorHom M).obj X) ((M.functorHom N).obj X)).hom x =
    ⟨x.1.1, x.1.2, x.2⟩ := rfl

noncomputable instance : EnrichedCategory (C ⥤ Type max v' v u) (C ⥤ D) where
  Hom := functorHom
  id F := natTransEquiv (𝟙 F)
  comp F G H := { app := fun X ⟨f, g⟩ => f.comp g }

end CategoryTheory.Enriched.Functor
