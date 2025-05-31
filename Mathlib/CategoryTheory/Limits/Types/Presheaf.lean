/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Natural transformations of presheaves as limits

Let `C` be a category and `F, G : Cᵒᵖ ⥤ Type w` two presheaves over `C`.
We give the natural isomorphism between natural transformations `F ⟶ G` and objects of the limit of
sections of `G` over sections of `F`.
-/

universe u v w

open CategoryTheory

variable {C : Type u} [Category.{v,u} C] (F G : Cᵒᵖ ⥤ Type v) -- Type w ???

def Over.IsRepresentable : ObjectProperty (Over F) :=
  fun X : Over F => Functor.IsRepresentable X.left

def sectionsOverCategory := (Over.IsRepresentable F).FullSubcategory

instance useless : Category (sectionsOverCategory F) :=
  ObjectProperty.FullSubcategory.category (Over.IsRepresentable F)

noncomputable def sectionsOverFunctor : (sectionsOverCategory F)ᵒᵖ ⥤ Type v where
  obj s := G.obj (Opposite.op (s.unop.obj.left.reprX (hF := s.unop.property)))
  map {s s'} f :=
    have : Functor.IsRepresentable s'.unop.obj.left := s'.unop.property
    have : Functor.IsRepresentable s.unop.obj.left := s.unop.property
    G.map ((Yoneda.fullyFaithful.preimage
      (s'.unop.obj.left.reprW.hom ≫ f.unop.left ≫ s.unop.obj.left.reprW.inv)).op)
  map_id s := by
    have : CommaMorphism.left (𝟙 s.unop) = 𝟙 (s.unop.obj.left) := rfl
    simp [this]
  map_comp {s s' s''} f g := by
    rw [← G.map_comp, ← op_comp, ← Yoneda.fullyFaithful.preimage_comp]
    have : (g.unop ≫ f.unop).left = g.unop.left ≫ f.unop.left := rfl
    simp [this]

/- def morphismsEquivSections :
    (F ⟶ G) ≃ Limits.limit (sectionsOverFunctor F G) -/
