/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Chosen.End

/-!
# Coends in Types

This file constructs explicit coends in `Type` as quotients and provides a
`ChosenCoends` instance using this construction.

TODO: dualize for ends (done in #38383)
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite TypeCat ConcreteCategory

namespace Limits.Types

variable {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ Type max w u)

/-- The relation on the sigma type `(W : J) × (F.obj (op W)).obj W` used to construct explicit
coends in `Type`. Two terms `⟨j, x⟩` and `⟨j', x'⟩` are related if and only if there is a
morphism `f : j ⟶ j'` in `J` and an element `y : (F.obj (op j')).obj j` such that
`(F.map f.op).app j y = x` and `(F.obj _).map f y = x'`, see `coendRel_iff` below. -/
inductive coendRel : (j : J) × (F.obj (op j)).obj j → (j : J) × (F.obj (op j)).obj j → Prop where
  | mk {j j' : J} (f : j ⟶ j') (x : (F.obj (op j')).obj j) :
    coendRel ⟨j, TypeCat.Hom.hom ((F.map f.op).app _) x⟩
      ⟨j', TypeCat.Hom.hom ((F.obj _).map f) x⟩

lemma coendRel_iff (j j' : J) (x : (F.obj (op j)).obj j) (x' : (F.obj (op j')).obj j') :
    coendRel F ⟨j, x⟩ ⟨j', x'⟩ ↔
      ∃ (f : j ⟶ j') (y : (F.obj (op j')).obj j),
        (F.map f.op).app _ y = x ∧ (F.obj _).map f y = x' := by
  constructor
  · rintro ⟨f, x⟩
    exact ⟨f, x, by simp⟩
  · rintro ⟨f, y, rfl, rfl⟩
    exact coendRel.mk f y

/-- The coend of a bifunctor valued in `Type`, defined as a quotient. -/
abbrev coend : Type max w u := Quot (coendRel F)

/-- Given `F : Jᵒᵖ ⥤ J ⥤ Type*`, this is the inclusion `(F.obj (op j)).obj j ⟶ coend F`
for any `j : J`, which sends `x` to `Quot.mk _ ⟨j, x⟩` -/
def coend.ι (j : J) : (F.obj (op j)).obj j ⟶ coend F := ↾fun x ↦ Quot.mk _ ⟨j, x⟩

variable {F}

lemma coend.condition {j j' : J} (f : j ⟶ j') :
    (F.map f.op).app _ ≫ coend.ι F j = (F.obj _).map f ≫ coend.ι F j' := by
  ext
  apply Quot.sound
  apply coendRel.mk

variable (F)

/-- The cowedge corresponding to the explicit coend in `Type` -/
def cowedge : Cowedge F := Cowedge.mk (coend F) (coend.ι F) (by intros; apply coend.condition)

/-- The cowedge corresponding to the explicit coend in `Type` is colimiting. -/
def cowedgeIsColimit : IsColimit (cowedge F) where
  desc s := TypeCat.ofHom <| Quot.lift (fun x ↦ Multicofork.π s x.fst x.snd) fun _ _ h ↦ by
    cases h with | mk f x => exact ConcreteCategory.congr_hom (Cowedge.condition s f) _
  fac s := by rintro (_ | _) <;> cat_disch
  uniq s m h := by ext ⟨j⟩; exact ConcreteCategory.congr_hom (h (.right j.fst)) j.snd

end Types

/-- A `ChosenCoends` instance on `Type` given by the explicit quotient construction above. -/
instance : ChosenCoends.{v, u} (Type max w u) where
  cowedge := Types.cowedge
  isCoend := Types.cowedgeIsColimit

variable {J : Type u} [Category.{v} J] {F : Jᵒᵖ ⥤ J ⥤ Type max w u}

lemma Types.chosenCoend_def : chosenCoend F = Quot (coendRel F) := rfl

attribute [local simp] Types.chosenCoend_def

lemma chosenCoend.ι_apply (j : J) (x : (F.obj (op j)).obj j) :
    dsimp% chosenCoend.ι F j x = Quot.mk _ ⟨j, x⟩ :=
  rfl

lemma chosenCoend.desc_apply {X : Type max w u} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j)
    (x : chosenCoend F) : dsimp% chosenCoend.desc f hf x =
      Quot.lift (fun j ↦ f j.fst j.snd) (fun _ _ h ↦ by
        cases h with | mk f x => exact ConcreteCategory.congr_hom (hf f) _) x :=
  rfl

lemma chosenCoend.map_apply {G : Jᵒᵖ ⥤ J ⥤ Type max w u} (f : F ⟶ G) (x : chosenCoend F) :
    dsimp% chosenCoend.map f x =
      Quot.lift (fun ⟨j, y⟩ ↦ Quot.mk _ ⟨j, (f.app _).app _ y⟩) (fun _ _ ↦ by
        rintro ⟨g, y⟩
        apply Quot.sound
        rw [Types.coendRel_iff]
        refine ⟨g, (f.app _).app _ y, ?_, ?_⟩
        · simp only [← NatTrans.comp_app_apply, f.naturality]
        · simp [← NatTrans.naturality_apply]) x :=
  rfl

end CategoryTheory.Limits
