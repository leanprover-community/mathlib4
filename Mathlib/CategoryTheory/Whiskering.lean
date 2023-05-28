/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
Ported by: Joël Riou

! This file was ported from Lean 3 source module category_theory.whiskering
! leanprover-community/mathlib commit d012cd09a9b256d870751284dd6a29882b0be105
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Whiskering

Given a functor `F  : C ⥤ D` and functors `G H : D ⥤ E` and a natural transformation `α : G ⟶ H`,
we can construct a new natural transformation `F ⋙ G ⟶ F ⋙ H`,
called `whiskerLeft F α`. This is the same as the horizontal composition of `𝟙 F` with `α`.

This operation is functorial in `F`, and we package this as `whiskeringLeft`. Here
`(whiskeringLeft.obj F).obj G` is `F ⋙ G`, and
`(whiskeringLeft.obj F).map α` is `whiskerLeft F α`.
(That is, we might have alternatively named this as the "left composition functor".)

We also provide analogues for composition on the right, and for these operations on isomorphisms.

At the end of the file, we provide the left and right unitors, and the associator,
for functor composition.
(In fact functor composition is definitionally associative, but very often relying on this causes
extremely slow elaboration, so it is better to insert it explicitly.)
We also show these natural isomorphisms satisfy the triangle and pentagon identities.
-/


namespace CategoryTheory

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

/-- If `α : G ⟶ H` then
`whiskerLeft F α : (F ⋙ G) ⟶ (F ⋙ H)` has components `α.app (F.obj X)`.
-/
@[simps]
def whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) :
    F ⋙ G ⟶ F ⋙ H where
  app X := α.app (F.obj X)
  naturality X Y f := by rw [Functor.comp_map, Functor.comp_map, α.naturality]
#align category_theory.whisker_left CategoryTheory.whiskerLeft
#align category_theory.whisker_left_app CategoryTheory.whiskerLeft_app

/-- If `α : G ⟶ H` then
`whisker_right α F : (G ⋙ F) ⟶ (G ⋙ F)` has components `F.map (α.app X)`.
-/
@[simps]
def whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) :
    G ⋙ F ⟶ H ⋙ F where
  app X := F.map (α.app X)
  naturality X Y f := by
    rw [Functor.comp_map, Functor.comp_map, ← F.map_comp, ← F.map_comp, α.naturality]
#align category_theory.whisker_right CategoryTheory.whiskerRight
#align category_theory.whisker_right_app CategoryTheory.whiskerRight_app

variable (C D E)

/-- Left-composition gives a functor `(C ⥤ D) ⥤ ((D ⥤ E) ⥤ (C ⥤ E))`.

`(whiskeringLeft.obj F).obj G` is `F ⋙ G`, and
`(whiskeringLeft.obj F).map α` is `whiskerLeft F α`.
-/
@[simps]
def whiskeringLeft : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where
  obj F :=
    { obj := fun G => F ⋙ G
      map := fun α => whiskerLeft F α }
  map τ :=
    { app := fun H =>
        { app := fun c => H.map (τ.app c)
          naturality := fun X Y f => by dsimp; rw [← H.map_comp, ← H.map_comp, ← τ.naturality] }
      naturality := fun X Y f => by ext; dsimp; rw [f.naturality] }
#align category_theory.whiskering_left CategoryTheory.whiskeringLeft
#align category_theory.whiskering_left_obj_map CategoryTheory.whiskeringLeft_obj_map
#align category_theory.whiskering_left_obj_obj CategoryTheory.whiskeringLeft_obj_obj
#align category_theory.whiskering_left_map_app_app CategoryTheory.whiskeringLeft_map_app_app

/-- Right-composition gives a functor `(D ⥤ E) ⥤ ((C ⥤ D) ⥤ (C ⥤ E))`.

`(whiskeringRight.obj H).obj F` is `F ⋙ H`, and
`(whiskeringRight.obj H).map α` is `whiskerRight α H`.
-/
@[simps]
def whiskeringRight : (D ⥤ E) ⥤ (C ⥤ D) ⥤ C ⥤ E where
  obj H :=
    { obj := fun F => F ⋙ H
      map := fun α => whiskerRight α H }
  map τ :=
    { app := fun F =>
        { app := fun c => τ.app (F.obj c)
          naturality := fun X Y f => by dsimp; rw [τ.naturality] }
      naturality := fun X Y f => by ext; dsimp; rw [← NatTrans.naturality] }
#align category_theory.whiskering_right CategoryTheory.whiskeringRight
#align category_theory.whiskering_right_map_app_app CategoryTheory.whiskeringRight_map_app_app
#align category_theory.whiskering_right_obj_obj CategoryTheory.whiskeringRight_obj_obj
#align category_theory.whiskering_right_obj_map CategoryTheory.whiskeringRight_obj_map

variable {C} {D} {E}

instance faithful_whiskeringRight_obj {F : D ⥤ E} [Faithful F] :
    Faithful ((whiskeringRight C D E).obj F) where
  map_injective hαβ := NatTrans.ext _ _
    (funext fun X => (F.map_injective <| congr_fun (congr_arg NatTrans.app hαβ) X))
#align category_theory.faithful_whiskering_right_obj CategoryTheory.faithful_whiskeringRight_obj

noncomputable
instance full_whiskeringRight_obj
    (F : D ⥤ E) [Full F] [Faithful F] : Full ((whiskeringRight C D E).obj F) :=
    ⟨(@NatTrans.equivOfCompFullyFaithful C _ D _ E _ _ _ F _ _).invFun,
     by intros X Y f
        convert (@NatTrans.equivOfCompFullyFaithful C _ D _ E _ _ _ F _ _).right_inv f
        ext; exact Eq.symm (Category.id_comp _)⟩

@[simp]
theorem whiskerLeft_id (F : C ⥤ D) {G : D ⥤ E} :
    whiskerLeft F (NatTrans.id G) = NatTrans.id (F.comp G) :=
  rfl
#align category_theory.whisker_left_id CategoryTheory.whiskerLeft_id

@[simp]
theorem whiskerLeft_id' (F : C ⥤ D) {G : D ⥤ E} : whiskerLeft F (𝟙 G) = 𝟙 (F.comp G) :=
  rfl
#align category_theory.whisker_left_id' CategoryTheory.whiskerLeft_id'

@[simp]
theorem whiskerRight_id {G : C ⥤ D} (F : D ⥤ E) :
    whiskerRight (NatTrans.id G) F = NatTrans.id (G.comp F) :=
  ((whiskeringRight C D E).obj F).map_id _
#align category_theory.whisker_right_id CategoryTheory.whiskerRight_id

@[simp]
theorem whiskerRight_id' {G : C ⥤ D} (F : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F) :=
  ((whiskeringRight C D E).obj F).map_id _
#align category_theory.whisker_right_id' CategoryTheory.whiskerRight_id'

@[simp]
theorem whiskerLeft_comp (F : C ⥤ D) {G H K : D ⥤ E} (α : G ⟶ H) (β : H ⟶ K) :
    whiskerLeft F (α ≫ β) = whiskerLeft F α ≫ whiskerLeft F β :=
  rfl
#align category_theory.whisker_left_comp CategoryTheory.whiskerLeft_comp

@[simp]
theorem whiskerRight_comp {G H K : C ⥤ D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) :
    whiskerRight (α ≫ β) F = whiskerRight α F ≫ whiskerRight β F :=
  ((whiskeringRight C D E).obj F).map_comp α β
#align category_theory.whisker_right_comp CategoryTheory.whiskerRight_comp

/-- If `α : G ≅ H` is a natural isomorphism then
`iso_whisker_left F α : (F ⋙ G) ≅ (F ⋙ H)` has components `α.app (F.obj X)`.
-/
def isoWhiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) : F ⋙ G ≅ F ⋙ H :=
  ((whiskeringLeft C D E).obj F).mapIso α
#align category_theory.iso_whisker_left CategoryTheory.isoWhiskerLeft

@[simp]
theorem isoWhiskerLeft_hom (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
    (isoWhiskerLeft F α).hom = whiskerLeft F α.hom :=
  rfl
#align category_theory.iso_whisker_left_hom CategoryTheory.isoWhiskerLeft_hom

@[simp]
theorem isoWhiskerLeft_inv (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
    (isoWhiskerLeft F α).inv = whiskerLeft F α.inv :=
  rfl
#align category_theory.iso_whisker_left_inv CategoryTheory.isoWhiskerLeft_inv

/-- If `α : G ≅ H` then
`iso_whisker_right α F : (G ⋙ F) ≅ (H ⋙ F)` has components `F.map_iso (α.app X)`.
-/
def isoWhiskerRight {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : G ⋙ F ≅ H ⋙ F :=
  ((whiskeringRight C D E).obj F).mapIso α
#align category_theory.iso_whisker_right CategoryTheory.isoWhiskerRight

@[simp]
theorem isoWhiskerRight_hom {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    (isoWhiskerRight α F).hom = whiskerRight α.hom F :=
  rfl
#align category_theory.iso_whisker_right_hom CategoryTheory.isoWhiskerRight_hom

@[simp]
theorem isoWhiskerRight_inv {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    (isoWhiskerRight α F).inv = whiskerRight α.inv F :=
  rfl
#align category_theory.iso_whisker_right_inv CategoryTheory.isoWhiskerRight_inv

instance isIso_whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [IsIso α] :
    IsIso (whiskerLeft F α) :=
  IsIso.of_iso (isoWhiskerLeft F (asIso α))
#align category_theory.is_iso_whisker_left CategoryTheory.isIso_whiskerLeft

instance isIso_whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [IsIso α] :
    IsIso (whiskerRight α F) :=
  IsIso.of_iso (isoWhiskerRight (asIso α) F)
#align category_theory.is_iso_whisker_right CategoryTheory.isIso_whiskerRight

variable {B : Type u₄} [Category.{v₄} B]

-- Porting note: it was `attribute [local elab_without_expected_type]`,
-- but now `elab_without_expected-type` must be global
attribute [elab_without_expected_type] whiskerLeft whiskerRight

@[simp]
theorem whiskerLeft_twice (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) :
    whiskerLeft F (whiskerLeft G α) = whiskerLeft (F ⋙ G) α :=
  rfl
#align category_theory.whisker_left_twice CategoryTheory.whiskerLeft_twice

@[simp]
theorem whiskerRight_twice {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) :
    whiskerRight (whiskerRight α F) G = whiskerRight α (F ⋙ G) :=
  rfl
#align category_theory.whisker_right_twice CategoryTheory.whiskerRight_twice

theorem whiskerRight_left (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E) :
    whiskerRight (whiskerLeft F α) K = whiskerLeft F (whiskerRight α K) :=
  rfl
#align category_theory.whisker_right_left CategoryTheory.whiskerRight_left

end

namespace Functor

universe u₅ v₅

variable {A : Type u₁} [Category.{v₁} A]

variable {B : Type u₂} [Category.{v₂} B]

/-- The left unitor, a natural isomorphism `((𝟭 _) ⋙ F) ≅ F`.
-/
@[simps]
def leftUnitor (F : A ⥤ B) :
    𝟭 A ⋙ F ≅ F where
  hom := { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }
#align category_theory.functor.left_unitor CategoryTheory.Functor.leftUnitor
#align category_theory.functor.left_unitor_inv_app CategoryTheory.Functor.leftUnitor_inv_app
#align category_theory.functor.left_unitor_hom_app CategoryTheory.Functor.leftUnitor_hom_app

/-- The right unitor, a natural isomorphism `(F ⋙ (𝟭 B)) ≅ F`.
-/
@[simps]
def rightUnitor (F : A ⥤ B) :
    F ⋙ 𝟭 B ≅ F where
  hom := { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }
#align category_theory.functor.right_unitor CategoryTheory.Functor.rightUnitor
#align category_theory.functor.right_unitor_hom_app CategoryTheory.Functor.rightUnitor_hom_app
#align category_theory.functor.right_unitor_inv_app CategoryTheory.Functor.rightUnitor_inv_app

variable {C : Type u₃} [Category.{v₃} C]

variable {D : Type u₄} [Category.{v₄} D]

/-- The associator for functors, a natural isomorphism `((F ⋙ G) ⋙ H) ≅ (F ⋙ (G ⋙ H))`.

(In fact, `iso.refl _` will work here, but it tends to make Lean slow later,
and it's usually best to insert explicit associators.)
-/
@[simps]
def associator (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    (F ⋙ G) ⋙ H ≅ F ⋙ G ⋙ H where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
#align category_theory.functor.associator CategoryTheory.Functor.associator
#align category_theory.functor.associator_inv_app CategoryTheory.Functor.associator_inv_app
#align category_theory.functor.associator_hom_app CategoryTheory.Functor.associator_hom_app

protected theorem assoc (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) : (F ⋙ G) ⋙ H = F ⋙ G ⋙ H :=
  rfl
#align category_theory.functor.assoc CategoryTheory.Functor.assoc

theorem triangle (F : A ⥤ B) (G : B ⥤ C) :
    (associator F (𝟭 B) G).hom ≫ whiskerLeft F (leftUnitor G).hom =
      whiskerRight (rightUnitor F).hom G := by aesop_cat
#align category_theory.functor.triangle CategoryTheory.Functor.triangle

-- See note [dsimp, simp].
variable {E : Type u₅} [Category.{v₅} E]

variable (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (K : D ⥤ E)

theorem pentagon :
    whiskerRight (associator F G H).hom K ≫
        (associator F (G ⋙ H) K).hom ≫ whiskerLeft F (associator G H K).hom =
      (associator (F ⋙ G) H K).hom ≫ (associator F G (H ⋙ K)).hom := by aesop_cat
#align category_theory.functor.pentagon CategoryTheory.Functor.pentagon

end Functor

end CategoryTheory
