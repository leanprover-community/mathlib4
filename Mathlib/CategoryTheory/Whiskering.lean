/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Tactic.CategoryTheory.IsoReassoc
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Whiskering

Given a functor `F : C ⥤ D` and functors `G H : D ⥤ E` and a natural transformation `α : G ⟶ H`,
we can construct a new natural transformation `F ⋙ G ⟶ F ⋙ H`,
called `whiskerLeft F α`. This is the same as the horizontal composition of `𝟙 F` with `α`.

This operation is functorial in `F`, and we package this as `whiskeringLeft`. Here
`(whiskeringLeft.obj F).obj G` is `F ⋙ G`, and
`(whiskeringLeft.obj F).map α` is `whiskerLeft F α`.
(That is, we might have alternatively named this as the "left composition functor".)

We also provide analogues for composition on the right, and for these operations on isomorphisms.

We show the associator and unitor natural isomorphisms satisfy the triangle and pentagon
identities.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


namespace CategoryTheory

namespace Functor

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

set_option backward.isDefEq.respectTransparency false in
/-- If `α : G ⟶ H` then `whiskerLeft F α : F ⋙ G ⟶ F ⋙ H` has components `α.app (F.obj X)`. -/
@[to_dual self, simps (attr := to_dual self)]
def whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) :
    F ⋙ G ⟶ F ⋙ H where
  app X := α.app (F.obj X)
  naturality X Y f := by rw [Functor.comp_map, Functor.comp_map, α.naturality]

set_option backward.defeqAttrib.useBackward true in
@[simp, to_dual self]
lemma id_hcomp (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) : 𝟙 F ◫ α = whiskerLeft F α := by
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/-- If `α : G ⟶ H` then `whiskerRight α F : G ⋙ F ⟶ H ⋙ F` has components `F.map (α.app X)`. -/
@[to_dual self, simps (attr := to_dual self)]
def whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) :
    G ⋙ F ⟶ H ⋙ F where
  app X := F.map (α.app X)
  naturality X Y f := by
    rw [Functor.comp_map, Functor.comp_map, ← F.map_comp, ← F.map_comp, α.naturality]

set_option backward.defeqAttrib.useBackward true in
@[simp, to_dual self]
lemma hcomp_id {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) : α ◫ 𝟙 F = whiskerRight α F := by
  ext
  simp

variable (C D E)

set_option backward.defeqAttrib.useBackward true in
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

set_option backward.defeqAttrib.useBackward true in
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

variable {C} {D} {E}

instance faithful_whiskeringRight_obj {F : D ⥤ E} [F.Faithful] :
    ((whiskeringRight C D E).obj F).Faithful where
  map_injective hαβ := by
    ext X
    exact F.map_injective <| congr_fun (congr_arg NatTrans.app hαβ) X

/-- If `F : D ⥤ E` is fully faithful, then so is
`(whiskeringRight C D E).obj F : (C ⥤ D) ⥤ C ⥤ E`. -/
@[simps]
def FullyFaithful.whiskeringRight {F : D ⥤ E} (hF : F.FullyFaithful)
    (C : Type*) [Category* C] :
    ((whiskeringRight C D E).obj F).FullyFaithful where
  preimage f :=
    { app := fun X => hF.preimage (f.app X)
      naturality := fun _ _ g => by
        apply hF.map_injective
        dsimp
        simp only [map_comp, map_preimage]
        apply f.naturality }

theorem whiskeringLeft_obj_id : (whiskeringLeft C C E).obj (𝟭 _) = 𝟭 _ :=
  rfl

/-- The isomorphism between left-whiskering on the identity functor and the identity of the functor
between the resulting functor categories. -/
@[simps!]
def whiskeringLeftObjIdIso : (whiskeringLeft C C E).obj (𝟭 _) ≅ 𝟭 _ :=
  Iso.refl _

theorem whiskeringLeft_obj_comp {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringLeft C D' E).obj (F ⋙ G) =
    (whiskeringLeft D D' E).obj G ⋙ (whiskeringLeft C D E).obj F :=
  rfl

/-- The isomorphism between left-whiskering on the composition of functors and the composition
of two left-whiskering applications. -/
@[simps!]
def whiskeringLeftObjCompIso {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringLeft C D' E).obj (F ⋙ G) ≅
    (whiskeringLeft D D' E).obj G ⋙ (whiskeringLeft C D E).obj F :=
  Iso.refl _

theorem whiskeringRight_obj_id : (whiskeringRight E C C).obj (𝟭 _) = 𝟭 _ :=
  rfl

/-- The isomorphism between right-whiskering on the identity functor and the identity of the functor
between the resulting functor categories. -/
@[simps!]
def whiskeringRightObjIdIso : (whiskeringRight E C C).obj (𝟭 _) ≅ 𝟭 _ :=
  Iso.refl _

theorem whiskeringRight_obj_comp {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringRight E C D).obj F ⋙ (whiskeringRight E D D').obj G =
    (whiskeringRight E C D').obj (F ⋙ G) :=
  rfl

/-- The isomorphism between right-whiskering on the composition of functors and the composition
of two right-whiskering applications. -/
@[simps!]
def whiskeringRightObjCompIso {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringRight E C D).obj F ⋙ (whiskeringRight E D D').obj G ≅
    (whiskeringRight E C D').obj (F ⋙ G) :=
  Iso.refl _

instance full_whiskeringRight_obj {F : D ⥤ E} [F.Faithful] [F.Full] :
    ((whiskeringRight C D E).obj F).Full :=
  ((Functor.FullyFaithful.ofFullyFaithful F).whiskeringRight C).full

@[simp]
theorem whiskerLeft_id (F : C ⥤ D) {G : D ⥤ E} :
    whiskerLeft F (NatTrans.id G) = NatTrans.id (F.comp G) :=
  rfl

@[simp]
theorem whiskerLeft_id' (F : C ⥤ D) {G : D ⥤ E} : whiskerLeft F (𝟙 G) = 𝟙 (F.comp G) :=
  rfl

@[simp]
theorem whiskerRight_id {G : C ⥤ D} (F : D ⥤ E) :
    whiskerRight (NatTrans.id G) F = NatTrans.id (G.comp F) :=
  ((whiskeringRight C D E).obj F).map_id _

@[simp]
theorem whiskerRight_id' {G : C ⥤ D} (F : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F) :=
  ((whiskeringRight C D E).obj F).map_id _

@[simp, to_dual self, reassoc]
theorem whiskerLeft_comp (F : C ⥤ D) {G H K : D ⥤ E} (α : G ⟶ H) (β : H ⟶ K) :
    whiskerLeft F (α ≫ β) = whiskerLeft F α ≫ whiskerLeft F β :=
  rfl

@[simp, to_dual self, reassoc]
theorem whiskerRight_comp {G H K : C ⥤ D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) :
    whiskerRight (α ≫ β) F = whiskerRight α F ≫ whiskerRight β F :=
  ((whiskeringRight C D E).obj F).map_comp α β

set_option backward.defeqAttrib.useBackward true in
@[to_dual none, reassoc]
theorem whiskerLeft_comp_whiskerRight {F G : C ⥤ D} {H K : D ⥤ E} (α : F ⟶ G) (β : H ⟶ K) :
    whiskerLeft F β ≫ whiskerRight α K = whiskerRight α H ≫ whiskerLeft G β := by
  ext
  simp

set_option backward.defeqAttrib.useBackward true in
@[to_dual hcomp_eq_whiskerRight_comp_whiskerLeft]
lemma NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight {F G : C ⥤ D} {H K : D ⥤ E}
    (α : F ⟶ G) (β : H ⟶ K) : α ◫ β = whiskerLeft F β ≫ whiskerRight α K := by
  ext
  simp

/-- If `α : G ≅ H` is a natural isomorphism then
`isoWhiskerLeft F α : (F ⋙ G) ≅ (F ⋙ H)` has components `α.app (F.obj X)`.
-/
def isoWhiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) : F ⋙ G ≅ F ⋙ H :=
  ((whiskeringLeft C D E).obj F).mapIso α

@[simp]
theorem isoWhiskerLeft_hom (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
    (isoWhiskerLeft F α).hom = whiskerLeft F α.hom :=
  rfl

@[simp]
theorem isoWhiskerLeft_inv (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
    (isoWhiskerLeft F α).inv = whiskerLeft F α.inv :=
  rfl

lemma isoWhiskerLeft_symm (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
    (isoWhiskerLeft F α).symm = isoWhiskerLeft F α.symm :=
  rfl

@[simp]
lemma isoWhiskerLeft_refl (F : C ⥤ D) (G : D ⥤ E) :
    isoWhiskerLeft F (Iso.refl G) = Iso.refl _ :=
  rfl

/-- If `α : G ≅ H` then
`isoWhiskerRight α F : (G ⋙ F) ≅ (H ⋙ F)` has components `F.map_iso (α.app X)`.
-/
def isoWhiskerRight {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : G ⋙ F ≅ H ⋙ F :=
  ((whiskeringRight C D E).obj F).mapIso α

@[simp]
theorem isoWhiskerRight_hom {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    (isoWhiskerRight α F).hom = whiskerRight α.hom F :=
  rfl

@[simp]
theorem isoWhiskerRight_inv {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    (isoWhiskerRight α F).inv = whiskerRight α.inv F :=
  rfl

lemma isoWhiskerRight_symm {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    (isoWhiskerRight α F).symm = isoWhiskerRight α.symm F :=
  rfl

@[simp]
lemma isoWhiskerRight_refl (F : C ⥤ D) (G : D ⥤ E) :
    isoWhiskerRight (Iso.refl F) G = Iso.refl _ := by
  cat_disch

@[to_dual self]
instance isIso_whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [IsIso α] :
    IsIso (whiskerLeft F α) :=
  (isoWhiskerLeft F (asIso α)).isIso_hom

@[to_dual self]
instance isIso_whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [IsIso α] :
    IsIso (whiskerRight α F) :=
  (isoWhiskerRight (asIso α) F).isIso_hom

@[simp, to_dual self]
theorem inv_whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [IsIso α] :
    inv (whiskerRight α F) = whiskerRight (inv α) F := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← whiskerRight_comp]

@[simp, to_dual self]
theorem inv_whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [IsIso α] :
    inv (whiskerLeft F α) = whiskerLeft F (inv α) := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← whiskerLeft_comp]

@[simp, reassoc]
theorem isoWhiskerLeft_trans (F : C ⥤ D) {G H K : D ⥤ E} (α : G ≅ H) (β : H ≅ K) :
    isoWhiskerLeft F (α ≪≫ β) = isoWhiskerLeft F α ≪≫ isoWhiskerLeft F β :=
  rfl

@[simp, reassoc]
theorem isoWhiskerRight_trans {G H K : C ⥤ D} (α : G ≅ H) (β : H ≅ K) (F : D ⥤ E) :
    isoWhiskerRight (α ≪≫ β) F = isoWhiskerRight α F ≪≫ isoWhiskerRight β F :=
  ((whiskeringRight C D E).obj F).mapIso_trans α β

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
theorem isoWhiskerLeft_trans_isoWhiskerRight {F G : C ⥤ D} {H K : D ⥤ E} (α : F ≅ G) (β : H ≅ K) :
    isoWhiskerLeft F β ≪≫ isoWhiskerRight α K = isoWhiskerRight α H ≪≫ isoWhiskerLeft G β := by
  ext
  simp

variable {B : Type u₄} [Category.{v₄} B]

set_option backward.defeqAttrib.useBackward true in
@[simp, to_dual none]
theorem whiskerLeft_twice (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) :
    whiskerLeft F (whiskerLeft G α) =
    (Functor.associator _ _ _).inv ≫ whiskerLeft (F ⋙ G) α ≫ (Functor.associator _ _ _).hom := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
@[simp, to_dual none]
theorem whiskerRight_twice {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) :
    whiskerRight (whiskerRight α F) G =
    (Functor.associator _ _ _).hom ≫ whiskerRight α (F ⋙ G) ≫ (Functor.associator _ _ _).inv := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
@[to_dual none]
theorem whiskerRight_left (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E) :
    whiskerRight (whiskerLeft F α) K =
    (Functor.associator _ _ _).hom ≫ whiskerLeft F (whiskerRight α K) ≫
      (Functor.associator _ _ _).inv := by
  cat_disch

@[simp]
theorem isoWhiskerLeft_twice (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ≅ K) :
    isoWhiskerLeft F (isoWhiskerLeft G α) =
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerLeft (F ⋙ G) α ≪≫ Functor.associator _ _ _ := by
  cat_disch

@[simp, reassoc]
theorem isoWhiskerRight_twice {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ≅ K) :
    isoWhiskerRight (isoWhiskerRight α F) G =
    Functor.associator _ _ _ ≪≫ isoWhiskerRight α (F ⋙ G) ≪≫ (Functor.associator _ _ _).symm := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
theorem isoWhiskerRight_left (F : B ⥤ C) {G H : C ⥤ D} (α : G ≅ H) (K : D ⥤ E) :
    isoWhiskerRight (isoWhiskerLeft F α) K =
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft F (isoWhiskerRight α K) ≪≫
      (Functor.associator _ _ _).symm := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
theorem isoWhiskerLeft_right (F : B ⥤ C) {G H : C ⥤ D} (α : G ≅ H) (K : D ⥤ E) :
    isoWhiskerLeft F (isoWhiskerRight α K) =
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (isoWhiskerLeft F α) K ≪≫
      Functor.associator _ _ _ := by
  cat_disch

end

universe u₅ v₅

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D] {E : Type u₅} [Category.{v₅} E]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (K : D ⥤ E)

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
theorem triangleIso :
    associator F (𝟭 B) G ≪≫ isoWhiskerLeft F (leftUnitor G) =
      isoWhiskerRight (rightUnitor F) G := by cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
theorem pentagonIso :
    isoWhiskerRight (associator F G H) K ≪≫
        associator F (G ⋙ H) K ≪≫ isoWhiskerLeft F (associator G H K) =
      associator (F ⋙ G) H K ≪≫ associator F G (H ⋙ K) := by cat_disch

set_option backward.defeqAttrib.useBackward true in
theorem triangle :
    (associator F (𝟭 B) G).hom ≫ whiskerLeft F (leftUnitor G).hom =
      whiskerRight (rightUnitor F).hom G := by cat_disch

set_option backward.defeqAttrib.useBackward true in
theorem pentagon :
    whiskerRight (associator F G H).hom K ≫
        (associator F (G ⋙ H) K).hom ≫ whiskerLeft F (associator G H K).hom =
      (associator (F ⋙ G) H K).hom ≫ (associator F G (H ⋙ K)).hom := by cat_disch

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃] (E : Type*) [Category* E]

set_option backward.defeqAttrib.useBackward true in
/-- The obvious functor `(C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (D₁ ⥤ D₂ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ E)`. -/
@[simps!]
def whiskeringLeft₂ :
    (C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (D₁ ⥤ D₂ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ E) where
  obj F₁ :=
    { obj := fun F₂ ↦
        (whiskeringRight D₁ (D₂ ⥤ E) (C₂ ⥤ E)).obj ((whiskeringLeft C₂ D₂ E).obj F₂) ⋙
          (whiskeringLeft C₁ D₁ (C₂ ⥤ E)).obj F₁
      map := fun φ ↦ whiskerRight
        ((whiskeringRight D₁ (D₂ ⥤ E) (C₂ ⥤ E)).map ((whiskeringLeft C₂ D₂ E).map φ)) _ }
  map ψ :=
    { app := fun F₂ ↦ whiskerLeft _ ((whiskeringLeft C₁ D₁ (C₂ ⥤ E)).map ψ) }

/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[simps!]
def whiskeringLeft₃ObjObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃) :
    (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E :=
  (whiskeringRight _ _ _).obj (((whiskeringLeft₂ E).obj F₂).obj F₃) ⋙
    (whiskeringLeft C₁ D₁ _).obj F₁

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[simps]
def whiskeringLeft₃ObjObjMap (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) {F₃ F₃' : C₃ ⥤ D₃} (τ₃ : F₃ ⟶ F₃') :
    whiskeringLeft₃ObjObjObj E F₁ F₂ F₃ ⟶
      whiskeringLeft₃ObjObjObj E F₁ F₂ F₃' where
  app F := whiskerLeft _ (whiskerLeft _ (((whiskeringLeft₂ E).obj F₂).map τ₃))

variable (C₃ D₃) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[simps]
def whiskeringLeft₃ObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) :
    (C₃ ⥤ D₃) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) where
  obj F₃ := whiskeringLeft₃ObjObjObj E F₁ F₂ F₃
  map τ₃ := whiskeringLeft₃ObjObjMap E F₁ F₂ τ₃

set_option backward.defeqAttrib.useBackward true in
variable (C₃ D₃) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[simps]
def whiskeringLeft₃ObjMap (F₁ : C₁ ⥤ D₁) {F₂ F₂' : C₂ ⥤ D₂} (τ₂ : F₂ ⟶ F₂') :
    whiskeringLeft₃ObjObj C₃ D₃ E F₁ F₂ ⟶ whiskeringLeft₃ObjObj C₃ D₃ E F₁ F₂' where
  app F₃ := whiskerRight ((whiskeringRight _ _ _).map (((whiskeringLeft₂ E).map τ₂).app F₃)) _

variable (C₂ C₃ D₂ D₃) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[simps]
def whiskeringLeft₃Obj (F₁ : C₁ ⥤ D₁) :
    (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) where
  obj F₂ := whiskeringLeft₃ObjObj C₃ D₃ E F₁ F₂
  map τ₂ := whiskeringLeft₃ObjMap C₃ D₃ E F₁ τ₂

set_option backward.defeqAttrib.useBackward true in
variable (C₂ C₃ D₂ D₃) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[simps]
def whiskeringLeft₃Map {F₁ F₁' : C₁ ⥤ D₁} (τ₁ : F₁ ⟶ F₁') :
    whiskeringLeft₃Obj C₂ C₃ D₂ D₃ E F₁ ⟶ whiskeringLeft₃Obj C₂ C₃ D₂ D₃ E F₁' where
  app F₂ := { app F₃ := whiskerLeft _ ((whiskeringLeft _ _ _).map τ₁) }

/-- The obvious functor
`(C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E)`. -/
@[simps!]
def whiskeringLeft₃ :
    (C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) where
  obj F₁ := whiskeringLeft₃Obj C₂ C₃ D₂ D₃ E F₁
  map τ₁ := whiskeringLeft₃Map C₂ C₃ D₂ D₃ E τ₁

variable {E}

/-- The "postcomposition" with a functor `E ⥤ E'` gives a functor
`(E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ E'`. -/
@[simps!]
def postcompose₂ {E' : Type*} [Category* E'] :
    (E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ E' :=
  whiskeringRight C₂ _ _ ⋙ whiskeringRight C₁ _ _

/-- The "postcomposition" with a functor `E ⥤ E'` gives a functor
`(E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E'`. -/
@[simps!]
def postcompose₃ {E' : Type*} [Category* E'] :
    (E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E' :=
  whiskeringRight C₃ _ _ ⋙ whiskeringRight C₂ _ _ ⋙ whiskeringRight C₁ _ _

end Functor

end CategoryTheory
