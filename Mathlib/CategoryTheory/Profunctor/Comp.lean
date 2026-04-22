/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Types.End
public import Mathlib.CategoryTheory.Profunctor.Basic

/-!

# Composition of Profunctors

This file defines composition of profunctors. Given profunctors `P : C ⥤ Dᵒᵖ ⥤ Type` and
`Q : D ⥤ Eᵒᵖ ⥤ Type`, the composite `P.comp Q` is the profunctor `C ⥤ Eᵒᵖ ⥤ Type` given on objects
`X : C` and `Y : E` by the coend `∫ d, P X d × Q d Y`, where `d` ranges over objects of `D`.

## Main Definitions

(All in the namespace `CategoryTheory.Profunctor`)

* `comp` : Composition of profunctors.
* `whiskerLeft` : Left whiskering of a natural transformation of profunctors.
* `whiskerRight` : Right whiskering of a natural transformation of profunctors.
* `leftUnitor` : The left unitor isomorphism `Profunctor.id.comp P ≅ P`.
* `rightUnitor` : The right unitor isomorphism `P.comp Profunctor.id ≅ P`.
* `associator` : The associator isomorphism `(P.comp Q).comp R ≅ P.comp (Q.comp R)`.

These satisfy the coherence laws for a bicategory, see the file
`CategoryTheory.Profunctor.Bicategory`.
-/

@[expose] public section

universe w w' v u

open Opposite

namespace CategoryTheory

namespace Profunctor

section Composition

section Definition

variable {C : Type*} [Category* C] {D : Type u} [Category.{v} D] {E : Type*} [Category* E]

/-- The bifunctor whose coend defines the composite of two profunctors. -/
@[simps! obj_obj obj_map map_app]
def compDiagram (P : Profunctor.{w} C D) (Q : Profunctor.{w'} D E) (X : C) (Y : E) :
    Dᵒᵖ ⥤ D ⥤ Type max w w' where
  obj U := {
    obj V := ((P.obj X).obj U) × ((Q.obj V).obj (Opposite.op Y))
    map f := TypeCat.ofHom (Prod.map id ((Q.map f).app _)) }
  map g := { app U := TypeCat.ofHom (Prod.map ((P.obj _).map g) id) }

/-- The map on composition diagrams induced by morphisms in the outer variables. -/
@[simps]
def compDiagramMap (P : Profunctor.{w} C D) (Q : Profunctor.{w'} D E)
    {X X' : C} {Y Y' : E} (f : X ⟶ X') (g : Y ⟶ Y') :
    compDiagram P Q X Y' ⟶ compDiagram P Q X' Y where
  app d := { app d' := TypeCat.ofHom (Prod.map ((P.map f).app d) ((Q.obj d').map g.op)) }

@[simp]
lemma compDiagramMap_id (P : Profunctor.{w} C D) (Q : Profunctor.{w'} D E) (X : C) (Y : E) :
    P.compDiagramMap Q (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  cat_disch

@[simp]
lemma compDiagramMap_comp (P : Profunctor.{w} C D) (Q : Profunctor.{w'} D E)
    {X₁ X₂ X₃ : C} {Y₁ Y₂ Y₃ : E} (f : X₁ ⟶ X₂) (f' : X₂ ⟶ X₃) (g : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃) :
    P.compDiagramMap Q (f ≫ f') (g ≫ g') = P.compDiagramMap Q f g' ≫ P.compDiagramMap Q f' g := by
  cat_disch

open Limits

/-- Composition of profunctors using a chosen coend construction. -/
@[simps! obj_obj obj_map map_app]
def univComp [Limits.ChosenCoends.{v, u} (Type (max w w'))]
    (P : Profunctor.{w} C D) (Q : Profunctor.{w'} D E) : Profunctor.{max w w'} C E :=
  .ofCore {
    obj X Y := chosenCoend <| compDiagram P Q X Y
    map f g := chosenCoend.map <| compDiagramMap P Q f g }

/-- Composition of profunctors in the standard universe configuration. -/
@[simps! obj_obj obj_map map_app]
def comp (P : Profunctor.{max u w} C D) (Q : Profunctor.{max u w} D E) : Profunctor.{max u w} C E :=
  Profunctor.univComp.{max u w, max u w} P Q

end Definition

section Whisker

open TypeCat Limits Types Functor

variable {C D E : Type u} [Category* C] [Category* D] [Category* E]

section Left

variable (P : Profunctor.{max u w} C D) {Q R : Profunctor.{max u w} D E} (f : Q ⟶ R)

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] chosenCoend.map_apply in
/-- Left whiskering of a natural transformation of profunctors. -/
@[simps app_app]
def whiskerLeft : P.comp Q ⟶ P.comp R where
  app X := {
    app Y := chosenCoend.map { app d := {
      app d' := ↾Prod.map id ((f.app d').app Y)
      naturality _ _ _ := by
        ext
        dsimp
        apply Prod.ext <;>
        simp [← comp_apply, -types_comp_apply] } }
    naturality _ _ _ := by ext ⟨_, _, _⟩; simp }
  naturality _ _ _ := by ext _ ⟨_, _, _⟩; simp

variable (Q) in
@[simp]
lemma whiskerLeft_id : P.whiskerLeft (𝟙 Q) = 𝟙 (P.comp Q) := by
  ext _ _ ⟨_, _, _⟩
  rfl

@[simp]
lemma whiskerLeft_comp {S : Profunctor.{max u w} D E} (f : Q ⟶ R) (g : R ⟶ S) :
    P.whiskerLeft (f ≫ g) = P.whiskerLeft f ≫ P.whiskerLeft g := by
  ext _ _ ⟨_, _, _⟩
  rfl

end Left

section Right

variable {P Q : Profunctor.{max u w} C D} (R : Profunctor.{max u w} D E) (f : P ⟶ Q)

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] chosenCoend.map_apply in
/-- Right whiskering of a natural transformation of profunctors. -/
@[simps app_app]
def whiskerRight : P.comp R ⟶ Q.comp R where
  app X := { app Y := chosenCoend.map { app d := { app d' := ↾Prod.map ((f.app _).app _) id } } }
  naturality _ _ _ := by
    ext _ ⟨_, _, _⟩
    dsimp
    apply Quot.sound
    rw [coendRel_iff]
    exact ⟨𝟙 _, by simp [← comp_apply, -types_comp_apply]⟩

@[simp]
lemma id_whiskerRight : whiskerRight R (𝟙 P) = 𝟙 (P.comp R) := by
  ext _ _ ⟨_, _, _⟩
  rfl

@[simp]
lemma comp_whiskerRight {R : Profunctor.{max u w} C D} (f : P ⟶ Q) (g : Q ⟶ R)
    (S : Profunctor.{max u w} D E) :
    whiskerRight S (f ≫ g) = whiskerRight S f ≫ whiskerRight S g := by
  ext _ _ ⟨_, _, _⟩
  rfl

end Right

@[simp]
lemma whisker_exchange {P Q : Profunctor.{max u w} C D} {R S : Profunctor.{max u w} D E}
    (f : P ⟶ Q) (g : R ⟶ S) :
    P.whiskerLeft g ≫ whiskerRight S f = whiskerRight R f ≫ Q.whiskerLeft g := by
  ext _ _ ⟨_, _, _⟩
  rfl

end Whisker

section LeftUnitor

variable {C : Type u} [Category.{u} C] {D : Type u} [Category* D]

open Limits TypeCat

set_option backward.isDefEq.respectTransparency false in
/-- The left unitor isomorphism `Profunctor.id.comp P ≅ P` for composition of profunctors. -/
@[simps! hom_app_app inv_app_app]
def leftUnitor (P : Profunctor.{u} C D) : Profunctor.id.comp P ≅ P :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ {
    hom := ↾Quot.lift (fun ⟨d, f, x⟩ ↦ (P.map f).app _ x) fun _ _ ↦ by rintro ⟨f, x⟩; simp
    inv := ↾fun x ↦ Quot.mk _ ⟨X, 𝟙 X, x⟩
    hom_inv_id := by
      ext ⟨_, f, x⟩
      symm
      apply Quot.sound
      rw [Types.coendRel_iff]
      exact ⟨f, ⟨𝟙 X, x⟩, by cat_disch⟩ })
    (fun f ↦ by dsimp; ext; simp [compDiagram, chosenCoend.ι_apply _]))
    (fun f ↦ by ext _ ⟨_, _⟩; simp [chosenCoend.map_apply])

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma id_whiskerLeft {P Q : Profunctor.{u} C D} (f : P ⟶ Q) :
    (Profunctor.id (C := C)).whiskerLeft f =
      (P.leftUnitor).hom ≫ f ≫ (Q.leftUnitor).inv := by
  ext _ _ ⟨_, g, _⟩
  dsimp [chosenCoend.map_apply, Quot.map]
  apply Quot.sound
  rw [Types.coendRel_iff]
  exact ⟨g, by simp [← comp_apply, -types_comp_apply]⟩

end LeftUnitor

section RightUnitor

open Limits TypeCat

variable {C : Type u} [Category* C] {D : Type u} [Category.{u} D]

set_option backward.isDefEq.respectTransparency false in
/-- The right unitor isomorphism `P.comp Profunctor.id ≅ P` for composition of profunctors. -/
@[simps! hom_app_app inv_app_app]
def rightUnitor (P : Profunctor.{u} C D) : P.comp .id ≅ P :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ {
    hom := ↾Quot.lift (fun ⟨d, x, f⟩ ↦ (P.obj X).map f.op x) fun _ _ h ↦ by cases h; simp
    inv := ↾fun x ↦ Quot.mk _ ⟨Y.unop, x, 𝟙 Y.unop⟩
    hom_inv_id := by
      ext ⟨_, x, f⟩
      apply Quot.sound
      rw [Types.coendRel_iff]
      exact ⟨f, ⟨x, 𝟙 (unop Y)⟩, by cat_disch⟩ })
    (fun f ↦ by dsimp; ext; simp [compDiagram, chosenCoend.ι_apply _]))
    (fun f ↦ by ext _ ⟨_, _⟩; simp [chosenCoend.map_apply])

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma whiskerRight_id {P Q : Profunctor.{u} C D} (f : P ⟶ Q) :
    whiskerRight (Profunctor.id (C := D)) f =
      (P.rightUnitor).hom ≫ f ≫ (Q.rightUnitor).inv := by
  ext _ _ ⟨_, _, g⟩
  dsimp [chosenCoend.map_apply, Quot.map]
  symm
  apply Quot.sound
  rw [Types.coendRel_iff]
  exact ⟨g, by simp⟩


end RightUnitor

section Associator

variable {C D E F : Type u} [Category* C] [Category* D] [Category* E] [Category* F]
  (P : Profunctor.{max w u} C D) (Q : Profunctor.{max w u} D E) (R : Profunctor.{max w u} E F)

open TypeCat Limits Types Functor

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] chosenCoend.map_apply in
lemma associatorComponents_aux₁ {X : C} {Y : Fᵒᵖ} {e e' : E} {d d' : D}
    {p : (P.obj X).obj (Opposite.op d)} {q : (Q.obj d).obj (Opposite.op e)}
    {p' : (P.obj X).obj (Opposite.op d')} {q' : (Q.obj d').obj (Opposite.op e')}
    {f : e ⟶ e'} {r : (R.obj e).obj Y}
    (h : Relation.EqvGen (coendRel (P.compDiagram Q X e))
      ⟨d', p', (Q.obj d').map f.op q'⟩ ⟨d, p, q⟩) :
    Relation.EqvGen (coendRel (P.compDiagram (Q.comp R) X (unop Y)))
      ⟨d', p', Quot.mk _ ⟨e', (q', (R.map f).app Y r)⟩⟩
      ⟨d, p, Quot.mk _ ⟨e, (q, r)⟩⟩ := by
  replace h := Relation.EqvGen.map (fun ⟨d, p, q⟩ ↦ ⟨d, (p, Quot.mk _ ⟨e, q, r⟩)⟩)
      (Relation.EqvGen (coendRel (P.compDiagram (Q.comp R) X (unop Y)))) _ _ (h.mono <| by
    intro ⟨d, p, q⟩ ⟨d', p', q'⟩ h
    apply Relation.EqvGen.rel
    rw [coendRel_iff] at h ⊢
    obtain ⟨f, x, h₁, h₂⟩ := h
    use f
    simp_all [Prod.ext_iff])
  simp only [Relation.EqvGen.idempotent] at h
  refine Relation.EqvGen.trans _ _ _ ?_ h
  apply Relation.EqvGen.rel
  rw [coendRel_iff]
  exact ⟨𝟙 _, by simpa using (Quot.sound <| coendRel.mk (F := Q.compDiagram R _ _) f (_, _)).symm⟩

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] chosenCoend.map_apply in
lemma associatorComponents_aux₂ {X : C} {Y : Fᵒᵖ} {d d' : D} {e e' : E}
  {q : (Q.obj d).obj (Opposite.op e)} {r : (R.obj e).obj Y}
  {q' : (Q.obj d').obj (Opposite.op e')}
  {r' : (R.obj e').obj Y} {f : d ⟶ d'} {p : (P.obj X).obj (Opposite.op d')}
  (h : Relation.EqvGen (coendRel (Q.compDiagram R d' (unop Y)))
    ⟨e, ((ConcreteCategory.hom ((Q.map f).app (Opposite.op e))) q, r)⟩ ⟨e', (q', r')⟩) :
  Relation.EqvGen (coendRel ((P.comp Q).compDiagram R X (unop Y)))
    ⟨e, (Quot.mk (coendRel (P.compDiagram Q X e)) ⟨d, (P.obj X).map f.op p, q⟩, r)⟩
    ⟨e', (Quot.mk (coendRel (P.compDiagram Q X e')) ⟨d', (p, q')⟩, r')⟩ := by
  replace h := Relation.EqvGen.map (fun ⟨e, q, r⟩ ↦ ⟨e, Quot.mk _ ⟨d', p, q⟩, r⟩)
      (Relation.EqvGen (coendRel ((P.comp Q).compDiagram R X (unop Y)))) _ _ (h.mono <| by
    intro ⟨d, p, q⟩ ⟨d', p', q'⟩ h
    apply Relation.EqvGen.rel
    rw [coendRel_iff] at h ⊢
    obtain ⟨f, x, h₁, h₂⟩ := h
    exact ⟨f, by simp_all [Prod.ext_iff]⟩)
  simp only [Relation.EqvGen.idempotent] at h
  refine (Relation.EqvGen.trans _ _ _ ?_ h)
  apply Relation.EqvGen.rel
  rw [coendRel_iff]
  exact ⟨𝟙 _, by simpa using Quot.sound <| coendRel.mk (F := P.compDiagram Q _ _) f (_, _)⟩

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] chosenCoend.map_apply in
/-- The objectwise components of the associator isomorphism
`(P.comp Q).comp R ≅ P.comp (Q.comp R)`. -/
@[simps hom inv]
def associatorComponents (X : C) (Y : Fᵒᵖ) :
    (P.comp Q |>.comp R |>.obj X |>.obj Y) ≅ P.comp (Q.comp R) |>.obj X |>.obj Y where
  hom := by
    refine ↾Quot.lift (fun ⟨e, x, r⟩ ↦
      Quot.map (fun ⟨d, p, q⟩ ↦ ⟨d, p, Quot.mk _ ⟨e, q, r⟩⟩) ?_ x) ?_
    · rintro ⟨d, p, q⟩ ⟨d', p', q'⟩ ⟨f, x⟩
      rw [coendRel_iff]
      exact ⟨f, by simp⟩
    · rintro ⟨e, ⟨d, p, q⟩, r⟩ ⟨e', ⟨d', p', q'⟩, r'⟩ h
      dsimp
      rw [coendRel_iff] at h
      obtain ⟨f, ⟨x, r''⟩, h₁, h₂⟩ := h
      dsimp at h₁ h₂
      simp only [map_id, NatTrans.id_app, Prod.mk.injEq] at h₁
      obtain ⟨rfl, rfl⟩ := h₂
      obtain ⟨h₁, rfl⟩ := h₁
      dsimp at h₁
      symm
      dsimp [Quot.map]
      rw [Quot.eq] at h₁ ⊢
      exact associatorComponents_aux₁ _ _ _ h₁
  inv := by
    refine ↾Quot.lift (fun ⟨d, p, x⟩ ↦
        Quot.map (fun ⟨e, q, r⟩ ↦ ⟨e, Quot.mk _ ⟨d, p, q⟩, r⟩) ?_ x) ?_
    · rintro ⟨e, q, r⟩ ⟨e', q', r'⟩ ⟨f, x⟩
      rw [coendRel_iff]
      use f
      simp
    · rintro ⟨d, p, e, q, r⟩ ⟨d', p', e', q', r'⟩ h-- ⟨e', ⟨d', p', q'⟩, r'⟩ h
      dsimp
      rw [coendRel_iff] at h
      obtain ⟨f, ⟨p, x⟩, h₁, h₂⟩ := h
      dsimp at h₁ h₂
      simp only [map_id, Prod.mk.injEq] at h₂
      obtain ⟨rfl, rfl⟩ := h₁
      obtain ⟨rfl, h₂⟩ := h₂
      dsimp at h₂
      dsimp [Quot.map]
      rw [Quot.eq] at h₂ ⊢
      exact associatorComponents_aux₂ _ _ _ h₂
  hom_inv_id := by
    ext ⟨_, ⟨_, _, _⟩, _⟩
    dsimp [Quot.map]
  inv_hom_id := by
    ext ⟨_, _, ⟨_, _, _⟩⟩
    dsimp [Quot.map]

set_option backward.isDefEq.respectTransparency false in
/-- The associator isomorphism `(P.comp Q).comp R ≅ P.comp (Q.comp R)` for composition of
profunctors. -/
@[simps! hom_app_app inv_app_app]
def associator : (P.comp Q).comp R ≅ P.comp (Q.comp R) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ associatorComponents P Q R X Y)
    fun _ ↦ by ext ⟨_, ⟨_, _, _⟩, _⟩; simp [chosenCoend.map_apply, Quot.map])
    fun _ ↦ by ext _ ⟨_, ⟨_, _, _⟩, _⟩; simp [chosenCoend.map_apply, Quot.map]

@[simp]
lemma comp_whiskerLeft {S : Profunctor.{max u w} E F} (f : R ⟶ S) :
    (P.comp Q).whiskerLeft f =
      (P.associator Q R).hom ≫ P.whiskerLeft (Q.whiskerLeft f) ≫ (P.associator Q S).inv := by
  ext _ _ ⟨_, ⟨_, _, _⟩, _⟩
  rfl

variable {P} in
@[simp]
lemma whiskerRight_comp {Q : Profunctor.{max u w} C D} (f : P ⟶ Q)
    (R : Profunctor.{max u w} D E) (S : Profunctor.{max u w} E F) :
    whiskerRight (R.comp S) f =
      (P.associator R S).inv ≫ whiskerRight S (whiskerRight R f) ≫ (Q.associator R S).hom := by
  ext _ _ ⟨_, _, _, _, _⟩
  rfl

variable {Q} in
@[simp]
lemma whisker_assoc {R : Profunctor.{max u w} D E}
    (f : Q ⟶ R) (S : Profunctor.{max u w} E F) :
    whiskerRight S (P.whiskerLeft f) =
      (P.associator Q S).hom ≫ P.whiskerLeft (whiskerRight S f) ≫ (P.associator R S).inv := by
  ext _ _ ⟨_, ⟨_, _, _⟩, _⟩
  rfl

end Associator

end Composition

end Profunctor

end CategoryTheory
