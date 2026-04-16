/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Profunctor.Basic
/-!

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

open Opposite

namespace Limits

namespace Types

variable {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ Type max w u)

inductive coendRel : (W : J) × (F.obj (op W)).obj W → (W : J) × (F.obj (op W)).obj W → Prop where
  | mk {W W' : J} (f : W ⟶ W') (x : (F.obj (op W')).obj W) :
    coendRel ⟨_, (F.map f.op).app _ x⟩ ⟨_, (F.obj _).map f x⟩

def coend : Type max w u := Quot (coendRel F)

def coend.ι (j : J) : (F.obj (op j)).obj j ⟶ coend F := TypeCat.ofHom fun x ↦ Quot.mk _ ⟨j, x⟩

def coend.condition {j j' : J} (f : j ⟶ j') :
    (F.map f.op).app _ ≫ coend.ι F j = (F.obj _).map f ≫ coend.ι F j' := by
  ext
  apply Quot.sound
  apply coendRel.mk

def cowedge : Cowedge F := Cowedge.mk (coend F) (coend.ι F) (by intros; apply coend.condition F)

def cowedgeIsColimit : IsColimit (cowedge F) where
  desc s := TypeCat.ofHom <| Quot.lift (fun x ↦ Multicofork.π s x.fst x.snd) fun _ _ h ↦ by
    cases h with | mk f x => exact ConcreteCategory.congr_hom (Cowedge.condition s f) _
  fac s := by rintro (_ | _) <;> cat_disch
  uniq s m h := by ext ⟨j⟩; exact ConcreteCategory.congr_hom (h (.right j.fst)) j.snd

end Types

class ChosenCoends.{v',u'} (C : Type*) [Category* C] where
  cowedge {J : Type u'} [Category.{v'} J] (F : Jᵒᵖ ⥤ J ⥤ C) : Cowedge F
  isCoend {J : Type u'} [Category.{v'} J] (F : Jᵒᵖ ⥤ J ⥤ C) : IsColimit (cowedge F)

variable {C : Type*} [Category* C] [ChosenCoends.{v, u} C]

section

variable {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ C)

def chosenCoend : C := (ChosenCoends.cowedge F).pt

def chosenCoend.ι (X : J) : (F.obj (op X)).obj X ⟶ chosenCoend F :=
  (ChosenCoends.cowedge F).π X

lemma chosenCoend.condition {X X' : J} (f : X ⟶ X') :
    (F.map f.op).app _ ≫ chosenCoend.ι F X = (F.obj _).map f ≫ chosenCoend.ι F X' :=
  (ChosenCoends.cowedge F).condition f

variable {F}

@[ext]
lemma chosenCoend.hom_ext {X : C} {f g : chosenCoend F ⟶ X}
    (h : ∀ j, chosenCoend.ι F j ≫ f = chosenCoend.ι F j ≫ g) : f = g := by
  apply (ChosenCoends.isCoend F).hom_ext
  rintro (a | a)
  · simpa using _ ≫= h _
  · exact h _

variable {X : C} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j)

def chosenCoend.desc : chosenCoend F ⟶ X :=
  Cowedge.IsColimit.desc (ChosenCoends.isCoend F) f hf

@[reassoc (attr := simp)]
lemma chosenCoend.ι_desc (j : J) : chosenCoend.ι F j ≫ chosenCoend.desc f hf = f j := by
  apply IsColimit.fac

def chosenCoend.map {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) : chosenCoend F ⟶ chosenCoend G :=
  chosenCoend.desc (fun x ↦ (f.app (op x)).app x ≫ chosenCoend.ι _ _) (fun j j' φ ↦ by
    simp [chosenCoend.condition])

@[reassoc (attr := simp)]
lemma chosenCoend.ι_map {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (j : J) :
    chosenCoend.ι F j ≫ chosenCoend.map f = (f.app _).app _ ≫ chosenCoend.ι G j := by
  simp [chosenCoend.map]

@[simp]
lemma chosenCoend.map_id : chosenCoend.map (𝟙 F) = 𝟙 _ := by cat_disch

@[reassoc (attr := simp)]
lemma chosenCoend.map_comp {G H : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (g : G ⟶ H) :
    chosenCoend.map f ≫ chosenCoend.map g = chosenCoend.map (f ≫ g) := by
  cat_disch

end

section

instance : Limits.ChosenCoends.{v, u} (Type max w u) where
  cowedge := Types.cowedge
  isCoend := Types.cowedgeIsColimit

variable {J : Type u} [Category.{v} J] {F : Jᵒᵖ ⥤ J ⥤ Type max w u}

lemma chosenCoend.ι_apply (j : J) (x : (F.obj (op j)).obj j) :
    chosenCoend.ι F j x = Quot.mk _ ⟨j, x⟩ :=
  rfl

lemma chosenCoend.desc_apply {X : Type max w u} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j)
    (x : chosenCoend F) : chosenCoend.desc f hf x =
      Quot.lift (fun j ↦ f j.fst j.snd) (fun _ _ h ↦ by
        cases h with | mk f x => exact ConcreteCategory.congr_hom (hf f) _) x :=
  rfl

lemma chosenCoend.map_apply {G : Jᵒᵖ ⥤ J ⥤ Type max w u} (f : F ⟶ G) (x : chosenCoend F) :
    chosenCoend.map f x = Quot.map (fun ⟨j, y⟩ ↦ ⟨j, (f.app _).app _ y⟩) (fun _ _ h ↦ by
      cases h with | mk g x =>
        dsimp
        convert Types.coendRel.mk g ((f.app _).app _ x)
        · simp only [← NatTrans.comp_app_apply, f.naturality]
        · simp [← (f.app _).naturality_apply, -NatTrans.naturality_apply]) x :=
  rfl

end

end Limits

namespace Profunctor

section Composition

section Definition

variable {C : Type*} [Category* C] {D : Type u} [Category.{v} D]
  {E : Type*} [Category* E]

open Opposite

@[simps! obj_obj obj_map map_app]
def compDiagram (P : Profunctor.{w} C D) (Q : Profunctor.{w'} D E) (X : C) (Y : E) :
    Dᵒᵖ ⥤ D ⥤ Type max w w' where
  obj U := {
    obj V := ((P.obj X).obj U) × ((Q.obj V).obj (Opposite.op Y))
    map f := TypeCat.ofHom (Prod.map id ((Q.map f).app _)) }
  map g := { app U := TypeCat.ofHom (Prod.map ((P.obj _).map g) id) }

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

variable [Limits.ChosenCoends.{v, u} (Type (max w w'))]

@[simps! obj_obj obj_map map_app]
def univComp (P : Profunctor.{w} C D) (Q : Profunctor.{w'} D E) :
    Profunctor.{max w w'} C E :=
  .ofCore {
    obj X Y := chosenCoend <| compDiagram P Q X Y
    map f g := chosenCoend.map <| compDiagramMap P Q f g }

@[simps! obj_obj obj_map map_app]
def comp (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) : Profunctor.{u} C E :=
  Profunctor.univComp.{u, u} P Q

end Definition

section LeftUnitor

variable {C : Type u} [Category.{u} C] {D : Type u} [Category* D]

set_option backward.isDefEq.respectTransparency false in
def leftUnitor (P : Profunctor.{u} C D) : (Profunctor.id (C := C)).comp P ≅ P :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ Equiv.toIso {
      toFun := Quot.lift (fun ⟨d, f, x⟩ ↦ (P.map f).app _ x) fun _ _ h ↦ by cases h; simp
      invFun x := Quot.mk _ ⟨X, 𝟙 X, x⟩
      left_inv x := by
        obtain ⟨⟨_, f, x⟩, rfl⟩ := Quot.mk_surjective x
        symm
        apply Quot.sound
        dsimp
        convert Limits.Types.coendRel.mk
          (F := compDiagram (Profunctor.id.{u} (C := C)) P X (unop Y)) f ⟨𝟙 X, x⟩
        cat_disch
      right_inv _ := by simp })
    (fun f ↦ by dsimp; ext; simp [compDiagram, Limits.chosenCoend.ι_apply _]))
    (fun f ↦ by
      ext _ z
      simp [Limits.chosenCoend.map_apply, Quot.map]
      obtain ⟨_, rfl⟩ := Quot.mk_surjective z
      simp)

end LeftUnitor

section RightUnitor

variable {C : Type u} [Category* C] {D : Type u} [Category.{u} D]

set_option backward.isDefEq.respectTransparency false in
def rightUnitor (P : Profunctor.{u} C D) : P.comp (.id (C := D)) ≅ P :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ Equiv.toIso {
      toFun := Quot.lift (fun ⟨d, x, f⟩ ↦ (P.obj X).map f.op x) fun _ _ h ↦ by cases h; simp
      invFun x := Quot.mk _ ⟨Y.unop, x, 𝟙 Y.unop⟩
      left_inv x := by
        obtain ⟨⟨_, x, f⟩, rfl⟩ := Quot.mk_surjective x
        apply Quot.sound
        dsimp
        convert Limits.Types.coendRel.mk
          (F := compDiagram P (.id (C := D)) X (unop Y)) f ⟨x, 𝟙 _⟩
        cat_disch
      right_inv x := by simp })
    (fun f ↦ by dsimp; ext; simp [compDiagram, Limits.chosenCoend.ι_apply _]))
    (fun f ↦ by
      ext _ z
      simp [Limits.chosenCoend.map_apply, Quot.map]
      obtain ⟨_, rfl⟩ := Quot.mk_surjective z
      simp)

end RightUnitor

section Associator

variable {C D E F : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E] [Category.{u} F]
variable (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) (R : Profunctor.{u} E F)

set_option backward.isDefEq.respectTransparency false in
noncomputable def associator : (P.comp Q).comp R ≅ P.comp (Q.comp R) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ Equiv.toIso {
    toFun := Quot.lift (fun ⟨e, x⟩ ↦ Quot.mk _ ⟨(Quot.out x.1).1, (Quot.out x.1).2.1,
      Quot.mk _ ⟨e, (Quot.out x.1).2.2, x.snd⟩⟩) sorry
    invFun := sorry
    left_inv := sorry
    right_inv := sorry
  }) sorry) sorry

end Associator

end Composition

end Profunctor

end CategoryTheory
