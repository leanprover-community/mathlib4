/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Profunctor.Basic
/-!

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

namespace Functor

variable {A B C D E : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]

@[simps!]
def flipping₃₄₁₂ : (A ⥤ B ⥤ C ⥤ D ⥤ E) ≌ (C ⥤ D ⥤ A ⥤ B ⥤ E) :=
  (flipping.congrRight.trans flipping).trans (flipping.congrRight.trans flipping).congrRight

end Functor

open Opposite

namespace Limits

namespace Types

variable {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ Type max w u)

inductive coendRel : (W : J) × (F.obj (op W)).obj W → (W : J) × (F.obj (op W)).obj W → Prop where
  | mk {W W' : J} (f : W ⟶ W') (x : (F.obj (op W')).obj W) :
    coendRel ⟨W, ConcreteCategory.hom ((F.map f.op).app _) x⟩ ⟨W', ConcreteCategory.hom ((F.obj _).map f) x⟩

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

section

variable {C : Type*} [Category* C] [ChosenCoends.{v, u} C]

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

def chosenCoend.uniq (c : Cowedge F) (hc : IsColimit c) : c.pt ≅ chosenCoend F :=
  hc.coconePointUniqueUpToIso (ChosenCoends.isCoend _)

@[simp]
lemma chosenCoend.map_id : chosenCoend.map (𝟙 F) = 𝟙 _ := by cat_disch

@[reassoc (attr := simp)]
lemma chosenCoend.map_comp {G H : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (g : G ⟶ H) :
    chosenCoend.map f ≫ chosenCoend.map g = chosenCoend.map (f ≫ g) := by
  cat_disch

@[simps]
def chosenCoendFunctor : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  obj := chosenCoend
  map := chosenCoend.map

end

section

@[simps -isSimp]
instance : Limits.ChosenCoends.{v, u} (Type max w u) where
  cowedge := Types.cowedge
  isCoend := Types.cowedgeIsColimit

section GeneralUniverse

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
        convert Types.coendRel.mk g ((f.app _).app _ x)
        · simp only [← NatTrans.comp_app_apply, f.naturality]
        · simp [← NatTrans.naturality_apply]) x :=
  rfl

end GeneralUniverse

section Small

open scoped TypeCat

variable {J : Type u} [Category.{u} J]

@[simps! obj_obj_obj obj_obj_map obj_map_app map_app_app]
def adjoint : Type u ⥤ Jᵒᵖ ⥤ J ⥤ Type u where
  obj X := (Functor.postcompose₂.obj (yoneda.obj X)).obj
    (yoneda ⋙ (opOpEquivalence (Type u)).congrRight.inverse ⋙
      (Functor.opUnopEquiv J (Type uᵒᵖ)).inverse).leftOp
  map f := { app c := { app d := TypeCat.ofHom fun g ↦ g ≫ f } }

set_option backward.isDefEq.respectTransparency false in
def chosenCoendAdjunction : chosenCoendFunctor (C := Type u) (J := J) ⊣ adjoint (J := J) where
  unit := {
    app F := {
      app j := { app j' := ↾fun f ↦ ↾fun g ↦ Quot.mk _ ⟨j.unop, (F.obj _).map g f⟩ }
      naturality _ _ f := by
        ext j x
        dsimp
        ext g
        dsimp
        apply Quot.sound
        have := Types.coendRel.mk f.unop ((F.obj _).map g x)
        simp_all }
    naturality F G f := by
      ext j j' x
      dsimp
      ext g
      dsimp [chosenCoend.map_apply, Quot.map]
      apply Quot.sound
      simpa using Types.coendRel.mk (𝟙 (unop j)) ((G.obj _).map g ((f.app _).app _ x)) }
  counit := {
    app X := ↾Quot.lift (fun ⟨j, (x : (j ⟶ j) ⟶ X)⟩ ↦ x (𝟙 j)) (fun _ _ h ↦ by induction h; simp) }
  left_triangle_components := by
    intro F
    ext x
    obtain ⟨x, rfl⟩ := Quot.mk_surjective x
    simp [chosenCoend.map_apply, Quot.map]

variable {I : Type u} [Category.{u} I] -- (F : Iᵒᵖ ⥤ I ⥤ Jᵒᵖ ⥤ J ⥤ Type u)

def iso' : adjoint (J := I) ⋙ Functor.postcompose₂.obj (adjoint (J := J)) ≅
    (adjoint (J := J) ⋙ Functor.postcompose₂.obj (adjoint (J := I))) ⋙
      Functor.flipping₃₄₁₂.inverse :=
  NatIso.ofComponents fun X ↦ NatIso.ofComponents fun i ↦ NatIso.ofComponents fun i' ↦
    NatIso.ofComponents fun j ↦ NatIso.ofComponents fun j' ↦ {
      hom := ↾fun x ↦ ↾fun y ↦ ↾fun z ↦ (x.hom z).hom y
      inv := ↾fun x ↦ ↾fun y ↦ ↾fun z ↦ (x.hom z).hom y }

def fubini :
    Functor.postcompose₂.obj (chosenCoendFunctor (J := J) (C := Type u)) ⋙
      chosenCoendFunctor (J := I) ≅
    Functor.flipping₃₄₁₂.functor ⋙ Functor.postcompose₂.obj (chosenCoendFunctor (J := I)) ⋙
      chosenCoendFunctor (J := J) :=
  (conjugateIsoEquiv (Adjunction.comp Functor.flipping₃₄₁₂.toAdjunction
    (((chosenCoendAdjunction.whiskerRight _ ).whiskerRight _).comp chosenCoendAdjunction))
    (((chosenCoendAdjunction.whiskerRight _ ).whiskerRight _).comp chosenCoendAdjunction)).symm <|
      NatIso.ofComponents fun X ↦ NatIso.ofComponents fun i ↦ NatIso.ofComponents fun i' ↦
        NatIso.ofComponents fun j ↦ NatIso.ofComponents fun j' ↦ {
          hom := ↾fun x ↦ ↾fun y ↦ ↾fun z ↦ (x.hom z).hom y
          inv := ↾fun x ↦ ↾fun y ↦ ↾fun z ↦ (x.hom z).hom y }

end Small

end

end Limits

namespace Profunctor

section Composition

section Definition

variable {C : Type*} [Category* C] {D : Type u} [Category.{v} D] {E : Type*} [Category* E]

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

open Limits TypeCat

set_option backward.isDefEq.respectTransparency false in
def leftUnitor (P : Profunctor.{u} C D) : Profunctor.id.comp P ≅ P :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ {
      hom := ↾Quot.lift (fun ⟨d, f, x⟩ ↦ (P.map f).app _ x) fun _ _ h ↦ by cases h; simp
      inv := ↾fun x ↦ Quot.mk _ ⟨X, 𝟙 X, x⟩
      hom_inv_id := by
        ext x
        obtain ⟨⟨_, f, x⟩, rfl⟩ := Quot.mk_surjective x
        symm
        apply Quot.sound
        dsimp
        have := Types.coendRel.mk (F := compDiagram Profunctor.id.{u} P X (unop Y)) f ⟨𝟙 X, x⟩
        cat_disch })
    (fun f ↦ by dsimp; ext; simp [compDiagram, chosenCoend.ι_apply _]))
    (fun f ↦ by
      ext _ z
      simp [chosenCoend.map_apply, Quot.map]
      obtain ⟨_, rfl⟩ := Quot.mk_surjective z
      simp)

end LeftUnitor

section RightUnitor

open Limits TypeCat

variable {C : Type u} [Category* C] {D : Type u} [Category.{u} D]

set_option backward.isDefEq.respectTransparency false in
def rightUnitor (P : Profunctor.{u} C D) : P.comp .id ≅ P :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ {
      hom := ↾Quot.lift (fun ⟨d, x, f⟩ ↦ (P.obj X).map f.op x) fun _ _ h ↦ by cases h; simp
      inv := ↾fun x ↦ Quot.mk _ ⟨Y.unop, x, 𝟙 Y.unop⟩
      hom_inv_id := by
        ext x
        obtain ⟨⟨_, x, f⟩, rfl⟩ := Quot.mk_surjective x
        apply Quot.sound
        dsimp
        have := Types.coendRel.mk (F := compDiagram P (.id (C := D)) X (unop Y)) f ⟨x, 𝟙 _⟩
        cat_disch })
    (fun f ↦ by dsimp; ext; simp [compDiagram, chosenCoend.ι_apply _]))
    (fun f ↦ by
      ext _ z
      simp [chosenCoend.map_apply, Quot.map]
      obtain ⟨_, rfl⟩ := Quot.mk_surjective z
      simp)

end RightUnitor

section Associator

variable {C D E F : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E] [Category.{u} F]
variable (P : Profunctor.{u} C D) (Q : Profunctor.{u} D E) (R : Profunctor.{u} E F)

open TypeCat Limits Types Functor MonoidalCategory

variable (X : C) (Y : F)

@[simps! obj_obj_obj obj_obj_map obj_map_app map_app_app]
def compDiagram₃ : Dᵒᵖ ⥤ D ⥤ Eᵒᵖ ⥤ E ⥤ Type u where
  obj U := {
    obj V := (postcompose₂.obj (tensorLeft ((P.obj X).obj U))).obj <| Q.compDiagram R V Y
    map f := (postcompose₂.obj (tensorLeft ((P.obj X).obj U))).map (Q.compDiagramMap R f (𝟙 _))
  }
  map g := { app U := (postcompose₂.map { app V := (P.obj _).map g ▷ _ }).app _ }

@[simps! obj_obj_obj obj_obj_map obj_map_app map_app_app]
def compDiagram₃' : Eᵒᵖ ⥤ E ⥤ Dᵒᵖ ⥤ D ⥤ Type u where
  obj U := {
    obj V := (postcompose₂.obj (tensorRight ((R.obj V).obj (Opposite.op Y)))).obj <|
      P.compDiagram Q X (unop U)
    map f := (postcompose₂.map { app V := _ ◁ (R.map f).app _ }).app _
  }
  map g := { app _ := (postcompose₂.obj _).map <| P.compDiagramMap _ (𝟙 _) g.unop }

def compDiagram₃Iso : (compDiagram₃ P Q R X Y) ≅
    flipping₃₄₁₂.functor.obj (compDiagram₃' P Q R X Y) :=
  NatIso.ofComponents fun d ↦ NatIso.ofComponents fun d' ↦ NatIso.ofComponents fun e ↦
    NatIso.ofComponents fun e' ↦ (Equiv.prodAssoc _ _ _).symm.toIso

instance (X : Type u) : IsLeftAdjoint (tensorRight X) :=
  Functor.isLeftAdjoint_of_iso (BraidedCategory.tensorLeftIsoTensorRight X)

-- attribute [elementwise] Multicofork.condition
-- attribute [simp] Multicofork.condition_apply

noncomputable def compIso₃ (X : C) (Y : Fᵒᵖ) :
    (postcompose₂.obj chosenCoendFunctor ⋙ chosenCoendFunctor).obj (compDiagram₃' P Q R X Y.unop) ≅
      (((P.comp Q).comp R).obj X).obj Y := by
  refine chosenCoendFunctor.mapIso (NatIso.ofComponents
      (fun e ↦ NatIso.ofComponents (fun e' ↦ ?_) ?_) ?_)
  · refine ((ChosenCoends.isCoend
      (((P.compDiagram₃' Q R X (unop Y)).obj e).obj e'))).coconePointsIsoOfEquivalence
        (isColimitOfPreserves (tensorRight ((R.obj e').obj Y))
          (ChosenCoends.isCoend (P.compDiagram Q X (unop e))))
        Equivalence.refl (NatIso.ofComponents ?_ ?_)
    · rintro (_ | _)
      exacts [Iso.refl _, Iso.refl _]
    · rintro (_ | _) (_ | _) (_ | _ | _)
      all_goals cat_disch
  · cat_disch
  · intro X Y f
    ext : 2
    apply chosenCoend.hom_ext
    intro j
    dsimp
    ext x
    · apply Quot.sound
      convert coendRel.mk (𝟙 j) _
      rotate_right
      · exact (x.1.1, (Q.obj j).map f x.1.2)
      · apply Prod.ext
        · simp; rfl
        · rfl
      · apply Prod.ext
        · simp; rfl
        · simp; rfl
    · rfl

noncomputable def compIso₃' (X : C) (Y : Fᵒᵖ) :
    (postcompose₂.obj chosenCoendFunctor ⋙ chosenCoendFunctor).obj (compDiagram₃ P Q R X Y.unop) ≅
      ((P.comp (Q.comp R)).obj X).obj Y := by
  refine chosenCoendFunctor.mapIso (NatIso.ofComponents
      (fun d ↦ NatIso.ofComponents (fun d' ↦ ?_) ?_) ?_)
  · refine ((ChosenCoends.isCoend
      (((P.compDiagram₃ Q R X (unop Y)).obj d).obj d'))).coconePointsIsoOfEquivalence
        (isColimitOfPreserves (tensorLeft ((P.obj X).obj d))
          (ChosenCoends.isCoend (Q.compDiagram R d' (unop Y))))
        Equivalence.refl (NatIso.ofComponents ?_ ?_)
    · rintro (_ | _)
      exacts [Iso.refl _, Iso.refl _]
    · rintro (_ | _) (_ | _) (_ | _ | _)
      all_goals cat_disch
  · cat_disch
  · intro X Y f
    ext : 2
    apply chosenCoend.hom_ext
    intro j
    dsimp
    ext x
    · rfl
    · apply Quot.sound
      convert coendRel.mk (𝟙 j) _
      rotate_right
      · exact (x.2.1, x.2.2)
      · apply Prod.ext
        · simp; rfl
        · rfl
      · apply Prod.ext
        · rfl
        · simp; rfl

noncomputable def associatorComponents (X : C) (Y : Fᵒᵖ) :
    (P.comp Q |>.comp R |>.obj X |>.obj Y) ≅ P.comp (Q.comp R) |>.obj X |>.obj Y :=
  (compIso₃ P Q R X Y).symm ≪≫ fubini.app (P.compDiagram₃' Q R X (unop Y)) ≪≫
    (_ ⋙ chosenCoendFunctor).mapIso (compDiagram₃Iso P Q R X (unop Y)).symm ≪≫ compIso₃' P Q R X Y


noncomputable def associatorComponents' (X : C) (Y : Fᵒᵖ) :
    (P.comp Q |>.comp R |>.obj X |>.obj Y) ≅ P.comp (Q.comp R) |>.obj X |>.obj Y where
  hom := ↾fun x ↦ Quot.mk _ ⟨x.out.2.1.out.1, x.out.2.1.out.2.1,
      Quot.mk _ ⟨x.out.1, x.out.2.1.out.2.2, x.out.2.2⟩⟩
  inv := ↾fun x ↦ Quot.mk _ ⟨x.out.2.2.out.1,
    Quot.mk _ ⟨x.out.1, x.out.2.1, x.out.2.2.out.2.1⟩, x.out.2.2.out.2.2⟩
  hom_inv_id :=
    sorry
  inv_hom_id :=
    sorry

lemma associatorComponents_apply (X : C) (Y : Fᵒᵖ) (d : D) (e : E)
    (r : (R.obj e).obj Y) (p : (P.obj X).obj (Opposite.op d)) (q : (Q.obj d).obj (Opposite.op e)) :
    (associatorComponents P Q R X Y).hom (Quot.mk _ ⟨e, Quot.mk _ ⟨d, (p, q)⟩, r⟩) =
      Quot.mk _ ⟨d, (p, Quot.mk _ ⟨e, (q, r)⟩)⟩ := by
  sorry
  -- obtain ⟨⟨d', x⟩, h⟩ := Quot.mk_surjective ((associatorComponents P Q R X Y).hom (Quot.mk _ ⟨e, Quot.mk _ ⟨d, (p, q)⟩, r⟩))
  -- rw [← h]
  -- apply Quot.sound
  -- have := coendRel.mk (𝟙 d') x



set_option backward.isDefEq.respectTransparency false in
noncomputable def associator : (P.comp Q).comp R ≅ P.comp (Q.comp R) := by
  refine NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦
    associatorComponents P Q R X Y) ?_) ?_
  · intro f f' g
    ext ⟨e, ⟨d, p, x⟩, r⟩
    dsimp
    erw [associatorComponents_apply, associatorComponents_apply]
    simp [chosenCoend.map_apply, Quot.map]
  · intro f f' g
    ext _ ⟨e, ⟨d, p, x⟩, r⟩
    dsimp
    erw [associatorComponents_apply, associatorComponents_apply]
    simp [chosenCoend.map_apply, Quot.map]

end Associator

end Composition

end Profunctor

end CategoryTheory
