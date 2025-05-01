/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Trifunctor
import Mathlib.CategoryTheory.Functor.CurryingThree
import Mathlib.CategoryTheory.Whiskering

/-!
# Quatrifunctors

-/

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ C₁₂₃ C₂₃₄ C D₁ D₂ D₃ D₄ E : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₁₂₃]
  [Category C₄] [Category C₂₃₄] [Category C]
  [Category D₁] [Category D₂] [Category D₃] [Category D₄] [Category E]

@[simps!]
def trifunctorComp₁₂₃ (F₁₂₃ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₁₂₃) (G : C₁₂₃ ⥤ C₄ ⥤ C) :
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ C :=
  (Functor.postcompose₃.obj G).obj F₁₂₃

@[simps!]
def trifunctorComp₂₃₄ (F : C₁ ⥤ C₂₃₄ ⥤ C) (G₂₃₄ : C₂ ⥤ C₃ ⥤ C₄ ⥤ C₂₃₄) :
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ C :=
  (F ⋙ Functor.postcompose₃).flip.obj G₂₃₄

variable (E)

/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[simps!]
def whiskeringLeft₄ObjObjObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃) (F₄ : C₄ ⥤ D₄) :
    (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E :=
  (whiskeringRight _ _ _).obj ((((whiskeringLeft₃ E).obj F₂).obj F₃).obj F₄) ⋙
    (whiskeringLeft C₁ D₁ _).obj F₁

/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[simps]
def whiskeringLeft₄ObjObjObjMap (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃)
    {F₄ F₄' : C₄ ⥤ D₄} (τ₄ : F₄ ⟶ F₄') :
    whiskeringLeft₄ObjObjObjObj E F₁ F₂ F₃ F₄ ⟶
      whiskeringLeft₄ObjObjObjObj E F₁ F₂ F₃ F₄' where
  app F := whiskerLeft _ (whiskerLeft _ ((((whiskeringLeft₃ E).obj F₂).obj F₃).map τ₄))

variable (C₄ D₄) in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[simps]
def whiskeringLeft₄ObjObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃) :
    (C₄ ⥤ D₄) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) where
  obj F₄ := whiskeringLeft₄ObjObjObjObj E F₁ F₂ F₃ F₄
  map τ₄ := whiskeringLeft₄ObjObjObjMap E F₁ F₂ F₃ τ₄

variable (C₄ D₄) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[simps]
def whiskeringLeft₄ObjObjMap (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) {F₃ F₃' : C₃ ⥤ D₃} (τ₃ : F₃ ⟶ F₃') :
    whiskeringLeft₄ObjObjObj C₄ D₄ E F₁ F₂ F₃ ⟶ whiskeringLeft₄ObjObjObj C₄ D₄ E F₁ F₂ F₃' where
  app F₄ := whiskerRight ((whiskeringRight _ _ _).map
    ((((whiskeringLeft₃ E).obj F₂).map τ₃).app F₄)) _

variable (C₃ C₄ D₃ D₄) in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[simps]
def whiskeringLeft₄ObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) :
    (C₃ ⥤ D₃) ⥤ (C₄ ⥤ D₄) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) where
  obj F₃ := whiskeringLeft₄ObjObjObj C₄ D₄ E F₁ F₂ F₃
  map τ₃ := whiskeringLeft₄ObjObjMap C₄ D₄ E F₁ F₂ τ₃

variable (C₃ C₄ D₃ D₄) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[simps]
def whiskeringLeft₄ObjMap (F₁ : C₁ ⥤ D₁) {F₂ F₂' : C₂ ⥤ D₂} (τ₂ : F₂ ⟶ F₂') :
    whiskeringLeft₄ObjObj C₃ C₄ D₃ D₄ E F₁ F₂ ⟶ whiskeringLeft₄ObjObj C₃ C₄ D₃ D₄ E F₁ F₂' where
  app F₃ :=
    { app F₄ := whiskerRight ((whiskeringRight _ _ _).map
        ((((whiskeringLeft₃ E).map τ₂).app F₃).app F₄)) _ }
  naturality F₃ F₃' τ₃ := by
    ext F₄ G X₁ X₂ X₃ X₄
    exact congr_app (((G.obj (F₁.obj X₁)).map (τ₂.app X₂)).naturality (τ₃.app X₃)) (F₄.obj X₄)

variable (C₂ C₃ C₄ D₂ D₃ D₄) in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[simps]
def whiskeringLeft₄Obj (F₁ : C₁ ⥤ D₁) :
    (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (C₄ ⥤ D₄) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) where
  obj F₂ := whiskeringLeft₄ObjObj C₃ C₄ D₃ D₄ E F₁ F₂
  map τ₂ := whiskeringLeft₄ObjMap C₃ C₄ D₃ D₄ E F₁ τ₂

set_option maxHeartbeats 800000 in
-- this is slow
variable (C₂ C₃ C₄ D₂ D₃ D₄) in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[simps]
def whiskeringLeft₄Map {F₁ F₁' : C₁ ⥤ D₁} (τ₁ : F₁ ⟶ F₁') :
    whiskeringLeft₄Obj C₂ C₃ C₄ D₂ D₃ D₄ E F₁ ⟶ whiskeringLeft₄Obj C₂ C₃ C₄ D₂ D₃ D₄ E F₁' where
  app F₂ :=
    { app F₃ :=
      { app F₄ := whiskerLeft _ ((whiskeringLeft _ _ _).map τ₁)
        naturality _ _ _ := by
          ext
          dsimp
          simp only [NatTrans.naturality] }
      naturality F₃ F₃' τ₃ := by
        ext F₄ G X₁ X₂ X₃ X₄
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality] }
  naturality F₂ F₂' τ₂ := by
    ext F₃ F₄ G X₁ X₂ X₃ X₄
    dsimp
    simp only [← NatTrans.comp_app, NatTrans.naturality]

/-- The obvious functor
`(C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (C₄ ⥤ D₄) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)`.
-/
@[simps!]
def whiskeringLeft₄ :
    (C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (C₄ ⥤ D₄) ⥤
    (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) where
  obj F₁ := whiskeringLeft₄Obj C₂ C₃ C₄ D₂ D₃ D₄ E F₁
  map τ₁ := whiskeringLeft₄Map C₂ C₃ C₄ D₂ D₃ D₄ E τ₁

variable {E}

/-- The equivalence of categories `(C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ≌ C₁ × C₂ × C₃ × C₄ ⥤ E`
given by the curryfication of functors in four variables. -/
def currying₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ≌ (C₁ × C₂ × C₃ × C₄ ⥤ E) :=
  currying.trans (currying₃.trans ((prod.associativity C₁ C₂ (C₃ × C₄)).congrLeft))

/-- Uncurrying a functor in four variables. -/
abbrev uncurry₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ⥤ C₁ × C₂ × C₃ × C₄ ⥤ E := currying₄.functor

/-- Currying a functor in four variables. -/
abbrev curry₄ : (C₁ × C₂ × C₃ × C₄ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E := currying₄.inverse

/-- Uncurrying functors in four variables gives a fully faithful functor. -/
def fullyFaithfulUncurry₄ :
    (uncurry₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ⥤ (C₁ × C₂ × C₃ × C₄ ⥤ E)).FullyFaithful :=
  currying₄.fullyFaithfulFunctor

@[simp]
lemma curry₄_obj_map_app_app_app (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄):
    ((((curry₄.obj F).map f).app X₂).app X₃).app X₄ = F.map ⟨f, 𝟙 X₂, 𝟙 X₃, 𝟙 X₄⟩ := rfl

@[simp]
lemma curry₄_obj_obj_map_app_app (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    (X₁ : C₁) {X₂ Y₂ : C₂} (f : X₂ ⟶ Y₂) (X₃ : C₃) (X₄ : C₄) :
    ((((curry₄.obj F).obj X₁).map f).app X₃).app X₄ = F.map ⟨𝟙 X₁, f, 𝟙 X₃, 𝟙 X₄⟩ := rfl

@[simp]
lemma curry₄_obj_obj_obj_map_app (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) {X₃ Y₃ : C₃} (f : X₃ ⟶ Y₃) (X₄ : C₄) :
    ((((curry₄.obj F).obj X₁).obj X₂).map f).app X₄ = F.map ⟨𝟙 X₁, 𝟙 X₂, f, 𝟙 X₄⟩ := rfl

@[simp]
lemma curry₄_obj_obj_obj_obj_map (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) {X₄ Y₄ : C₄} (f : X₄ ⟶ Y₄) :
    ((((curry₄.obj F).obj X₁).obj X₂).obj X₃).map f = F.map ⟨𝟙 X₁, 𝟙 X₂, 𝟙 X₃, f⟩ := rfl

@[simp]
lemma curry₄_map_app_app_app_app {F G : C₁ × C₂ × C₃ × C₄ ⥤ E} (f : F ⟶ G)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((curry₄.map f).app X₁).app X₂).app X₃).app X₄ = f.app ⟨X₁, X₂, X₃, X₄⟩ := rfl

@[simp]
lemma uncurry₄_obj_map (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) {X Y : C₁ × C₂ × C₃ × C₄} (f : X ⟶ Y) :
    (uncurry₄.obj F).map f =
      (((((F.map f.1).app X.2.1).app X.2.2.1).app X.2.2.2 ≫
        (((F.obj Y.1).map f.2.1).app X.2.2.1).app X.2.2.2) ≫
          (((F.obj Y.1).obj Y.2.1).map f.2.2.1).app X.2.2.2) ≫
          (((F.obj Y.1).obj Y.2.1).obj Y.2.2.1).map f.2.2.2 := by
  rfl

@[simp]
lemma uncurry₄_map_app {F G : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E} (f : F ⟶ G) (X : C₁ × C₂ × C₃ × C₄) :
    (uncurry₄.map f).app X = (((f.app X.1).app X.2.1).app X.2.2.1).app X.2.2.2 := by
  rfl

end CategoryTheory
