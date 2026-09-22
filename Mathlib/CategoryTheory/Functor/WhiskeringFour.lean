/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Whiskering of functors in four variables

We define simultaneous precomposition (`whiskeringLeft₄`) and postcomposition (`postcompose₄`)
for functors in four variables. Their projection lemmas are not global simp lemmas.
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*} [Category* C₁] [Category* C₂]
  [Category* C₃] [Category* C₄] [Category* D₁] [Category* D₂] [Category* D₃]
  [Category* D₄] (E : Type*) [Category* E]

section

-- The projection lemmas for four-variable whiskering are expensive for the simp linter.
-- Enable them only locally when constructing the auxiliary functors.

/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[implicit_reducible, simps! (attr := local simp) -isSimp]
def whiskeringLeft₄ObjObjObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    (F₃ : C₃ ⥤ D₃) (F₄ : C₄ ⥤ D₄) :
    (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E :=
  (whiskeringRight _ _ _).obj ((((whiskeringLeft₃ E).obj F₂).obj F₃).obj F₄) ⋙
    (whiskeringLeft C₁ D₁ _).obj F₁

/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[implicit_reducible, simps (attr := local simp) -isSimp]
def whiskeringLeft₄ObjObjObjMap (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    (F₃ : C₃ ⥤ D₃) {F₄ F₄' : C₄ ⥤ D₄} (τ₄ : F₄ ⟶ F₄') :
    whiskeringLeft₄ObjObjObjObj E F₁ F₂ F₃ F₄ ⟶
      whiskeringLeft₄ObjObjObjObj E F₁ F₂ F₃ F₄' where
  app F := whiskerLeft _ (whiskerLeft _ ((((whiskeringLeft₃ E).obj F₂).obj F₃).map τ₄))

variable (C₄ D₄) in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[implicit_reducible, simps (attr := local simp) -isSimp]
def whiskeringLeft₄ObjObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃) :
    (C₄ ⥤ D₄) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤
      (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) where
  obj F₄ := whiskeringLeft₄ObjObjObjObj E F₁ F₂ F₃ F₄
  map τ₄ := whiskeringLeft₄ObjObjObjMap E F₁ F₂ F₃ τ₄

variable (C₄ D₄) in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[implicit_reducible, simps (attr := local simp) -isSimp]
def whiskeringLeft₄ObjObjMap (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    {F₃ F₃' : C₃ ⥤ D₃} (τ₃ : F₃ ⟶ F₃') :
    whiskeringLeft₄ObjObjObj C₄ D₄ E F₁ F₂ F₃ ⟶
      whiskeringLeft₄ObjObjObj C₄ D₄ E F₁ F₂ F₃' where
  app F₄ := whiskerRight
    ((whiskeringRight _ _ _).map ((((whiskeringLeft₃ E).obj F₂).map τ₃).app F₄)) _

variable (C₃ C₄ D₃ D₄) in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[implicit_reducible, simps (attr := local simp) -isSimp]
def whiskeringLeft₄ObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) :
    (C₃ ⥤ D₃) ⥤ (C₄ ⥤ D₄) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤
      (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) where
  obj F₃ := whiskeringLeft₄ObjObjObj C₄ D₄ E F₁ F₂ F₃
  map τ₃ := whiskeringLeft₄ObjObjMap C₄ D₄ E F₁ F₂ τ₃

variable (C₃ C₄ D₃ D₄) in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[implicit_reducible, simps (attr := local simp) -isSimp]
def whiskeringLeft₄ObjMap (F₁ : C₁ ⥤ D₁) {F₂ F₂' : C₂ ⥤ D₂} (τ₂ : F₂ ⟶ F₂') :
    whiskeringLeft₄ObjObj C₃ C₄ D₃ D₄ E F₁ F₂ ⟶
      whiskeringLeft₄ObjObj C₃ C₄ D₃ D₄ E F₁ F₂' where
  app F₃ :=
    { app F₄ := whiskerRight
        ((whiskeringRight _ _ _).map ((((whiskeringLeft₃ E).map τ₂).app F₃).app F₄)) _ }

variable (C₂ C₃ C₄ D₂ D₃ D₄) in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[implicit_reducible, simps (attr := local simp) -isSimp]
def whiskeringLeft₄Obj (F₁ : C₁ ⥤ D₁) :
    (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (C₄ ⥤ D₄) ⥤
      (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) where
  obj F₂ := whiskeringLeft₄ObjObj C₃ C₄ D₃ D₄ E F₁ F₂
  map τ₂ := whiskeringLeft₄ObjMap C₃ C₄ D₃ D₄ E F₁ τ₂

variable (C₂ C₃ C₄ D₂ D₃ D₄) in
/-- Auxiliary definition for `whiskeringLeft₄`. -/
@[implicit_reducible, simps (attr := local simp) -isSimp]
def whiskeringLeft₄Map {F₁ F₁' : C₁ ⥤ D₁} (τ₁ : F₁ ⟶ F₁') :
    whiskeringLeft₄Obj C₂ C₃ C₄ D₂ D₃ D₄ E F₁ ⟶
      whiskeringLeft₄Obj C₂ C₃ C₄ D₂ D₃ D₄ E F₁' where
  app F₂ := { app F₃ := { app F₄ := whiskerLeft _ ((whiskeringLeft _ _ _).map τ₁) } }

/-- The obvious functor
`(C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (C₄ ⥤ D₄) ⥤`
`(D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)`. -/
@[simps! -isSimp, implicit_reducible]
def whiskeringLeft₄ :
    (C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (C₄ ⥤ D₄) ⥤
      (D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) where
  obj F₁ := whiskeringLeft₄Obj C₂ C₃ C₄ D₂ D₃ D₄ E F₁
  map τ₁ := whiskeringLeft₄Map C₂ C₃ C₄ D₂ D₃ D₄ E τ₁

end

variable {E}

/-- The "postcomposition" with a functor `E ⥤ E'` gives a functor
`(E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E'`. -/
@[simps! -isSimp, implicit_reducible]
def postcompose₄ {E' : Type*} [Category* E'] :
    (E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E' :=
  whiskeringRight C₄ _ _ ⋙ whiskeringRight C₃ _ _ ⋙ whiskeringRight C₂ _ _ ⋙
    whiskeringRight C₁ _ _

end CategoryTheory.Functor
