/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.Trifunctor
public import Mathlib.CategoryTheory.Whiskering
/-!
# Quadrifunctors obtained by composition of multifunctors

Given a bifunctor `F : C₁ ⥤ C₂₃₄ ⥤ E` and a trifunctor
`G : C₂ ⥤ C₃ ⥤ C₄ ⥤ C₂₃₄`, we define the quadrifunctor
`trifunctorComp₂₃₄ F G : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E`.

Similarly, given a trifunctor `F : C₁ ⥤ C₂ ⥤ C₃₄ ⥤ E` and a bifunctor
`G : C₃ ⥤ C₄ ⥤ C₃₄`, we define the quadrifunctor
`trifunctorComp₃₄ F G : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E`.
-/

@[expose] public section

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ C₂₃₄ C₃₄ E : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Category* C₂₃₄] [Category* C₃₄] [Category* E]

section trifunctorComp₂₃₄Functor

set_option backward.defeqAttrib.useBackward true in
/-- Given a bifunctor `F : C₁ ⥤ C₂₃₄ ⥤ E` and a trifunctor
`G : C₂ ⥤ C₃ ⥤ C₄ ⥤ C₂₃₄`, this is the quadrifunctor `C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E`
obtained by composition. -/
@[simps]
def trifunctorComp₂₃₄ (F : C₁ ⥤ C₂₃₄ ⥤ E) (G : C₂ ⥤ C₃ ⥤ C₄ ⥤ C₂₃₄) :
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E where
  obj X₁ := (Functor.postcompose₃.obj (F.obj X₁)).obj G
  map f := (Functor.postcompose₃.map (F.map f)).app G

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `trifunctorComp₂₃₄Functor`. -/
@[simps]
def trifunctorComp₂₃₄FunctorObj (F : C₁ ⥤ C₂₃₄ ⥤ E) :
    (C₂ ⥤ C₃ ⥤ C₄ ⥤ C₂₃₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E where
  obj G := trifunctorComp₂₃₄ F G
  map {G G'} τ :=
    { app X₁ := (Functor.postcompose₃.obj (F.obj X₁)).map τ
      naturality X₁ Y₁ f := by
        ext X₂ X₃ X₄
        change (F.map f).app (((G.obj X₂).obj X₃).obj X₄) ≫
            (F.obj Y₁).map ((((τ.app X₂).app X₃).app X₄)) =
          (F.obj X₁).map ((((τ.app X₂).app X₃).app X₄)) ≫
            (F.map f).app (((G'.obj X₂).obj X₃).obj X₄)
        exact ((F.map f).naturality _).symm }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `trifunctorComp₂₃₄Functor`. -/
@[simps]
def trifunctorComp₂₃₄FunctorMap {F F' : C₁ ⥤ C₂₃₄ ⥤ E} (τ : F ⟶ F') :
    trifunctorComp₂₃₄FunctorObj (C₂ := C₂) (C₃ := C₃) (C₄ := C₄) F ⟶
      trifunctorComp₂₃₄FunctorObj F' where
  app G :=
    { app X₁ := (Functor.postcompose₃.map (τ.app X₁)).app G
      naturality X₁ Y₁ f := by
        ext X₂ X₃ X₄
        exact NatTrans.congr_app (τ.naturality f) (((G.obj X₂).obj X₃).obj X₄) }
  naturality G G' σ := by
    ext X₁ X₂ X₃ X₄
    exact (τ.app X₁).naturality ((((σ.app X₂).app X₃).app X₄))

/-- The functor
`(C₁ ⥤ C₂₃₄ ⥤ E) ⥤ (C₂ ⥤ C₃ ⥤ C₄ ⥤ C₂₃₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E` which
sends `F : C₁ ⥤ C₂₃₄ ⥤ E` and `G : C₂ ⥤ C₃ ⥤ C₄ ⥤ C₂₃₄` to
`trifunctorComp₂₃₄ F G`. -/
@[simps]
def trifunctorComp₂₃₄Functor :
    (C₁ ⥤ C₂₃₄ ⥤ E) ⥤ (C₂ ⥤ C₃ ⥤ C₄ ⥤ C₂₃₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E where
  obj := trifunctorComp₂₃₄FunctorObj
  map := trifunctorComp₂₃₄FunctorMap

end trifunctorComp₂₃₄Functor

section trifunctorComp₃₄Functor

set_option backward.defeqAttrib.useBackward true in
/-- Given a trifunctor `F : C₁ ⥤ C₂ ⥤ C₃₄ ⥤ E` and a bifunctor
`G : C₃ ⥤ C₄ ⥤ C₃₄`, this is the quadrifunctor `C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E`
obtained by composition. -/
@[simps]
def trifunctorComp₃₄ (F : C₁ ⥤ C₂ ⥤ C₃₄ ⥤ E) (G : C₃ ⥤ C₄ ⥤ C₃₄) :
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E where
  obj X₁ := bifunctorComp₂₃ (F.obj X₁) G
  map f := (bifunctorComp₂₃Functor.map (F.map f)).app G

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `trifunctorComp₃₄Functor`. -/
@[simps]
def trifunctorComp₃₄FunctorObj (F : C₁ ⥤ C₂ ⥤ C₃₄ ⥤ E) :
    (C₃ ⥤ C₄ ⥤ C₃₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E where
  obj G := trifunctorComp₃₄ F G
  map {G G'} τ :=
    { app X₁ := (bifunctorComp₂₃Functor.obj (F.obj X₁)).map τ
      naturality X₁ Y₁ f := by
        ext X₂ X₃ X₄
        exact (((F.map f).app X₂).naturality (((τ.app X₃).app X₄))).symm }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `trifunctorComp₃₄Functor`. -/
@[simps]
def trifunctorComp₃₄FunctorMap {F F' : C₁ ⥤ C₂ ⥤ C₃₄ ⥤ E} (τ : F ⟶ F') :
    trifunctorComp₃₄FunctorObj (C₃ := C₃) (C₄ := C₄) F ⟶
      trifunctorComp₃₄FunctorObj F' where
  app G :=
    { app X₁ := (bifunctorComp₂₃Functor.map (τ.app X₁)).app G
      naturality X₁ Y₁ f := by
        ext X₂ X₃ X₄
        exact NatTrans.congr_app (NatTrans.congr_app (τ.naturality f) X₂)
          ((G.obj X₃).obj X₄) }
  naturality G G' σ := by
    ext X₁ X₂ X₃ X₄
    exact ((τ.app X₁).app X₂).naturality (((σ.app X₃).app X₄))

/-- The functor
`(C₁ ⥤ C₂ ⥤ C₃₄ ⥤ E) ⥤ (C₃ ⥤ C₄ ⥤ C₃₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E` which
sends `F : C₁ ⥤ C₂ ⥤ C₃₄ ⥤ E` and `G : C₃ ⥤ C₄ ⥤ C₃₄` to
`trifunctorComp₃₄ F G`. -/
@[simps]
def trifunctorComp₃₄Functor :
    (C₁ ⥤ C₂ ⥤ C₃₄ ⥤ E) ⥤ (C₃ ⥤ C₄ ⥤ C₃₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E where
  obj := trifunctorComp₃₄FunctorObj
  map := trifunctorComp₃₄FunctorMap

end trifunctorComp₃₄Functor

end CategoryTheory
