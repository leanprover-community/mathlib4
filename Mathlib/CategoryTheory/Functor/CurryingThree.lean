/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Functor.Trifunctor
import Mathlib.CategoryTheory.Products.Associator

/-!
# Currying of functors in three variables

We study the equivalence of categories
`currying₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ≌ C₁ × C₂ × C₃ ⥤ E`.

-/

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ C₁₂ C₃ C₂₃ D₁ D₂ D₃ E : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₁₂] [Category C₂₃]
  [Category D₁] [Category D₂] [Category D₃] [Category E]

/-- The equivalence of categories `(C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ≌ C₁ × C₂ × C₃ ⥤ E`
given by the curryfication of functors in three variables. -/
def currying₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ≌ C₁ × C₂ × C₃ ⥤ E :=
  currying.trans (currying.trans (prod.associativity C₁ C₂ C₃).congrLeft)

/-- Uncurrying a functor in three variables. -/
abbrev uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ × C₂ × C₃ ⥤ E := currying₃.functor

/-- Currying a functor in three variables. -/
abbrev curry₃ : (C₁ × C₂ × C₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E := currying₃.inverse

/-- Uncurrying functors in three variables gives a fully faithful functor. -/
def fullyFaithfulUncurry₃ :
    (uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₁ × C₂ × C₃ ⥤ E)).FullyFaithful :=
  currying₃.fullyFaithfulFunctor

@[simp]
lemma curry₃_obj_map_app_app (F : C₁ × C₂ × C₃ ⥤ E)
    {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) (X₂ : C₂) (X₃ : C₃) :
    (((curry₃.obj F).map f).app X₂).app X₃ = F.map ⟨f, 𝟙 X₂, 𝟙 X₃⟩ := rfl

@[simp]
lemma curry₃_obj_obj_map_app (F : C₁ × C₂ × C₃ ⥤ E)
    (X₁ : C₁) {X₂ Y₂ : C₂} (f : X₂ ⟶ Y₂) (X₃ : C₃) :
    (((curry₃.obj F).obj X₁).map f).app X₃ = F.map ⟨𝟙 X₁, f, 𝟙 X₃⟩ := rfl

@[simp]
lemma curry₃_obj_obj_obj_map (F : C₁ × C₂ × C₃ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) {X₃ Y₃ : C₃} (f : X₃ ⟶ Y₃) :
    (((curry₃.obj F).obj X₁).obj X₂).map f = F.map ⟨𝟙 X₁, 𝟙 X₂, f⟩ := rfl

@[simp]
lemma curry₃_map_app_app_app {F G : C₁ × C₂ × C₃ ⥤ E} (f : F ⟶ G)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((curry₃.map f).app X₁).app X₂).app X₃ = f.app ⟨X₁, X₂, X₃⟩ := rfl

@[simp]
lemma currying₃_unitIso_hom_app_app_app_app (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((currying₃.unitIso.hom.app F).app X₁).app X₂).app X₃ = 𝟙 _ := by
  simp [currying₃, Equivalence.unit]

@[simp]
lemma currying₃_unitIso_inv_app_app_app_app (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((currying₃.unitIso.inv.app F).app X₁).app X₂).app X₃ = 𝟙 _ := by
  simp [currying₃, Equivalence.unitInv]

/-- Given functors `F₁ : C₁ ⥤ D₁`, `F₂ : C₂ ⥤ D₂`, `F₃ : C₃ ⥤ D₃`
and `G : D₁ × D₂ × D₃ ⥤ E`, this is the isomorphism between
`curry₃.obj (F₁.prod (F₂.prod F₃) ⋙ G) : C₁ ⥤ C₂ ⥤ C₃ ⥤ E`
and `F₁ ⋙ curry₃.obj G ⋙ ((whiskeringLeft₂ E).obj F₂).obj F₃`. -/
@[simps!]
def curry₃ObjProdComp (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃) (G : D₁ × D₂ × D₃ ⥤ E) :
    curry₃.obj (F₁.prod (F₂.prod F₃) ⋙ G) ≅
      F₁ ⋙ curry₃.obj G ⋙ ((whiskeringLeft₂ E).obj F₂).obj F₃ :=
  NatIso.ofComponents
    (fun X₁ ↦ NatIso.ofComponents
      (fun X₂ ↦ NatIso.ofComponents (fun X₃ ↦ Iso.refl _)))

/-- `bifunctorComp₁₂` can be described in terms of the curryfication of functors. -/
@[simps!]
def bifunctorComp₁₂Iso (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ E) :
    bifunctorComp₁₂ F₁₂ G ≅ curry.obj (uncurry.obj F₁₂ ⋙ G) :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _))

/-- `bifunctorComp₂₃` can be described in terms of the curryfication of functors. -/
@[simps!]
def bifunctorComp₂₃Iso (F : C₁ ⥤ C₂₃ ⥤ E) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃) :
    bifunctorComp₂₃ F G₂₃ ≅
    curry.obj (curry.obj (prod.associator _ _ _ ⋙
      uncurry.obj (uncurry.obj G₂₃ ⋙ F.flip).flip)) :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦
    NatIso.ofComponents (fun _ ↦ Iso.refl _)))

/--
Flip the first and third arguments in a trifunctor.
-/
@[simps!]
def flip₁₃ (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) : C₃ ⥤ C₂ ⥤ C₁ ⥤ E where
  obj G := {
    obj H := {
      obj K := ((F.obj K).obj H).obj G
      map f := ((F.map f).app _).app _ }
    map g := { app X := ((F.obj X).map g).app _ } }
  map h := { app X := { app Y := ((F.obj Y).obj X).map h } }

/--
Flip the first and third arguments in a trifunctor, as a functor.
-/
@[simps!]
def flip₁₃Functor : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₃ ⥤ C₂ ⥤ C₁ ⥤ E) where
  obj F := F.flip₁₃
  map f := {
    app X := {
      app Y := {
        app Z := ((f.app _).app _).app _
        naturality _ _ g := by
          simp [← NatTrans.comp_app] } } }

/--
Flip the second and third arguments in a trifunctor.
-/
@[simps!]
def flip₂₃ (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) : C₁ ⥤ C₃ ⥤ C₂ ⥤ E where
  obj G := (F.obj G).flip
  map f := (flipFunctor _ _ _).map (F.map f)

/--
Flip the second and third arguments in a trifunctor, as a functor.
-/
@[simps!]
def flip₂₃Functor : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₁ ⥤ C₃ ⥤ C₂ ⥤ E) where
  obj F := F.flip₂₃
  map f := {
    app X := {
      app Y := {
        app Z := ((f.app _).app _).app _
        naturality _ _ g := by
          simp [← NatTrans.comp_app] } }
    naturality _ _ g := by
      ext
      simp only [flip₂₃_obj_obj_obj, NatTrans.comp_app, flip₂₃_map_app_app]
      simp [← NatTrans.comp_app] }

end Functor

end CategoryTheory
