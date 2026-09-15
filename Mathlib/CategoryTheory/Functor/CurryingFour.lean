/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.CurryingThree
public import Mathlib.CategoryTheory.Functor.Quadrifunctor
public import Mathlib.CategoryTheory.Products.Associator

/-!
# Currying of functors in four variables

We study the equivalence of categories
`currying₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ≌ C₁ × C₂ × C₃ × C₄ ⥤ E`.
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ E : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄] [Category* E]

/-- The equivalence of categories `(C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ≌ C₁ × C₂ × C₃ × C₄ ⥤ E`
given by the curryfication of functors in four variables. -/
def currying₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ≌ C₁ × C₂ × C₃ × C₄ ⥤ E :=
  currying.trans (currying.trans (currying.trans
    (((prod.associativity (C₁ × C₂) C₃ C₄).trans
      (prod.associativity C₁ C₂ (C₃ × C₄))).congrLeft)))

/-- Uncurrying a functor in four variables. -/
abbrev uncurry₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ⥤ C₁ × C₂ × C₃ × C₄ ⥤ E :=
  currying₄.functor

/-- Currying a functor in four variables. -/
abbrev curry₄ : (C₁ × C₂ × C₃ × C₄ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E :=
  currying₄.inverse

/-- Uncurrying functors in four variables gives a fully faithful functor. -/
def fullyFaithfulUncurry₄ :
    (uncurry₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ⥤ (C₁ × C₂ × C₃ × C₄ ⥤ E)).FullyFaithful :=
  currying₄.fullyFaithfulFunctor

/-- Currying functors in four variables gives a fully faithful functor. -/
def fullyFaithfulCurry₄ :
    (curry₄ : (C₁ × C₂ × C₃ × C₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)).FullyFaithful :=
  currying₄.fullyFaithfulInverse

instance : (uncurry₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ⥤
    C₁ × C₂ × C₃ × C₄ ⥤ E).Full :=
  fullyFaithfulUncurry₄.full

instance : (uncurry₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ⥤
    C₁ × C₂ × C₃ × C₄ ⥤ E).Faithful :=
  fullyFaithfulUncurry₄.faithful

instance : (curry₄ : (C₁ × C₂ × C₃ × C₄ ⥤ E) ⥤
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E).Full :=
  fullyFaithfulCurry₄.full

instance : (curry₄ : (C₁ × C₂ × C₃ × C₄ ⥤ E) ⥤
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E).Faithful :=
  fullyFaithfulCurry₄.faithful

@[simp]
lemma curry₄_obj_map_app_app_app (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((curry₄.obj F).map f).app X₂).app X₃).app X₄ =
      F.map ⟨f, 𝟙 X₂, 𝟙 X₃, 𝟙 X₄⟩ := rfl

@[simp]
lemma curry₄_obj_obj_map_app_app (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    (X₁ : C₁) {X₂ Y₂ : C₂} (f : X₂ ⟶ Y₂) (X₃ : C₃) (X₄ : C₄) :
    ((((curry₄.obj F).obj X₁).map f).app X₃).app X₄ =
      F.map ⟨𝟙 X₁, f, 𝟙 X₃, 𝟙 X₄⟩ := rfl

@[simp]
lemma curry₄_obj_obj_obj_map_app (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) {X₃ Y₃ : C₃} (f : X₃ ⟶ Y₃) (X₄ : C₄) :
    ((((curry₄.obj F).obj X₁).obj X₂).map f).app X₄ =
      F.map ⟨𝟙 X₁, 𝟙 X₂, f, 𝟙 X₄⟩ := rfl

@[simp]
lemma curry₄_obj_obj_obj_obj_map (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) {X₄ Y₄ : C₄} (f : X₄ ⟶ Y₄) :
    ((((curry₄.obj F).obj X₁).obj X₂).obj X₃).map f =
      F.map ⟨𝟙 X₁, 𝟙 X₂, 𝟙 X₃, f⟩ := rfl

@[simp]
lemma curry₄_map_app_app_app_app {F G : C₁ × C₂ × C₃ × C₄ ⥤ E} (f : F ⟶ G)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((curry₄.map f).app X₁).app X₂).app X₃).app X₄ = f.app ⟨X₁, X₂, X₃, X₄⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma currying₄_unitIso_hom_app_app_app_app_app (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((currying₄.unitIso.hom.app F).app X₁).app X₂).app X₃).app X₄ = 𝟙 _ := by
  simp [currying₄, Equivalence.unit]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma currying₄_unitIso_inv_app_app_app_app_app (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((currying₄.unitIso.inv.app F).app X₁).app X₂).app X₃).app X₄ = 𝟙 _ := by
  simp [currying₄, Equivalence.unitInv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given functors `F₁ : C₁ ⥤ D₁`, `F₂ : C₂ ⥤ D₂`, `F₃ : C₃ ⥤ D₃`,
`F₄ : C₄ ⥤ D₄` and `G : D₁ × D₂ × D₃ × D₄ ⥤ E`, this is the isomorphism between
`curry₄.obj (F₁.prod (F₂.prod (F₃.prod F₄)) ⋙ G) : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E`
and `F₁ ⋙ curry₄.obj G ⋙ ((((whiskeringLeft₃ E).obj F₂).obj F₃).obj F₄)`. -/
@[simps!]
def curry₄ObjProdComp (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃)
    (F₄ : C₄ ⥤ D₄) (G : D₁ × D₂ × D₃ × D₄ ⥤ E) :
    curry₄.obj (F₁.prod (F₂.prod (F₃.prod F₄)) ⋙ G) ≅
      F₁ ⋙ curry₄.obj G ⋙ ((((whiskeringLeft₃ E).obj F₂).obj F₃).obj F₄) :=
  NatIso.ofComponents
    (fun X₁ ↦ NatIso.ofComponents
      (fun X₂ ↦ NatIso.ofComponents
        (fun X₃ ↦ NatIso.ofComponents (fun X₄ ↦ Iso.refl _))))

end Functor
end CategoryTheory
