/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Retract

/-!
# Retracts of 1-morphisms in bicategories

If `f : X ⟶ Y` and `f' : X' ⟶ Y'` are 1-morphisms in a bicategory,
we introduce a structure `RetractArrow₁ f' f` expressing that
`f'` is a retract of `f`, and we show that if `f` is an
equivalence, then `f'` is also an equivalence.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

namespace Bicategory

variable {C : Type u} [Bicategory.{w, v} C] {X Y X' Y' : C}

/-- A structure expressing that a 1-morphism `f' : X' ⟶ Y`'
in a bicategory is a retract of `f : X ⟶ Y`. -/
structure RetractArrow₁ (f' : X' ⟶ Y') (f : X ⟶ Y) where
  /-- the inclusion of the source object -/
  i₁ : X' ⟶ X
  /-- the retraction to the source object -/
  r₁ : X ⟶ X'
  /-- the inclusion of the target object -/
  i₂ : Y' ⟶ Y
  /-- the retraction to the target object -/
  r₂ : Y ⟶ Y'
  /-- the source of `f'` is a retract of the source of `f` -/
  id₁ : i₁ ≫ r₁ ≅ 𝟙 X'
  /-- the target of `f'` is a retract of the target of `f` -/
  id₂ : i₂ ≫ r₂ ≅ 𝟙 Y'
  /-- compatibility of the inclusions -/
  commi : f' ≫ i₂ ≅ i₁ ≫ f
  /-- compatibility of the retractions -/
  commr : f ≫ r₂ ≅ r₁ ≫ f'
  comm : commi.hom ▷ r₂ ≫ (α_ _ _ _).hom ≫ i₁ ◁ commr.hom =
    (α_ _ _ _).hom ≫ f' ◁ id₂.hom ≫ (ρ_ _).hom ≫ (λ_ _).inv ≫
      id₁.inv ▷ f' ≫ (α_ _ _ _).hom := by cat_disch

namespace RetractArrow₁

attribute [reassoc] comm

@[reassoc]
lemma comm' {f' : X' ⟶ Y'} {f : X ⟶ Y} (r : RetractArrow₁ f' f) :
    r.i₁ ◁ r.commr.inv ≫ (α_ _ _ _).inv ≫ r.commi.inv ▷ r.r₂ =
      (α_ _ _ _).inv ≫ r.id₁.hom ▷ f' ≫ (λ_ _).hom ≫ (ρ_ _).inv ≫
        f' ◁ r.id₂.inv ≫ (α_ _ _ _).inv := by
  rw [← cancel_epi (r.i₁ ◁ r.commr.hom),
    ← cancel_epi (α_ _ _ _).hom,
    ← cancel_epi (r.commi.hom ▷ r.r₂)]
  nth_rw 2 [r.comm_assoc]
  simp

/-- If a `1`-morphism is a retract of another, it stays so
after the applicaton of a pseudofunctor. -/
@[implicit_reducible, simps]
def map {f' : X' ⟶ Y'} {f : X ⟶ Y} (r : RetractArrow₁ f' f)
    {D : Type*} [Bicategory D] (F : C ⥤ᵖ D) :
    RetractArrow₁ (F.map f') (F.map f) where
  i₁ := F.map r.i₁
  i₂ := F.map r.i₂
  r₁ := F.map r.r₁
  r₂ := F.map r.r₂
  id₁ := (F.mapComp _ _).symm ≪≫ F.map₂Iso r.id₁ ≪≫ F.mapId _
  id₂ := (F.mapComp _ _).symm ≪≫ F.map₂Iso r.id₂ ≪≫ F.mapId _
  commi := (F.mapComp _ _).symm ≪≫ F.map₂Iso r.commi ≪≫ F.mapComp _ _
  commr := (F.mapComp _ _).symm ≪≫ F.map₂Iso r.commr ≪≫ F.mapComp _ _
  comm := by
    have := congr_arg (fun f ↦ F.map₂ f) r.comm
    simp at this
    simp [← cancel_mono (F.map r.i₁ ◁ (F.mapComp r.r₁ f').inv),
      ← cancel_mono ( (F.mapComp r.i₁ (r.r₁ ≫ f')).inv),
      this, dsimp% F.toLax.map₂_leftUnitor_assoc f']

/-- In a bicategory, if a `1`-morphism is a retract of a left adjoint,
it is also a left adjoint. -/
@[implicit_reducible, simps]
def adjunctionLeft {f' : X' ⟶ Y'} {f : X ⟶ Y} (r : RetractArrow₁ f' f)
    {g : Y ⟶ X} (adj : Adjunction f g) :
    Adjunction f' (r.i₂ ≫ g ≫ r.r₁) where
  unit :=
    r.id₁.inv ≫ _ ◁ (λ_ _).inv ≫ r.i₁ ◁ adj.unit ▷ r.r₁ ≫
      _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫ (r.commi.inv ▷ (g ≫ r.r₁)) ≫ (α_ _ _ _).hom
  counit :=
    (α_ _ _ _).hom ≫ _ ◁ ((α_ _ _ _).hom ≫ _ ◁ r.commr.inv ≫ (α_ _ _ _).inv) ≫
      r.i₂ ◁ adj.counit ▷ r.r₂ ≫ _ ◁ (λ_ _).hom ≫ r.id₂.hom
  left_triangle := by
    calc
      _ = r.id₁.inv ▷ f' ⊗≫ ((r.i₁ ◁ adj.unit ⊗≫ r.commi.inv ▷ g) ▷ (r.r₁ ≫ f') ≫
          ((f' ≫ r.i₂) ≫ g) ◁ r.commr.inv) ⊗≫
          f' ◁ r.i₂ ◁ adj.counit ▷ r.r₂ ⊗≫ f' ◁ r.id₂.hom := by
        bicategory
      _ = r.id₁.inv ▷ f' ⊗≫ r.i₁ ◁ r.commr.inv ⊗≫
          (r.i₁ ◁ adj.unit) ▷ (f ≫ r.r₂) ⊗≫
          ((r.commi.inv ▷ (g ≫ f) ≫ ((f' ≫ r.i₂) ◁ adj.counit)) ▷ r.r₂) ⊗≫
          f' ◁ r.id₂.hom := by
        rw [← whisker_exchange]
        bicategory
      _ = r.id₁.inv ▷ f' ⊗≫ r.i₁ ◁ r.commr.inv ⊗≫
          r.i₁ ◁ (leftZigzag adj.unit adj.counit) ▷ r.r₂ ⊗≫
          (r.commi.inv ▷ r.r₂) ⊗≫ f' ◁ r.id₂.hom := by
        rw [← whisker_exchange]
        bicategory
      _ = r.id₁.inv ▷ f' ⊗≫ r.i₁ ◁ r.commr.inv ⊗≫
          (r.commi.inv ▷ r.r₂) ⊗≫ f' ◁ r.id₂.hom := by
        rw [adj.left_triangle]
        bicategory
      _ = _ := by
        simp [bicategoricalComp, r.comm'_assoc]
  right_triangle := by
    calc
      _ = (r.i₂ ≫ g ≫ r.r₁) ◁ (r.id₁.inv ⊗≫ r.i₁ ◁ adj.unit ▷ r.r₁ ⊗≫
          r.commi.inv ▷ (g ≫ r.r₁)) ⊗≫
          (r.i₂ ◁ g ◁ r.commr.inv ⊗≫ r.i₂ ◁ adj.counit ▷ r.r₂ ⊗≫ r.id₂.hom) ▷
            (r.i₂ ≫ g ≫ r.r₁) := by
        bicategory
      _ = _ := sorry

/-- In a bicategory, a `1`-morphism that is a retract
of an equivalence is an equivalence. -/
@[implicit_reducible, simps]
def equivalence {f' : X' ⟶ Y'} {f : X ≌ Y} (r : RetractArrow₁ f' f.hom) :
    X' ≌ Y' where
  hom := f'
  inv := r.i₂ ≫ f.inv ≫ r.r₁
  unit :=
    r.id₁.symm ≪≫ _ ◁ᵢ (λ_ _).symm ≪≫ r.i₁ ◁ᵢ f.unit ▷ᵢ r.r₁ ≪≫
      _ ◁ᵢ (α_ _ _ _) ≪≫ (α_ _ _ _).symm ≪≫ (r.commi.symm ▷ᵢ (f.inv ≫ r.r₁)) ≪≫ α_ _ _ _
  counit :=
    α_ _ _ _ ≪≫ _ ◁ᵢ (α_ _ _ _ ≪≫ _ ◁ᵢ r.commr.symm ≪≫ (α_ _ _ _).symm) ≪≫
      r.i₂ ◁ᵢ f.counit ▷ᵢ r.r₂ ≪≫ _ ◁ᵢ λ_ _ ≪≫ r.id₂
  left_triangle := by
    ext : 1
    exact (r.adjunctionLeft f.toAdjunction).left_triangle

end RetractArrow₁

end Bicategory

open Bicategory

/-- A retract of morphisms in a category `C` induces a retract of
`1`-morphisms in the bicategory `LocallyDiscrete C`. -/
@[implicit_reducible, simps]
def RetractArrow.toLoc {C : Type*} [Category* C] {X Y X' Y' : C}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} (r : RetractArrow f' f) :
    RetractArrow₁ (Quiver.Hom.toLoc f') (Quiver.Hom.toLoc f) where
  i₁ := Quiver.Hom.toLoc r.i.left
  i₂ := Quiver.Hom.toLoc r.i.right
  r₁ := Quiver.Hom.toLoc r.r.left
  r₂ := Quiver.Hom.toLoc r.r.right
  id₁ := eqToIso (by simp [← Quiver.Hom.comp_toLoc])
  id₂ := eqToIso (by simp [← Quiver.Hom.comp_toLoc])
  commi := eqToIso (by simp [← Quiver.Hom.comp_toLoc])
  commr := eqToIso (by simp [← Quiver.Hom.comp_toLoc])

end CategoryTheory
