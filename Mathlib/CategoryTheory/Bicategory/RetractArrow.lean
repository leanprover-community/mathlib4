/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# Retracts of 1-morphisms in bicategories

If `f : X ⟶ Y` and `f' : X' ⟶ Y'` are 1-morphisms in a bicategory,
we introduce a structure `RetractArrow₁ f' f` expressing that
`f'` is a retract of `f`, and we show that if `f` is an
equivalence, then `f'` is also an equivalence.

-/

@[expose] public section

universe w v u

namespace CategoryTheory.Bicategory

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
      id₁.inv ▷ f' ≫ (α_ _ _ _).hom

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

/-- In a bicategory, a `1`-morphism that is a retract
of an equivalence is an equivalence. -/
@[implicit_reducible, simps]
def equivalence {f' : X' ⟶ Y'} {f : Equivalence X Y} (r : RetractArrow₁ f' f.hom) :
    Equivalence X' Y' where
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
    calc
      _ = r.id₁.inv ▷ f' ⊗≫ ((r.i₁ ◁ f.unit.hom ⊗≫ r.commi.inv ▷ f.inv) ▷ (r.r₁ ≫ f') ≫
          ((f' ≫ r.i₂) ≫ f.inv) ◁ r.commr.inv) ⊗≫
          f' ◁ r.i₂ ◁ f.counit.hom ▷ r.r₂ ⊗≫ f' ◁ r.id₂.hom := by
        simp only [leftZigzagIso_hom, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
          whiskerRightIso_hom]
        bicategory
      _ = r.id₁.inv ▷ f' ⊗≫ r.i₁ ◁ r.commr.inv ⊗≫
          (r.i₁ ◁ f.unit.hom) ▷ (f.hom ≫ r.r₂) ⊗≫
          ((r.commi.inv ▷ (f.inv ≫ f.hom) ≫ ((f' ≫ r.i₂) ◁ f.counit.hom)) ▷ r.r₂) ⊗≫
          f' ◁ r.id₂.hom := by
        rw [← whisker_exchange]
        bicategory
      _ = r.id₁.inv ▷ f' ⊗≫ r.i₁ ◁ r.commr.inv ⊗≫
          r.i₁ ◁ (leftZigzag f.unit.hom f.counit.hom) ▷ r.r₂ ⊗≫
          (r.commi.inv ▷ r.r₂) ⊗≫ f' ◁ r.id₂.hom := by
        rw [← whisker_exchange]
        bicategory
      _ = r.id₁.inv ▷ f' ⊗≫ r.i₁ ◁ r.commr.inv ⊗≫
          (r.commi.inv ▷ r.r₂) ⊗≫ f' ◁ r.id₂.hom := by
        rw [f.left_triangle_hom]
        bicategory
      _ = _ := by
        simp [bicategoricalComp, r.comm'_assoc]

end RetractArrow₁

end CategoryTheory.Bicategory
