/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.GuitartExact.Basic

/-!
# Vertical composition of Guitart exact squares

In this file, we show that the vertical composition of Guitart exact squares
is Guitart exact.

-/

namespace CategoryTheory

open Category

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category D₁] [Category D₂] [Category D₃]

namespace TwoSquare

section WhiskerVertical

variable {T : C₁ ⥤ D₁} {L : C₁ ⥤ C₂} {R : D₁ ⥤ D₂} {B : C₂ ⥤ D₂} (w : TwoSquare T L R B)
  {L' : C₁ ⥤ C₂} {R' : D₁ ⥤ D₂}

/-- Given `w : TwoSquare T L R B`, one may obtain a 2-square `TwoSquare T L' R' B` if we
provide natural transformations `α : L ⟶ L'` and `β : R' ⟶ R`. -/
@[simps!]
def whiskerVertical (α : L ⟶ L') (β : R' ⟶ R) :
    TwoSquare T L' R' B :=
  whiskerLeft _ β ≫ w ≫ whiskerRight α _

namespace GuitartExact

/-- A 2-square stays Guitart exact if we replace the left and right functors
by isomorphic functors. See also `whiskerVertical_iff`. -/
lemma whiskerVertical [w.GuitartExact] (α : L ≅ L') (β : R ≅ R') :
    (w.whiskerVertical α.hom β.inv).GuitartExact := by
  rw [guitartExact_iff_initial]
  intro X₂
  let e : structuredArrowDownwards (w.whiskerVertical α.hom β.inv) X₂ ≅
      w.structuredArrowDownwards X₂ ⋙ (StructuredArrow.mapIso (β.app X₂) ).functor :=
    NatIso.ofComponents (fun f => StructuredArrow.isoMk (α.symm.app f.right) (by
      dsimp
      simp only [NatTrans.naturality_assoc, assoc, NatIso.cancel_natIso_inv_left, ← B.map_comp,
        Iso.hom_inv_id_app, B.map_id, comp_id]))
  rw [Functor.initial_natIso_iff e]
  infer_instance

/-- A 2-square is Guitart exact iff it is so after replacing the left and right functors by
isomorphic functors. -/
@[simp]
lemma whiskerVertical_iff (α : L ≅ L') (β : R ≅ R') :
    (w.whiskerVertical α.hom β.inv).GuitartExact ↔ w.GuitartExact := by
  constructor
  · intro h
    have : w = TwoSquare.whiskerVertical
        (TwoSquare.whiskerVertical w α.hom β.inv) α.inv β.hom := by
      ext X₁
      simp only [Functor.comp_obj, whiskerVertical_app, assoc, Iso.hom_inv_id_app_assoc,
        ← B.map_comp, Iso.hom_inv_id_app, B.map_id, comp_id]
    rw [this]
    exact whiskerVertical (w.whiskerVertical α.hom β.inv) α.symm β.symm
  · intro h
    exact whiskerVertical w α β

instance [w.GuitartExact] (α : L ⟶ L') (β : R' ⟶ R)
    [IsIso α] [IsIso β] : (w.whiskerVertical α β).GuitartExact :=
  whiskerVertical w (asIso α) (asIso β).symm

end GuitartExact

end WhiskerVertical

section VerticalComposition

variable {H₁ : C₁ ⥤ D₁} {L₁ : C₁ ⥤ C₂} {R₁ : D₁ ⥤ D₂} {H₂ : C₂ ⥤ D₂}
  (w : TwoSquare H₁ L₁ R₁ H₂)
  {L₂ : C₂ ⥤ C₃} {R₂ : D₂ ⥤ D₃} {H₃ : C₃ ⥤ D₃}
  (w' : TwoSquare H₂ L₂ R₂ H₃)

/-- The vertical composition of 2-squares. -/
@[simps!]
def vComp : TwoSquare H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ :=
  (Functor.associator _ _ _).inv ≫ whiskerRight w R₂ ≫
    (Functor.associator _ _ _).hom ≫ whiskerLeft L₁ w' ≫ (Functor.associator _ _ _).inv

/-- The canonical isomorphism between
`w.structuredArrowDownwards Y₁ ⋙ w'.structuredArrowDownwards (R₁.obj Y₁)` and
`(w.vComp w').structuredArrowDownwards Y₁.` -/
def structuredArrowDownwardsComp (Y₁ : D₁) :
    w.structuredArrowDownwards Y₁ ⋙ w'.structuredArrowDownwards (R₁.obj Y₁) ≅
      (w.vComp w').structuredArrowDownwards Y₁ :=
  NatIso.ofComponents (fun _ => StructuredArrow.isoMk (Iso.refl _))

/-- The vertical composition of 2-squares. (Variant where we allow the replacement of
the vertical compositions by isomorphic functors.) -/
@[simps!]
def vComp' {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂)
    (eR : R₁ ⋙ R₂ ≅ R₁₂) : TwoSquare H₁ L₁₂ R₁₂ H₃ :=
  (w.vComp w').whiskerVertical eL.hom eR.inv

namespace GuitartExact

instance vComp [hw : w.GuitartExact] [hw' : w'.GuitartExact] :
    (w.vComp w').GuitartExact := by
  simp only [TwoSquare.guitartExact_iff_initial]
  intro Y₁
  rw [← Functor.initial_natIso_iff (structuredArrowDownwardsComp w w' Y₁)]
  infer_instance

instance vComp' [GuitartExact w] [GuitartExact w'] {L₁₂ : C₁ ⥤ C₃}
    {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂)
    (eR : R₁ ⋙ R₂ ≅ R₁₂) : (w.vComp' w' eL eR).GuitartExact := by
  dsimp only [TwoSquare.vComp']
  infer_instance

end GuitartExact

end VerticalComposition

end TwoSquare

end CategoryTheory
