/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GuitartExact.Basic

/-!
# External products of Guitart exact squares

In this file, we show that the external product of two Guitart exact
squares is a Guitart exact square.

-/

@[expose] public section

namespace CategoryTheory.TwoSquare

variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
  {T' : D₁ ⥤ D₂} {L' : D₁ ⥤ D₃} {R' : D₂ ⥤ D₄} {B' : D₃ ⥤ D₄}
  (w : TwoSquare T L R B) (w' : TwoSquare T' L' R' B')

namespace StructuredArrowRightwards

namespace prodEquivalence

variable {Y₂ : C₂ × D₂} {Y₃ : C₃ × D₃} (g : (R.prod R').obj Y₂ ⟶ (B.prod B').obj Y₃)

/-- Auxiliary definition for `TwoSquare.StructuredArrowRightwards.prodEquivalence`. -/
@[simps, implicit_reducible]
def functorObj (X : StructuredArrowRightwards (w.prod w') g) :
    (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2) :=
  ⟨StructuredArrowRightwards.mk w g.1 _ X.hom.left.1 X.right.hom.1 (by
      simpa only [Category.comp_id] using! dsimp% congr($(X.hom.w).fst)),
    StructuredArrowRightwards.mk w' g.2 _ X.hom.left.2 X.right.hom.2 (by
      simpa only [Category.comp_id] using! dsimp% congr($(X.hom.w).snd))⟩

/-- Auxiliary definition for `TwoSquare.StructuredArrowRightwards.prodEquivalence`. -/
@[simps!, implicit_reducible]
def functor : StructuredArrowRightwards (w.prod w') g ⥤
    (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2) where
  obj X := functorObj w w' g X
  map f :=
    Prod.mkHom (StructuredArrow.homMk (CostructuredArrow.homMk f.right.left.1) (by
        have := (StructuredArrow.w f).symm
        cat_disch))
      (StructuredArrow.homMk (CostructuredArrow.homMk f.right.left.2) (by
        have := (StructuredArrow.w f).symm
        cat_disch))

/-- Auxiliary definition for `TwoSquare.StructuredArrowRightwards.prodEquivalence`. -/
@[simps!, implicit_reducible]
def inverseObj (X : (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2)) :
  StructuredArrowRightwards (w.prod w') g :=
  StructuredArrowRightwards.mk _ _ ⟨X.1.right.left, X.2.right.left⟩
    ⟨X.1.hom.left, X.2.hom.left⟩ ⟨X.1.right.hom, X.2.right.hom⟩ (by
      dsimp
      ext
      · simpa only [Category.comp_id] using! dsimp% X.1.hom.w
      · simpa only [Category.comp_id] using! dsimp% X.2.hom.w)

/-- Auxiliary definition for `TwoSquare.StructuredArrowRightwards.prodEquivalence`. -/
@[simps, implicit_reducible]
def inverse : (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2) ⥤
    StructuredArrowRightwards (w.prod w') g where
  obj X := inverseObj w w' g X
  map f :=
    StructuredArrow.homMk
      (CostructuredArrow.homMk ⟨f.1.right.left, f.2.right.left⟩) (by
        have := StructuredArrow.w f.1
        have := StructuredArrow.w f.2
        cat_disch)

end prodEquivalence

/-- If `w` and `w'` are two `2`-squares of functors, then the categories
`StructuredArrowRightwards (w.prod w') g` decomposes as a product of two
`StructuredArrowRightwards` for `w` and `w'`. -/
@[simps, implicit_reducible]
def prodEquivalence {Y₂ : C₂ × D₂} {Y₃ : C₃ × D₃} (g : (R.prod R').obj Y₂ ⟶ (B.prod B').obj Y₃) :
    StructuredArrowRightwards (w.prod w') g ≌
      (StructuredArrowRightwards w g.1) × (StructuredArrowRightwards w' g.2) where
  functor := prodEquivalence.functor w w' g
  inverse := prodEquivalence.inverse w w' g
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end StructuredArrowRightwards

instance GuitartExact.prod [w.GuitartExact] [w'.GuitartExact] :
    (w.prod w').GuitartExact := by
  rw [guitartExact_iff_isConnected_rightwards]
  intro Y₂ Y₃ g
  exact isConnected_of_equivalent (StructuredArrowRightwards.prodEquivalence w w' g).symm

end CategoryTheory.TwoSquare
