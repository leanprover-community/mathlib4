/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.GuitartExact.VerticalComposition

/-!
# The opposite of a Guitart exact square

A `2`-square is Guitart exact iff the opposite (transposed) `2`-square
is Guitart exact.

-/

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}

namespace TwoSquare

variable (w : TwoSquare T L R B)

section

variable {X₃ : C₃ᵒᵖ} {X₂ : C₂ᵒᵖ} (g : B.op.obj X₃ ⟶ R.op.obj X₂)

namespace structuredArrowRightwardsOpEquivalence

/-- Auxiliary definition for `structuredArrowRightwardsOpEquivalence`. -/
@[simps!]
def functor :
    (w.op.StructuredArrowRightwards g)ᵒᵖ ⥤
      w.CostructuredArrowDownwards g.unop where
  obj f := CostructuredArrowDownwards.mk _ _ f.unop.right.left.unop
      f.unop.right.hom.unop f.unop.hom.left.unop
      (Quiver.Hom.op_inj (by simpa using CostructuredArrow.w f.unop.hom))
  map {f f'} φ :=
    CostructuredArrow.homMk
      (StructuredArrow.homMk (φ.unop.right.left.unop)
        (Quiver.Hom.op_inj (CostructuredArrow.w φ.unop.right))) (by
          ext
          exact Quiver.Hom.op_inj
            ((CostructuredArrow.proj _ _).congr_map (StructuredArrow.w φ.unop)))

/-- Auxiliary definition for `structuredArrowRightwardsOpEquivalence`. -/
def inverse :
    w.CostructuredArrowDownwards g.unop ⥤
      (w.op.StructuredArrowRightwards g)ᵒᵖ where
  obj f := Opposite.op
    (StructuredArrowRightwards.mk _ _ (Opposite.op f.left.right)
      f.hom.right.op f.left.hom.op (Quiver.Hom.unop_inj (StructuredArrow.w f.hom)))
  map {f f'} φ :=
    (StructuredArrow.homMk
      (CostructuredArrow.homMk (φ.left.right.op)
        (Quiver.Hom.unop_inj (by exact StructuredArrow.w φ.left)))
          (by
            ext
            exact Quiver.Hom.unop_inj
              ((StructuredArrow.proj _ _).congr_map (CostructuredArrow.w φ)))).op

end structuredArrowRightwardsOpEquivalence

/-- If `w : TwoSquare T L R B`, and `g : B.op.obj X₃ ⟶ R.op.obj X₂`, this is
the obvious equivalence of categories between
`(w.op.StructuredArrowRightwards g)ᵒᵖ` and `w.CostructuredArrowDownwards g.unop`. -/
@[simps]
def structuredArrowRightwardsOpEquivalence :
    (w.op.StructuredArrowRightwards g)ᵒᵖ ≌
      w.CostructuredArrowDownwards g.unop where
  functor := structuredArrowRightwardsOpEquivalence.functor w g
  inverse := structuredArrowRightwardsOpEquivalence.inverse w g
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end

instance [w.GuitartExact] : w.op.GuitartExact := by
  rw [guitartExact_iff_isConnected_rightwards]
  intro X₃ X₂ g
  rw [← isConnected_op_iff_isConnected,
    isConnected_iff_of_equivalence (w.structuredArrowRightwardsOpEquivalence g)]
  infer_instance

lemma guitartExact_op_iff : w.op.GuitartExact ↔ w.GuitartExact := by
  constructor
  · intro
    let w₁ : TwoSquare T (opOp C₁) (opOp C₂) T.op.op := 𝟙 _
    let w₂ : TwoSquare B.op.op (unopUnop C₃) (unopUnop C₄) B := 𝟙 _
    have : w = (w₁ ≫ᵥ w.op.op) ≫ᵥ w₂ := by cat_disch
    rw [this]
    infer_instance
  · intro
    infer_instance

instance guitartExact_id' (F : C₁ ⥤ C₂) :
    GuitartExact (TwoSquare.mk F (𝟭 C₁) (𝟭 C₂) F (𝟙 F)) := by
  rw [← guitartExact_op_iff]
  apply guitartExact_id

end TwoSquare

end CategoryTheory
