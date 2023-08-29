/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach, Joël Riou
-/
import Mathlib.CategoryTheory.CommSq

#align_import category_theory.lifting_properties.basic from "leanprover-community/mathlib"@"32253a1a1071173b33dc7d6a218cf722c6feb514"

/-!
# Lifting properties

This file defines the lifting property of two morphisms in a category and
shows basic properties of this notion.

## Main results
- `HasLiftingProperty`: the definition of the lifting property

## Tags
lifting property

@TODO :
1) define llp/rlp with respect to a `morphism_property`
2) retracts, direct/inverse images, (co)products, adjunctions

-/


universe v

namespace CategoryTheory

open Category

variable {C : Type*} [Category C] {A B B' X Y Y' : C} (i : A ⟶ B) (i' : B ⟶ B') (p : X ⟶ Y)
  (p' : Y ⟶ Y')

/-- `HasLiftingProperty i p` means that `i` has the left lifting
property with respect to `p`, or equivalently that `p` has
the right lifting property with respect to `i`. -/
class HasLiftingProperty : Prop where
  /-- Unique field expressing that any commutative square built from `f` and `g` has a lift -/
  sq_hasLift : ∀ {f : A ⟶ X} {g : B ⟶ Y} (sq : CommSq f i p g), sq.HasLift
#align category_theory.has_lifting_property CategoryTheory.HasLiftingProperty
#align category_theory.has_lifting_property.sq_has_lift CategoryTheory.HasLiftingProperty.sq_hasLift

instance (priority := 100) sq_hasLift_of_hasLiftingProperty {f : A ⟶ X} {g : B ⟶ Y}
    (sq : CommSq f i p g) [hip : HasLiftingProperty i p] : sq.HasLift := by apply hip.sq_hasLift
                                                                            -- 🎉 no goals
#align category_theory.sq_has_lift_of_has_lifting_property CategoryTheory.sq_hasLift_of_hasLiftingProperty

namespace HasLiftingProperty

variable {i p}

theorem op (h : HasLiftingProperty i p) : HasLiftingProperty p.op i.op :=
  ⟨fun {f} {g} sq => by
    simp only [CommSq.HasLift.iff_unop, Quiver.Hom.unop_op]
    -- ⊢ CommSq.HasLift (_ : CommSq g.unop i p f.unop)
    infer_instance⟩
    -- 🎉 no goals
#align category_theory.has_lifting_property.op CategoryTheory.HasLiftingProperty.op

theorem unop {A B X Y : Cᵒᵖ} {i : A ⟶ B} {p : X ⟶ Y} (h : HasLiftingProperty i p) :
    HasLiftingProperty p.unop i.unop :=
  ⟨fun {f} {g} sq => by
    rw [CommSq.HasLift.iff_op]
    -- ⊢ CommSq.HasLift (_ : CommSq g.op i.unop.op p.unop.op f.op)
    simp only [Quiver.Hom.op_unop]
    -- ⊢ CommSq.HasLift (_ : CommSq g.op i p f.op)
    infer_instance⟩
    -- 🎉 no goals
#align category_theory.has_lifting_property.unop CategoryTheory.HasLiftingProperty.unop

theorem iff_op : HasLiftingProperty i p ↔ HasLiftingProperty p.op i.op :=
  ⟨op, unop⟩
#align category_theory.has_lifting_property.iff_op CategoryTheory.HasLiftingProperty.iff_op

theorem iff_unop {A B X Y : Cᵒᵖ} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ HasLiftingProperty p.unop i.unop :=
  ⟨unop, op⟩
#align category_theory.has_lifting_property.iff_unop CategoryTheory.HasLiftingProperty.iff_unop

variable (i p)

instance (priority := 100) of_left_iso [IsIso i] : HasLiftingProperty i p :=
  ⟨fun {f} {g} sq =>
    CommSq.HasLift.mk'
      { l := inv i ≫ f
        fac_left := by simp only [IsIso.hom_inv_id_assoc]
                       -- 🎉 no goals
        fac_right := by simp only [sq.w, assoc, IsIso.inv_hom_id_assoc] }⟩
                        -- 🎉 no goals
#align category_theory.has_lifting_property.of_left_iso CategoryTheory.HasLiftingProperty.of_left_iso

instance (priority := 100) of_right_iso [IsIso p] : HasLiftingProperty i p :=
  ⟨fun {f} {g} sq =>
    CommSq.HasLift.mk'
      { l := g ≫ inv p
        fac_left := by simp only [← sq.w_assoc, IsIso.hom_inv_id, comp_id]
                       -- 🎉 no goals
        fac_right := by simp only [assoc, IsIso.inv_hom_id, comp_id] }⟩
                        -- 🎉 no goals
#align category_theory.has_lifting_property.of_right_iso CategoryTheory.HasLiftingProperty.of_right_iso

instance of_comp_left [HasLiftingProperty i p] [HasLiftingProperty i' p] :
    HasLiftingProperty (i ≫ i') p :=
  ⟨fun {f} {g} sq => by
    have fac := sq.w
    -- ⊢ CommSq.HasLift sq
    rw [assoc] at fac
    -- ⊢ CommSq.HasLift sq
    exact
      CommSq.HasLift.mk'
        { l := (CommSq.mk (CommSq.mk fac).fac_right).lift
          fac_left := by simp only [assoc, CommSq.fac_left]
          fac_right := by simp only [CommSq.fac_right] }⟩
#align category_theory.has_lifting_property.of_comp_left CategoryTheory.HasLiftingProperty.of_comp_left

instance of_comp_right [HasLiftingProperty i p] [HasLiftingProperty i p'] :
    HasLiftingProperty i (p ≫ p') :=
  ⟨fun {f} {g} sq => by
    have fac := sq.w
    -- ⊢ CommSq.HasLift sq
    rw [← assoc] at fac
    -- ⊢ CommSq.HasLift sq
    let _ := (CommSq.mk (CommSq.mk fac).fac_left.symm).lift
    -- ⊢ CommSq.HasLift sq
    exact
      CommSq.HasLift.mk'
        { l := (CommSq.mk (CommSq.mk fac).fac_left.symm).lift
          fac_left := by simp only [CommSq.fac_left]
          fac_right := by simp only [CommSq.fac_right_assoc, CommSq.fac_right] }⟩
#align category_theory.has_lifting_property.of_comp_right CategoryTheory.HasLiftingProperty.of_comp_right

theorem of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) [hip : HasLiftingProperty i p] :
    HasLiftingProperty i' p := by
  rw [Arrow.iso_w' e]
  -- ⊢ HasLiftingProperty (e.inv.left ≫ i ≫ e.hom.right) p
  infer_instance
  -- 🎉 no goals
#align category_theory.has_lifting_property.of_arrow_iso_left CategoryTheory.HasLiftingProperty.of_arrow_iso_left

theorem of_arrow_iso_right {A B X Y X' Y' : C} (i : A ⟶ B) {p : X ⟶ Y} {p' : X' ⟶ Y'}
    (e : Arrow.mk p ≅ Arrow.mk p') [hip : HasLiftingProperty i p] : HasLiftingProperty i p' := by
  rw [Arrow.iso_w' e]
  -- ⊢ HasLiftingProperty i (e.inv.left ≫ p ≫ e.hom.right)
  infer_instance
  -- 🎉 no goals
#align category_theory.has_lifting_property.of_arrow_iso_right CategoryTheory.HasLiftingProperty.of_arrow_iso_right

theorem iff_of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ HasLiftingProperty i' p := by
  constructor <;> intro
  -- ⊢ HasLiftingProperty i p → HasLiftingProperty i' p
                  -- ⊢ HasLiftingProperty i' p
                  -- ⊢ HasLiftingProperty i p
  exacts [of_arrow_iso_left e p, of_arrow_iso_left e.symm p]
  -- 🎉 no goals
#align category_theory.has_lifting_property.iff_of_arrow_iso_left CategoryTheory.HasLiftingProperty.iff_of_arrow_iso_left

theorem iff_of_arrow_iso_right {A B X Y X' Y' : C} (i : A ⟶ B) {p : X ⟶ Y} {p' : X' ⟶ Y'}
    (e : Arrow.mk p ≅ Arrow.mk p') : HasLiftingProperty i p ↔ HasLiftingProperty i p' := by
  constructor <;> intro
  -- ⊢ HasLiftingProperty i p → HasLiftingProperty i p'
                  -- ⊢ HasLiftingProperty i p'
                  -- ⊢ HasLiftingProperty i p
  exacts [of_arrow_iso_right i e, of_arrow_iso_right i e.symm]
  -- 🎉 no goals
#align category_theory.has_lifting_property.iff_of_arrow_iso_right CategoryTheory.HasLiftingProperty.iff_of_arrow_iso_right

end HasLiftingProperty

end CategoryTheory
