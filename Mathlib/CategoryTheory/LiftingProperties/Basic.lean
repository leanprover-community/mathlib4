/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach, Joël Riou
-/
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Retract

/-!
# Lifting properties

This file defines the lifting property of two morphisms in a category and
shows basic properties of this notion.

## Main results
- `HasLiftingProperty`: the definition of the lifting property

## Tags
lifting property

@TODO :
1) direct/inverse images, adjunctions

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

instance (priority := 100) sq_hasLift_of_hasLiftingProperty {f : A ⟶ X} {g : B ⟶ Y}
    (sq : CommSq f i p g) [hip : HasLiftingProperty i p] : sq.HasLift := hip.sq_hasLift _

namespace HasLiftingProperty

variable {i p}

theorem op (h : HasLiftingProperty i p) : HasLiftingProperty p.op i.op :=
  ⟨fun {f} {g} sq => by
    simp only [CommSq.HasLift.iff_unop, Quiver.Hom.unop_op]
    infer_instance⟩

theorem unop {A B X Y : Cᵒᵖ} {i : A ⟶ B} {p : X ⟶ Y} (h : HasLiftingProperty i p) :
    HasLiftingProperty p.unop i.unop :=
  ⟨fun {f} {g} sq => by
    rw [CommSq.HasLift.iff_op]
    simp only [Quiver.Hom.op_unop]
    infer_instance⟩

theorem iff_op : HasLiftingProperty i p ↔ HasLiftingProperty p.op i.op :=
  ⟨op, unop⟩

theorem iff_unop {A B X Y : Cᵒᵖ} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ HasLiftingProperty p.unop i.unop :=
  ⟨unop, op⟩

variable (i p)

instance (priority := 100) of_left_iso [IsIso i] : HasLiftingProperty i p :=
  ⟨fun {f} {g} sq =>
    CommSq.HasLift.mk'
      { l := inv i ≫ f
        fac_left := by simp only [IsIso.hom_inv_id_assoc]
        fac_right := by simp only [sq.w, assoc, IsIso.inv_hom_id_assoc] }⟩

instance (priority := 100) of_right_iso [IsIso p] : HasLiftingProperty i p :=
  ⟨fun {f} {g} sq =>
    CommSq.HasLift.mk'
      { l := g ≫ inv p
        fac_left := by simp only [← sq.w_assoc, IsIso.hom_inv_id, comp_id]
        fac_right := by simp only [assoc, IsIso.inv_hom_id, comp_id] }⟩

instance of_comp_left [HasLiftingProperty i p] [HasLiftingProperty i' p] :
    HasLiftingProperty (i ≫ i') p :=
  ⟨fun {f} {g} sq => by
    have fac := sq.w
    rw [assoc] at fac
    exact
      CommSq.HasLift.mk'
        { l := (CommSq.mk (CommSq.mk fac).fac_right).lift
          fac_left := by simp only [assoc, CommSq.fac_left]
          fac_right := by simp only [CommSq.fac_right] }⟩

instance of_comp_right [HasLiftingProperty i p] [HasLiftingProperty i p'] :
    HasLiftingProperty i (p ≫ p') :=
  ⟨fun {f} {g} sq => by
    have fac := sq.w
    rw [← assoc] at fac
    let _ := (CommSq.mk (CommSq.mk fac).fac_left.symm).lift
    exact
      CommSq.HasLift.mk'
        { l := (CommSq.mk (CommSq.mk fac).fac_left.symm).lift
          fac_left := by simp only [CommSq.fac_left]
          fac_right := by simp only [CommSq.fac_right_assoc, CommSq.fac_right] }⟩

theorem of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) [hip : HasLiftingProperty i p] :
    HasLiftingProperty i' p := by
  rw [Arrow.iso_w' e]
  infer_instance

theorem of_arrow_iso_right {A B X Y X' Y' : C} (i : A ⟶ B) {p : X ⟶ Y} {p' : X' ⟶ Y'}
    (e : Arrow.mk p ≅ Arrow.mk p') [hip : HasLiftingProperty i p] : HasLiftingProperty i p' := by
  rw [Arrow.iso_w' e]
  infer_instance

theorem iff_of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ HasLiftingProperty i' p := by
  constructor <;> intro
  exacts [of_arrow_iso_left e p, of_arrow_iso_left e.symm p]

theorem iff_of_arrow_iso_right {A B X Y X' Y' : C} (i : A ⟶ B) {p : X ⟶ Y} {p' : X' ⟶ Y'}
    (e : Arrow.mk p ≅ Arrow.mk p') : HasLiftingProperty i p ↔ HasLiftingProperty i p' := by
  constructor <;> intro
  exacts [of_arrow_iso_right i e, of_arrow_iso_right i e.symm]

end HasLiftingProperty

lemma RetractArrow.leftLiftingProperty
    {X Y Z W Z' W' : C} {g : Z ⟶ W} {g' : Z' ⟶ W'}
    (h : RetractArrow g' g) (f : X ⟶ Y) [HasLiftingProperty g f] : HasLiftingProperty g' f where
  sq_hasLift := fun {u v} sq ↦ by
    have sq' : CommSq (h.r.left ≫ u) g f (h.r.right ≫ v) := by simp only [Arrow.mk_left,
      Arrow.mk_right, Category.assoc, sq.w, Arrow.w_mk_right_assoc, Arrow.mk_hom, CommSq.mk]
    exact
      ⟨⟨{ l := h.i.right ≫ sq'.lift
          fac_left := by
            simp only [← h.i_w_assoc, sq'.fac_left, h.retract_left_assoc,
              Arrow.mk_left, Category.id_comp]}⟩⟩

lemma RetractArrow.rightLiftingProperty
    {X Y Z W X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (h : RetractArrow f' f) (g : Z ⟶ W) [HasLiftingProperty g f] : HasLiftingProperty g f' where
  sq_hasLift := fun {u v} sq ↦
    have sq' : CommSq (u ≫ h.i.left) g f (v ≫ h.i.right) :=
      ⟨by rw [← Category.assoc, ← sq.w, Category.assoc, RetractArrow.i_w, Category.assoc]⟩
    ⟨⟨{ l := sq'.lift ≫ h.r.left}⟩⟩

namespace Arrow

/-- Given a morphism `φ : f ⟶ g` in the category `Arrow C`, this is an
abbreviation for the `CommSq.LiftStruct` structure for
the square corresponding to `φ`. -/
abbrev LiftStruct {f g : Arrow C} (φ : f ⟶ g) := (CommSq.mk φ.w).LiftStruct

lemma hasLiftingProperty_iff {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔
      ∀ (φ : Arrow.mk i ⟶ Arrow.mk p), Nonempty (LiftStruct φ) := by
  constructor
  · intro _ φ
    have sq : CommSq φ.left i p φ.right := CommSq.mk φ.w
    exact ⟨{ l := sq.lift }⟩
  · intro h
    exact ⟨fun {f g} sq ↦ ⟨h (Arrow.homMk f g sq.w)⟩⟩

end Arrow

end CategoryTheory
