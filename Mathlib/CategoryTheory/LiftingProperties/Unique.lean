/-
Copyright (c) 2026 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Unique and at-most-one lifting properties

For `i : A ⟶ B` and `p : X ⟶ Y`, a commutative square from `i` to `p` may have at least one
lift (`HasLiftingProperty`), at most one (`HasAtMostOneLiftingProperty`, expressed
as `Subsingleton sq.LiftStruct`), or exactly one (`HasUniqueLiftingProperty`, extending both).
This file develops the at-most-one and unique variants: their basic API and their stability
under composition, cancellation, isomorphism of arrows, retracts and duality.

## Main declarations

* `HasAtMostOneLiftingProperty i p`, `HasUniqueLiftingProperty i p`: the two classes.
* `CommSq.lift_eq_of_hasAtMostOneLiftingProperty`: two fillers of the same square agree.
* `hasUniqueLiftingProperty_iff`: the unique lifting property as an explicit `∃!` statement.
-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C : Type*} [Category* C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)

-- `to_dual` cannot validate the auto-generated translations of the class' field and
-- constructor, because the reordering of `A B X Y` and `i p` has to be applied to them by
-- hand; the linter asks for exactly that, and the two `attribute [to_dual …]` commands below
-- supply the manual translations it wants. The suppression covers only those two.
set_option linter.translate.warnInvalid false in
/-- `i` has the at most one lift against `p` if every
commutative square from `i` to `p` has at most one filler, i.e. its type of lifts is a
subsingleton. -/
@[to_dual self (reorder := A Y, B X, i p)]
class HasAtMostOneLiftingProperty : Prop where
  /-- Every commutative square from `i` to `p` has at most one filler. -/
  subsingleton_liftStruct :
    ∀ {f : A ⟶ X} {g : B ⟶ Y} (sq : CommSq f i p g), Subsingleton sq.LiftStruct

attribute [to_dual self] HasAtMostOneLiftingProperty.subsingleton_liftStruct
attribute [to_dual self (reorder := A Y, B X, i p, subsingleton_liftStruct (f g))]
  HasAtMostOneLiftingProperty.mk

/-- `i` has the unique lifting property against `p` if every commutative
square from `i` to `p` has exactly one filler. -/
@[to_dual self (reorder := A Y, B X, i p)]
class HasUniqueLiftingProperty : Prop extends HasLiftingProperty i p,
    HasAtMostOneLiftingProperty i p

/-- Unfolding of `HasAtMostOneLiftingProperty` as an instance about a given square. -/
@[to_dual self]
instance subsingleton_liftStruct_of_hasAtMostOneLiftingProperty
    {f : A ⟶ X} {g : B ⟶ Y} (sq : CommSq f i p g)
    [h : HasAtMostOneLiftingProperty i p] :
    Subsingleton sq.LiftStruct :=
  h.subsingleton_liftStruct sq

/-- If `i` has the unique lifting property against `p`, a commutative square from `i` to `p`
has exactly one lift. This is choice-based data, not an instance: the `Unique` structure carries
the chosen lift, so making it an instance would let unrelated `Unique` goals be closed by an
arbitrary filler. -/
@[to_dual self, instance_reducible]
noncomputable def CommSq.uniqueLiftStruct {f : A ⟶ X} {g : B ⟶ Y}
    (sq : CommSq f i p g) [HasUniqueLiftingProperty i p] : Unique sq.LiftStruct :=
  uniqueOfSubsingleton (inferInstance : sq.HasLift).exists_lift.some

/-- Two morphisms `B ⟶ X` filling the same commutative square from `i` to `p` are equal,
provided `i` has at most one lift against `p`. -/
@[to_dual self (reorder := A Y, B X, i p, f g, h₁ h₁', h₂ h₂')]
theorem CommSq.lift_eq_of_hasAtMostOneLiftingProperty
    {f : A ⟶ X} {g : B ⟶ Y} {sq : CommSq f i p g}
    [HasAtMostOneLiftingProperty i p] {l₁ l₂ : B ⟶ X}
    (h₁ : i ≫ l₁ = f) (h₁' : l₁ ≫ p = g)
    (h₂ : i ≫ l₂ = f) (h₂' : l₂ ≫ p = g) : l₁ = l₂ := by
  have : (⟨l₁, h₁, h₁'⟩ : sq.LiftStruct) = ⟨l₂, h₂, h₂'⟩ := Subsingleton.elim _ _
  exact congrArg CommSq.LiftStruct.l this

namespace HasAtMostOneLiftingProperty

/-- An epimorphism has at most one lift against any `p`: two fillers agree after precomposition
with `i`, hence agree. -/
@[to_dual]
instance of_epi [Epi i] : HasAtMostOneLiftingProperty i p where
  subsingleton_liftStruct _ := inferInstance -- inferring from CommSq.subsingleton_liftStruct_of_epi

variable {i p}

/-- Having at most one lift is self-dual: it passes to the opposite category, with the roles
of `i` and `p` exchanged. -/
@[to_dual self]
theorem op (h : HasAtMostOneLiftingProperty i p) :
    HasAtMostOneLiftingProperty p.op i.op where
  subsingleton_liftStruct sq := by
    have := h.subsingleton_liftStruct sq.unop
    exact (CommSq.LiftStruct.unopEquiv sq).subsingleton

/-- The converse of `HasAtMostOneLiftingProperty.op`, for arrows of an opposite category. -/
@[to_dual self]
theorem unop {A B X Y : Cᵒᵖ} {i : A ⟶ B} {p : X ⟶ Y}
    (h : HasAtMostOneLiftingProperty i p) :
    HasAtMostOneLiftingProperty p.unop i.unop where
  subsingleton_liftStruct sq := by
    have := h.subsingleton_liftStruct sq.op
    exact (CommSq.LiftStruct.opEquiv sq).subsingleton

/-- Having at most one lift is invariant under passing to the opposite category. -/
@[to_dual self]
theorem iff_op : HasAtMostOneLiftingProperty i p ↔
    HasAtMostOneLiftingProperty p.op i.op :=
  ⟨op, unop⟩

/-- The version of `HasAtMostOneLiftingProperty.iff_op` for arrows of an opposite category. -/
@[to_dual self]
theorem iff_unop {A B X Y : Cᵒᵖ} (i : A ⟶ B) (p : X ⟶ Y) :
    HasAtMostOneLiftingProperty i p ↔
    HasAtMostOneLiftingProperty p.unop i.unop :=
  ⟨unop, op⟩

/-- If two composable maps `i` and `i'` have at most one lift against `p`, then the same is true
for their composite. -/
@[to_dual of_comp_right]
instance of_comp_left {A B B' X Y : C} (i : A ⟶ B) (i' : B ⟶ B') (p : X ⟶ Y)
    [HasAtMostOneLiftingProperty i p] [HasAtMostOneLiftingProperty i' p] :
    HasAtMostOneLiftingProperty (i ≫ i') p where
  subsingleton_liftStruct {f g} sq := ⟨fun l₁ l₂ => by
    have hl : ∀ l : sq.LiftStruct, i ≫ i' ≫ l.l = f := fun l => by rw [← assoc, l.fac_left]
    have hr : ∀ l : sq.LiftStruct, (i' ≫ l.l) ≫ p = i' ≫ g := fun l => by simp [l.fac_right]
    have step : i' ≫ l₁.l = i' ≫ l₂.l :=
      CommSq.lift_eq_of_hasAtMostOneLiftingProperty i p (sq := ⟨by simp [sq.w]⟩)
        (hl l₁) (hr l₁) (hl l₂) (hr l₂)
    exact CommSq.LiftStruct.ext (CommSq.lift_eq_of_hasAtMostOneLiftingProperty i' p
      (sq := ⟨hr l₁⟩) rfl l₁.fac_right step.symm l₂.fac_right)⟩

/-- If `i` has at most one lift against `p ≫ q`, then it has at most one lift against `p`.
No hypothesis on the cancelled factor `q` is needed: a lift of a square against `p` is
also a lift of the composed square against `p ≫ q`. -/
@[to_dual of_comp_left_cancel]
theorem of_comp_right_cancel {A B X Y Z : C} (i : A ⟶ B) (p : X ⟶ Y) (q : Y ⟶ Z)
    [HasAtMostOneLiftingProperty i (p ≫ q)] : HasAtMostOneLiftingProperty i p where
  subsingleton_liftStruct {f g} sq := ⟨fun l₁ l₂ =>
    CommSq.LiftStruct.ext (CommSq.lift_eq_of_hasAtMostOneLiftingProperty i (p ≫ q)
      (sq := ⟨by rw [← assoc, sq.w, assoc]⟩)
      l₁.fac_left (by rw [← assoc, l₁.fac_right])
      l₂.fac_left (by rw [← assoc, l₂.fac_right]))⟩

/-- Having at most one lift against a given map `p` is stable under isomorphism of arrows. -/
@[to_dual (reorder := i i' e p) of_arrow_iso_right]
theorem of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y)
    [HasAtMostOneLiftingProperty i p] : HasAtMostOneLiftingProperty i' p := by
  rw [Arrow.iso_w' e]
  infer_instance

/-- The `Iff` version of `HasAtMostOneLiftingProperty.of_arrow_iso_left`. -/
@[to_dual (reorder := i i' e p) iff_of_arrow_iso_right]
theorem iff_of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) :
    HasAtMostOneLiftingProperty i p ↔ HasAtMostOneLiftingProperty i' p := by
  constructor <;> intro
  exacts [of_arrow_iso_left e p, of_arrow_iso_left e.symm p]

end HasAtMostOneLiftingProperty

/-- Maps having at most one lift against a given map `i` are stable under retracts: if `p'` is a
retract of `p` and `i` has at most one lift against `p`, then it has at most one lift
against `p'`. -/
@[to_dual leftAtMostOneLiftingProperty]
lemma RetractArrow.rightAtMostOneLiftingProperty
    {A B X Y X' Y' : C} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    (h : RetractArrow p' p) (i : A ⟶ B) [HasAtMostOneLiftingProperty i p] :
    HasAtMostOneLiftingProperty i p' where
  subsingleton_liftStruct := fun {f g} sq ↦ by
    have sq' : CommSq (f ≫ h.i.left) i p (g ≫ h.i.right) :=
      ⟨by rw [← sq.w_assoc, assoc, RetractArrow.i_w]⟩
    refine Function.Injective.subsingleton
      (f := fun l : sq.LiftStruct ↦ (⟨l.l ≫ h.i.left, by rw [← assoc, l.fac_left],
        by rw [assoc, RetractArrow.i_w, ← assoc, l.fac_right]⟩ : sq'.LiftStruct)) ?_
    intro l₁ l₂ hl
    apply CommSq.LiftStruct.ext
    have := congrArg (fun m ↦ CommSq.LiftStruct.l m ≫ h.r.left) hl
    simpa using this

namespace HasUniqueLiftingProperty

/-- Existence and uniqueness of lifts together give the unique lifting property. -/
@[to_dual self]
theorem mk' [HasLiftingProperty i p] [HasAtMostOneLiftingProperty i p] :
    HasUniqueLiftingProperty i p :=
  { toHasLiftingProperty := inferInstance
    toHasAtMostOneLiftingProperty := inferInstance }

/-- An epimorphism with the lifting property against `p` has the unique lifting property
against `p`. -/
@[to_dual]
theorem of_epi [Epi i] [HasLiftingProperty i p] : HasUniqueLiftingProperty i p :=
  mk' i p

/-- An isomorphism has the unique lifting property against any `p`. -/
@[to_dual of_right_iso]
instance (priority := 100) of_left_iso [IsIso i] : HasUniqueLiftingProperty i p :=
  mk' i p

variable {i p}

/-- The unique lifting property is self-dual: it passes to the opposite category, with the roles
of `i` and `p` exchanged. -/
@[to_dual self]
theorem op (h : HasUniqueLiftingProperty i p) : HasUniqueLiftingProperty p.op i.op :=
  { h.toHasLiftingProperty.op, h.toHasAtMostOneLiftingProperty.op with }

/-- The converse of `HasUniqueLiftingProperty.op`, for arrows of an opposite category. -/
@[to_dual self]
theorem unop {A B X Y : Cᵒᵖ} {i : A ⟶ B} {p : X ⟶ Y}
    (h : HasUniqueLiftingProperty i p) : HasUniqueLiftingProperty p.unop i.unop :=
  { h.toHasLiftingProperty.unop, h.toHasAtMostOneLiftingProperty.unop with }

/-- The unique lifting property is invariant under passing to the opposite category. -/
@[to_dual self]
theorem iff_op : HasUniqueLiftingProperty i p ↔ HasUniqueLiftingProperty p.op i.op :=
  ⟨op, unop⟩

/-- The version of `HasUniqueLiftingProperty.iff_op` for arrows of an opposite category. -/
@[to_dual self]
theorem iff_unop {A B X Y : Cᵒᵖ} (i : A ⟶ B) (p : X ⟶ Y) :
    HasUniqueLiftingProperty i p ↔ HasUniqueLiftingProperty p.unop i.unop :=
  ⟨unop, op⟩

/-- The unique lifting property against `p` is stable under composition on the left. -/
@[to_dual of_comp_right]
instance of_comp_left {A B B' X Y : C} (i : A ⟶ B) (i' : B ⟶ B') (p : X ⟶ Y)
    [HasUniqueLiftingProperty i p] [HasUniqueLiftingProperty i' p] :
    HasUniqueLiftingProperty (i ≫ i') p :=
  mk' _ _

/-- A cancellation property: if `i` has the unique lifting property against
`p ≫ q` and at most one lift against `q`, then it has the unique lifting property against `p`. -/
@[to_dual of_comp_left_cancel]
theorem of_comp_right_cancel {A B X Y Z : C} (i : A ⟶ B) (p : X ⟶ Y) (q : Y ⟶ Z)
    [HasUniqueLiftingProperty i (p ≫ q)] [HasAtMostOneLiftingProperty i q] :
    HasUniqueLiftingProperty i p := by
  have hamo : HasAtMostOneLiftingProperty i p :=
    HasAtMostOneLiftingProperty.of_comp_right_cancel i p q
  have hlift : HasLiftingProperty i p := ⟨fun {u v} sq => by
    have sq' : CommSq u i (p ≫ q) (v ≫ q) := ⟨by rw [← assoc, sq.w, assoc]⟩
    have key : sq'.lift ≫ p = v :=
      CommSq.lift_eq_of_hasAtMostOneLiftingProperty i q
        (sq := ⟨by rw [sq.w, assoc]⟩)
        (by rw [← assoc, sq'.fac_left]) (by rw [assoc, sq'.fac_right])
        sq.w.symm rfl
    exact CommSq.HasLift.mk' { l := sq'.lift, fac_left := sq'.fac_left, fac_right := key }⟩
  exact { hlift, hamo with }

set_option backward.isDefEq.respectTransparency false in
/-- The unique lifting property against a given map `p` is stable under isomorphism of arrows. -/
@[to_dual (reorder := i i' e p) of_arrow_iso_right]
theorem of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) [HasUniqueLiftingProperty i p] :
    HasUniqueLiftingProperty i' p :=
    { HasLiftingProperty.of_arrow_iso_left e p,
        HasAtMostOneLiftingProperty.of_arrow_iso_left e p with }

/-- The `Iff` version of `HasUniqueLiftingProperty.of_arrow_iso_left`. -/
@[to_dual (reorder := i i' e p) iff_of_arrow_iso_right]
theorem iff_of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) :
    HasUniqueLiftingProperty i p ↔ HasUniqueLiftingProperty i' p := by
  constructor <;> intro
  exacts [of_arrow_iso_left e p, of_arrow_iso_left e.symm p]

end HasUniqueLiftingProperty

/-- Maps against which `i` has the unique lifting property are stable under retracts. -/
@[to_dual leftUniqueLiftingProperty]
lemma RetractArrow.rightUniqueLiftingProperty
    {A B X Y X' Y' : C} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    (h : RetractArrow p' p) (i : A ⟶ B) [HasUniqueLiftingProperty i p] :
    HasUniqueLiftingProperty i p' :=
    have := h.rightLiftingProperty i
    have := h.rightAtMostOneLiftingProperty i
    HasUniqueLiftingProperty.mk' i p'

/-- The unique lifting property of `i` against `p` is equivalent to: every commutative square
from `i` to `p` has a unique filler. -/
theorem hasUniqueLiftingProperty_iff (i : A ⟶ B) (p : X ⟶ Y) :
    HasUniqueLiftingProperty i p ↔
    ∀ (t : A ⟶ X) (b : B ⟶ Y), CommSq t i p b → ∃! l : B ⟶ X, i ≫ l = t ∧ l ≫ p = b := by
  constructor
  · intro h t b sq
    exact ⟨sq.lift, ⟨sq.fac_left, sq.fac_right⟩, fun l hl =>
      CommSq.lift_eq_of_hasAtMostOneLiftingProperty i p (sq := sq) hl.1 hl.2
        sq.fac_left sq.fac_right⟩
  · intro H
    have hlp : HasLiftingProperty i p :=
      ⟨fun {t b} sq => CommSq.HasLift.mk'
        { l := (H t b sq).choose
          fac_left := (H t b sq).choose_spec.1.1
          fac_right := (H t b sq).choose_spec.1.2 }⟩
    have hamo : HasAtMostOneLiftingProperty i p :=
      ⟨fun {t b} sq => ⟨fun l₁ l₂ => by
        apply CommSq.LiftStruct.ext
        have huniq := (H t b sq).choose_spec.2
        rw [huniq l₁.l ⟨l₁.fac_left, l₁.fac_right⟩, huniq l₂.l ⟨l₂.fac_left, l₂.fac_right⟩]⟩⟩
    exact HasUniqueLiftingProperty.mk' i p

end CategoryTheory
