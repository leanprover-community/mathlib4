/-
Copyright (c) 2026 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Orthogonal
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Unique lifting is stable under transfinite composition (pointwise)

This file provides the uniqueness half of the statement that the class of maps
with the unique left lifting property against a fixed map `p` is stable under
transfinite composition. (The existence half is
`HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot`.)

## Main declarations

* `HasUniqueLiftingProperty.transfiniteComposition.hasUniqueLiftingProperty_ι_app_bot`
  — if every successor map lifts uniquely against `p`, so does the transfinite
  composite.
* `MorphismProperty.isStableUnderTransfiniteCompositionOfShape_leftOrthogonal` and
  `MorphismProperty.isStableUnderTransfiniteComposition_leftOrthogonal` — instances
  saying that `T.leftOrthogonal` is closed under transfinite composition, of a fixed
  shape `J` and of arbitrary shape respectively.

## The proof

Two lifts `m₁ m₂ : c.pt ⟶ X` of a square along the transfinite composition
`c.ι.app ⊥` are compared stage by stage, by transfinite induction on `j : J`
(`HasAtMostOneLiftingProperty.transfiniteComposition.comp_ext`):

* at the bottom stage, `c.ι.app ⊥ ≫ m₁ = c.ι.app ⊥ ≫ m₂` is the hypothesis;
* to pass from `j` to `Order.succ j`, the two composites with `c.ι.app (Order.succ j)`
  are two lifts of one and the same square along
  `F.obj j ⟶ F.obj (Order.succ j)`, so they agree by the assumption on that map;
* at a limit stage, `F.obj j` is the colimit of the earlier stages, so the claim
  follows from the inductive hypothesis by `hom_ext`.

Since `c` is a colimit, extensionality of `c.pt` then gives `m₁ = m₂`.
-/

public section

universe w

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C]

namespace HasAtMostOneLiftingProperty

namespace transfiniteComposition

/- Throughout this section `J` is a well-ordered type, `F : J ⥤ C` is a
well-order-continuous functor and `c` is a cocone over `F`, so that once `c` is a colimit
(`hc`) the map `c.ι.app ⊥ : F.obj ⊥ ⟶ c.pt` is the transfinite composition of `F`. The map
to lift against is `p : X ⟶ Y`, and `hF` says that each successor map
`F.obj j ⟶ F.obj (Order.succ j)` has at most one lift against `p`. -/
variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {F : J ⥤ C} [F.IsWellOrderContinuous] {c : Cocone F} (hc : IsColimit c)
  {X Y : C} {p : X ⟶ Y}
  (hF : ∀ (j : J) (_ : ¬IsMax j),
    HasAtMostOneLiftingProperty (F.map (homOfLE (Order.le_succ j))) p)

include hF

/-- Two lifts `m₁ m₂ : c.pt ⟶ X` of the same square agree after precomposition
with `c.ι.app j`, for every `j : J`, provided they agree at the bottom stage and
have the same composite with `p`. -/
lemma comp_ext (m₁ m₂ : c.pt ⟶ X)
    (hbot : c.ι.app ⊥ ≫ m₁ = c.ι.app ⊥ ≫ m₂)
    (hp : m₁ ≫ p = m₂ ≫ p) (j : J) :
    c.ι.app j ≫ m₁ = c.ι.app j ≫ m₂ := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := isMin_iff_eq_bot.mp hj
    exact hbot
  | succ j hj IH =>
    have := hF j hj
    have w : (c.ι.app j ≫ m₁) ≫ p =
        F.map (homOfLE (Order.le_succ j)) ≫ (c.ι.app (Order.succ j) ≫ m₁ ≫ p) := by
      rw [Category.assoc, Cocone.w_assoc]
    let sq : CommSq (c.ι.app j ≫ m₁) (F.map (homOfLE (Order.le_succ j))) p
        (c.ι.app (Order.succ j) ≫ m₁ ≫ p) := ⟨w⟩
    exact congrArg CommSq.LiftStruct.l (Subsingleton.elim
      (⟨c.ι.app (Order.succ j) ≫ m₁, by rw [Cocone.w_assoc], by rw [Category.assoc]⟩ :
        sq.LiftStruct)
      ⟨c.ι.app (Order.succ j) ≫ m₂, by rw [Cocone.w_assoc, IH], by rw [Category.assoc, hp]⟩)
  | isSuccLimit j hj IH =>
    apply (F.isColimitOfIsWellOrderContinuous j hj).hom_ext
    rintro ⟨b, hb⟩
    have hbj : b < j := hb
    change F.map (homOfLE hbj.le) ≫ c.ι.app j ≫ m₁
        = F.map (homOfLE hbj.le) ≫ c.ι.app j ≫ m₂
    rw [Cocone.w_assoc, Cocone.w_assoc]
    exact IH b hbj

include hc

/-- The transfinite composition `c.ι.app ⊥` has at most one lift against `p`
whenever each successor map does. -/
lemma hasAtMostOneLiftingProperty_ι_app_bot :
    HasAtMostOneLiftingProperty (c.ι.app ⊥) p where
  subsingleton_liftStruct sq := ⟨fun l₁ l₂ => by
    apply CommSq.LiftStruct.ext
    apply hc.hom_ext
    intro j
    exact comp_ext hF l₁.l l₂.l
      (by rw [l₁.fac_left, l₂.fac_left]) (by rw [l₁.fac_right, l₂.fac_right]) j⟩

end transfiniteComposition

end HasAtMostOneLiftingProperty

namespace HasUniqueLiftingProperty

namespace transfiniteComposition

variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {F : J ⥤ C} [F.IsWellOrderContinuous] {c : Cocone F} (hc : IsColimit c)
  {X Y : C} {p : X ⟶ Y}

include hc

/-- The transfinite composition `c.ι.app ⊥` has a unique lift against `p`
whenever each successor map does. -/
lemma hasUniqueLiftingProperty_ι_app_bot
    (hF : ∀ (j : J) (_ : ¬IsMax j),
      HasUniqueLiftingProperty (F.map (homOfLE (Order.le_succ j))) p) :
    HasUniqueLiftingProperty (c.ι.app ⊥) p :=
  have := HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot hc
    (fun j hj => (hF j hj).toHasLiftingProperty)
  have := HasAtMostOneLiftingProperty.transfiniteComposition.hasAtMostOneLiftingProperty_ι_app_bot
    hc (fun j hj => (hF j hj).toHasAtMostOneLiftingProperty)
  HasUniqueLiftingProperty.mk' (c.ι.app ⊥) p

end transfiniteComposition

end HasUniqueLiftingProperty

namespace MorphismProperty

variable (T : MorphismProperty C)
  (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

set_option backward.isDefEq.respectTransparency false in
/-- The left orthogonal of `T` is stable under transfinite compositions of shape `J`.
(Compare to `MorphismProperty.isStableUnderTransfiniteCompositionOfShape_llp`.) -/
instance isStableUnderTransfiniteCompositionOfShape_leftOrthogonal :
    T.leftOrthogonal.IsStableUnderTransfiniteCompositionOfShape J := by
  rw [isStableUnderTransfiniteCompositionOfShape_iff]
  rintro X Y f ⟨h⟩
  have : T.leftOrthogonal (h.incl.app ⊥) := fun _ _ p hp ↦
    HasUniqueLiftingProperty.transfiniteComposition.hasUniqueLiftingProperty_ι_app_bot
      (hc := h.isColimit) (fun j hj ↦ h.map_mem j hj _ hp)
  exact (MorphismProperty.arrow_mk_iso_iff _
    (Arrow.isoMk h.isoBot.symm (Iso.refl _))).2 this

/-- The left orthogonal of `T` is stable under (arbitrary-shape) transfinite
compositions. -/
instance isStableUnderTransfiniteComposition_leftOrthogonal :
    MorphismProperty.IsStableUnderTransfiniteComposition.{w} T.leftOrthogonal where

end MorphismProperty

end CategoryTheory
