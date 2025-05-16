/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Lifting properties and (co)limits

In this file, we show some consequences of lifting properties in the presence of
certain (co)limits.

-/

universe v

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] {X Y Z W : C}
  {f : X ⟶ Y} {s : X ⟶ Z} {g : Z ⟶ W} {t : Y ⟶ W}

lemma IsPushout.hasLiftingProperty (h : IsPushout s f g t)
    {Z' W' : C} (g' : Z' ⟶ W') [HasLiftingProperty f g'] : HasLiftingProperty g g' where
  sq_hasLift := fun {u v} sq ↦ by
    have w : (s ≫ u) ≫ g' = f ≫ (t ≫ v) := by
      rw [← Category.assoc, ← h.w, Category.assoc, Category.assoc, sq.w]
    exact ⟨h.desc u (CommSq.mk w).lift (by rw [CommSq.fac_left]), h.inl_desc ..,
      h.hom_ext (by rw [h.inl_desc_assoc, sq.w]) (by rw [h.inr_desc_assoc, CommSq.fac_right])⟩

lemma IsPullback.hasLiftingProperty (h : IsPullback s f g t)
    {X' Y' : C} (f' : X' ⟶ Y') [HasLiftingProperty f' g] : HasLiftingProperty f' f where
  sq_hasLift := fun {u v} sq ↦ by
    have w : (u ≫ s) ≫ g = f' ≫ v ≫ t := by
      rw [Category.assoc, h.toCommSq.w, ← Category.assoc, ← Category.assoc, sq.w]
    exact ⟨h.lift (CommSq.mk w).lift v (by rw [CommSq.fac_right]),
      h.hom_ext (by rw [Category.assoc, h.lift_fst, CommSq.fac_left])
        (by rw [Category.assoc, h.lift_snd, sq.w]), h.lift_snd _ _ _⟩

instance [HasPushout s f] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasLiftingProperty f p] :
    HasLiftingProperty (pushout.inl s f) p :=
  (IsPushout.of_hasPushout s f).hasLiftingProperty p

instance [HasPushout s f] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasLiftingProperty s p] :
    HasLiftingProperty (pushout.inr s f) p :=
  (IsPushout.of_hasPushout s f).flip.hasLiftingProperty p

instance [HasPullback g t] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasLiftingProperty p g] :
    HasLiftingProperty p (pullback.snd g t) :=
  (IsPullback.of_hasPullback g t).hasLiftingProperty p

instance [HasPullback g t] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasLiftingProperty p t] :
    HasLiftingProperty p (pullback.fst g t) :=
  (IsPullback.of_hasPullback g t).flip.hasLiftingProperty p

instance {J : Type*} {A B : J → C} [HasProduct A] [HasProduct B]
    (f : (j : J) → A j ⟶ B j) {X Y : C} (p : X ⟶ Y)
    [∀ j, HasLiftingProperty p (f j)] :
    HasLiftingProperty p (Limits.Pi.map f) where
  sq_hasLift {t b} sq := by
    have sq' (j : J) :
        CommSq (t ≫ Pi.π _ j) p (f j) (b ≫ Pi.π _ j) :=
      ⟨by rw [← Category.assoc, ← sq.w]; simp⟩
    exact ⟨⟨{ l := Pi.lift (fun j ↦ (sq' j).lift) }⟩⟩

instance {J : Type*} {A B : J → C} [HasCoproduct A] [HasCoproduct B]
    (f : (j : J) → A j ⟶ B j) {X Y : C} (p : X ⟶ Y)
    [∀ j, HasLiftingProperty (f j) p] :
    HasLiftingProperty (Limits.Sigma.map f) p where
  sq_hasLift {t b} sq := by
    have sq' (j : J) :
        CommSq (Sigma.ι _ j ≫ t) (f j) p (Sigma.ι _ j ≫ b) :=
      ⟨by simp [sq.w]⟩
    exact ⟨⟨{ l := Sigma.desc (fun j ↦ (sq' j).lift) }⟩⟩

end CategoryTheory
