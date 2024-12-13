/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Retract

/-!
# Left and right lifting properties

Given a morphism property `T`, we define the left and right lifting property with respect to `T`.

We show that the left lifting property is stable under retracts, cobase change, and composition,
with dual statements for the right lifting property.

-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

/-- The left lifting property (llp) with respect to a class of morphisms. -/
def llp (T : MorphismProperty C) : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ ⦃g : X ⟶ Y⦄ (_ : T g), HasLiftingProperty f g

/-- The right lifting property (rlp) with respect to a class of morphisms. -/
def rlp (T : MorphismProperty C) : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ ⦃g : X ⟶ Y⦄ (_ : T g), HasLiftingProperty g f

open RetractArrow in
lemma liftOfRetractLeft {X Y Z W Z' W' : C} {f : X ⟶ Y} {g : Z ⟶ W} {g' : Z' ⟶ W'}
    (h : RetractArrow g' g) (h' : HasLiftingProperty g f) : HasLiftingProperty g' f where
  sq_hasLift := fun {u v} sq ↦
    ⟨h.i.right ≫ h'.lift ⟨show (h.r.left ≫ u) ≫ f = g ≫ (h.r.right ≫ v) by simp [sq.w]⟩,
      by rw [← Category.assoc, ← i_w, Category.assoc, CommSq.fac_left, ← Category.assoc,
        retract_left, Category.id_comp],
      by rw [Category.assoc, CommSq.fac_right, ← Category.assoc, retract_right, Category.id_comp]⟩

open RetractArrow in
lemma liftOfRetractRight {X Y Z W X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Z ⟶ W}
    (h : RetractArrow f' f) (h' : HasLiftingProperty g f) : HasLiftingProperty g f' where
  sq_hasLift := fun {u v} sq ↦
    ⟨h'.lift ⟨show (u ≫ h.i.left) ≫ f = g ≫ (v ≫ h.i.right)
      by rw [← Category.assoc, ← sq.w, Category.assoc, i_w, Category.assoc]⟩ ≫ h.r.left,
      by rw [← Category.assoc, CommSq.fac_left, Category.assoc, retract_left, Category.comp_id],
      by rw [Category.assoc, r_w, ← Category.assoc, CommSq.fac_right, Category.assoc, retract_right,
        Category.comp_id]⟩

lemma llp.IsStableUnderRetracts {T : MorphismProperty C} : T.llp.IsStableUnderRetracts :=
  ⟨fun {_ _} _ _ _ _ h hg _ _ _ hf ↦ liftOfRetractLeft h (hg hf)⟩

lemma rlp.IsStableUnderRetracts {T : MorphismProperty C} : T.rlp.IsStableUnderRetracts :=
  ⟨fun {_ _} _ _ _ _ h hf _ _ _ hg ↦ liftOfRetractRight h (hf hg)⟩

open IsPushout in
instance llp.IsStableUnderCobaseChange {T : MorphismProperty C} :
    T.llp.IsStableUnderCobaseChange where
  of_isPushout {_ _ _ _ f s _ t} P hf _ _ g hg := {
    sq_hasLift := fun {u v} sq ↦ by
      have w : (s ≫ u) ≫ g = f ≫ (t ≫ v) := by
        rw [← Category.assoc, ← P.toCommSq.w, Category.assoc, Category.assoc, sq.w]
      exact ⟨P.desc u ((hf hg).lift ⟨w⟩) (by rw [CommSq.fac_left]), P.inl_desc ..,
        P.hom_ext (by rw [inl_desc_assoc, sq.w]) (by rw [inr_desc_assoc, CommSq.fac_right])⟩}

open IsPullback in
instance rlp.IsStableUnderBaseChange {T : MorphismProperty C} :
    T.rlp.IsStableUnderBaseChange where
  of_isPullback {_ _ _ _ t f s _} P hf _ _ g hg := {
    sq_hasLift := fun {u v} sq ↦ by
      have w : (u ≫ s) ≫ f = g ≫ v ≫ t := by
        rw [Category.assoc, P.toCommSq.w, ← Category.assoc, ← Category.assoc, sq.w]
      exact ⟨P.lift ((hf hg).lift (.mk w)) v (by rw [CommSq.fac_right]),
        P.hom_ext (by rw [Category.assoc, lift_fst, CommSq.fac_left])
          (by rw [Category.assoc, lift_snd, sq.w]), P.lift_snd _ _ _⟩}

instance llp.ContainsIdentities (T : MorphismProperty C) : T.llp.ContainsIdentities :=
  ⟨fun _ _ _ _ _ ↦
    ⟨fun {f _} sq ↦ ⟨f, Category.id_comp _, by simp only [sq.w, Category.id_comp]⟩⟩⟩

instance rlp.ContainsIdentities (T : MorphismProperty C) : T.rlp.ContainsIdentities :=
  ⟨fun _ _ _ _ _ ↦
    ⟨fun {_ g} sq ↦ ⟨g, by simp only [sq.w.symm, Category.comp_id], Category.comp_id _⟩⟩⟩

instance llp.IsStableUnderComposition (T : MorphismProperty C) :
    T.llp.IsStableUnderComposition where
  comp_mem p q hp hq _ _ i hi := {
    sq_hasLift := fun {f g} sq ↦
      ⟨(hq hi).lift ⟨(hp hi).fac_right ⟨show f ≫ i = p ≫ q ≫ g by rw [← Category.assoc, ← sq.w]⟩⟩,
        by aesop, (hq hi).fac_right _⟩}

instance rlp.IsStableUnderComposition (T : MorphismProperty C) :
    T.rlp.IsStableUnderComposition where
  comp_mem p q hp hq _ _ i hi := {
    sq_hasLift := fun {f g} sq ↦
      ⟨(hp hi).lift ⟨((hq hi).fac_left ⟨show (f ≫ p) ≫ q = i ≫ g
        by rw [Category.assoc, sq.w]⟩).symm⟩, (hp hi).fac_left _, by aesop⟩}

instance llp.IsMultiplicative (T : MorphismProperty C) : T.llp.IsMultiplicative where
  id_mem := T.llp.id_mem
  comp_mem := T.llp.comp_mem

instance rlp.IsMultiplicative (T : MorphismProperty C) : T.rlp.IsMultiplicative where
  id_mem := T.rlp.id_mem
  comp_mem := T.rlp.comp_mem

instance llp.RespectsIso (T : MorphismProperty C) : T.llp.RespectsIso where
  precomp i hi f hf _ _ g hg := ⟨fun {u v} sq ↦ by
    obtain ⟨r, h₁, h₂⟩  := hi.out
    have w : (r ≫ u) ≫ g = f ≫ v := by
      rw [Category.assoc, sq.w, ← Category.assoc, ← Category.assoc, h₂, Category.id_comp]
    exact ⟨(hf hg).lift ⟨w⟩,
      by rw [Category.assoc, (hf hg).fac_left _, ← Category.assoc, h₁, Category.id_comp],
      (hf hg).fac_right _⟩⟩
  postcomp i hi f hf _ _ g hg := ⟨fun {u v} sq ↦ by
    obtain ⟨r, h₁, h₂⟩  := hi.out
    have w : u ≫ g = f ≫ (i ≫ v) := by simp only [sq.w, Category.assoc]
    refine ⟨r ≫ (hf hg).lift ⟨w⟩,
      by rw [Category.assoc, ← Category.assoc i, h₁, Category.id_comp, (hf hg).fac_left],
      by rw [Category.assoc, (hf hg).fac_right, ← Category.assoc, h₂, Category.id_comp]⟩⟩

instance rlp.RespectsIso (T : MorphismProperty C) : T.rlp.RespectsIso where
  precomp i hi f hf _ _ g hg := ⟨fun {u v} sq ↦ by
    obtain ⟨r, h₁, h₂⟩  := hi.out
    have w : (u ≫ i) ≫ f = g ≫ v := by rw [Category.assoc, sq.w]
    exact ⟨(hf hg).lift ⟨w⟩ ≫ r,
      by rw [← Category.assoc, (hf hg).fac_left, Category.assoc, h₁, Category.comp_id],
      by rw [Category.assoc, ← Category.assoc r, h₂, Category.id_comp, (hf hg).fac_right]⟩⟩
  postcomp {X Y Z} i hi f hf A B g hg := ⟨fun {u v} sq ↦ by
    obtain ⟨r, h₁, h₂⟩  := hi.out
    have w : u ≫ f = g ≫ (v ≫ r) := by
      have := sq.w =≫ r
      aesop
    exact ⟨(hf hg).lift ⟨w⟩, (hf hg).fac_left _,
      by rw [← Category.assoc, (hf hg).fac_right, Category.assoc, h₂, Category.comp_id]⟩⟩

end MorphismProperty

end CategoryTheory
