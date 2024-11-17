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
    (h : RetractArrow g' g) (h' : HasLiftingProperty g f) : HasLiftingProperty g' f := by
  refine ⟨fun {u v} sq ↦ ?_⟩
  have : (h.r.left ≫ u) ≫ f = g ≫ (h.r.right ≫ v) := by simp [sq.w]
  obtain lift := (h'.sq_hasLift (CommSq.mk this)).exists_lift.some
  refine ⟨h.i.right ≫ lift.l, ?_, ?_⟩
  · rw [← Category.assoc, ← leftSqComm, Category.assoc, lift.fac_left, ← Category.assoc, topCompId,
      Category.id_comp]
  · rw [Category.assoc, lift.fac_right, ← Category.assoc, bottomCompId, Category.id_comp]

open RetractArrow in
lemma liftOfRetractRight {X Y Z W X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Z ⟶ W}
    (h : RetractArrow f' f) (h' : HasLiftingProperty g f) : HasLiftingProperty g f' := by
  refine ⟨fun {u v} sq ↦ ?_⟩
  have : (u ≫ h.i.left) ≫ f = g ≫ (v ≫ h.i.right) := by
    rw [← Category.assoc, ← sq.w]
    aesop
  obtain lift := (h'.sq_hasLift (CommSq.mk this)).exists_lift.some
  refine ⟨lift.l ≫ h.r.left, ?_, ?_⟩
  · rw [← Category.assoc, lift.fac_left, Category.assoc, topCompId, Category.comp_id]
  · rw [Category.assoc, rightSqComm, ← Category.assoc, lift.fac_right, Category.assoc, bottomCompId,
      Category.comp_id]

lemma llp.IsStableUnderRetracts {T : MorphismProperty C} : T.llp.IsStableUnderRetracts :=
  ⟨fun {_ _} _ _ _ _ h hg _ _ _ hf ↦ liftOfRetractLeft h (hg hf)⟩

lemma rlp.IsStableUnderRetracts {T : MorphismProperty C} : T.rlp.IsStableUnderRetracts :=
  ⟨fun {_ _} _ _ _ _ h hf _ _ _ hg ↦ liftOfRetractRight h (hf hg)⟩

open Limits.PushoutCocone in
instance llp.IsStableUnderCobaseChange {T : MorphismProperty C} :
    T.llp.IsStableUnderCobaseChange := by
  refine ⟨fun {A B A' B'} f s f' t P L X Y g hg ↦ ⟨fun {u v} sq ↦ ?_⟩⟩
  have w : (s ≫ u) ≫ g = f ≫ (t ≫ v) := by
    rw [← Category.assoc, ← P.toCommSq.w, Category.assoc, Category.assoc, sq.w]
  obtain lift := ((L hg).sq_hasLift (CommSq.mk w)).exists_lift.some
  let lift' : B' ⟶ X := IsColimit.desc P.isColimit u lift.l (by rw [lift.fac_left])
  let l : f' ≫ lift' = u := IsColimit.inl_desc P.isColimit u lift.l (by rw [lift.fac_left])
  let l' : t ≫ lift' = lift.l := IsColimit.inr_desc P.isColimit u lift.l (by rw [lift.fac_left])
  let newCocone := mk (f' ≫ v) (t ≫ v) (by have := P.w; apply_fun (fun f ↦ f ≫ v) at this; aesop)
  refine ⟨lift', l,
    (P.isColimit.uniq newCocone (lift' ≫ g) ?_).trans (P.isColimit.uniq newCocone v ?_).symm⟩
  all_goals dsimp [newCocone]; intro j; cases j; simp only [Limits.span_zero, condition_zero,
    IsPushout.cocone_inl, Category.assoc]
  · rw [← Category.assoc, ← Category.assoc, Category.assoc s f' lift', l, ← sq.w, Category.assoc]
  · rename_i k; cases k; all_goals dsimp
    · rw [← Category.assoc, l, sq.w]
    · rw [← Category.assoc, l', lift.fac_right]
  · rename_i k; cases k; all_goals dsimp

open Limits.PullbackCone in
instance rlp.IsStableUnderBaseChange {T : MorphismProperty C} :
    T.rlp.IsStableUnderBaseChange := by
  refine ⟨fun {B' A A' B} t f s f' P L X Y g hg ↦ ⟨fun {u v} sq ↦ ?_⟩⟩
  have w : (u ≫ s) ≫ f = g ≫ v ≫ t := by
    rw [Category.assoc, P.toCommSq.w, ← Category.assoc, ← Category.assoc, sq.w]
  obtain lift := ((L hg).sq_hasLift (CommSq.mk w)).exists_lift.some
  let lift' : Y ⟶ A' := IsLimit.lift P.isLimit lift.l v (by rw [lift.fac_right])
  let l : lift' ≫ f' = v := IsLimit.lift_snd P.isLimit lift.l v (by rw [lift.fac_right])
  let l' : lift' ≫ s = lift.l := IsLimit.lift_fst P.isLimit lift.l v (by rw [lift.fac_right])
  have comm : (u ≫ s) ≫ f = (g ≫ v) ≫ t := by aesop
  let newCone := mk _ _ comm
  refine ⟨lift',
      (P.isLimit.uniq newCone (g ≫ lift') ?_).trans (P.isLimit.uniq newCone u ?_).symm, l⟩
  all_goals dsimp [newCone]; intro j; cases j; simp only [Limits.cospan_one, condition_one,
    IsPullback.cone_fst, Category.assoc]
  · rw [← Category.assoc u, ← lift.fac_left, ← l', Category.assoc, Category.assoc]
  · rename_i k; cases k; all_goals dsimp
    · rw [← lift.fac_left, ← l', Category.assoc]
    · rw [← sq.w, Category.assoc, l, sq.w]
  · rename_i k; cases k; all_goals dsimp
    exact sq.w

instance llp.ContainsIdentities (T : MorphismProperty C) : T.llp.ContainsIdentities :=
  ⟨fun _ _ _ _ _ ↦
    ⟨fun {f _} sq ↦ ⟨f, Category.id_comp _, by simp only [sq.w, Category.id_comp]⟩⟩⟩

instance rlp.ContainsIdentities (T : MorphismProperty C) : T.rlp.ContainsIdentities :=
  ⟨fun _ _ _ _ _ ↦
    ⟨fun {_ g} sq ↦ ⟨g, by simp only [sq.w.symm, Category.comp_id], Category.comp_id _⟩⟩⟩

instance llp.IsStableUnderComposition (T : MorphismProperty C) :
    T.llp.IsStableUnderComposition := by
  refine ⟨fun p q hp hq _ _ i hi ↦ ⟨fun {f g} sq ↦ ?_⟩⟩
  have q_sq_comm : f ≫ i = p ≫ (q ≫ g) := by rw [← Category.assoc, ← sq.w]
  obtain ⟨p_lift, p_fac_left, p_fac_right⟩ :=
    ((hp hi).sq_hasLift (CommSq.mk q_sq_comm)).exists_lift.some
  obtain ⟨q_lift, q_fac_left, q_fac_right⟩ :=
    ((hq hi).sq_hasLift (CommSq.mk p_fac_right)).exists_lift.some
  refine ⟨q_lift, by rw [Category.assoc, q_fac_left, p_fac_left], q_fac_right⟩

instance rlp.IsStableUnderComposition (T : MorphismProperty C) :
    T.rlp.IsStableUnderComposition := by
  refine ⟨fun p q hp hq _ _ i hi ↦ ⟨fun {f g} sq ↦ ?_⟩⟩
  have q_sq_comm : (f ≫ p) ≫ q = i ≫ g := by rw [Category.assoc, sq.w]
  obtain ⟨q_lift, q_fac_left, q_fac_right⟩ :=
    ((hq hi).sq_hasLift (CommSq.mk q_sq_comm)).exists_lift.some
  obtain ⟨p_lift, p_fac_left, p_fac_right⟩ :=
    ((hp hi).sq_hasLift (CommSq.mk q_fac_left.symm)).exists_lift.some
  refine ⟨p_lift, p_fac_left, by rw [← Category.assoc, p_fac_right, q_fac_right]⟩

instance llp.IsMultiplicative (T : MorphismProperty C) : T.llp.IsMultiplicative where
  id_mem := (llp.ContainsIdentities T).id_mem
  comp_mem := (llp.IsStableUnderComposition T).comp_mem

instance rlp.IsMultiplicative (T : MorphismProperty C) : T.rlp.IsMultiplicative where
  id_mem := (rlp.ContainsIdentities T).id_mem
  comp_mem := (rlp.IsStableUnderComposition T).comp_mem

instance llp.RespectsIso (T : MorphismProperty C) : T.llp.RespectsIso where
  precomp i hi f hf _ _ g hg := ⟨fun {u v} sq ↦ by
    obtain ⟨r, h₁, h₂⟩  := hi.out
    have : (r ≫ u) ≫ g = f ≫ v := by
      rw [Category.assoc, sq.w, ← Category.assoc, ← Category.assoc, h₂, Category.id_comp]
    obtain ⟨l, fac_left, fac_right⟩ := ((hf hg).sq_hasLift (CommSq.mk this)).exists_lift.some
    exact ⟨l, by rw [Category.assoc, fac_left, ← Category.assoc, h₁, Category.id_comp], fac_right⟩⟩
  postcomp i hi f hf _ _ g hg := ⟨fun {u v} sq ↦ by
    obtain ⟨r, h₁, h₂⟩  := hi.out
    have : u ≫ g = f ≫ (i ≫ v) := by simp only [sq.w, Category.assoc]
    obtain ⟨l, fac_left, fac_right⟩ := ((hf hg).sq_hasLift (CommSq.mk this)).exists_lift.some
    refine ⟨r ≫ l, by rwa [Category.assoc, ← Category.assoc i, h₁, Category.id_comp],
      by rw [Category.assoc, fac_right, ← Category.assoc, h₂, Category.id_comp]⟩⟩

instance rlp.RespectsIso (T : MorphismProperty C) : T.rlp.RespectsIso := by
  sorry

end MorphismProperty

end CategoryTheory
