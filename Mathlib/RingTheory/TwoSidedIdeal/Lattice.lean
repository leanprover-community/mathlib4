/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# The complete lattice structure on two-sided ideals
-/

namespace TwoSidedIdeal

variable (R : Type*) [NonUnitalNonAssocRing R]

instance : Sup (TwoSidedIdeal R) where
  sup := fun I J => { ringCon := I.ringCon ⊔ J.ringCon }

instance : Inf (TwoSidedIdeal R) where
  inf := fun I J => { ringCon := I.ringCon ⊓ J.ringCon }

lemma mem_inf {I J : TwoSidedIdeal R} {x : R} :
    x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J :=
  Iff.rfl

instance : SupSet (TwoSidedIdeal R) where
  sSup := fun s => { ringCon := sSup $ TwoSidedIdeal.ringCon '' s }

instance : InfSet (TwoSidedIdeal R) where
  sInf := fun s => { ringCon := sInf $ TwoSidedIdeal.ringCon '' s }

lemma mem_iInf {ι : Type*} {I : ι → TwoSidedIdeal R} {x : R} :
    x ∈ iInf I ↔ ∀ i, x ∈ I i :=
  show (∀ _, _) ↔ _ by simp [mem_iff]

lemma mem_sInf {S : Set (TwoSidedIdeal R)} {x : R} :
    x ∈ sInf S ↔ ∀ I ∈ S, x ∈ I :=
  show (∀ _, _) ↔ _ by simp [mem_iff]

instance : Top (TwoSidedIdeal R) where
  top := { ringCon := ⊤ }

instance : Bot (TwoSidedIdeal R) where
  bot := { ringCon := ⊥ }

lemma mem_bot {x : R} : x ∈ (⊥ : TwoSidedIdeal R) ↔ x = 0 :=
  Iff.rfl

instance : CompleteLattice (TwoSidedIdeal R) :=
  Function.Injective.completeLattice (f := TwoSidedIdeal.ringCon (R := R))
    ringCon_injective (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ => sSup_image) (fun _ => sInf_image) rfl rfl

section sup

variable {R}

lemma mem_sup_left {I J : TwoSidedIdeal R} {x : R} :
    x ∈ I → x ∈ I ⊔ J :=
  fun h => (show I ≤ I ⊔ J from le_sup_left) h

lemma mem_sup_right {I J : TwoSidedIdeal R} {x : R} :
    x ∈ J → x ∈ I ⊔ J :=
  fun h => (show J ≤ I ⊔ J from le_sup_right) h

lemma mem_sup {I J : TwoSidedIdeal R} {x : R} :
    x ∈ I ⊔ J ↔ ∃ y ∈ I, ∃ z ∈ J, y + z = x :=
  ⟨by
    let s : TwoSidedIdeal R := .mk'
      {x | ∃ y ∈ I, ∃ z ∈ J, y + z = x}
      ⟨0, ⟨zero_mem _, ⟨0, ⟨zero_mem _, zero_add _⟩⟩⟩⟩
      (by rintro _ _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩ ⟨a, ⟨ha, ⟨b, ⟨hb, rfl⟩⟩⟩⟩;
          exact ⟨x + a, ⟨add_mem _ hx ha, ⟨y + b, ⟨add_mem _ hy hb, by abel⟩⟩⟩⟩)
      (by rintro _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩
          exact ⟨-x, ⟨neg_mem _ hx, ⟨-y, ⟨neg_mem _ hy, by abel⟩⟩⟩⟩)
      (by rintro r _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩
          exact ⟨_, ⟨mul_mem_left _ _ _ hx, ⟨_, ⟨mul_mem_left _ _ _ hy, mul_add _ _ _ |>.symm⟩⟩⟩⟩)
      (by rintro r _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩
          exact ⟨_, ⟨mul_mem_right _ _ _ hx, ⟨_, ⟨mul_mem_right _ _ _ hy, add_mul _ _ _ |>.symm⟩⟩⟩⟩)

    suffices (I.ringCon ⊔ J.ringCon) ≤ s.ringCon by
      intro h; convert this h; rw [rel_iff, sub_zero, mem_mk']; rfl
    refine sup_le
      (show I ≤ s from fun x y h => by
        rw [rel_iff] at h ⊢; rw [mem_mk']; exact ⟨_, ⟨h, ⟨0, ⟨zero_mem _, add_zero _⟩⟩⟩⟩)
      (show J ≤ s from fun x y h => by
        rw [rel_iff] at h ⊢; rw [mem_mk']; exact ⟨0, ⟨zero_mem _, ⟨_, ⟨h, zero_add _⟩⟩⟩⟩),
    by rintro ⟨y, ⟨hy, ⟨z, ⟨hz, rfl⟩⟩⟩⟩; exact add_mem _ (mem_sup_left hy) (mem_sup_right hz)⟩

end sup

end TwoSidedIdeal
