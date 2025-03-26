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

instance : SemilatticeSup (TwoSidedIdeal R) where
  sup I J := { ringCon := I.ringCon ⊔ J.ringCon }
  le_sup_left I J :=  by rw [ringCon_le_iff]; exact le_sup_left
  le_sup_right I J := by rw [ringCon_le_iff]; exact le_sup_right
  sup_le I J K h1 h2 := by rw [ringCon_le_iff] at h1 h2 ⊢; exact sup_le h1 h2

lemma sup_ringCon (I J : TwoSidedIdeal R) : (I ⊔ J).ringCon = I.ringCon ⊔ J.ringCon := rfl

section sup

variable {R}

lemma mem_sup_left {I J : TwoSidedIdeal R} {x : R} (h : x ∈ I) :
    x ∈ I ⊔ J :=
  (show I ≤ I ⊔ J from le_sup_left) h

lemma mem_sup_right {I J : TwoSidedIdeal R} {x : R} (h : x ∈ J) :
    x ∈ I ⊔ J :=
  (show J ≤ I ⊔ J from le_sup_right) h

lemma mem_sup {I J : TwoSidedIdeal R} {x : R} :
    x ∈ I ⊔ J ↔ ∃ y ∈ I, ∃ z ∈ J, y + z = x := by
  constructor
  · let s : TwoSidedIdeal R := .mk'
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
    refine sup_le (fun x y h => ?_) (fun x y h => ?_) <;> rw [rel_iff] at h ⊢ <;> rw [mem_mk']
    exacts [⟨_, ⟨h, ⟨0, ⟨zero_mem _, add_zero _⟩⟩⟩⟩, ⟨0, ⟨zero_mem _, ⟨_, ⟨h, zero_add _⟩⟩⟩⟩]
  · rintro ⟨y, ⟨hy, ⟨z, ⟨hz, rfl⟩⟩⟩⟩; exact add_mem _ (mem_sup_left hy) (mem_sup_right hz)

end sup

instance : SemilatticeInf (TwoSidedIdeal R) where
  inf I J := { ringCon := I.ringCon ⊓ J.ringCon }
  inf_le_left I J := by rw [ringCon_le_iff]; exact inf_le_left
  inf_le_right I J := by rw [ringCon_le_iff]; exact inf_le_right
  le_inf I J K h1 h2 := by rw [ringCon_le_iff] at h1 h2 ⊢; exact le_inf h1 h2

lemma inf_ringCon (I J : TwoSidedIdeal R) : (I ⊓ J).ringCon = I.ringCon ⊓ J.ringCon := rfl

lemma mem_inf {I J : TwoSidedIdeal R} {x : R} :
    x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J :=
  Iff.rfl

instance : SupSet (TwoSidedIdeal R) where
  sSup s := { ringCon := sSup <| TwoSidedIdeal.ringCon '' s }

lemma sSup_ringCon (S : Set (TwoSidedIdeal R)) :
    (sSup S).ringCon = sSup (TwoSidedIdeal.ringCon '' S) := rfl

lemma iSup_ringCon {ι : Type*} (I : ι → TwoSidedIdeal R) :
    (⨆ i, I i).ringCon = ⨆ i, (I i).ringCon := by
  simp only [iSup, sSup_ringCon]; congr; ext; simp

instance : CompleteSemilatticeSup (TwoSidedIdeal R) where
  sSup_le s I h := by simp_rw [ringCon_le_iff] at h ⊢; exact sSup_le <| by aesop
  le_sSup s I hI := by rw [ringCon_le_iff]; exact le_sSup <| by aesop

instance : InfSet (TwoSidedIdeal R) where
  sInf s := { ringCon := sInf <| TwoSidedIdeal.ringCon '' s }

lemma sInf_ringCon (S : Set (TwoSidedIdeal R)) :
    (sInf S).ringCon = sInf (TwoSidedIdeal.ringCon '' S) := rfl

lemma iInf_ringCon {ι : Type*} (I : ι → TwoSidedIdeal R) :
    (⨅ i, I i).ringCon = ⨅ i, (I i).ringCon := by
  simp only [iInf, sInf_ringCon]; congr!; ext; simp

instance : CompleteSemilatticeInf (TwoSidedIdeal R) where
  le_sInf s I h := by simp_rw [ringCon_le_iff] at h ⊢; exact le_sInf <| by aesop
  sInf_le s I hI := by rw [ringCon_le_iff]; exact sInf_le <| by aesop

lemma mem_iInf {ι : Type*} {I : ι → TwoSidedIdeal R} {x : R} :
    x ∈ iInf I ↔ ∀ i, x ∈ I i :=
  show (∀ _, _) ↔ _ by simp [mem_iff]

lemma mem_sInf {S : Set (TwoSidedIdeal R)} {x : R} :
    x ∈ sInf S ↔ ∀ I ∈ S, x ∈ I :=
  show (∀ _, _) ↔ _ by simp [mem_iff]

instance : Top (TwoSidedIdeal R) where
  top := { ringCon := ⊤ }

lemma top_ringCon : (⊤ : TwoSidedIdeal R).ringCon = ⊤ := rfl

@[simp]
lemma mem_top {x : R} : x ∈ (⊤: TwoSidedIdeal R) := trivial

instance : Bot (TwoSidedIdeal R) where
  bot := { ringCon := ⊥ }

lemma bot_ringCon : (⊥ : TwoSidedIdeal R).ringCon = ⊥ := rfl

@[simp]
lemma mem_bot {x : R} : x ∈ (⊥ : TwoSidedIdeal R) ↔ x = 0 :=
  Iff.rfl

instance : CompleteLattice (TwoSidedIdeal R) where
  __ := (inferInstance : SemilatticeSup (TwoSidedIdeal R))
  __ := (inferInstance : SemilatticeInf (TwoSidedIdeal R))
  __ := (inferInstance : CompleteSemilatticeSup (TwoSidedIdeal R))
  __ := (inferInstance : CompleteSemilatticeInf (TwoSidedIdeal R))
  le_top _ := by rw [ringCon_le_iff]; exact le_top
  bot_le _ := by rw [ringCon_le_iff]; exact bot_le

@[simp]
lemma coe_bot : ((⊥ : TwoSidedIdeal R) : Set R) = {0} := rfl

@[simp]
lemma coe_top : ((⊤ : TwoSidedIdeal R) : Set R) = Set.univ := rfl

lemma one_mem_iff {R : Type*} [NonAssocRing R] (I : TwoSidedIdeal R) :
    (1 : R) ∈ I ↔ I = ⊤ :=
  ⟨fun h => eq_top_iff.2 fun x _ => by simpa using I.mul_mem_left x _ h, fun h ↦ h.symm ▸ trivial⟩

alias ⟨eq_top, one_mem⟩ := one_mem_iff

end TwoSidedIdeal
