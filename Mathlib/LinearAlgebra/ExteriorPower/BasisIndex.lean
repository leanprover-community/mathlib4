/-
Copyright (c) 2026 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Finset.Card

/-!
# Helper lemmas for working with the index type of basis elements over the exterior power.
-/

@[expose] public section

namespace exteriorPower

abbrev basisIndex (I : Type*) (n : ℕ) := {a : Finset I // a.card = n}

namespace basisIndex

variable {I : Type*} {m n : ℕ}

section cast

def cast (h : m = n) : basisIndex I m ≃ basisIndex I n where
  toFun s := ⟨s.val, h ▸ s.prop⟩
  invFun t := ⟨t.val, h ▸ t.prop⟩

variable (h : m = n) (s : basisIndex I m) (t : basisIndex I n)

lemma cast_apply : (cast h s) = ⟨s.val, h ▸ s.prop⟩ := rfl

lemma cast_symm_apply : (cast h).symm t = ⟨t.val, h ▸ t.prop⟩ := rfl

@[simp]
lemma val_cast : (cast h s).val = s.val := rfl

@[simp]
lemma val_cast_symm : ((cast h).symm t).val = t.val := rfl

end cast

instance instSetLike : SetLike (basisIndex I n) I := SetLike.instSubtype

section basic

variable (s t : basisIndex I n)

@[simp]
lemma mem_val_iff (i : I) : i ∈ s.val ↔ i ∈ s := Iff.rfl

@[ext]
theorem ext (h : ∀ i, i ∈ s ↔ i ∈ t) : s = t := SetLike.ext h

@[ext]
theorem val_ext (h : ∀ i, i ∈ s.val ↔ i ∈ t.val) : s = t := SetLike.ext h

lemma eq_of_subset (h : s.val ⊆ t.val) : s = t := by
  apply Subtype.val_injective
  apply Finset.eq_of_subset_of_card_le h
  rw [s.prop, t.prop]

lemma eq_of_subset' (h : t.val ⊆ s.val) : s = t := by
  symm
  exact eq_of_subset t s h

end basic

section cons

variable (i : I) (s : basisIndex I m) (his : i ∉ s)

def cons : basisIndex I (m + 1) := ⟨Finset.cons i s.val his, by rw [Finset.card_cons his, s.prop]⟩

@[simp]
lemma val_cons : (s.cons i his).val = s.val.cons i his := rfl

lemma cons_inj_right (j : I) (hjs : j ∉ s) : s.cons i his = s.cons j hjs ↔ i = j := by
  rw [← Subtype.val_inj, val_cons, val_cons]
  refine ⟨?_, fun h => Finset.cons.congr_simp i j h s.val s.val rfl his⟩
  intro h
  apply Finset.eq_of_mem_cons_of_notMem hjs _ his
  rw [← h]
  exact Finset.mem_cons_self i s.val

lemma cons_inj_left (t : basisIndex I m) (hit : i ∉ t) : s.cons i his = t.cons i hit ↔ s = t := by
  rw [← Subtype.val_inj, val_cons, val_cons, ← Subtype.val_inj]
  refine ⟨?_, fun h => Finset.cons.congr_simp i i rfl s.val t.val h his⟩
  rw [subset_antisymm_iff, subset_antisymm_iff]
  exact fun h => ⟨Finset.cons_subset_cons.mp h.1, Finset.cons_subset_cons.mp h.2⟩

end cons

section erase

variable [DecidableEq I] (i : I) (s : basisIndex I m) (his : i ∈ s)

def erase : basisIndex I (m - 1) := ⟨s.val.erase i, by rw [Finset.card_erase_of_mem his, s.prop]⟩

@[simp]
lemma val_erase : (s.erase i his).val = s.val.erase i := rfl

lemma erase_inj_right (j : I) (hjs : j ∈ s) : s.erase i his = s.erase j hjs ↔ i = j := by
  rw [← Subtype.val_inj, val_erase, val_erase]
  exact Finset.erase_inj s.val his

lemma erase_inj_left (t : basisIndex I m) (hit : i ∈ t) :
    s.erase i his = t.erase i hit ↔ s = t := by
  rw [← Subtype.val_inj, val_erase, val_erase, ← Subtype.val_inj]
  refine ⟨?_, fun h => Finset.erase.congr_simp s.val t.val h i i rfl⟩
  intro h
  apply subset_antisymm
  · rw [← Finset.erase_subset_iff_of_mem hit, h]
    exact Finset.erase_subset i t.val
  · rw [← Finset.erase_subset_iff_of_mem his, ← h]
    exact Finset.erase_subset i s.val

end erase

section disjUnion

variable (s : basisIndex I m) (t : basisIndex I n) (hst : Disjoint s.val t.val)

def disjUnion : basisIndex I (m + n) :=
  ⟨s.val.disjUnion t.val hst, by rw [Finset.card_disjUnion, s.prop, t.prop]⟩

@[simp]
lemma val_disjUnion : (s.disjUnion t hst).val = s.val.disjUnion t.val hst := rfl

lemma disjUnion_val_comm : (s.disjUnion t hst).val = (t.disjUnion s hst.symm).val := by
  rw [val_disjUnion, val_disjUnion, Finset.disjUnion_comm]

lemma disjUnion_comm :
    s.disjUnion t hst = cast (add_comm n m) (t.disjUnion s hst.symm) := by
  apply Subtype.val_injective
  rw [val_cast, disjUnion_val_comm]

lemma disjUnion_inj_right (r : basisIndex I n) (hsr : Disjoint s.val r.val) :
    s.disjUnion r hsr = s.disjUnion t hst ↔ r = t := by
  rw [← Subtype.val_inj, val_disjUnion, val_disjUnion, ← Subtype.val_inj]
  exact Finset.disjUnion_inj_right hsr hst

lemma disjUnion_inj_left (r : basisIndex I m) (hrt : Disjoint r.val t.val) :
    s.disjUnion t hst = r.disjUnion t hrt ↔ s = r := by
  rw [← Subtype.val_inj, val_disjUnion, val_disjUnion, ← Subtype.val_inj]
  exact Finset.disjUnion_inj_left hst hrt

end disjUnion

section sdiff

variable [DecidableEq I] (s : basisIndex I m) (t : basisIndex I n) (hts : t.val ⊆ s.val)

def sdiff : basisIndex I (m - n) :=
  ⟨s.val \ t.val, by rw [Finset.card_sdiff_of_subset hts, s.prop, t.prop]⟩

@[simp]
lemma val_sdiff : (s.sdiff t hts).val = s.val \ t.val := rfl

lemma sdiff_inj_right (r : basisIndex I n) (hrs : r.val ⊆ s.val) :
    s.sdiff r hrs = s.sdiff t hts ↔ r = t := by
  rw [← Subtype.val_inj, val_sdiff, val_sdiff, ← Subtype.val_inj]
  refine ⟨?_, fun h => by rw [h]⟩
  intro h
  rw [subset_antisymm_iff] at h
  apply subset_antisymm ((Finset.sdiff_subset_sdiff_iff_subset hts hrs).mp h.2)
  exact (Finset.sdiff_subset_sdiff_iff_subset hrs hts).mp h.1

lemma sdiff_inj_left (r : basisIndex I m) (htr : t.val ⊆ r.val) :
    s.sdiff t hts = r.sdiff t htr ↔ s = r := by
  rw [← Subtype.val_inj, val_sdiff, val_sdiff, ← Subtype.val_inj]
  refine ⟨?_, fun h => by rw [h]⟩
  exact fun h => by rw [← Finset.sdiff_union_of_subset hts, ← Finset.sdiff_union_of_subset htr, h]

end sdiff

end basisIndex

end exteriorPower
