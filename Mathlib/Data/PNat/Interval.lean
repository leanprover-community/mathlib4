/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Ralf Stephan
-/
import Mathlib.Data.Nat.Interval
import Mathlib.Data.PNat.Defs
import Mathlib.Data.PNat.Basic

#align_import data.pnat.interval from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Finite intervals of positive naturals

This file proves that `ℕ+` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as finsets and fintypes.
-/


open Finset Function PNat

namespace PNat

variable (a b : ℕ+)

instance instLocallyFiniteOrder : LocallyFiniteOrder ℕ+ := Subtype.instLocallyFiniteOrder _

theorem Icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Icc_eq_finset_subtype PNat.Icc_eq_finset_subtype

theorem Ico_eq_finset_subtype : Ico a b = (Ico (a : ℕ) b).subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Ico_eq_finset_subtype PNat.Ico_eq_finset_subtype

theorem Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Ioc_eq_finset_subtype PNat.Ioc_eq_finset_subtype

theorem Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Ioo_eq_finset_subtype PNat.Ioo_eq_finset_subtype

theorem uIcc_eq_finset_subtype : uIcc a b = (uIcc (a : ℕ) b).subtype fun n : ℕ => 0 < n := rfl
#align pnat.uIcc_eq_finset_subtype PNat.uIcc_eq_finset_subtype

theorem map_subtype_embedding_Icc : (Icc a b).map (Embedding.subtype _) = Icc ↑a ↑b :=
  Finset.map_subtype_embedding_Icc _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Icc PNat.map_subtype_embedding_Icc

theorem map_subtype_embedding_Ico : (Ico a b).map (Embedding.subtype _) = Ico ↑a ↑b :=
  Finset.map_subtype_embedding_Ico _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Ico PNat.map_subtype_embedding_Ico

theorem map_subtype_embedding_Ioc : (Ioc a b).map (Embedding.subtype _) = Ioc ↑a ↑b :=
  Finset.map_subtype_embedding_Ioc _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Ioc PNat.map_subtype_embedding_Ioc

theorem map_subtype_embedding_Ioo : (Ioo a b).map (Embedding.subtype _) = Ioo ↑a ↑b :=
  Finset.map_subtype_embedding_Ioo _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Ioo PNat.map_subtype_embedding_Ioo

theorem map_subtype_embedding_uIcc : (uIcc a b).map (Embedding.subtype _) = uIcc ↑a ↑b :=
  map_subtype_embedding_Icc _ _
#align pnat.map_subtype_embedding_uIcc PNat.map_subtype_embedding_uIcc

@[simp]
theorem card_Icc : (Icc a b).card = b + 1 - a := by
  rw [← Nat.card_Icc]
  -- Porting note: I had to change this to `erw` *and* provide the proof, yuck.
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  erw [← Finset.map_subtype_embedding_Icc _ a b (fun c x _ hx _ hc _ => hc.trans_le hx)]
  rw [card_map]
#align pnat.card_Icc PNat.card_Icc

@[simp]
theorem card_Ico : (Ico a b).card = b - a := by
  rw [← Nat.card_Ico]
  -- Porting note: I had to change this to `erw` *and* provide the proof, yuck.
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  erw [← Finset.map_subtype_embedding_Ico _ a b (fun c x _ hx _ hc _ => hc.trans_le hx)]
  rw [card_map]
#align pnat.card_Ico PNat.card_Ico

@[simp]
theorem card_Ioc : (Ioc a b).card = b - a := by
  rw [← Nat.card_Ioc]
  -- Porting note: I had to change this to `erw` *and* provide the proof, yuck.
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  erw [← Finset.map_subtype_embedding_Ioc _ a b (fun c x _ hx _ hc _ => hc.trans_le hx)]
  rw [card_map]
#align pnat.card_Ioc PNat.card_Ioc

@[simp]
theorem card_Ioo : (Ioo a b).card = b - a - 1 := by
  rw [← Nat.card_Ioo]
  -- Porting note: I had to change this to `erw` *and* provide the proof, yuck.
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  erw [← Finset.map_subtype_embedding_Ioo _ a b (fun c x _ hx _ hc _ => hc.trans_le hx)]
  rw [card_map]
#align pnat.card_Ioo PNat.card_Ioo

@[simp]
theorem card_uIcc : (uIcc a b).card = (b - a : ℤ).natAbs + 1 := by
  rw [← Nat.card_uIcc, ← map_subtype_embedding_uIcc, card_map]
#align pnat.card_uIcc PNat.card_uIcc

-- Porting note: `simpNF` says `simp` can prove this
theorem card_fintype_Icc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [← card_Icc, Fintype.card_ofFinset]
#align pnat.card_fintype_Icc PNat.card_fintype_Icc

-- Porting note: `simpNF` says `simp` can prove this
theorem card_fintype_Ico : Fintype.card (Set.Ico a b) = b - a := by
  rw [← card_Ico, Fintype.card_ofFinset]
#align pnat.card_fintype_Ico PNat.card_fintype_Ico

-- Porting note: `simpNF` says `simp` can prove this
theorem card_fintype_Ioc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [← card_Ioc, Fintype.card_ofFinset]
#align pnat.card_fintype_Ioc PNat.card_fintype_Ioc

-- Porting note: `simpNF` says `simp` can prove this
theorem card_fintype_Ioo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [← card_Ioo, Fintype.card_ofFinset]
#align pnat.card_fintype_Ioo PNat.card_fintype_Ioo

-- Porting note: `simpNF` says `simp` can prove this
theorem card_fintype_uIcc : Fintype.card (Set.uIcc a b) = (b - a : ℤ).natAbs + 1 := by
  rw [← card_uIcc, Fintype.card_ofFinset]
#align pnat.card_fintype_uIcc PNat.card_fintype_uIcc

-- The following lemmas support Icc in combination with sub
theorem mem_insert_Icc_sub_one {a b x : ℕ+} (hab : a < b) (hins: x ∈ insert b (Icc a (b - 1))):
    a ≤ x ∧ x ≤ b := by
  rw [mem_insert, mem_Icc] at hins
  apply le_of_lt at hab
  rcases hins with hh | hh
  · rw [hh]; exact ⟨ hab, Eq.le rfl ⟩
  · exact ⟨ hh.1, PNat.le_of_le_sub_one hh.2 ⟩
#align pnat.mem_insert_Icc_sub_one PNat.mem_insert_Icc_sub_one

theorem insert_Icc_sub_one_right {a b : ℕ+} (hab : a < b) : insert b (Icc a (b - 1)) = Icc a b := by
  ext x
  constructor
  · intro h
    apply PNat.mem_insert_Icc_sub_one hab at h
    rw [mem_Icc]
    exact h
  · intro hh
    rw [mem_insert, mem_Icc]
    rw [mem_Icc] at hh
    have hl: x = b ∨ a ≤ x ∧ x ≤ b - 1 ↔ (x = b ∨ a ≤ x) ∧ (x = b ∨ x ≤ b - 1) :=
      Iff.intro (Or.rec (fun ha => ⟨.inl ha, .inl ha⟩) (.imp .inr .inr))
            (And.rec <| .rec (fun _ => .inl ·) (.imp_right ∘ .intro))
    rw [hl]
    constructor
    · exact Or.inr hh.1
    · rw [PNat.le_iff_eq_or_le_sub_one]
      exact hh.2
#align pnat.insert_Icc_sub_one_right PNat.insert_Icc_sub_one_right

end PNat
