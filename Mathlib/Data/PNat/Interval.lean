/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Nat.Interval
import Mathlib.Data.PNat.Defs

#align_import data.pnat.interval from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Finite intervals of positive naturals

This file proves that `ℕ+` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as finsets and fintypes.
-/


open Finset Function PNat

instance : LocallyFiniteOrder ℕ+ :=
  Subtype.instLocallyFiniteOrder _

namespace PNat

variable (a b : ℕ+)

theorem Icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).subtype fun n : ℕ => 0 < n :=
  rfl

theorem Ico_eq_finset_subtype : Ico a b = (Ico (a : ℕ) b).subtype fun n : ℕ => 0 < n :=
  rfl

theorem Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).subtype fun n : ℕ => 0 < n :=
  rfl

theorem Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).subtype fun n : ℕ => 0 < n :=
  rfl

theorem uIcc_eq_finset_subtype : uIcc a b = (uIcc (a : ℕ) b).subtype fun n : ℕ => 0 < n := rfl

theorem map_subtype_embedding_Icc : (Icc a b).map (Embedding.subtype _) = Icc ↑a ↑b :=
  Finset.map_subtype_embedding_Icc _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

theorem map_subtype_embedding_Ico : (Ico a b).map (Embedding.subtype _) = Ico ↑a ↑b :=
  Finset.map_subtype_embedding_Ico _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

theorem map_subtype_embedding_Ioc : (Ioc a b).map (Embedding.subtype _) = Ioc ↑a ↑b :=
  Finset.map_subtype_embedding_Ioc _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

theorem map_subtype_embedding_Ioo : (Ioo a b).map (Embedding.subtype _) = Ioo ↑a ↑b :=
  Finset.map_subtype_embedding_Ioo _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

theorem map_subtype_embedding_uIcc : (uIcc a b).map (Embedding.subtype _) = uIcc ↑a ↑b :=
  map_subtype_embedding_Icc _ _

@[simp]
theorem card_Icc : (Icc a b).card = b + 1 - a := by
  rw [← Nat.card_Icc]
  -- porting note: I had to change this to `erw` *and* provide the proof, yuck.
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  erw [← Finset.map_subtype_embedding_Icc _ a b (fun c x _ hx _ hc _ => hc.trans_le hx)]
  rw [card_map]

@[simp]
theorem card_Ico : (Ico a b).card = b - a := by
  rw [← Nat.card_Ico]
  -- porting note: I had to change this to `erw` *and* provide the proof, yuck.
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  erw [← Finset.map_subtype_embedding_Ico _ a b (fun c x _ hx _ hc _ => hc.trans_le hx)]
  rw [card_map]

@[simp]
theorem card_Ioc : (Ioc a b).card = b - a := by
  rw [← Nat.card_Ioc]
  -- porting note: I had to change this to `erw` *and* provide the proof, yuck.
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  erw [← Finset.map_subtype_embedding_Ioc _ a b (fun c x _ hx _ hc _ => hc.trans_le hx)]
  rw [card_map]

@[simp]
theorem card_Ioo : (Ioo a b).card = b - a - 1 := by
  rw [← Nat.card_Ioo]
  -- porting note: I had to change this to `erw` *and* provide the proof, yuck.
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  erw [← Finset.map_subtype_embedding_Ioo _ a b (fun c x _ hx _ hc _ => hc.trans_le hx)]
  rw [card_map]

@[simp]
theorem card_uIcc : (uIcc a b).card = (b - a : ℤ).natAbs + 1 := by
  rw [←Nat.card_uIcc, ←map_subtype_embedding_uIcc, card_map]

-- porting note: `simpNF` says `simp` can prove this
theorem card_fintype_Icc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [← card_Icc, Fintype.card_ofFinset]

-- porting note: `simpNF` says `simp` can prove this
theorem card_fintype_Ico : Fintype.card (Set.Ico a b) = b - a := by
  rw [← card_Ico, Fintype.card_ofFinset]

-- porting note: `simpNF` says `simp` can prove this
theorem card_fintype_Ioc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [← card_Ioc, Fintype.card_ofFinset]

-- porting note: `simpNF` says `simp` can prove this
theorem card_fintype_Ioo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [← card_Ioo, Fintype.card_ofFinset]

-- porting note: `simpNF` says `simp` can prove this
theorem card_fintype_uIcc : Fintype.card (Set.uIcc a b) = (b - a : ℤ).natAbs + 1 := by
  rw [←card_uIcc, Fintype.card_ofFinset]

end PNat
