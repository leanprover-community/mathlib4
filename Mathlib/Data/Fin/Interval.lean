/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Nat.Interval
import Mathlib.Order.Interval.Finset.Basic

#align_import data.fin.interval from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Finite intervals in `Fin n`

This file proves that `Fin n` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as Finsets and Fintypes.
-/

namespace Fin

variable {n : ℕ} (a b : Fin n)

@[simp, norm_cast]
lemma coe_sup : ↑(a ⊔ b) = (a ⊔ b : ℕ) := rfl
#align fin.coe_sup Fin.coe_sup

@[simp, norm_cast]
lemma coe_inf : ↑(a ⊓ b) = (a ⊓ b : ℕ) := rfl
#align fin.coe_inf Fin.coe_inf

@[simp, norm_cast]
lemma coe_max : ↑(max a b) = (max a b : ℕ) := rfl
#align fin.coe_max Fin.coe_max

@[simp, norm_cast]
lemma coe_min : ↑(min a b) = (min a b : ℕ) := rfl
#align fin.coe_min Fin.coe_min

end Fin

open Finset Fin Function

namespace Fin

variable (n : ℕ)

instance instLocallyFiniteOrder : LocallyFiniteOrder (Fin n) :=
  OrderIso.locallyFiniteOrder Fin.orderIsoSubtype

instance instLocallyFiniteOrderBot : LocallyFiniteOrderBot (Fin n) :=
  OrderIso.locallyFiniteOrderBot Fin.orderIsoSubtype

instance instLocallyFiniteOrderTop : ∀ n, LocallyFiniteOrderTop (Fin n)
  | 0 => IsEmpty.toLocallyFiniteOrderTop
  | _ + 1 => inferInstance

variable {n} (a b : Fin n)

lemma Icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).fin n :=
  rfl
#align fin.Icc_eq_finset_subtype Fin.Icc_eq_finset_subtype

lemma Ico_eq_finset_subtype : Ico a b = (Ico (a : ℕ) b).fin n :=
  rfl
#align fin.Ico_eq_finset_subtype Fin.Ico_eq_finset_subtype

lemma Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).fin n :=
  rfl
#align fin.Ioc_eq_finset_subtype Fin.Ioc_eq_finset_subtype

lemma Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).fin n :=
  rfl
#align fin.Ioo_eq_finset_subtype Fin.Ioo_eq_finset_subtype

lemma uIcc_eq_finset_subtype : uIcc a b = (uIcc (a : ℕ) b).fin n := rfl
#align fin.uIcc_eq_finset_subtype Fin.uIcc_eq_finset_subtype

@[simp]
lemma map_valEmbedding_Icc : (Icc a b).map Fin.valEmbedding = Icc ↑a ↑b := by
  simp [Icc_eq_finset_subtype, Finset.fin, Finset.map_map, Icc_filter_lt_of_lt_right]
#align fin.map_subtype_embedding_Icc Fin.map_valEmbedding_Icc

@[simp]
lemma map_valEmbedding_Ico : (Ico a b).map Fin.valEmbedding = Ico ↑a ↑b := by
  simp [Ico_eq_finset_subtype, Finset.fin, Finset.map_map]
#align fin.map_subtype_embedding_Ico Fin.map_valEmbedding_Ico

@[simp]
lemma map_valEmbedding_Ioc : (Ioc a b).map Fin.valEmbedding = Ioc ↑a ↑b := by
  simp [Ioc_eq_finset_subtype, Finset.fin, Finset.map_map, Ioc_filter_lt_of_lt_right]
#align fin.map_subtype_embedding_Ioc Fin.map_valEmbedding_Ioc

@[simp]
lemma map_valEmbedding_Ioo : (Ioo a b).map Fin.valEmbedding = Ioo ↑a ↑b := by
  simp [Ioo_eq_finset_subtype, Finset.fin, Finset.map_map]
#align fin.map_subtype_embedding_Ioo Fin.map_valEmbedding_Ioo

@[simp]
lemma map_subtype_embedding_uIcc : (uIcc a b).map valEmbedding = uIcc ↑a ↑b :=
  map_valEmbedding_Icc _ _
#align fin.map_subtype_embedding_uIcc Fin.map_subtype_embedding_uIcc

@[simp]
lemma card_Icc : (Icc a b).card = b + 1 - a := by
  rw [← Nat.card_Icc, ← map_valEmbedding_Icc, card_map]
#align fin.card_Icc Fin.card_Icc

@[simp]
lemma card_Ico : (Ico a b).card = b - a := by
  rw [← Nat.card_Ico, ← map_valEmbedding_Ico, card_map]
#align fin.card_Ico Fin.card_Ico

@[simp]
lemma card_Ioc : (Ioc a b).card = b - a := by
  rw [← Nat.card_Ioc, ← map_valEmbedding_Ioc, card_map]
#align fin.card_Ioc Fin.card_Ioc

@[simp]
lemma card_Ioo : (Ioo a b).card = b - a - 1 := by
  rw [← Nat.card_Ioo, ← map_valEmbedding_Ioo, card_map]
#align fin.card_Ioo Fin.card_Ioo

@[simp]
lemma card_uIcc : (uIcc a b).card = (b - a : ℤ).natAbs + 1 := by
  rw [← Nat.card_uIcc, ← map_subtype_embedding_uIcc, card_map]
#align fin.card_uIcc Fin.card_uIcc

-- Porting note (#10618): simp can prove this
-- @[simp]
lemma card_fintypeIcc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [← card_Icc, Fintype.card_ofFinset]
#align fin.card_fintype_Icc Fin.card_fintypeIcc

-- Porting note (#10618): simp can prove this
-- @[simp]
lemma card_fintypeIco : Fintype.card (Set.Ico a b) = b - a := by
  rw [← card_Ico, Fintype.card_ofFinset]
#align fin.card_fintype_Ico Fin.card_fintypeIco

-- Porting note (#10618): simp can prove this
-- @[simp]
lemma card_fintypeIoc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [← card_Ioc, Fintype.card_ofFinset]
#align fin.card_fintype_Ioc Fin.card_fintypeIoc

-- Porting note (#10618): simp can prove this
-- @[simp]
lemma card_fintypeIoo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [← card_Ioo, Fintype.card_ofFinset]
#align fin.card_fintype_Ioo Fin.card_fintypeIoo

lemma card_fintype_uIcc : Fintype.card (Set.uIcc a b) = (b - a : ℤ).natAbs + 1 := by
  rw [← card_uIcc, Fintype.card_ofFinset]
#align fin.card_fintype_uIcc Fin.card_fintype_uIcc

lemma Ici_eq_finset_subtype : Ici a = (Icc (a : ℕ) n).fin n := by
  ext
  simp
#align fin.Ici_eq_finset_subtype Fin.Ici_eq_finset_subtype

lemma Ioi_eq_finset_subtype : Ioi a = (Ioc (a : ℕ) n).fin n := by
  ext
  simp
#align fin.Ioi_eq_finset_subtype Fin.Ioi_eq_finset_subtype

lemma Iic_eq_finset_subtype : Iic b = (Iic (b : ℕ)).fin n :=
  rfl
#align fin.Iic_eq_finset_subtype Fin.Iic_eq_finset_subtype

lemma Iio_eq_finset_subtype : Iio b = (Iio (b : ℕ)).fin n :=
  rfl
#align fin.Iio_eq_finset_subtype Fin.Iio_eq_finset_subtype

@[simp]
lemma map_valEmbedding_Ici : (Ici a).map Fin.valEmbedding = Icc ↑a (n - 1) := by
-- Porting note: without `clear b` Lean includes `b` in the statement (because the `rfl`) in the
-- `rintro` below acts on it.
  clear b
  ext x
  simp only [exists_prop, Embedding.coe_subtype, mem_Ici, mem_map, mem_Icc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, le_tsub_of_add_le_right <| x.2⟩
  cases n
  · exact Fin.elim0 a
  · exact fun hx => ⟨⟨x, Nat.lt_succ_iff.2 hx.2⟩, hx.1, rfl⟩
#align fin.map_subtype_embedding_Ici Fin.map_valEmbedding_Ici

@[simp]
lemma map_valEmbedding_Ioi : (Ioi a).map Fin.valEmbedding = Ioc ↑a (n - 1) := by
-- Porting note: without `clear b` Lean includes `b` in the statement (because the `rfl`) in the
-- `rintro` below acts on it.
  clear b
  ext x
  simp only [exists_prop, Embedding.coe_subtype, mem_Ioi, mem_map, mem_Ioc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, le_tsub_of_add_le_right <| x.2⟩
  cases n
  · exact Fin.elim0 a
  · exact fun hx => ⟨⟨x, Nat.lt_succ_iff.2 hx.2⟩, hx.1, rfl⟩
#align fin.map_subtype_embedding_Ioi Fin.map_valEmbedding_Ioi

@[simp]
lemma map_valEmbedding_Iic : (Iic b).map Fin.valEmbedding = Iic ↑b := by
  simp [Iic_eq_finset_subtype, Finset.fin, Finset.map_map, Iic_filter_lt_of_lt_right]
#align fin.map_subtype_embedding_Iic Fin.map_valEmbedding_Iic

@[simp]
lemma map_valEmbedding_Iio : (Iio b).map Fin.valEmbedding = Iio ↑b := by
  simp [Iio_eq_finset_subtype, Finset.fin, Finset.map_map]
#align fin.map_subtype_embedding_Iio Fin.map_valEmbedding_Iio

@[simp]
lemma card_Ici : (Ici a).card = n - a := by
-- Porting note: without `clear b` Lean includes `b` in the statement.
  clear b
  cases n with
  | zero => exact Fin.elim0 a
  | succ =>
    rw [← card_map, map_valEmbedding_Ici, Nat.card_Icc, Nat.add_one_sub_one]
#align fin.card_Ici Fin.card_Ici

@[simp]
lemma card_Ioi : (Ioi a).card = n - 1 - a := by
  rw [← card_map, map_valEmbedding_Ioi, Nat.card_Ioc]
#align fin.card_Ioi Fin.card_Ioi

@[simp]
lemma card_Iic : (Iic b).card = b + 1 := by
  rw [← Nat.card_Iic b, ← map_valEmbedding_Iic, card_map]
#align fin.card_Iic Fin.card_Iic

@[simp]
lemma card_Iio : (Iio b).card = b := by
  rw [← Nat.card_Iio b, ← map_valEmbedding_Iio, card_map]
#align fin.card_Iio Fin.card_Iio

-- Porting note (#10618): simp can prove this
-- @[simp]
lemma card_fintypeIci : Fintype.card (Set.Ici a) = n - a := by
  rw [Fintype.card_ofFinset, card_Ici]
#align fin.card_fintype_Ici Fin.card_fintypeIci

-- Porting note (#10618): simp can prove this
-- @[simp]
lemma card_fintypeIoi : Fintype.card (Set.Ioi a) = n - 1 - a := by
  rw [Fintype.card_ofFinset, card_Ioi]
#align fin.card_fintype_Ioi Fin.card_fintypeIoi

-- Porting note (#10618): simp can prove this
-- @[simp]
lemma card_fintypeIic : Fintype.card (Set.Iic b) = b + 1 := by
  rw [Fintype.card_ofFinset, card_Iic]
#align fin.card_fintype_Iic Fin.card_fintypeIic

-- Porting note (#10618): simp can prove this
-- @[simp]
lemma card_fintypeIio : Fintype.card (Set.Iio b) = b := by
  rw [Fintype.card_ofFinset, card_Iio]
#align fin.card_fintype_Iio Fin.card_fintypeIio

end Fin
