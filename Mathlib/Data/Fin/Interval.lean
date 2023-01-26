/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.fin.interval
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Interval
import Mathbin.Data.Finset.LocallyFinite

/-!
# Finite intervals in `fin n`

This file proves that `fin n` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/


open Finset Fin Function

open BigOperators

variable (n : ℕ)

instance : LocallyFiniteOrder (Fin n) :=
  OrderIso.locallyFiniteOrder Fin.orderIsoSubtype

instance : LocallyFiniteOrderBot (Fin n) :=
  OrderIso.locallyFiniteOrderBot Fin.orderIsoSubtype

instance : ∀ n, LocallyFiniteOrderTop (Fin n)
  | 0 => IsEmpty.toLocallyFiniteOrderTop
  | n + 1 => inferInstance

namespace Fin

variable {n} (a b : Fin n)

theorem icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).Fin n :=
  rfl
#align fin.Icc_eq_finset_subtype Fin.icc_eq_finset_subtype

theorem ico_eq_finset_subtype : Ico a b = (Ico (a : ℕ) b).Fin n :=
  rfl
#align fin.Ico_eq_finset_subtype Fin.ico_eq_finset_subtype

theorem ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).Fin n :=
  rfl
#align fin.Ioc_eq_finset_subtype Fin.ioc_eq_finset_subtype

theorem ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).Fin n :=
  rfl
#align fin.Ioo_eq_finset_subtype Fin.ioo_eq_finset_subtype

@[simp]
theorem map_subtype_embedding_icc : (Icc a b).map Fin.valEmbedding = Icc a b := by
  simp [Icc_eq_finset_subtype, Finset.fin, Finset.map_map, Icc_filter_lt_of_lt_right]
#align fin.map_subtype_embedding_Icc Fin.map_subtype_embedding_icc

@[simp]
theorem map_subtype_embedding_ico : (Ico a b).map Fin.valEmbedding = Ico a b := by
  simp [Ico_eq_finset_subtype, Finset.fin, Finset.map_map]
#align fin.map_subtype_embedding_Ico Fin.map_subtype_embedding_ico

@[simp]
theorem map_subtype_embedding_ioc : (Ioc a b).map Fin.valEmbedding = Ioc a b := by
  simp [Ioc_eq_finset_subtype, Finset.fin, Finset.map_map, Ioc_filter_lt_of_lt_right]
#align fin.map_subtype_embedding_Ioc Fin.map_subtype_embedding_ioc

@[simp]
theorem map_subtype_embedding_ioo : (Ioo a b).map Fin.valEmbedding = Ioo a b := by
  simp [Ioo_eq_finset_subtype, Finset.fin, Finset.map_map]
#align fin.map_subtype_embedding_Ioo Fin.map_subtype_embedding_ioo

@[simp]
theorem card_icc : (Icc a b).card = b + 1 - a := by
  rw [← Nat.card_icc, ← map_subtype_embedding_Icc, card_map]
#align fin.card_Icc Fin.card_icc

@[simp]
theorem card_ico : (Ico a b).card = b - a := by
  rw [← Nat.card_ico, ← map_subtype_embedding_Ico, card_map]
#align fin.card_Ico Fin.card_ico

@[simp]
theorem card_ioc : (Ioc a b).card = b - a := by
  rw [← Nat.card_ioc, ← map_subtype_embedding_Ioc, card_map]
#align fin.card_Ioc Fin.card_ioc

@[simp]
theorem card_ioo : (Ioo a b).card = b - a - 1 := by
  rw [← Nat.card_ioo, ← map_subtype_embedding_Ioo, card_map]
#align fin.card_Ioo Fin.card_ioo

@[simp]
theorem card_fintypeIcc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [← card_Icc, Fintype.card_ofFinset]
#align fin.card_fintype_Icc Fin.card_fintypeIcc

@[simp]
theorem card_fintypeIco : Fintype.card (Set.Ico a b) = b - a := by
  rw [← card_Ico, Fintype.card_ofFinset]
#align fin.card_fintype_Ico Fin.card_fintypeIco

@[simp]
theorem card_fintypeIoc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [← card_Ioc, Fintype.card_ofFinset]
#align fin.card_fintype_Ioc Fin.card_fintypeIoc

@[simp]
theorem card_fintypeIoo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [← card_Ioo, Fintype.card_ofFinset]
#align fin.card_fintype_Ioo Fin.card_fintypeIoo

theorem ici_eq_finset_subtype : Ici a = (Icc (a : ℕ) n).Fin n :=
  by
  ext
  simp
#align fin.Ici_eq_finset_subtype Fin.ici_eq_finset_subtype

theorem ioi_eq_finset_subtype : Ioi a = (Ioc (a : ℕ) n).Fin n :=
  by
  ext
  simp
#align fin.Ioi_eq_finset_subtype Fin.ioi_eq_finset_subtype

theorem iic_eq_finset_subtype : Iic b = (Iic (b : ℕ)).Fin n :=
  rfl
#align fin.Iic_eq_finset_subtype Fin.iic_eq_finset_subtype

theorem iio_eq_finset_subtype : Iio b = (Iio (b : ℕ)).Fin n :=
  rfl
#align fin.Iio_eq_finset_subtype Fin.iio_eq_finset_subtype

@[simp]
theorem map_subtype_embedding_ici : (Ici a).map Fin.valEmbedding = Icc a (n - 1) :=
  by
  ext x
  simp only [exists_prop, embedding.coe_subtype, mem_Ici, mem_map, mem_Icc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, le_tsub_of_add_le_right <| x.2⟩
  cases n
  · exact Fin.elim0 a
  · exact fun hx => ⟨⟨x, Nat.lt_succ_iff.2 hx.2⟩, hx.1, rfl⟩
#align fin.map_subtype_embedding_Ici Fin.map_subtype_embedding_ici

@[simp]
theorem map_subtype_embedding_ioi : (Ioi a).map Fin.valEmbedding = Ioc a (n - 1) :=
  by
  ext x
  simp only [exists_prop, embedding.coe_subtype, mem_Ioi, mem_map, mem_Ioc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, le_tsub_of_add_le_right <| x.2⟩
  cases n
  · exact Fin.elim0 a
  · exact fun hx => ⟨⟨x, Nat.lt_succ_iff.2 hx.2⟩, hx.1, rfl⟩
#align fin.map_subtype_embedding_Ioi Fin.map_subtype_embedding_ioi

@[simp]
theorem map_subtype_embedding_iic : (Iic b).map Fin.valEmbedding = Iic b := by
  simp [Iic_eq_finset_subtype, Finset.fin, Finset.map_map, Iic_filter_lt_of_lt_right]
#align fin.map_subtype_embedding_Iic Fin.map_subtype_embedding_iic

@[simp]
theorem map_subtype_embedding_iio : (Iio b).map Fin.valEmbedding = Iio b := by
  simp [Iio_eq_finset_subtype, Finset.fin, Finset.map_map]
#align fin.map_subtype_embedding_Iio Fin.map_subtype_embedding_iio

@[simp]
theorem card_ici : (Ici a).card = n - a := by
  cases n
  · exact Fin.elim0 a
  rw [← card_map, map_subtype_embedding_Ici, Nat.card_icc]
  rfl
#align fin.card_Ici Fin.card_ici

@[simp]
theorem card_ioi : (Ioi a).card = n - 1 - a := by
  rw [← card_map, map_subtype_embedding_Ioi, Nat.card_ioc]
#align fin.card_Ioi Fin.card_ioi

@[simp]
theorem card_iic : (Iic b).card = b + 1 := by
  rw [← Nat.card_iic b, ← map_subtype_embedding_Iic, card_map]
#align fin.card_Iic Fin.card_iic

@[simp]
theorem card_iio : (Iio b).card = b := by
  rw [← Nat.card_iio b, ← map_subtype_embedding_Iio, card_map]
#align fin.card_Iio Fin.card_iio

@[simp]
theorem card_fintypeIci : Fintype.card (Set.Ici a) = n - a := by
  rw [Fintype.card_ofFinset, card_Ici]
#align fin.card_fintype_Ici Fin.card_fintypeIci

@[simp]
theorem card_fintypeIoi : Fintype.card (Set.Ioi a) = n - 1 - a := by
  rw [Fintype.card_ofFinset, card_Ioi]
#align fin.card_fintype_Ioi Fin.card_fintypeIoi

@[simp]
theorem card_fintypeIic : Fintype.card (Set.Iic b) = b + 1 := by
  rw [Fintype.card_ofFinset, card_Iic]
#align fin.card_fintype_Iic Fin.card_fintypeIic

@[simp]
theorem card_fintypeIio : Fintype.card (Set.Iio b) = b := by rw [Fintype.card_ofFinset, card_Iio]
#align fin.card_fintype_Iio Fin.card_fintypeIio

end Fin

