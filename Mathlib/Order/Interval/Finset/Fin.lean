/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite intervals in `Fin n`

This file proves that `Fin n` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as Finsets and Fintypes.
-/

assert_not_exists MonoidWithZero

open Finset Function

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

theorem Icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).fin n :=
  rfl

theorem Ico_eq_finset_subtype : Ico a b = (Ico (a : ℕ) b).fin n :=
  rfl

theorem Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).fin n :=
  rfl

theorem Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).fin n :=
  rfl

theorem uIcc_eq_finset_subtype : uIcc a b = (uIcc (a : ℕ) b).fin n := rfl

@[simp]
theorem map_valEmbedding_Icc : (Icc a b).map Fin.valEmbedding = Icc ↑a ↑b := by
  simp [Icc_eq_finset_subtype, Finset.fin, Finset.map_map, Icc_filter_lt_of_lt_right]

@[simp]
theorem map_valEmbedding_Ico : (Ico a b).map Fin.valEmbedding = Ico ↑a ↑b := by
  simp [Ico_eq_finset_subtype, Finset.fin, Finset.map_map]

@[simp]
theorem map_valEmbedding_Ioc : (Ioc a b).map Fin.valEmbedding = Ioc ↑a ↑b := by
  simp [Ioc_eq_finset_subtype, Finset.fin, Finset.map_map, Ioc_filter_lt_of_lt_right]

@[simp]
theorem map_valEmbedding_Ioo : (Ioo a b).map Fin.valEmbedding = Ioo ↑a ↑b := by
  simp [Ioo_eq_finset_subtype, Finset.fin, Finset.map_map]

@[simp]
theorem map_subtype_embedding_uIcc : (uIcc a b).map valEmbedding = uIcc ↑a ↑b :=
  map_valEmbedding_Icc _ _

@[simp]
lemma card_Icc : #(Icc a b) = b + 1 - a := by rw [← Nat.card_Icc, ← map_valEmbedding_Icc, card_map]

@[simp]
lemma card_Ico : #(Ico a b) = b - a := by rw [← Nat.card_Ico, ← map_valEmbedding_Ico, card_map]

@[simp]
lemma card_Ioc : #(Ioc a b) = b - a := by rw [← Nat.card_Ioc, ← map_valEmbedding_Ioc, card_map]

@[simp]
lemma card_Ioo : #(Ioo a b) = b - a - 1 := by rw [← Nat.card_Ioo, ← map_valEmbedding_Ioo, card_map]

@[simp]
theorem card_uIcc : #(uIcc a b) = (b - a : ℤ).natAbs + 1 := by
  rw [← Nat.card_uIcc, ← map_subtype_embedding_uIcc, card_map]

theorem card_fintypeIcc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [← card_Icc, Fintype.card_ofFinset]

theorem card_fintypeIco : Fintype.card (Set.Ico a b) = b - a := by
  rw [← card_Ico, Fintype.card_ofFinset]

theorem card_fintypeIoc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [← card_Ioc, Fintype.card_ofFinset]

theorem card_fintypeIoo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [← card_Ioo, Fintype.card_ofFinset]

theorem card_fintype_uIcc : Fintype.card (Set.uIcc a b) = (b - a : ℤ).natAbs + 1 := by
  rw [← card_uIcc, Fintype.card_ofFinset]

theorem Ici_eq_finset_subtype : Ici a = (Icc (a : ℕ) n).fin n := by
  ext
  simp

theorem Ioi_eq_finset_subtype : Ioi a = (Ioc (a : ℕ) n).fin n := by
  ext
  simp

theorem Iic_eq_finset_subtype : Iic b = (Iic (b : ℕ)).fin n :=
  rfl

theorem Iio_eq_finset_subtype : Iio b = (Iio (b : ℕ)).fin n :=
  rfl

@[simp]
theorem map_valEmbedding_Ici : (Ici a).map Fin.valEmbedding = Icc ↑a (n - 1) := by
  ext x
  simp only [exists_prop, Embedding.coe_subtype, mem_Ici, mem_map, mem_Icc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, Nat.le_sub_of_add_le <| x.2⟩
  cases n
  · exact Fin.elim0 a
  · exact fun hx => ⟨⟨x, Nat.lt_succ_iff.2 hx.2⟩, hx.1, rfl⟩

@[simp]
theorem map_valEmbedding_Ioi : (Ioi a).map Fin.valEmbedding = Ioc ↑a (n - 1) := by
  ext x
  simp only [exists_prop, Embedding.coe_subtype, mem_Ioi, mem_map, mem_Ioc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, Nat.le_sub_of_add_le <| x.2⟩
  cases n
  · exact Fin.elim0 a
  · exact fun hx => ⟨⟨x, Nat.lt_succ_iff.2 hx.2⟩, hx.1, rfl⟩

@[simp]
theorem map_valEmbedding_Iic : (Iic b).map Fin.valEmbedding = Iic ↑b := by
  simp [Iic_eq_finset_subtype, Finset.fin, Finset.map_map, Iic_filter_lt_of_lt_right]

@[simp]
theorem map_valEmbedding_Iio : (Iio b).map Fin.valEmbedding = Iio ↑b := by
  simp [Iio_eq_finset_subtype, Finset.fin, Finset.map_map]

@[simp]
theorem card_Ici : #(Ici a) = n - a := by
  cases n with
  | zero => exact Fin.elim0 a
  | succ =>
    rw [← card_map, map_valEmbedding_Ici, Nat.card_Icc, Nat.add_one_sub_one]

@[simp]
theorem card_Ioi : #(Ioi a) = n - 1 - a := by rw [← card_map, map_valEmbedding_Ioi, Nat.card_Ioc]

@[simp]
theorem card_Iic : #(Iic b) = b + 1 := by rw [← Nat.card_Iic b, ← map_valEmbedding_Iic, card_map]

@[simp]
theorem card_Iio : #(Iio b) = b := by rw [← Nat.card_Iio b, ← map_valEmbedding_Iio, card_map]

theorem card_fintypeIci : Fintype.card (Set.Ici a) = n - a := by
  rw [Fintype.card_ofFinset, card_Ici]

theorem card_fintypeIoi : Fintype.card (Set.Ioi a) = n - 1 - a := by
  rw [Fintype.card_ofFinset, card_Ioi]

theorem card_fintypeIic : Fintype.card (Set.Iic b) = b + 1 := by
  rw [Fintype.card_ofFinset, card_Iic]

theorem card_fintypeIio : Fintype.card (Set.Iio b) = b := by
  rw [Fintype.card_ofFinset, card_Iio]

end Fin
