/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
import Mathlib.Order.Interval.Set.Fin
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

/-!
### Locally finite order etc instances
-/

instance instLocallyFiniteOrder : LocallyFiniteOrder (Fin n) :=
  OrderIso.locallyFiniteOrder Fin.orderIsoSubtype

instance instLocallyFiniteOrderBot : LocallyFiniteOrderBot (Fin n) :=
  OrderIso.locallyFiniteOrderBot Fin.orderIsoSubtype

instance instLocallyFiniteOrderTop : ∀ n, LocallyFiniteOrderTop (Fin n)
  | 0 => IsEmpty.toLocallyFiniteOrderTop
  | _ + 1 => inferInstance

end Fin

namespace Finset

variable {n} (a b : Fin n)

@[simp]
theorem fin_Icc_val_val : (Icc (a : ℕ) b).fin n = Icc a b := rfl

theorem Icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).fin n := rfl
theorem Ico_eq_finset_subtype : Ico a b = (Ico (a : ℕ) b).fin n := rfl
theorem Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).fin n := rfl
theorem Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).fin n := rfl
theorem uIcc_eq_finset_subtype : uIcc a b = (uIcc (a : ℕ) b).fin n := rfl

@[simp]
theorem finsetImage_val_Icc : (Icc a b).image val = Icc (a : ℕ) b := by simp [← coe_inj]

@[simp]
theorem map_valEmbedding_Icc : (Icc a b).map valEmbedding = Icc ↑a ↑b := by simp [map_eq_image]

@[simp]
theorem finsetImage_val_Ico : (Ico a b).image val = Ico (a : ℕ) b := by simp [← coe_inj]

@[simp]
theorem map_valEmbedding_Ico : (Ico a b).map valEmbedding = Ico ↑a ↑b := by simp [map_eq_image]

@[simp]
theorem finsetImage_val_Ioc : (Ioc a b).image val = Ioc (a : ℕ) b := by simp [← coe_inj]

@[simp]
theorem map_valEmbedding_Ioc : (Ioc a b).map valEmbedding = Ioc ↑a ↑b := by simp [map_eq_image]

@[simp]
theorem finsetImage_val_Ioo : (Ioo a b).image val = Ioo (a : ℕ) b := by simp [← coe_inj]

@[simp]
theorem map_valEmbedding_Ioo : (Ioo a b).map valEmbedding = Ioo ↑a ↑b := by simp [map_eq_image]

@[simp]
theorem map_subtype_embedding_uIcc : (uIcc a b).map valEmbedding = uIcc ↑a ↑b :=
  map_valEmbedding_Icc _ _

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
theorem map_valEmbedding_Ici : (Ici a).map valEmbedding = Ico ↑a n := by simp [← coe_inj]

@[simp]
theorem map_valEmbedding_Ioi : (Ioi a).map valEmbedding = Ioo ↑a n := by simp [← coe_inj]

@[simp]
theorem map_valEmbedding_Iic : (Iic b).map valEmbedding = Iic ↑b := by simp [← coe_inj]

@[simp]
theorem map_valEmbedding_Iio : (Iio b).map valEmbedding = Iio ↑b := by
  simp [Iio_eq_finset_subtype, Finset.fin, Finset.map_map]

@[simp]
theorem card_Ici : #(Ici a) = n - a := by rw [← card_map, map_valEmbedding_Ici, Nat.card_Ico]

@[simp]
theorem card_Ioi : #(Ioi a) = n - 1 - a := by
  rw [← card_map, map_valEmbedding_Ioi, Nat.card_Ioo, Nat.sub_right_comm]

@[simp]
theorem card_Iic : #(Iic b) = b + 1 := by rw [← Nat.card_Iic b, ← map_valEmbedding_Iic, card_map]

@[simp]
theorem card_Iio : #(Iio b) = b := by rw [← Nat.card_Iio b, ← map_valEmbedding_Iio, card_map]


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


theorem fintypeCard_Ici : Fintype.card (Set.Ici a) = n - a := by simp

@[deprecated (since := "2025-03-12")]
alias card_fintypeIci := fintypeCard_Ici

theorem fintypeCard_Ioi : Fintype.card (Set.Ioi a) = n - 1 - a := by simp

@[deprecated (since := "2025-03-12")]
alias card_fintypeIoi := fintypeCard_Ioi

theorem fintypeCard_Iic : Fintype.card (Set.Iic b) = b + 1 := by simp

@[deprecated (since := "2025-03-12")]
alias card_fintypeIic := fintypeCard_Iic

theorem fintypeCard_Iio : Fintype.card (Set.Iio b) = b := by simp

@[deprecated (since := "2025-03-12")]
alias card_fintypeIio := fintypeCard_Iio

end Fin
