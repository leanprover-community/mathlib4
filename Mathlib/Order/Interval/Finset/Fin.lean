/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
import Mathlib.Data.Finset.Fin
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

instance instLocallyFiniteOrder (n : ℕ) : LocallyFiniteOrder (Fin n) where
  finsetIcc a b := attachFin (Icc a b) fun x hx ↦ (mem_Icc.mp hx).2.trans_lt b.2
  finsetIco a b := attachFin (Ico a b) fun x hx ↦ (mem_Ico.mp hx).2.trans b.2
  finsetIoc a b := attachFin (Ioc a b) fun x hx ↦ (mem_Ioc.mp hx).2.trans_lt b.2
  finsetIoo a b := attachFin (Ioo a b) fun x hx ↦ (mem_Ioo.mp hx).2.trans b.2
  finset_mem_Icc a b := by simp
  finset_mem_Ico a b := by simp
  finset_mem_Ioc a b := by simp
  finset_mem_Ioo a b := by simp

instance instLocallyFiniteOrderBot : ∀ n, LocallyFiniteOrderBot (Fin n)
  | 0 => IsEmpty.toLocallyFiniteOrderBot
  | _ + 1 => inferInstance

instance instLocallyFiniteOrderTop : ∀ n, LocallyFiniteOrderTop (Fin n)
  | 0 => IsEmpty.toLocallyFiniteOrderTop
  | _ + 1 => inferInstance

variable {n}
variable {m : ℕ} (a b : Fin n)

@[simp]
theorem attachFin_Icc :
    attachFin (Icc a b) (fun _x hx ↦ (mem_Icc.mp hx).2.trans_lt b.2) = Icc a b :=
  rfl

@[simp]
theorem attachFin_Ico :
    attachFin (Ico a b) (fun _x hx ↦ (mem_Ico.mp hx).2.trans b.2) = Ico a b :=
  rfl

@[simp]
theorem attachFin_Ioc :
    attachFin (Ioc a b) (fun _x hx ↦ (mem_Ioc.mp hx).2.trans_lt b.2) = Ioc a b :=
  rfl

@[simp]
theorem attachFin_Ioo :
    attachFin (Ioo a b) (fun _x hx ↦ (mem_Ioo.mp hx).2.trans b.2) = Ioo a b :=
  rfl

@[simp]
theorem attachFin_uIcc :
    attachFin (uIcc a b) (fun _x hx ↦ (mem_Icc.mp hx).2.trans_lt (max a b).2) = uIcc a b :=
  rfl

@[simp]
theorem attachFin_Iic : attachFin (Iic a) (fun _x hx ↦ (mem_Iic.mp hx).trans_lt a.2) = Iic a := by
  ext; simp

@[simp]
theorem attachFin_Ico_eq_Ici : attachFin (Ico a n) (fun _x hx ↦ (mem_Ico.mp hx).2) = Ici a := by
  ext; simp

@[simp]
theorem attachFin_Iio : attachFin (Iio a) (fun _x hx ↦ (mem_Iio.mp hx).trans a.2) = Iio a := by
  ext; simp

@[simp]
theorem attachFin_Ioo_eq_Ioi : attachFin (Ioo a n) (fun _x hx ↦ (mem_Ioo.mp hx).2) = Ioi a := by
  ext; simp

section deprecated

@[deprecated attachFin_Icc (since := "2025-04-06")]
theorem Icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).fin n := attachFin_eq_fin _

@[deprecated attachFin_Ico (since := "2025-04-06")]
theorem Ico_eq_finset_subtype : Ico a b = (Ico (a : ℕ) b).fin n := attachFin_eq_fin _

@[deprecated attachFin_Ioc (since := "2025-04-06")]
theorem Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).fin n := attachFin_eq_fin _

@[deprecated attachFin_Ioo (since := "2025-04-06")]
theorem Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).fin n := attachFin_eq_fin _

set_option linter.deprecated false in
@[deprecated attachFin_uIcc (since := "2025-04-06")]
theorem uIcc_eq_finset_subtype : uIcc a b = (uIcc (a : ℕ) b).fin n := Icc_eq_finset_subtype _ _

@[deprecated attachFin_Ico_eq_Ici (since := "2025-04-06")]
theorem Ici_eq_finset_subtype : Ici a = (Ico (a : ℕ) n).fin n := by ext; simp

@[deprecated attachFin_Ioo_eq_Ioi (since := "2025-04-06")]
theorem Ioi_eq_finset_subtype : Ioi a = (Ioo (a : ℕ) n).fin n := by ext; simp

@[deprecated attachFin_Iic (since := "2025-04-06")]
theorem Iic_eq_finset_subtype : Iic b = (Iic (b : ℕ)).fin n := by ext; simp

@[deprecated attachFin_Iio (since := "2025-04-06")]
theorem Iio_eq_finset_subtype : Iio b = (Iio (b : ℕ)).fin n := by ext; simp

end deprecated

@[simp]
theorem map_valEmbedding_Icc : (Icc a b).map Fin.valEmbedding = Icc ↑a ↑b :=
  map_valEmbedding_attachFin _

@[simp]
theorem map_valEmbedding_Ico : (Ico a b).map Fin.valEmbedding = Ico ↑a ↑b :=
  map_valEmbedding_attachFin _

@[simp]
theorem map_valEmbedding_Ioc : (Ioc a b).map Fin.valEmbedding = Ioc ↑a ↑b :=
  map_valEmbedding_attachFin _

@[simp]
theorem map_valEmbedding_Ioo : (Ioo a b).map Fin.valEmbedding = Ioo ↑a ↑b :=
  map_valEmbedding_attachFin _

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

@[simp]
theorem map_valEmbedding_Ici : (Ici a).map Fin.valEmbedding = Icc ↑a (n - 1) := by
  rw [← attachFin_Ico_eq_Ici, map_valEmbedding_attachFin, Nat.Icc_pred_right]
  exact a.pos

@[simp]
theorem map_valEmbedding_Ioi : (Ioi a).map Fin.valEmbedding = Ioc ↑a (n - 1) := by
  rw [← attachFin_Ioo_eq_Ioi, map_valEmbedding_attachFin]
  ext i
  simp [Nat.le_sub_one_iff_lt a.pos]

@[simp]
theorem map_valEmbedding_Iic : (Iic b).map Fin.valEmbedding = Iic ↑b := by
  rw [← attachFin_Iic, map_valEmbedding_attachFin]

@[simp]
theorem map_valEmbedding_Iio : (Iio b).map Fin.valEmbedding = Iio ↑b := by
  rw [← attachFin_Iio, map_valEmbedding_attachFin]

@[simp]
theorem card_Ici : #(Ici a) = n - a := by
  rw [← attachFin_Ico_eq_Ici, card_attachFin, Nat.card_Ico]

@[simp]
theorem card_Ioi : #(Ioi a) = n - 1 - a := by rw [← card_map, map_valEmbedding_Ioi, Nat.card_Ioc]

@[simp]
theorem card_Iic : #(Iic b) = b + 1 := by rw [← Nat.card_Iic b, ← map_valEmbedding_Iic, card_map]

@[simp]
theorem card_Iio : #(Iio b) = b := by rw [← Nat.card_Iio b, ← map_valEmbedding_Iio, card_map]

@[deprecated Fintype.card_Icc (since := "2025-03-28")]
theorem card_fintypeIcc : Fintype.card (Set.Icc a b) = b + 1 - a := by simp

@[deprecated Fintype.card_Ico (since := "2025-03-28")]
theorem card_fintypeIco : Fintype.card (Set.Ico a b) = b - a := by simp

@[deprecated Fintype.card_Ioc (since := "2025-03-28")]
theorem card_fintypeIoc : Fintype.card (Set.Ioc a b) = b - a := by simp

@[deprecated Fintype.card_Ioo (since := "2025-03-28")]
theorem card_fintypeIoo : Fintype.card (Set.Ioo a b) = b - a - 1 := by simp

@[deprecated Fintype.card_uIcc (since := "2025-03-28")]
theorem card_fintype_uIcc : Fintype.card (Set.uIcc a b) = (b - a : ℤ).natAbs + 1 := by simp

@[deprecated Fintype.card_Ici (since := "2025-03-28")]
theorem card_fintypeIci : Fintype.card (Set.Ici a) = n - a := by simp

@[deprecated Fintype.card_Ioi (since := "2025-03-28")]
theorem card_fintypeIoi : Fintype.card (Set.Ioi a) = n - 1 - a := by simp

@[deprecated Fintype.card_Iic (since := "2025-03-28")]
theorem card_fintypeIic : Fintype.card (Set.Iic b) = b + 1 := by simp

@[deprecated Fintype.card_Iio (since := "2025-03-28")]
theorem card_fintypeIio : Fintype.card (Set.Iio b) = b := by simp

end Fin
