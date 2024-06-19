/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Order.Interval.Finset.Fin

#align_import data.fintype.fin from "leanprover-community/mathlib"@"759575657f189ccb424b990164c8b1fa9f55cdfe"

/-!
# The structure of `Fintype (Fin n)`

This file contains some basic results about the `Fintype` instance for `Fin`,
especially properties of `Finset.univ : Finset (Fin n)`.
-/

open Finset

open Fintype

namespace Fin

variable {α β : Type*} {n : ℕ}

theorem map_valEmbedding_univ : (Finset.univ : Finset (Fin n)).map Fin.valEmbedding = Iio n := by
  ext
  simp [orderIsoSubtype.symm.surjective.exists, OrderIso.symm]
#align fin.map_subtype_embedding_univ Fin.map_valEmbedding_univ

@[simp]
theorem Ioi_zero_eq_map : Ioi (0 : Fin n.succ) = univ.map (Fin.succEmb _) :=
  coe_injective <| by ext; simp [pos_iff_ne_zero]
#align fin.Ioi_zero_eq_map Fin.Ioi_zero_eq_map

@[simp]
theorem Iio_last_eq_map : Iio (Fin.last n) = Finset.univ.map Fin.castSuccEmb :=
  coe_injective <| by ext; simp [lt_def]
#align fin.Iio_last_eq_map Fin.Iio_last_eq_map

@[simp]
theorem Ioi_succ (i : Fin n) : Ioi i.succ = (Ioi i).map (Fin.succEmb _) := by
  ext i
  simp only [mem_filter, mem_Ioi, mem_map, mem_univ, true_and_iff, Function.Embedding.coeFn_mk,
    exists_true_left]
  constructor
  · refine cases ?_ ?_ i
    · rintro ⟨⟨⟩⟩
    · intro i hi
      exact ⟨i, succ_lt_succ_iff.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    simpa
#align fin.Ioi_succ Fin.Ioi_succ

@[simp]
theorem Iio_castSucc (i : Fin n) : Iio (castSucc i) = (Iio i).map Fin.castSuccEmb := by
  apply Finset.map_injective Fin.valEmbedding
  rw [Finset.map_map, Fin.map_valEmbedding_Iio]
  exact (Fin.map_valEmbedding_Iio i).symm
#align fin.Iio_cast_succ Fin.Iio_castSucc

theorem card_filter_univ_succ' (p : Fin (n + 1) → Prop) [DecidablePred p] :
    (univ.filter p).card = ite (p 0) 1 0 + (univ.filter (p ∘ Fin.succ)).card := by
  rw [Fin.univ_succ, filter_cons, card_disjUnion, filter_map, card_map]
  split_ifs <;> simp
#align fin.card_filter_univ_succ' Fin.card_filter_univ_succ'

theorem card_filter_univ_succ (p : Fin (n + 1) → Prop) [DecidablePred p] :
    (univ.filter p).card =
    if p 0 then (univ.filter (p ∘ Fin.succ)).card + 1 else (univ.filter (p ∘ Fin.succ)).card :=
  (card_filter_univ_succ' p).trans (by split_ifs <;> simp [add_comm 1])
#align fin.card_filter_univ_succ Fin.card_filter_univ_succ

theorem card_filter_univ_eq_vector_get_eq_count [DecidableEq α] (a : α) (v : Vector α n) :
    (univ.filter fun i => a = v.get i).card = v.toList.count a := by
  induction' v with n x xs hxs
  · simp
  · simp_rw [card_filter_univ_succ', Vector.get_cons_zero, Vector.toList_cons, Function.comp,
      Vector.get_cons_succ, hxs, List.count_cons, add_comm (ite (a = x) 1 0)]
#align fin.card_filter_univ_eq_vector_nth_eq_count Fin.card_filter_univ_eq_vector_get_eq_count

end Fin
