/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Vector.Basic

/-!
# The structure of `Fintype (Fin n)`

This file contains some basic results about the `Fintype` instance for `Fin`,
especially properties of `Finset.univ : Finset (Fin n)`.
-/

open List (Vector)

open Finset

open Fintype

namespace Fin

variable {α β : Type*} {n : ℕ}

theorem map_valEmbedding_univ : (Finset.univ : Finset (Fin n)).map Fin.valEmbedding = Iio n := by
  ext
  simp [orderIsoSubtype.symm.surjective.exists, OrderIso.symm]

@[simp]
theorem Ioi_zero_eq_map : Ioi (0 : Fin n.succ) = univ.map (Fin.succEmb _) :=
  coe_injective <| by ext; simp [pos_iff_ne_zero]

@[simp]
theorem Iio_last_eq_map : Iio (Fin.last n) = Finset.univ.map Fin.castSuccEmb :=
  coe_injective <| by ext; simp [lt_def]

theorem Ioi_succ (i : Fin n) : Ioi i.succ = (Ioi i).map (Fin.succEmb _) := by simp

theorem Iio_castSucc (i : Fin n) : Iio (castSucc i) = (Iio i).map Fin.castSuccEmb := by simp

theorem card_filter_univ_succ (p : Fin (n + 1) → Prop) [DecidablePred p] :
    #{x | p x} = if p 0 then #{x | p (.succ x)} + 1 else #{x | p (.succ x)} := by
  rw [Fin.univ_succ, filter_cons, apply_ite Finset.card, card_cons, filter_map, card_map]; rfl

theorem card_filter_univ_succ' (p : Fin (n + 1) → Prop) [DecidablePred p] :
    #{x | p x} = ite (p 0) 1 0 + #{x | p (.succ x)} := by
  rw [card_filter_univ_succ]; split_ifs <;> simp [add_comm]

theorem card_filter_univ_eq_vector_get_eq_count [DecidableEq α] (a : α) (v : List.Vector α n) :
    #{i | v.get i = a} = v.toList.count a := by
  induction v with
  | nil => simp
  | @cons n x xs hxs =>
    simp_rw [card_filter_univ_succ', Vector.get_cons_zero, Vector.toList_cons, Vector.get_cons_succ,
      hxs, List.count_cons, add_comm (ite (x = a) 1 0), beq_iff_eq]

end Fin
