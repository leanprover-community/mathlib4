/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module data.fintype.fin
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fin.Interval

/-!
# The structure of `Fintype (Fin n)`

This file contains some basic results about the `Fintype` instance for `Fin`,
especially properties of `Finset.univ : Finset (Fin n)`.
-/

open Finset

open Fintype

namespace Fin

variable {α β : Type _} {n : ℕ}

@[simp]
theorem Ioi_zero_eq_map : Ioi (0 : Fin n.succ) = univ.map (Fin.succEmbedding _).toEmbedding := by
  ext i
  simp only [mem_Ioi, mem_map, mem_univ, Function.Embedding.coeFn_mk, exists_true_left]
  constructor
  · refine' cases _ _ i
    · rintro ⟨⟨⟩⟩
    · intro j _
      use j
      simp only [val_succEmbedding, and_self]
  · rintro ⟨i, _, rfl⟩
    exact succ_pos _
#align fin.Ioi_zero_eq_map Fin.Ioi_zero_eq_map

@[simp]
theorem Ioi_succ (i : Fin n) : Ioi i.succ = (Ioi i).map (Fin.succEmbedding _).toEmbedding := by
  ext i
  simp only [mem_filter, mem_Ioi, mem_map, mem_univ, true_and_iff, Function.Embedding.coeFn_mk,
    exists_true_left]
  constructor
  · refine' cases _ _ i
    · rintro ⟨⟨⟩⟩
    · intro i hi
      refine' ⟨i, succ_lt_succ_iff.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    simpa
#align fin.Ioi_succ Fin.Ioi_succ

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
  induction' v using Vector.inductionOn with n x xs hxs
  · simp
  · simp_rw [card_filter_univ_succ', Vector.get_cons_zero, Vector.toList_cons, Function.comp,
      Vector.get_cons_succ, hxs, List.count_cons', add_comm (ite (a = x) 1 0)]
#align fin.card_filter_univ_eq_vector_nth_eq_count Fin.card_filter_univ_eq_vector_get_eq_count

end Fin
