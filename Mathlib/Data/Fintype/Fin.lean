/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Data.Fin.Interval

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
  -- ⊢ a✝ ∈ map valEmbedding univ ↔ a✝ ∈ Iio n
  simp [orderIsoSubtype.symm.surjective.exists, OrderIso.symm]
  -- 🎉 no goals
#align fin.map_subtype_embedding_univ Fin.map_valEmbedding_univ

@[simp]
theorem Ioi_zero_eq_map : Ioi (0 : Fin n.succ) = univ.map (Fin.succEmbedding _).toEmbedding := by
  ext i
  -- ⊢ i ∈ Ioi 0 ↔ i ∈ map (succEmbedding n).toEmbedding univ
  simp only [mem_Ioi, mem_map, mem_univ, Function.Embedding.coeFn_mk, exists_true_left]
  -- ⊢ 0 < i ↔ ∃ a, True ∧ ↑(succEmbedding n).toEmbedding a = i
  constructor
  -- ⊢ 0 < i → ∃ a, True ∧ ↑(succEmbedding n).toEmbedding a = i
  · refine' cases _ _ i
    -- ⊢ 0 < 0 → ∃ a, True ∧ ↑(succEmbedding n).toEmbedding a = 0
    · rintro ⟨⟨⟩⟩
      -- 🎉 no goals
    · intro j _
      -- ⊢ ∃ a, True ∧ ↑(succEmbedding n).toEmbedding a = succ j
      use j
      -- ⊢ True ∧ ↑(succEmbedding n).toEmbedding j = succ j
      simp only [val_succEmbedding, and_self, RelEmbedding.coe_toEmbedding]
      -- 🎉 no goals
  · rintro ⟨i, _, rfl⟩
    -- ⊢ 0 < ↑(succEmbedding n).toEmbedding i
    exact succ_pos _
    -- 🎉 no goals
#align fin.Ioi_zero_eq_map Fin.Ioi_zero_eq_map

@[simp]
theorem Iio_last_eq_map : Iio (Fin.last n) = Finset.univ.map Fin.castSuccEmb.toEmbedding := by
  apply Finset.map_injective Fin.valEmbedding
  -- ⊢ map valEmbedding (Iio (last n)) = map valEmbedding (map castSuccEmb.toEmbedd …
  rw [Finset.map_map, Fin.map_valEmbedding_Iio, Fin.val_last]
  -- ⊢ Iio n = map (Function.Embedding.trans castSuccEmb.toEmbedding valEmbedding)  …
  exact map_valEmbedding_univ.symm
  -- 🎉 no goals
#align fin.Iio_last_eq_map Fin.Iio_last_eq_map

@[simp]
theorem Ioi_succ (i : Fin n) : Ioi i.succ = (Ioi i).map (Fin.succEmbedding _).toEmbedding := by
  ext i
  -- ⊢ i ∈ Ioi (succ i✝) ↔ i ∈ map (succEmbedding n).toEmbedding (Ioi i✝)
  simp only [mem_filter, mem_Ioi, mem_map, mem_univ, true_and_iff, Function.Embedding.coeFn_mk,
    exists_true_left]
  constructor
  -- ⊢ succ i✝ < i → ∃ a, i✝ < a ∧ ↑(succEmbedding n).toEmbedding a = i
  · refine' cases _ _ i
    -- ⊢ succ i✝ < 0 → ∃ a, i✝ < a ∧ ↑(succEmbedding n).toEmbedding a = 0
    · rintro ⟨⟨⟩⟩
      -- 🎉 no goals
    · intro i hi
      -- ⊢ ∃ a, i✝¹ < a ∧ ↑(succEmbedding n).toEmbedding a = succ i
      refine' ⟨i, succ_lt_succ_iff.mp hi, rfl⟩
      -- 🎉 no goals
  · rintro ⟨i, hi, rfl⟩
    -- ⊢ succ i✝ < ↑(succEmbedding n).toEmbedding i
    simpa
    -- 🎉 no goals
#align fin.Ioi_succ Fin.Ioi_succ

@[simp]
theorem Iio_castSucc (i : Fin n) :
    Iio (castSucc i) = (Iio i).map Fin.castSuccEmb.toEmbedding := by
  apply Finset.map_injective Fin.valEmbedding
  -- ⊢ map valEmbedding (Iio (castSucc i)) = map valEmbedding (map castSuccEmb.toEm …
  rw [Finset.map_map, Fin.map_valEmbedding_Iio]
  -- ⊢ Iio ↑(castSucc i) = map (Function.Embedding.trans castSuccEmb.toEmbedding va …
  exact (Fin.map_valEmbedding_Iio i).symm
  -- 🎉 no goals
#align fin.Iio_cast_succ Fin.Iio_castSucc

theorem card_filter_univ_succ' (p : Fin (n + 1) → Prop) [DecidablePred p] :
    (univ.filter p).card = ite (p 0) 1 0 + (univ.filter (p ∘ Fin.succ)).card := by
  rw [Fin.univ_succ, filter_cons, card_disjUnion, filter_map, card_map]
  -- ⊢ Finset.card (if p 0 then {0} else ∅) + Finset.card (filter (p ∘ ↑{ toFun :=  …
  split_ifs <;> simp
  -- ⊢ Finset.card {0} + Finset.card (filter (p ∘ ↑{ toFun := succ, inj' := (_ : Fu …
                -- 🎉 no goals
                -- 🎉 no goals
#align fin.card_filter_univ_succ' Fin.card_filter_univ_succ'

theorem card_filter_univ_succ (p : Fin (n + 1) → Prop) [DecidablePred p] :
    (univ.filter p).card =
    if p 0 then (univ.filter (p ∘ Fin.succ)).card + 1 else (univ.filter (p ∘ Fin.succ)).card :=
  (card_filter_univ_succ' p).trans (by split_ifs <;> simp [add_comm 1])
                                       -- ⊢ 1 + Finset.card (filter (p ∘ succ) univ) = Finset.card (filter (p ∘ succ) un …
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
#align fin.card_filter_univ_succ Fin.card_filter_univ_succ

theorem card_filter_univ_eq_vector_get_eq_count [DecidableEq α] (a : α) (v : Vector α n) :
    (univ.filter fun i => a = v.get i).card = v.toList.count a := by
  induction' v using Vector.inductionOn with n x xs hxs
  -- ⊢ Finset.card (filter (fun i => a = Vector.get Vector.nil i) univ) = List.coun …
  · simp
    -- 🎉 no goals
  · simp_rw [card_filter_univ_succ', Vector.get_cons_zero, Vector.toList_cons, Function.comp,
      Vector.get_cons_succ, hxs, List.count_cons, add_comm (ite (a = x) 1 0)]
#align fin.card_filter_univ_eq_vector_nth_eq_count Fin.card_filter_univ_eq_vector_get_eq_count

end Fin
