/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Data.List.Chain
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sort

/-!
This file mainly contains some lemmas about lists of type with partial orders

The reason a separate file is needed is to avoid import cycles
-/

variable {α : Type _} [PartialOrder α]

namespace List

lemma le_of_chain'_le [PartialOrder α]
    (x : α) (l : List α) (l_chain : (x :: l).Chain' (. ≤ .)) (y : α) (hy : y ∈ (x :: l)) :
    x ≤ y := by
  rw [List.mem_cons] at hy
  refine hy.elim (by rintro rfl; rfl) (fun hy => ?_)
  rw [List.mem_iff_get] at hy
  obtain ⟨n, hn, rfl⟩ := hy
  have s' : (x :: l).Sorted (. ≤ .)
  · rw [List.chain'_iff_pairwise] at l_chain
    exact l_chain
  rw [show x = (x :: l).get ⟨0, (Nat.zero_lt_succ _)⟩ from rfl,
    show l.get n = (x :: l).get n.succ from rfl]
  exact s'.rel_get_of_le (Nat.zero_le _ : (⟨0, _⟩ : Fin (x :: l).length) ≤ n.succ)

lemma le_getLast_of_chain'_le [PartialOrder α]
    (x : α) (l : List α) (l_chain : (x :: l).Chain' (. ≤ .)) (y : α) (hy : y ∈ (x :: l)) :
    y ≤ List.getLast (x :: l) (List.cons_ne_nil _ _)  := by
  have s' : (x :: l).Sorted (. ≤ .)
  · rw [List.chain'_iff_pairwise] at l_chain
    exact l_chain
  rw [List.mem_iff_get] at hy
  obtain ⟨m, hm, rfl⟩ := hy
  rw [List.getLast_eq_get]
  refine s'.rel_get_of_le (Nat.lt_succ_iff.mp m.2 : (⟨_, _⟩ : Fin _) ≤ ⟨_, _⟩)

lemma dedup_head?_of_chain_wcovby [DecidableEq α]
  (l : List α) (l_chain : l.Chain' (. ⩿ .)) : l.dedup.head? = l.head? :=
match l, l_chain with
| [], _ => by simp
| x0::l, l_chain => by
  have ne_nil : (x0 :: l).dedup ≠ List.nil
  · apply List.dedup_ne_nil_of_ne_nil; exact List.cons_ne_nil _ _
  obtain ⟨y, l', h⟩ : ∃ (y : α) (l' : List α), (x0 :: l).dedup = y :: l'
  · set L := dedup (x0 :: l); clear_value L; revert ne_nil
    induction L with
    | nil => intro h; cases h rfl
    | cons y l' _ => exact fun _ => ⟨_, _, rfl⟩
  have h1 : ∀ (x : α) (_ : x ∈ y :: l'), y ≤ x
  · apply List.le_of_chain'_le
    rw [← h]
    exact List.Chain'.sublist (l_chain.imp $ fun {_ _} => Wcovby.le) (List.dedup_sublist _)
  have h2 : ∀ (x : α) (_ : x ∈ x0 :: l), x0 ≤ x := fun x hx =>
    List.le_of_chain'_le _ l (l_chain.imp $ fun {_ _} => Wcovby.le) _ hx
  specialize h1 x0 (by rw [← h, List.mem_dedup]; exact List.mem_cons_self _ _)
  specialize h2 y (by
      have mem1 : y ∈ y :: l' := List.mem_cons_self _ _
      rwa [← h, List.mem_dedup] at mem1)
  rw [h, _root_.le_antisymm h1 h2]
  rfl

end List
