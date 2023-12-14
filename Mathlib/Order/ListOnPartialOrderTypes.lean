/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Data.List.Chain
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sort
import Mathlib.Order.Cover

/-!
This file mainly contains some lemmas about lists of type with partial orders

The reason a separate file is needed is to avoid import cycles
-/

variable {α : Type _} [PartialOrder α]

namespace List

lemma le_of_chain'_le
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

lemma le_getLast_of_chain'_le
    (x : α) (l : List α) (l_chain : (x :: l).Chain' (. ≤ .)) (y : α) (hy : y ∈ (x :: l)) :
    y ≤ List.getLast (x :: l) (List.cons_ne_nil _ _)  := by
  have s' : (x :: l).Sorted (. ≤ .)
  · rw [List.chain'_iff_pairwise] at l_chain
    exact l_chain
  rw [List.mem_iff_get] at hy
  obtain ⟨m, hm, rfl⟩ := hy
  rw [List.getLast_eq_get]
  refine s'.rel_get_of_le (Nat.lt_succ_iff.mp m.2 : (⟨_, _⟩ : Fin _) ≤ ⟨_, _⟩)

lemma dedup_head?_of_chain'_wcovby [DecidableEq α]
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

lemma dedup_head!_of_chain'_wcovby [DecidableEq α] [Inhabited α]
    (l : List α) (l_chain : l.Chain' (. ⩿ .)) : l.dedup.head! = l.head! :=
  by rwa [List.head!_eq_head?, List.head!_eq_head?, List.dedup_head?_of_chain'_wcovby]

lemma dedup_getLast_eq_getLast_of_chain'_wcovby [DecidableEq α] [PartialOrder α]
    (l : List α) (l_chain : l.Chain' (. ⩿ .)) (l_ne_nil : l ≠ []) :
    l.dedup.getLast (List.dedup_ne_nil_of_ne_nil _ l_ne_nil) = l.getLast l_ne_nil := by
  obtain ⟨y, l', rfl⟩ : ∃ (y : α) (l' : List α), l = y :: l'
  · induction l with | nil => ?_ | cons y l' _ => ?_
    · cases l_ne_nil rfl
    · exact ⟨y, l', rfl⟩

  refine _root_.le_antisymm ?_ ?_

  · apply List.le_getLast_of_chain'_le _ _ (l_chain.imp $ λ _ _ ↦ Wcovby.le)
    rw [← List.mem_dedup]
    exact List.getLast_mem _

  · have ne_nil2 : (y :: l').dedup ≠ []
    · exact List.dedup_ne_nil_of_ne_nil _ l_ne_nil
    obtain ⟨x, l, hl⟩ : ∃ (x : α) (l : List α), x :: l = (y :: l').dedup
    · set L := dedup (y :: l'); clear_value L
      induction L with | nil => ?_ | cons y l' _ => ?_
      · cases ne_nil2 rfl
      · exact ⟨_, _, rfl⟩
    simp_rw [← hl]
    refine List.le_getLast_of_chain'_le x l ?_ _ ?_
    · rw [hl]
      exact List.Chain'.sublist (l_chain.imp $ λ _ _ ↦ Wcovby.le) (List.dedup_sublist _)
    rw [hl, List.mem_dedup]
    exact List.getLast_mem _

lemma dedup_chain'_wcovby_of_chain'_wcovby [DecidableEq α]
    (l : List α) (l_chain : l.Chain' (. ⩿ .)) : l.dedup.Chain' (. ⩿ .) := by
  induction l with
  | nil => simp only [dedup_nil, chain'_nil]
  | cons x l ih => ?_
  rw [List.chain'_cons'] at l_chain
  by_cases hx : x ∈ l
  · rw [List.dedup_cons_of_mem hx]
    exact ih l_chain.2
  · rw [List.dedup_cons_of_not_mem hx, List.chain'_cons']
    refine ⟨?_, ih l_chain.2⟩
    rintro y (hy : _ = _)
    exact l_chain.1 y (Eq.trans (l.dedup_head?_of_chain'_wcovby l_chain.2).symm hy)

lemma dedup_chain'_covby_of_chain'_wcovby [DecidableEq α]
    (l : List α) (l_chain : l.Chain' (. ⩿ .)) : l.dedup.Chain' (. ⋖ .) := by
  have c := dedup_chain'_wcovby_of_chain'_wcovby l l_chain
  rw [chain'_iff_get] at c ⊢
  simp_rw [wcovby_iff_covby_or_eq] at c
  intros i hi
  refine (c i hi).resolve_right (fun h => ?_)
  simpa only [Fin.mk.injEq, self_eq_add_right] using List.nodup_iff_injective_get.mp l.nodup_dedup h

lemma chain'_covby_of_chain'_wcovby_of_nodup
    (l : List α) (l_chain : l.Chain' (. ⩿ .)) (l_nodup : l.Nodup) :
    List.Chain' (. ⋖ .) l := by
  classical
  rw [← List.dedup_eq_self] at l_nodup
  rw [← l_nodup]
  exact dedup_chain'_covby_of_chain'_wcovby _ l_chain

end List
