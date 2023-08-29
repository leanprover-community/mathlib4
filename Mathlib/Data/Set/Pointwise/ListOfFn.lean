/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Data.List.OfFn

#align_import data.set.pointwise.list_of_fn from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# Pointwise operations with lists of sets

This file proves some lemmas about pointwise algebraic operations with lists of sets.
-/

namespace Set

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

open Pointwise

@[to_additive]
theorem mem_prod_list_ofFn {a : α} {s : Fin n → Set α} :
    a ∈ (List.ofFn s).prod ↔ ∃ f : ∀ i : Fin n, s i, (List.ofFn fun i ↦ (f i : α)).prod = a := by
  induction' n with n ih generalizing a
  -- ⊢ a ∈ List.prod (List.ofFn s) ↔ ∃ f, List.prod (List.ofFn fun i => ↑(f i)) = a
  · simp_rw [List.ofFn_zero, List.prod_nil, Fin.exists_fin_zero_pi, eq_comm, Set.mem_one]
    -- 🎉 no goals
  · simp_rw [List.ofFn_succ, List.prod_cons, Fin.exists_fin_succ_pi, Fin.cons_zero, Fin.cons_succ,
      mem_mul, @ih, exists_and_left, exists_exists_eq_and, SetCoe.exists, exists_prop]
#align set.mem_prod_list_of_fn Set.mem_prod_list_ofFn
#align set.mem_sum_list_of_fn Set.mem_sum_list_ofFn

@[to_additive]
theorem mem_list_prod {l : List (Set α)} {a : α} :
    a ∈ l.prod ↔
      ∃ l' : List (Σs : Set α, ↥s),
        List.prod (l'.map fun x ↦ (Sigma.snd x : α)) = a ∧ l'.map Sigma.fst = l := by
  induction' l using List.ofFnRec with n f
  -- ⊢ a ∈ List.prod (List.ofFn f) ↔ ∃ l', List.prod (List.map (fun x => ↑x.snd) l' …
  simp only [mem_prod_list_ofFn, List.exists_iff_exists_tuple, List.map_ofFn, Function.comp,
    List.ofFn_inj', Sigma.mk.inj_iff, and_left_comm, exists_and_left, exists_eq_left, heq_eq_eq]
  constructor
  -- ⊢ (∃ f_1, List.prod (List.ofFn fun i => ↑(f_1 i)) = a) → ∃ x, List.prod (List. …
  · rintro ⟨fi, rfl⟩
    -- ⊢ ∃ x, List.prod (List.ofFn fun x_1 => ↑(x x_1).snd) = List.prod (List.ofFn fu …
    exact ⟨fun i ↦ ⟨_, fi i⟩, rfl, rfl⟩
    -- 🎉 no goals
  · rintro ⟨fi, rfl, rfl⟩
    -- ⊢ ∃ f, List.prod (List.ofFn fun i => ↑(f i)) = List.prod (List.ofFn fun x => ↑ …
    exact ⟨fun i ↦ _, rfl⟩
    -- 🎉 no goals
#align set.mem_list_prod Set.mem_list_prod
#align set.mem_list_sum Set.mem_list_sum

@[to_additive]
theorem mem_pow {a : α} {n : ℕ} :
    a ∈ s ^ n ↔ ∃ f : Fin n → s, (List.ofFn fun i ↦ (f i : α)).prod = a := by
  rw [← mem_prod_list_ofFn, List.ofFn_const, List.prod_replicate]
  -- 🎉 no goals
#align set.mem_pow Set.mem_pow
#align set.mem_nsmul Set.mem_nsmul

end Set
