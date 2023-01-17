/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module data.set.pointwise.list_of_fn
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Pointwise.Basic
import Mathbin.Data.List.OfFn

/-!
# Pointwise operations with lists of sets

This file proves some lemmas about pointwise algebraic operations with lists of sets.
-/


namespace Set

variable {F α β γ : Type _}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

open Pointwise

@[to_additive]
theorem mem_prod_list_of_fn {a : α} {s : Fin n → Set α} :
    a ∈ (List.ofFn s).Prod ↔ ∃ f : ∀ i : Fin n, s i, (List.ofFn fun i => (f i : α)).Prod = a :=
  by
  induction' n with n ih generalizing a
  · simp_rw [List.of_fn_zero, List.prod_nil, Fin.exists_fin_zero_pi, eq_comm, Set.mem_one]
  ·
    simp_rw [List.of_fn_succ, List.prod_cons, Fin.exists_fin_succ_pi, Fin.cons_zero, Fin.cons_succ,
      mem_mul, @ih, exists_and_left, exists_exists_eq_and, SetCoe.exists, Subtype.coe_mk,
      exists_prop]
#align set.mem_prod_list_of_fn Set.mem_prod_list_of_fn

@[to_additive]
theorem mem_list_prod {l : List (Set α)} {a : α} :
    a ∈ l.Prod ↔
      ∃ l' : List (Σs : Set α, ↥s),
        List.prod (l'.map fun x => (Sigma.snd x : α)) = a ∧ l'.map Sigma.fst = l :=
  by
  induction' l using List.ofFnRec with n f
  simp_rw [List.exists_iff_exists_tuple, List.map_of_fn, List.of_fn_inj', and_left_comm,
    exists_and_left, exists_eq_left, heq_iff_eq, Function.comp, mem_prod_list_of_fn]
  constructor
  · rintro ⟨fi, rfl⟩
    exact ⟨fun i => ⟨_, fi i⟩, rfl, rfl⟩
  · rintro ⟨fi, rfl, rfl⟩
    exact ⟨fun i => _, rfl⟩
#align set.mem_list_prod Set.mem_list_prod

@[to_additive]
theorem mem_pow {a : α} {n : ℕ} :
    a ∈ s ^ n ↔ ∃ f : Fin n → s, (List.ofFn fun i => (f i : α)).Prod = a := by
  rw [← mem_prod_list_of_fn, List.of_fn_const, List.prod_repeat]
#align set.mem_pow Set.mem_pow

end Set

