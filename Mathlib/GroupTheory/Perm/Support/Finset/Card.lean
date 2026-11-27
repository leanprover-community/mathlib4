/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.Perm.Support.Finset.Basic

/-!
# Cardinality of the `Finset`-valued support of a permutation

This file studies the cardinality of `Equiv.Perm.supportFinset`. The results mirror those for
the `Set`-valued `Equiv.Perm.support` in `Mathlib/GroupTheory/Perm/Support/Card.lean`, but are
proved directly, so that this file does not depend on `Set.encard` or `Set.ncard`.

## Main statements

In the following, `f g : Equiv.Perm α`, where `α` is a `Fintype` with decidable equality.

* `Equiv.Perm.card_supportFinset_le_one`: `#f.supportFinset ≤ 1` iff `f = 1`. In particular, the
  support of `f ≠ 1` has at least two elements (`Equiv.Perm.two_le_card_supportFinset_of_ne_one`).
* `Equiv.Perm.card_supportFinset_eq_two`: `#f.supportFinset = 2` iff `f` is a swap.
* `Equiv.Perm.Disjoint.card_supportFinset_mul`: the support of a product of disjoint permutations
  has cardinality the sum of the cardinalities.
* `Equiv.Perm.fixed_point_card_lt_of_ne_one f` says that `f` has
  strictly less than `Fintype.card α - 1` fixed points, unless `f = 1`.
-/

assert_not_exists Set.encard Set.ncard Finset.noncommProd

public section

open Finset

namespace Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α] {f g : Perm α}

theorem card_supportFinset_eq_zero : #f.supportFinset = 0 ↔ f = 1 := by
  rw [Finset.card_eq_zero, supportFinset_eq_empty_iff]

@[deprecated (since := "2026-11-16")] alias card_support_eq_zero := card_supportFinset_eq_zero

theorem card_supportFinset_ne_one (f : Perm α) : #f.supportFinset ≠ 1 := by
  simp [Finset.card_eq_one, supportFinset_ne_singleton]

@[deprecated (since := "2026-11-16")] alias card_support_ne_one := card_supportFinset_ne_one

@[simp]
theorem card_supportFinset_le_one : #f.supportFinset ≤ 1 ↔ f = 1 := by
  rw [Nat.le_one_iff_eq_zero_or_eq_one, card_supportFinset_eq_zero]
  exact or_iff_left (card_supportFinset_ne_one f)

@[deprecated (since := "2026-11-16")] alias card_support_le_one := card_supportFinset_le_one

@[simp]
theorem one_lt_card_supportFinset_iff : 1 < #f.supportFinset ↔ f ≠ 1 := by
  rw [← not_le, card_supportFinset_le_one]

theorem one_lt_card_supportFinset_of_ne_one (h : f ≠ 1) : 1 < #f.supportFinset :=
  one_lt_card_supportFinset_iff.mpr h

@[deprecated (since := "2026-11-16")] alias one_lt_card_support_of_ne_one :=
    one_lt_card_supportFinset_of_ne_one

theorem two_le_card_supportFinset_iff : 2 ≤ #f.supportFinset ↔ f ≠ 1 :=
  Nat.add_one_le_iff.trans one_lt_card_supportFinset_iff

theorem two_le_card_supportFinset_of_ne_one (h : f ≠ 1) : 2 ≤ #f.supportFinset :=
  two_le_card_supportFinset_iff.mpr h

@[deprecated (since := "2026-11-16")] alias two_le_card_support_of_ne_one :=
    two_le_card_supportFinset_of_ne_one

@[simp]
theorem card_supportFinset_eq_two : #f.supportFinset = 2 ↔ IsSwap f := by
  simp_rw [Finset.card_eq_two, ne_eq, supportFinset_eq_pair_iff, ← and_assoc, and_self,
    and_assoc, isSwap_iff_exists_apply]

@[deprecated (since := "2026-11-16")] alias card_support_eq_two := card_supportFinset_eq_two

theorem card_supportFinset_swap {x y : α} (hxy : x ≠ y) : #(swap x y).supportFinset = 2 := by
  rw [supportFinset_swap hxy, card_pair hxy]

@[deprecated (since := "2026-11-16")] alias card_support_swap := card_supportFinset_swap

theorem Disjoint.card_supportFinset_mul (h : f.Disjoint g) :
    #(f * g).supportFinset = #f.supportFinset + #g.supportFinset := by
  rw [h.supportFinset_mul, card_union_of_disjoint h.disjoint_supportFinset]

@[deprecated (since := "2026-11-16")] alias Disjoint.card_support_mul :=
    Disjoint.card_supportFinset_mul

theorem card_supportFinset_prod_list_of_pairwise_disjoint {l : List (Perm α)}
    (h : l.Pairwise Perm.Disjoint) :
    #l.prod.supportFinset = (l.map (card ∘ supportFinset)).sum := by
  induction h with
  | nil => simp
  | cons ha hl IH =>
    rw [List.prod_cons, List.map_cons, List.sum_cons, ← IH]
    exact (disjoint_prod_right _ ha).card_supportFinset_mul

@[deprecated (since := "2026-11-16")] alias card_support_prod_list_of_pairwise_disjoint :=
    card_supportFinset_prod_list_of_pairwise_disjoint

theorem card_supportFinset_conj : #(f * g * f⁻¹).supportFinset = #g.supportFinset := by
  rw [supportFinset_conj, card_map]

@[deprecated (since := "2026-11-16")] alias card_support_conj := card_supportFinset_conj

theorem card_supportFinset_extend_domain {β : Type*} [DecidableEq β] [Fintype β] {p : β → Prop}
    [DecidablePred p] (e : α ≃ Subtype p) :
    #(g.extendDomain e).supportFinset = #g.supportFinset := by
  rw [supportFinset_extend_domain, card_map]

@[deprecated (since := "2026-11-16")] alias card_support_extend_domain :=
    card_supportFinset_extend_domain

theorem card_supportFinset_swap_mul {x : α} (hx : f x ≠ x) :
    #(swap x (f x) * f).supportFinset < #f.supportFinset :=
  have h : (swap x (f x) * f).supportFinset ⊆ f.supportFinset := fun _ hz =>
    (mem_supportFinset_swap_mul_imp_mem_supportFinset_ne hz).left
  card_lt_card ⟨h, fun h =>
    absurd (h (mem_supportFinset.2 hx)) (mt mem_supportFinset.1 (by simp))⟩

@[deprecated (since := "2026-11-16")] alias card_support_swap_mul := card_supportFinset_swap_mul

theorem fixed_point_card_add_two_le_of_ne_one (h : f ≠ 1) :
    #{x | f x = x} + 2 ≤ Fintype.card α := by
  have hc : #{x | f x = x} = #f.supportFinsetᶜ := by congr 1; ext; simp [mem_supportFinset]
  rw [hc, Nat.add_comm, ← card_add_card_compl f.supportFinset]
  exact Nat.add_le_add_right (two_le_card_supportFinset_of_ne_one h) _

theorem fixed_point_card_lt_of_ne_one (h : f ≠ 1) : #{x | f x = x} < Fintype.card α - 1 := by
  have := fixed_point_card_add_two_le_of_ne_one h
  omega

end Equiv.Perm
