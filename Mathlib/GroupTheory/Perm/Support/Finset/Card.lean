/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
module

public import Mathlib.GroupTheory.Perm.Support.Finset.Basic

/-!
# Cardinality of the support of a permutation

## Main statements

In the following, `f g : Equiv.Perm α`, where `α` is a `Fintype` with decidable equality.

* `Equiv.Perm.fixed_point_card_lt_of_ne_one f` says that `f` has
  strictly less than `Fintype.card α - 1` fixed points, unless `f = 1`.
  (Equivalently, `f.support` has at least 2 elements.)
-/

@[expose] public section

open Equiv Finset Function

namespace Equiv.Perm

variable {α : Type*}

section support

variable [DecidableEq α] [Fintype α] {f g : Perm α}

section ExtendDomain

variable {β : Type*} [DecidableEq β] [Fintype β] {p : β → Prop} [DecidablePred p]

theorem card_support_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    #(g.extendDomain f).support = #g.support := by simp

end ExtendDomain

section Card

theorem card_support_eq_zero {f : Perm α} : #f.support = 0 ↔ f = 1 := by
  rw [Finset.card_eq_zero, support_eq_empty_iff]

theorem one_lt_card_support_of_ne_one {f : Perm α} (h : f ≠ 1) : 1 < #f.support := by
  simp_rw [one_lt_card_iff, mem_support, ← not_or]
  contrapose! h
  ext a
  specialize h (f a) a
  rwa [apply_eq_iff_eq, or_self_iff, or_self_iff] at h

theorem card_support_ne_one (f : Perm α) : #f.support ≠ 1 := by
  by_cases h : f = 1
  · exact ne_of_eq_of_ne (card_support_eq_zero.mpr h) zero_ne_one
  · exact ne_of_gt (one_lt_card_support_of_ne_one h)

@[simp]
theorem card_support_le_one {f : Perm α} : #f.support ≤ 1 ↔ f = 1 := by
  rw [le_iff_lt_or_eq, Nat.lt_succ_iff, Nat.le_zero, card_support_eq_zero, or_iff_not_imp_right,
    imp_iff_right f.card_support_ne_one]

theorem two_le_card_support_of_ne_one {f : Perm α} (h : f ≠ 1) : 2 ≤ #f.support :=
  one_lt_card_support_of_ne_one h

theorem card_support_swap_mul {f : Perm α} {x : α} (hx : f x ≠ x) :
    #(swap x (f x) * f).support < #f.support :=
  Finset.card_lt_card
    ⟨fun _ hz => (mem_support_swap_mul_imp_mem_support_ne hz).left, fun h =>
      absurd (h (mem_support.2 hx)) (mt mem_support.1 (by simp))⟩

theorem card_support_swap {x y : α} (hxy : x ≠ y) : #(swap x y).support = 2 :=
  show #(swap x y).support = #⟨x ::ₘ y ::ₘ 0, by simp [hxy]⟩ from
    congr(card $(by simp [support_swap hxy, *, Finset.ext_iff]))

@[simp]
theorem card_support_eq_two {f : Perm α} : #f.support = 2 ↔ IsSwap f := by
  constructor <;> intro h
  · obtain ⟨x, t, hmem, hins, ht⟩ := card_eq_succ.1 h
    obtain ⟨y, rfl⟩ := card_eq_one.1 ht
    rw [mem_singleton] at hmem
    refine ⟨x, y, hmem, ?_⟩
    ext a
    have key : ∀ b, f b ≠ b ↔ _ := fun b => by rw [← mem_support, ← hins, mem_insert, mem_singleton]
    by_cases ha : f a = a
    · have ha' := not_or.mp (mt (key a).mpr (not_not.mpr ha))
      rw [ha, swap_apply_of_ne_of_ne ha'.1 ha'.2]
    · have ha' := (key (f a)).mp (mt f.apply_eq_iff_eq.mp ha)
      obtain rfl | rfl := (key a).mp ha
      · rw [Or.resolve_left ha' ha, swap_apply_left]
      · rw [Or.resolve_right ha' ha, swap_apply_right]
  · obtain ⟨x, y, hxy, rfl⟩ := h
    exact card_support_swap hxy

theorem Disjoint.card_support_mul (h : Disjoint f g) :
    #(f * g).support = #f.support + #g.support := by
  rw [← Finset.card_union_of_disjoint]
  · congr
    ext
    simp [h.support_mul]
  · simpa using h.disjoint_support

theorem card_support_prod_list_of_pairwise_disjoint {l : List (Perm α)} (h : l.Pairwise Disjoint) :
    #l.prod.support = (l.map (card ∘ support)).sum := by
  induction l with
  | nil => exact card_support_eq_zero.mpr rfl
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h
    rw [List.prod_cons, List.map_cons, List.sum_cons, ← ih ht]
    exact (disjoint_prod_right _ ha).card_support_mul

end Card

end support

section FixedPoints

/-!
### Fixed points
-/

theorem fixed_point_card_lt_of_ne_one [DecidableEq α] [Fintype α] {σ : Perm α} (h : σ ≠ 1) :
    #{x | σ x = x} < Fintype.card α - 1 := by
  rw [Nat.lt_sub_iff_add_lt, ← Nat.lt_sub_iff_add_lt', ← Finset.card_compl, Finset.compl_filter]
  exact one_lt_card_support_of_ne_one h

end FixedPoints

section Conjugation

variable [Fintype α] [DecidableEq α] {σ τ : Perm α}

theorem card_support_conj : #(σ * τ * σ⁻¹).support = #τ.support := by simp

end Conjugation

end Equiv.Perm
