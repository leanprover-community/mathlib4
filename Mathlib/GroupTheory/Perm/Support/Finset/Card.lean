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
  (Equivalently, `f.supportFinset` has at least 2 elements.)
-/

public section

open Equiv Finset Function

namespace Equiv.Perm

variable {α : Type*}

section supportFinset

variable [DecidableEq α] [Fintype α] {f g : Perm α}

section ExtendDomain

variable {β : Type*} [DecidableEq β] [Fintype β] {p : β → Prop} [DecidablePred p]

theorem card_supportFinset_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    #(g.extendDomain f).supportFinset = #g.supportFinset := by simp

@[deprecated (since := "2026-11-16")] alias card_support_extend_domain :=
    card_supportFinset_extend_domain

end ExtendDomain

section Card

theorem card_supportFinset_eq_zero {f : Perm α} : #f.supportFinset = 0 ↔ f = 1 := by
  rw [Finset.card_eq_zero, supportFinset_eq_empty_iff]

@[deprecated (since := "2026-11-16")] alias card_support_eq_zero := card_supportFinset_eq_zero

theorem one_lt_card_supportFinset_of_ne_one {f : Perm α} (h : f ≠ 1) : 1 < #f.supportFinset := by
  simp_rw [one_lt_card_iff, mem_supportFinset, ← not_or]
  contrapose! h
  ext a
  specialize h (f a) a
  rwa [apply_eq_iff_eq, or_self_iff, or_self_iff] at h

@[deprecated (since := "2026-11-16")] alias one_lt_card_support_of_ne_one :=
    one_lt_card_supportFinset_of_ne_one

theorem card_supportFinset_ne_one (f : Perm α) : #f.supportFinset ≠ 1 := by
  by_cases h : f = 1
  · exact ne_of_eq_of_ne (card_supportFinset_eq_zero.mpr h) zero_ne_one
  · exact ne_of_gt (one_lt_card_supportFinset_of_ne_one h)

@[deprecated (since := "2026-11-16")] alias card_support_ne_one := card_supportFinset_ne_one

@[simp]
theorem card_supportFinset_le_one {f : Perm α} : #f.supportFinset ≤ 1 ↔ f = 1 := by
  rw [le_iff_lt_or_eq, Nat.lt_succ_iff, Nat.le_zero, card_supportFinset_eq_zero,
    or_iff_not_imp_right, imp_iff_right f.card_supportFinset_ne_one]

@[deprecated (since := "2026-11-16")] alias card_support_le_one := card_supportFinset_le_one

theorem two_le_card_supportFinset_of_ne_one {f : Perm α} (h : f ≠ 1) : 2 ≤ #f.supportFinset :=
  one_lt_card_supportFinset_of_ne_one h

@[deprecated (since := "2026-11-16")] alias two_le_card_support_of_ne_one :=
    two_le_card_supportFinset_of_ne_one

theorem card_supportFinset_swap_mul {f : Perm α} {x : α} (hx : f x ≠ x) :
    #(swap x (f x) * f).supportFinset < #f.supportFinset :=
  Finset.card_lt_card
    ⟨fun _ hz => (mem_supportFinset_swap_mul_imp_mem_supportFinset_ne hz).left, fun h =>
      absurd (h (mem_supportFinset.2 hx)) (mt mem_supportFinset.1 (by simp))⟩

@[deprecated (since := "2026-11-16")] alias card_support_swap_mul := card_supportFinset_swap_mul

theorem card_supportFinset_swap {x y : α} (hxy : x ≠ y) : #(swap x y).supportFinset = 2 :=
  show #(swap x y).supportFinset = #⟨x ::ₘ y ::ₘ 0, by simp [hxy]⟩ from
    congr(card $(by simp [supportFinset_swap hxy, *, Finset.ext_iff]))

@[deprecated (since := "2026-11-16")] alias card_support_swap := card_supportFinset_swap

@[simp]
theorem card_supportFinset_eq_two {f : Perm α} : #f.supportFinset = 2 ↔ IsSwap f := by
  constructor <;> intro h
  · obtain ⟨x, t, hmem, hins, ht⟩ := card_eq_succ.1 h
    obtain ⟨y, rfl⟩ := card_eq_one.1 ht
    rw [mem_singleton] at hmem
    refine ⟨x, y, hmem, ?_⟩
    ext a
    have key : ∀ b, f b ≠ b ↔ _ := fun b => by
      rw [← mem_supportFinset, ← hins, mem_insert, mem_singleton]
    by_cases ha : f a = a
    · have ha' := not_or.mp (mt (key a).mpr (not_not.mpr ha))
      rw [ha, swap_apply_of_ne_of_ne ha'.1 ha'.2]
    · have ha' := (key (f a)).mp (mt f.apply_eq_iff_eq.mp ha)
      obtain rfl | rfl := (key a).mp ha
      · rw [Or.resolve_left ha' ha, swap_apply_left]
      · rw [Or.resolve_right ha' ha, swap_apply_right]
  · obtain ⟨x, y, hxy, rfl⟩ := h
    exact card_supportFinset_swap hxy

@[deprecated (since := "2026-11-16")] alias card_support_eq_two := card_supportFinset_eq_two

theorem Disjoint.card_supportFinset_mul (h : Disjoint f g) :
    #(f * g).supportFinset = #f.supportFinset + #g.supportFinset := by
  rw [← Finset.card_union_of_disjoint]
  · congr
    ext
    simp [h.supportFinset_mul]
  · simpa using h.disjoint_supportFinset

@[deprecated (since := "2026-11-16")] alias Disjoint.card_support_mul :=
    Disjoint.card_supportFinset_mul

theorem card_supportFinset_prod_list_of_pairwise_disjoint {l : List (Perm α)}
    (h : l.Pairwise Disjoint) :
    #l.prod.supportFinset = (l.map (card ∘ supportFinset)).sum := by
  induction l with
  | nil => exact card_supportFinset_eq_zero.mpr rfl
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h
    rw [List.prod_cons, List.map_cons, List.sum_cons, ← ih ht]
    exact (disjoint_prod_right _ ha).card_supportFinset_mul

@[deprecated (since := "2026-11-16")] alias card_support_prod_list_of_pairwise_disjoint :=
    card_supportFinset_prod_list_of_pairwise_disjoint

end Card

end supportFinset

section FixedPoints

/-!
### Fixed points
-/

theorem fixed_point_card_lt_of_ne_one [DecidableEq α] [Fintype α] {σ : Perm α} (h : σ ≠ 1) :
    #{x | σ x = x} < Fintype.card α - 1 := by
  rw [Nat.lt_sub_iff_add_lt, ← Nat.lt_sub_iff_add_lt', ← Finset.card_compl, Finset.compl_filter]
  exact one_lt_card_supportFinset_of_ne_one h

end FixedPoints

section Conjugation

variable [Fintype α] [DecidableEq α] {σ τ : Perm α}

theorem card_supportFinset_conj : #(σ * τ * σ⁻¹).supportFinset = #τ.supportFinset := by simp

@[deprecated (since := "2026-11-16")] alias card_support_conj := card_supportFinset_conj

end Conjugation

end Equiv.Perm
