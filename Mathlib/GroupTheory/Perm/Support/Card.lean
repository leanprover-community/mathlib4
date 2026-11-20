/-
Copyright (c) 2026 Kry10. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Perm.Support.Finset.Basic

/-!
# Cardinality of the support of a permutation

This file studies the cardinality of the `Set`-valued support `Equiv.Perm.support` of a
permutation, both as an extended natural number (`Set.encard`) and as a natural number
(`Set.ncard`).

The `ncard` lemmas that need finiteness of the
support - that is, that apply only to finitary permutation -
take it as an auto-param `hf : f.support.Finite`, discharged by `toFinite_tac`, so it is
found automatically when, for instance, `α` is `Finite`.

## Main statements

In the following, `f g : Equiv.Perm α`.

* `Equiv.Perm.encard_support_le_one`, `Equiv.Perm.ncard_support_le_one`: the support of `f` has
  at most one element iff `f = 1`. In particular, the support of `f ≠ 1` has at least two elements
  (`Equiv.Perm.two_le_encard_support_of_ne_one`, `Equiv.Perm.two_le_ncard_support_of_ne_one`).
* `Equiv.Perm.encard_support_eq_two`, `Equiv.Perm.ncard_support_eq_two`: the support of `f` has
  exactly two elements iff `f` is a swap.
* `Equiv.Perm.Disjoint.encard_support_mul`, `Equiv.Perm.Disjoint.ncard_support_mul`: the support
  of a product of disjoint permutations has cardinality the sum of the cardinalities.
* `Equiv.Perm.fixed_point_ncard_lt_of_ne_one`: for finite `α`, a permutation `f ≠ 1` has
  strictly fewer than `Nat.card α - 1` fixed points.
* `Equiv.Perm.card_supportFinset_eq_ncard_support`: `#f.supportFinset = f.support.ncard`.
* `Equiv.Perm.fixed_point_card_lt_of_ne_one f` says that `f` has
  strictly less than `Fintype.card α - 1` fixed points, unless `f = 1`.
  (Equivalently, `f.supportFinset` has at least 2 elements.)
-/

public section

open Finset

namespace Equiv.Perm

variable {α : Type*} {f g : Perm α}

section Encard

theorem encard_support_eq_zero : Set.encard f.support = 0 ↔ f = 1 := by
  rw [Set.encard_eq_zero, support_eq_empty_iff]

theorem encard_support_ne_one : Set.encard f.support ≠ 1 := by
  simp [Set.encard_eq_one, support_ne_singleton]

@[simp]
theorem encard_support_le_one : Set.encard f.support ≤ 1 ↔ f = 1 := by
  rw [Order.le_one_iff, encard_support_eq_zero]
  exact or_iff_left encard_support_ne_one

@[simp]
theorem one_lt_encard_support_iff : 1 < Set.encard f.support ↔ f ≠ 1 := by
  rw [← not_le, encard_support_le_one]

theorem one_lt_encard_support_of_ne_one (h : f ≠ 1) : 1 < Set.encard f.support :=
  one_lt_encard_support_iff.mpr h

theorem two_le_encard_support_iff : 2 ≤ Set.encard f.support ↔ f ≠ 1 :=
  (ENat.add_one_le_iff ENat.one_ne_top).trans one_lt_encard_support_iff

theorem two_le_encard_support_of_ne_one (h : f ≠ 1) : 2 ≤ Set.encard f.support :=
  two_le_encard_support_iff.mpr h

@[simp]
theorem encard_support_eq_two [DecidableEq α] : Set.encard f.support = 2 ↔ IsSwap f := by
  simp_rw [Set.encard_eq_two, ne_eq, support_eq_pair_iff, ← and_assoc, and_self, and_assoc,
    isSwap_iff_exists_apply]

theorem encard_support_swap [DecidableEq α] {x y : α} (hxy : x ≠ y) :
    Set.encard (swap x y).support = 2 := by
  rw [support_swap_of_ne hxy, Set.encard_pair hxy]

theorem Disjoint.encard_support_mul (h : f.Disjoint g) :
    Set.encard (f * g).support = Set.encard f.support + Set.encard g.support := by
  rw [h.support_mul, Set.encard_union_eq h.disjoint_support]

theorem encard_support_prod_list_of_pairwise_disjoint {l : List (Perm α)}
    (h : l.Pairwise Perm.Disjoint) :
    Set.encard l.prod.support = (l.map (Set.encard ∘ support)).sum := by
  induction h with
  | nil => simp
  | cons ha hl IH =>
    rw [List.prod_cons, List.map_cons, List.sum_cons, ← IH]
    exact (disjoint_prod_right _ ha).encard_support_mul

theorem encard_support_conj :
    Set.encard (f * g * f⁻¹).support = Set.encard g.support := by
  rw [support_conj, f.injective.encard_image]

theorem encard_support_extend_domain {β : Type*} {p : β → Prop} [DecidablePred p]
    (e : α ≃ Subtype p) : Set.encard (g.extendDomain e).support = Set.encard g.support := by
  rw [support_extend_domain, (Subtype.val_injective.comp e.injective).encard_image]

section Finitary

theorem encard_support_swap_mul [DecidableEq α] {x : α} (hf : f.support.Finite := by toFinite_tac)
    (hx : f x ≠ x) : Set.encard (swap x (f x) * f).support < Set.encard f.support :=
  have h : (swap x (f x) * f).support ⊆ f.support := fun _ hz =>
    (mem_support_swap_mul_imp_mem_support_ne hz).left
  (hf.subset h).encard_lt_encard
    ⟨h, fun h => absurd (h (mem_support.2 hx)) (mt mem_support.1 (by simp))⟩

end Finitary

theorem fixed_point_encard_add_two_le_of_ne_one (h : f ≠ 1) :
    Set.encard {x | f x = x} + 2 ≤ ENat.card α := by
  have hc : {x | f x = x} = f.supportᶜ := by ext; simp [mem_support]
  rw [hc, add_comm, ← Set.encard_add_encard_compl f.support]
  exact add_le_add_left (two_le_encard_support_of_ne_one h) _

end Encard

section NCard

theorem ncard_support_ne_one (f : Perm α) : Set.ncard f.support ≠ 1 := by
  rw [Ne, Set.ncard_eq_one, ← Set.encard_eq_one]
  exact f.encard_support_ne_one

theorem ncard_support_swap [DecidableEq α] {x y : α} (hxy : x ≠ y) :
    Set.ncard (swap x y).support = 2 := by
  rw [support_swap_of_ne hxy, Set.ncard_pair hxy]

@[simp]
theorem ncard_support_eq_two [DecidableEq α] : Set.ncard f.support = 2 ↔ IsSwap f := by
  rw [Set.ncard_eq_two, ← Set.encard_eq_two, encard_support_eq_two]

theorem ncard_support_conj : Set.ncard (f * g * f⁻¹).support = Set.ncard g.support := by
  rw [support_conj, Set.ncard_image_of_injective _ f.injective]

theorem ncard_support_extend_domain {β : Type*} {p : β → Prop} [DecidablePred p]
    (e : α ≃ Subtype p) : Set.ncard (g.extendDomain e).support = Set.ncard g.support := by
  rw [support_extend_domain,
    Set.ncard_image_of_injective _ (Subtype.val_injective.comp e.injective)]

section Finitary

theorem ncard_support_eq_zero (hf : f.support.Finite := by toFinite_tac) :
    Set.ncard f.support = 0 ↔ f = 1 := by
  rw [Set.ncard_eq_zero hf, support_eq_empty_iff]

theorem one_lt_ncard_support_of_ne_one (h : f ≠ 1) (hf : f.support.Finite := by toFinite_tac) :
    1 < Set.ncard f.support := by
  rw [← Nat.one_lt_cast (α := ℕ∞), hf.cast_ncard_eq]
  exact one_lt_encard_support_of_ne_one h

theorem ncard_support_le_one (hf : f.support.Finite := by toFinite_tac) :
    Set.ncard f.support ≤ 1 ↔ f = 1 := by
  rw [← Nat.cast_le (α := ℕ∞), Nat.cast_one, hf.cast_ncard_eq, encard_support_le_one]

theorem one_lt_ncard_support_iff (hf : f.support.Finite := by toFinite_tac) :
    1 < Set.ncard f.support ↔ f ≠ 1 := by
  rw [← not_le, ncard_support_le_one hf]

theorem two_le_ncard_support_iff (hf : f.support.Finite := by toFinite_tac) :
    2 ≤ Set.ncard f.support ↔ f ≠ 1 :=
  one_lt_ncard_support_iff hf

theorem two_le_ncard_support_of_ne_one (h : f ≠ 1) (hf : f.support.Finite := by toFinite_tac) :
    2 ≤ Set.ncard f.support :=
  one_lt_ncard_support_of_ne_one h hf

theorem ncard_support_swap_mul [DecidableEq α] {x : α} (hx : f x ≠ x)
    (hf : f.support.Finite := by toFinite_tac) :
    Set.ncard (swap x (f x) * f).support < Set.ncard f.support := by
  have h := encard_support_swap_mul hf hx
  have hfin := Set.encard_lt_top_iff.1 (h.trans hf.encard_lt_top)
  rwa [← Nat.cast_lt (α := ℕ∞), hfin.cast_ncard_eq, hf.cast_ncard_eq]

theorem Disjoint.ncard_support_mul (h : f.Disjoint g) (hf : f.support.Finite := by toFinite_tac)
    (hg : g.support.Finite := by toFinite_tac) :
    Set.ncard (f * g).support = Set.ncard f.support + Set.ncard g.support := by
  rw [h.support_mul, Set.ncard_union_eq h.disjoint_support hf hg]

theorem ncard_support_prod_list_of_pairwise_disjoint {l : List (Perm α)}
    (h : l.Pairwise Perm.Disjoint)
    (hl : ∀ f ∈ l, f.support.Finite := by intros h hf; toFinite_tac) :
    Set.ncard l.prod.support = (l.map (Set.ncard ∘ support)).sum := by
  have hmap : l.map (Set.encard ∘ support) = l.map (Nat.cast ∘ (Set.ncard ∘ support)) :=
    List.map_congr_left fun f hf ↦ ((hl f hf).cast_ncard_eq).symm
  rw [Set.ncard_def, encard_support_prod_list_of_pairwise_disjoint h, hmap, ← List.map_map]
  exact (congrArg ENat.toNat (map_list_sum (Nat.castAddMonoidHom ℕ∞) _).symm).trans
    (ENat.toNat_natCast _)

end Finitary

theorem fixed_point_ncard_lt_of_ne_one [Finite α] (h : f ≠ 1) :
    Set.ncard {x | f x = x} < Nat.card α - 1 := by
  have := fixed_point_encard_add_two_le_of_ne_one h
  rw [← (Set.toFinite _).cast_ncard_eq, ← Set.encard_univ, ← (Set.toFinite _).cast_ncard_eq,
    Set.ncard_univ] at this
  norm_cast at this
  omega

end NCard

section Card

variable [DecidableEq α] [Fintype α]

theorem card_supportFinset_eq_ncard_support (f : Perm α) :
    #f.supportFinset = f.support.ncard := (Set.ncard_coe_finset _).symm.trans <|
      congrArg _ f.coe_supportFinset_eq_support

attribute [local simp] card_supportFinset_eq_ncard_support
theorem card_supportFinset_eq_zero {f : Perm α} : #f.supportFinset = 0 ↔ f = 1 := by
  rw [card_supportFinset_eq_ncard_support]; exact ncard_support_eq_zero

@[deprecated (since := "2026-11-16")] alias card_support_eq_zero := card_supportFinset_eq_zero

theorem one_lt_card_supportFinset_of_ne_one {f : Perm α} (h : f ≠ 1) : 1 < #f.supportFinset := by
  rw [card_supportFinset_eq_ncard_support]; exact one_lt_ncard_support_of_ne_one h

@[deprecated (since := "2026-11-16")] alias one_lt_card_support_of_ne_one :=
    one_lt_card_supportFinset_of_ne_one

theorem card_supportFinset_ne_one (f : Perm α) : #f.supportFinset ≠ 1 := by
  rw [card_supportFinset_eq_ncard_support]; exact ncard_support_ne_one f

@[deprecated (since := "2026-11-16")] alias card_support_ne_one := card_supportFinset_ne_one

@[simp]
theorem card_supportFinset_le_one {f : Perm α} : #f.supportFinset ≤ 1 ↔ f = 1 := by
  rw [card_supportFinset_eq_ncard_support]; exact ncard_support_le_one

@[deprecated (since := "2026-11-16")] alias card_support_le_one := card_supportFinset_le_one

theorem two_le_card_supportFinset_of_ne_one {f : Perm α} (h : f ≠ 1) : 2 ≤ #f.supportFinset :=
  one_lt_card_supportFinset_of_ne_one h

@[deprecated (since := "2026-11-16")] alias two_le_card_support_of_ne_one :=
  two_le_card_supportFinset_of_ne_one

theorem card_supportFinset_swap_mul {f : Perm α} {x : α} (hx : f x ≠ x) :
    #(swap x (f x) * f).supportFinset < #f.supportFinset := by
  simp_rw [card_supportFinset_eq_ncard_support]; exact ncard_support_swap_mul hx

@[deprecated (since := "2026-11-16")] alias card_support_swap_mul := card_supportFinset_swap_mul

theorem card_supportFinset_swap {x y : α} (hxy : x ≠ y) : #(swap x y).supportFinset = 2 := by
  rw [card_supportFinset_eq_ncard_support]; exact ncard_support_swap hxy

@[deprecated (since := "2026-11-16")] alias card_support_swap := card_supportFinset_swap

@[simp]
theorem card_supportFinset_eq_two {f : Perm α} : #f.supportFinset = 2 ↔ IsSwap f := by
  rw [card_supportFinset_eq_ncard_support]; exact ncard_support_eq_two

@[deprecated (since := "2026-11-16")] alias card_support_eq_two := card_supportFinset_eq_two

theorem Disjoint.card_supportFinset_mul (h : f.Disjoint g) :
    #(f * g).supportFinset = #f.supportFinset + #g.supportFinset := by
  simp_rw [card_supportFinset_eq_ncard_support]; exact h.ncard_support_mul

@[deprecated (since := "2026-11-16")] alias Disjoint.card_support_mul :=
    Disjoint.card_supportFinset_mul

theorem card_supportFinset_prod_list_of_pairwise_disjoint {l : List (Perm α)}
    (h : l.Pairwise Perm.Disjoint) :
    #l.prod.supportFinset = (l.map (card ∘ supportFinset)).sum := by
  simp_rw [card_supportFinset_eq_ncard_support, ncard_support_prod_list_of_pairwise_disjoint h]
  exact congrArg _ <| l.map_congr_left (by simp)

@[deprecated (since := "2026-11-16")] alias card_support_prod_list_of_pairwise_disjoint :=
    card_supportFinset_prod_list_of_pairwise_disjoint

theorem card_supportFinset_extend_domain {β} [DecidableEq β] [Fintype β] {p : β → Prop}
    [DecidablePred p] (f : α ≃ Subtype p) {g : Perm α} :
    #(g.extendDomain f).supportFinset = #g.supportFinset := by simp

@[deprecated (since := "2026-11-16")] alias card_support_extend_domain :=
    card_supportFinset_extend_domain

theorem card_supportFinset_conj : #(f * g * f⁻¹).supportFinset = #g.supportFinset := by simp

@[deprecated (since := "2026-11-16")] alias card_support_conj := card_supportFinset_conj

theorem fixed_point_card_lt_of_ne_one {σ : Perm α} (h : σ ≠ 1) :
    #{x | σ x = x} < Fintype.card α - 1 := by
  rw [Nat.lt_sub_iff_add_lt, ← Nat.lt_sub_iff_add_lt', ← Finset.card_compl, Finset.compl_filter]
  exact one_lt_card_supportFinset_of_ne_one h

end Card

end Equiv.Perm
