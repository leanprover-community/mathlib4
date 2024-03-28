/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.List.Basic
import Mathlib.Algebra.BigOperators.Multiset.Basic
import Mathlib.Algebra.Order.Monoid.OrderDual
import Mathlib.Algebra.Order.Group.Abs

/-!
# Big operators in an algebraic ordered structure
-/

variable {ι α β : Type*}

namespace Multiset
section OrderedCommMonoid
variable [OrderedCommMonoid α] {s t : Multiset α} {a : α}

@[to_additive sum_nonneg]
lemma one_le_prod_of_one_le : (∀ x ∈ s, (1 : α) ≤ x) → 1 ≤ s.prod :=
  Quotient.inductionOn s fun l hl => by simpa using List.one_le_prod_of_one_le hl
#align multiset.one_le_prod_of_one_le Multiset.one_le_prod_of_one_le
#align multiset.sum_nonneg Multiset.sum_nonneg

@[to_additive]
lemma single_le_prod : (∀ x ∈ s, (1 : α) ≤ x) → ∀ x ∈ s, x ≤ s.prod :=
  Quotient.inductionOn s fun l hl x hx => by simpa using List.single_le_prod hl x hx
#align multiset.single_le_prod Multiset.single_le_prod
#align multiset.single_le_sum Multiset.single_le_sum

@[to_additive sum_le_card_nsmul]
lemma prod_le_pow_card (s : Multiset α) (n : α) (h : ∀ x ∈ s, x ≤ n) : s.prod ≤ n ^ card s := by
  induction s using Quotient.inductionOn
  simpa using List.prod_le_pow_card _ _ h
#align multiset.prod_le_pow_card Multiset.prod_le_pow_card
#align multiset.sum_le_card_nsmul Multiset.sum_le_card_nsmul

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
lemma all_one_of_le_one_le_of_prod_eq_one :
    (∀ x ∈ s, (1 : α) ≤ x) → s.prod = 1 → ∀ x ∈ s, x = (1 : α) :=
  Quotient.inductionOn s (by
    simp only [quot_mk_to_coe, prod_coe, mem_coe]
    exact fun l => List.all_one_of_le_one_le_of_prod_eq_one)
#align multiset.all_one_of_le_one_le_of_prod_eq_one Multiset.all_one_of_le_one_le_of_prod_eq_one
#align multiset.all_zero_of_le_zero_le_of_sum_eq_zero Multiset.all_zero_of_le_zero_le_of_sum_eq_zero

@[to_additive]
lemma prod_le_prod_of_rel_le (h : s.Rel (· ≤ ·) t) : s.prod ≤ t.prod := by
  induction' h with _ _ _ _ rh _ rt
  · rfl
  · rw [prod_cons, prod_cons]
    exact mul_le_mul' rh rt
#align multiset.prod_le_prod_of_rel_le Multiset.prod_le_prod_of_rel_le
#align multiset.sum_le_sum_of_rel_le Multiset.sum_le_sum_of_rel_le

@[to_additive]
lemma prod_map_le_prod_map {s : Multiset ι} (f : ι → α) (g : ι → α) (h : ∀ i, i ∈ s → f i ≤ g i) :
    (s.map f).prod ≤ (s.map g).prod :=
  prod_le_prod_of_rel_le <| rel_map.2 <| rel_refl_of_refl_on h
#align multiset.prod_map_le_prod_map Multiset.prod_map_le_prod_map
#align multiset.sum_map_le_sum_map Multiset.sum_map_le_sum_map

@[to_additive]
lemma prod_map_le_prod (f : α → α) (h : ∀ x, x ∈ s → f x ≤ x) : (s.map f).prod ≤ s.prod :=
  prod_le_prod_of_rel_le <| rel_map_left.2 <| rel_refl_of_refl_on h
#align multiset.prod_map_le_prod Multiset.prod_map_le_prod
#align multiset.sum_map_le_sum Multiset.sum_map_le_sum

@[to_additive]
lemma prod_le_prod_map (f : α → α) (h : ∀ x, x ∈ s → x ≤ f x) : s.prod ≤ (s.map f).prod :=
  @prod_map_le_prod αᵒᵈ _ _ f h
#align multiset.prod_le_prod_map Multiset.prod_le_prod_map
#align multiset.sum_le_sum_map Multiset.sum_le_sum_map

@[to_additive card_nsmul_le_sum]
lemma pow_card_le_prod (h : ∀ x ∈ s, a ≤ x) : a ^ card s ≤ s.prod := by
  rw [← Multiset.prod_replicate, ← Multiset.map_const]
  exact prod_map_le_prod _ h
#align multiset.pow_card_le_prod Multiset.pow_card_le_prod
#align multiset.card_nsmul_le_sum Multiset.card_nsmul_le_sum

end OrderedCommMonoid

section
variable [CommMonoid α] [OrderedCommMonoid β]

@[to_additive le_sum_of_subadditive_on_pred]
lemma le_prod_of_submultiplicative_on_pred (f : α → β)
    (p : α → Prop) (h_one : f 1 = 1) (hp_one : p 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Multiset α) (hps : ∀ a, a ∈ s → p a) : f s.prod ≤ (s.map f).prod := by
  revert s
  refine' Multiset.induction _ _
  · simp [le_of_eq h_one]
  intro a s hs hpsa
  have hps : ∀ x, x ∈ s → p x := fun x hx => hpsa x (mem_cons_of_mem hx)
  have hp_prod : p s.prod := prod_induction p s hp_mul hp_one hps
  rw [prod_cons, map_cons, prod_cons]
  exact (h_mul a s.prod (hpsa a (mem_cons_self a s)) hp_prod).trans (mul_le_mul_left' (hs hps) _)
#align multiset.le_prod_of_submultiplicative_on_pred Multiset.le_prod_of_submultiplicative_on_pred
#align multiset.le_sum_of_subadditive_on_pred Multiset.le_sum_of_subadditive_on_pred

@[to_additive le_sum_of_subadditive]
lemma le_prod_of_submultiplicative (f : α → β) (h_one : f 1 = 1)
    (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : Multiset α) : f s.prod ≤ (s.map f).prod :=
  le_prod_of_submultiplicative_on_pred f (fun _ => True) h_one trivial (fun x y _ _ => h_mul x y)
    (by simp) s (by simp)
#align multiset.le_prod_of_submultiplicative Multiset.le_prod_of_submultiplicative
#align multiset.le_sum_of_subadditive Multiset.le_sum_of_subadditive

@[to_additive le_sum_nonempty_of_subadditive_on_pred]
lemma le_prod_nonempty_of_submultiplicative_on_pred (f : α → β) (p : α → Prop)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Multiset α) (hs_nonempty : s ≠ ∅) (hs : ∀ a, a ∈ s → p a) : f s.prod ≤ (s.map f).prod := by
  revert s
  refine' Multiset.induction _ _
  · simp
  rintro a s hs - hsa_prop
  rw [prod_cons, map_cons, prod_cons]
  by_cases hs_empty : s = ∅
  · simp [hs_empty]
  have hsa_restrict : ∀ x, x ∈ s → p x := fun x hx => hsa_prop x (mem_cons_of_mem hx)
  have hp_sup : p s.prod := prod_induction_nonempty p hp_mul hs_empty hsa_restrict
  have hp_a : p a := hsa_prop a (mem_cons_self a s)
  exact (h_mul a _ hp_a hp_sup).trans (mul_le_mul_left' (hs hs_empty hsa_restrict) _)
#align multiset.le_prod_nonempty_of_submultiplicative_on_pred Multiset.le_prod_nonempty_of_submultiplicative_on_pred
#align multiset.le_sum_nonempty_of_subadditive_on_pred Multiset.le_sum_nonempty_of_subadditive_on_pred

@[to_additive le_sum_nonempty_of_subadditive]
lemma le_prod_nonempty_of_submultiplicative (f : α → β) (h_mul : ∀ a b, f (a * b) ≤ f a * f b)
    (s : Multiset α) (hs_nonempty : s ≠ ∅) : f s.prod ≤ (s.map f).prod :=
  le_prod_nonempty_of_submultiplicative_on_pred f (fun _ => True) (by simp [h_mul]) (by simp) s
    hs_nonempty (by simp)
#align multiset.le_prod_nonempty_of_submultiplicative Multiset.le_prod_nonempty_of_submultiplicative
#align multiset.le_sum_nonempty_of_subadditive Multiset.le_sum_nonempty_of_subadditive

end

section OrderedCancelCommMonoid
variable [OrderedCancelCommMonoid α] {s : Multiset ι} {f g : ι → α}

@[to_additive sum_lt_sum]
lemma prod_lt_prod' (hle : ∀ i ∈ s, f i ≤ g i) (hlt : ∃ i ∈ s, f i < g i) :
    (s.map f).prod < (s.map g).prod := by
  obtain ⟨l⟩ := s
  simp only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  exact List.prod_lt_prod' f g hle hlt

@[to_additive sum_lt_sum_of_nonempty]
lemma prod_lt_prod_of_nonempty' (hs : s ≠ ∅) (hfg : ∀ i ∈ s, f i < g i) :
    (s.map f).prod < (s.map g).prod := by
  obtain ⟨i, hi⟩ := exists_mem_of_ne_zero hs
  exact prod_lt_prod' (fun i hi => le_of_lt (hfg i hi)) ⟨i, hi, hfg i hi⟩

end OrderedCancelCommMonoid

@[to_additive]
lemma le_prod_of_mem [CanonicallyOrderedCommMonoid α] {s : Multiset α} {a : α} (h : a ∈ s) :
    a ≤ s.prod := by
  obtain ⟨t, rfl⟩ := exists_cons_of_mem h
  rw [prod_cons]
  exact _root_.le_mul_right (le_refl a)
#align multiset.le_prod_of_mem Multiset.le_prod_of_mem
#align multiset.le_sum_of_mem Multiset.le_sum_of_mem

lemma abs_sum_le_sum_abs [LinearOrderedAddCommGroup α] {s : Multiset α} :
    abs s.sum ≤ (s.map abs).sum :=
  le_sum_of_subadditive _ abs_zero abs_add s
#align multiset.abs_sum_le_sum_abs Multiset.abs_sum_le_sum_abs

lemma prod_nonneg [OrderedCommSemiring α] {s : Multiset α} (h : ∀ a ∈ s, (0 : α) ≤ a) :
    0 ≤ s.prod := by
  revert h
  refine s.induction_on ?_ fun a s hs ih ↦ ?_
  · simp
  · rw [prod_cons]
    exact mul_nonneg (ih _ <| mem_cons_self _ _) (hs fun a ha ↦ ih _ <| mem_cons_of_mem ha)
#align multiset.prod_nonneg Multiset.prod_nonneg
