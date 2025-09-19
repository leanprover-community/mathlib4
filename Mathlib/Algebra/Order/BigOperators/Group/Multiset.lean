/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Monoid.OrderDual
import Mathlib.Data.List.MinMax
import Mathlib.Data.Multiset.Fold
import Mathlib.Algebra.Order.Group.Unbundled.Abs

/-!
# Big operators on a multiset in ordered groups

This file contains the results concerning the interaction of multiset big operators with ordered
groups.
-/

assert_not_exists MonoidWithZero

variable {ι α β : Type*}

namespace Multiset
section OrderedCommMonoid
variable [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α] {s t : Multiset α} {a : α}

@[to_additive sum_nonneg]
lemma one_le_prod_of_one_le : (∀ x ∈ s, (1 : α) ≤ x) → 1 ≤ s.prod :=
  Quotient.inductionOn s fun l hl => by simpa using List.one_le_prod_of_one_le hl

@[to_additive]
lemma single_le_prod : (∀ x ∈ s, (1 : α) ≤ x) → ∀ x ∈ s, x ≤ s.prod :=
  Quotient.inductionOn s fun l hl x hx => by simpa using List.single_le_prod hl x hx

@[to_additive sum_le_card_nsmul]
lemma prod_le_pow_card (s : Multiset α) (n : α) (h : ∀ x ∈ s, x ≤ n) : s.prod ≤ n ^ card s := by
  induction s using Quotient.inductionOn
  simpa using List.prod_le_pow_card _ _ h

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
lemma all_one_of_le_one_le_of_prod_eq_one :
    (∀ x ∈ s, (1 : α) ≤ x) → s.prod = 1 → ∀ x ∈ s, x = (1 : α) :=
  Quotient.inductionOn s (by
    simp only [quot_mk_to_coe, prod_coe, mem_coe]
    exact fun l => List.all_one_of_le_one_le_of_prod_eq_one)

@[to_additive]
lemma prod_le_prod_of_rel_le (h : s.Rel (· ≤ ·) t) : s.prod ≤ t.prod := by
  induction h with
  | zero => rfl
  | cons rh _ rt =>
    rw [prod_cons, prod_cons]
    exact mul_le_mul' rh rt

@[to_additive]
lemma prod_map_le_prod_map {s : Multiset ι} (f : ι → α) (g : ι → α) (h : ∀ i, i ∈ s → f i ≤ g i) :
    (s.map f).prod ≤ (s.map g).prod :=
  prod_le_prod_of_rel_le <| rel_map.2 <| rel_refl_of_refl_on h

@[to_additive]
lemma prod_map_le_prod (f : α → α) (h : ∀ x, x ∈ s → f x ≤ x) : (s.map f).prod ≤ s.prod :=
  prod_le_prod_of_rel_le <| rel_map_left.2 <| rel_refl_of_refl_on h

@[to_additive]
lemma prod_le_prod_map (f : α → α) (h : ∀ x, x ∈ s → x ≤ f x) : s.prod ≤ (s.map f).prod :=
  prod_map_le_prod (α := αᵒᵈ) f h

@[to_additive card_nsmul_le_sum]
lemma pow_card_le_prod (h : ∀ x ∈ s, a ≤ x) : a ^ card s ≤ s.prod := by
  rw [← Multiset.prod_replicate, ← Multiset.map_const]
  exact prod_map_le_prod _ h

end OrderedCommMonoid

section
variable [CommMonoid α] [CommMonoid β] [PartialOrder β] [IsOrderedMonoid β]

@[to_additive le_sum_of_subadditive_on_pred]
lemma le_prod_of_submultiplicative_on_pred (f : α → β)
    (p : α → Prop) (h_one : f 1 = 1) (hp_one : p 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Multiset α) (hps : ∀ a, a ∈ s → p a) : f s.prod ≤ (s.map f).prod := by
  revert s
  refine Multiset.induction ?_ ?_
  · simp [le_of_eq h_one]
  intro a s hs hpsa
  have hps : ∀ x, x ∈ s → p x := fun x hx => hpsa x (mem_cons_of_mem hx)
  have hp_prod : p s.prod := prod_induction p s hp_mul hp_one hps
  rw [prod_cons, map_cons, prod_cons]
  exact (h_mul a s.prod (hpsa a (mem_cons_self a s)) hp_prod).trans (mul_le_mul_left' (hs hps) _)

@[to_additive le_sum_of_subadditive]
lemma le_prod_of_submultiplicative (f : α → β) (h_one : f 1 = 1)
    (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : Multiset α) : f s.prod ≤ (s.map f).prod :=
  le_prod_of_submultiplicative_on_pred f (fun _ => True) h_one trivial (fun x y _ _ => h_mul x y)
    (by simp) s (by simp)

@[to_additive le_sum_nonempty_of_subadditive_on_pred]
lemma le_prod_nonempty_of_submultiplicative_on_pred (f : α → β) (p : α → Prop)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Multiset α) (hs_nonempty : s ≠ ∅) (hs : ∀ a, a ∈ s → p a) : f s.prod ≤ (s.map f).prod := by
  revert s
  refine Multiset.induction ?_ ?_
  · simp
  rintro a s hs - hsa_prop
  rw [prod_cons, map_cons, prod_cons]
  by_cases hs_empty : s = ∅
  · simp [hs_empty]
  have hsa_restrict : ∀ x, x ∈ s → p x := fun x hx => hsa_prop x (mem_cons_of_mem hx)
  have hp_sup : p s.prod := prod_induction_nonempty p hp_mul hs_empty hsa_restrict
  have hp_a : p a := hsa_prop a (mem_cons_self a s)
  exact (h_mul a _ hp_a hp_sup).trans (mul_le_mul_left' (hs hs_empty hsa_restrict) _)

@[to_additive le_sum_nonempty_of_subadditive]
lemma le_prod_nonempty_of_submultiplicative (f : α → β) (h_mul : ∀ a b, f (a * b) ≤ f a * f b)
    (s : Multiset α) (hs_nonempty : s ≠ ∅) : f s.prod ≤ (s.map f).prod :=
  le_prod_nonempty_of_submultiplicative_on_pred f (fun _ => True) (by simp [h_mul]) (by simp) s
    hs_nonempty (by simp)

end

section OrderedCancelCommMonoid
variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] {s : Multiset ι} {f g : ι → α}

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

section CanonicallyOrderedMul
variable [CommMonoid α] [PartialOrder α] [CanonicallyOrderedMul α] {m : Multiset α} {a : α}

@[to_additive] lemma prod_eq_one_iff [IsOrderedMonoid α] : m.prod = 1 ↔ ∀ x ∈ m, x = (1 : α) :=
  Quotient.inductionOn m fun l ↦ by simpa using List.prod_eq_one_iff

@[to_additive] lemma le_prod_of_mem (ha : a ∈ m) : a ≤ m.prod := by
  obtain ⟨t, rfl⟩ := exists_cons_of_mem ha
  rw [prod_cons]
  exact _root_.le_mul_right (le_refl a)

end CanonicallyOrderedMul

lemma max_le_of_forall_le {α : Type*} [LinearOrder α] [OrderBot α] (l : Multiset α)
    (n : α) (h : ∀ x ∈ l, x ≤ n) : l.fold max ⊥ ≤ n := by
  induction l using Quotient.inductionOn
  simpa using List.max_le_of_forall_le _ _ h

@[to_additive]
lemma max_prod_le [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    {s : Multiset ι} {f g : ι → α} :
    max (s.map f).prod (s.map g).prod ≤ (s.map fun i ↦ max (f i) (g i)).prod := by
  obtain ⟨l⟩ := s
  simp_rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  apply List.max_prod_le

@[to_additive]
lemma prod_min_le [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    {s : Multiset ι} {f g : ι → α} :
    (s.map fun i ↦ min (f i) (g i)).prod ≤ min (s.map f).prod (s.map g).prod := by
  obtain ⟨l⟩ := s
  simp_rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  apply List.prod_min_le

lemma abs_sum_le_sum_abs [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {s : Multiset α} :
    |s.sum| ≤ (s.map abs).sum :=
  le_sum_of_subadditive _ abs_zero abs_add_le s

end Multiset
