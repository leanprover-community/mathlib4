/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module algebra.big_operators.multiset.basic
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.BigOperators.Basic
import Mathbin.Data.Multiset.Basic

/-!
# Sums and products over multisets

In this file we define products and sums indexed by multisets. This is later used to define products
and sums indexed by finite sets.

## Main declarations

* `multiset.prod`: `s.prod f` is the product of `f i` over all `i ∈ s`. Not to be mistaken with
  the cartesian product `multiset.product`.
* `multiset.sum`: `s.sum f` is the sum of `f i` over all `i ∈ s`.

## Implementation notes

Nov 2022: To speed the Lean 4 port, lemmas requiring extra algebra imports
(`data.list.big_operators.lemmas` rather than `.basic`) have been moved to a separate file,
`algebra.big_operators.multiset.lemmas`.  This split does not need to be permanent.
-/


variable {ι α β γ : Type _}

namespace Multiset

section CommMonoid

variable [CommMonoid α] {s t : Multiset α} {a : α} {m : Multiset ι} {f g : ι → α}

/-- Product of a multiset given a commutative monoid structure on `α`.
  `prod {a, b, c} = a * b * c` -/
@[to_additive
      "Sum of a multiset given a commutative additive monoid structure on `α`.\n  `sum {a, b, c} = a + b + c`"]
def prod : Multiset α → α :=
  foldr (· * ·) (fun x y z => by simp [mul_left_comm]) 1
#align multiset.prod Multiset.prod

@[to_additive]
theorem prod_eq_foldr (s : Multiset α) :
    prod s = foldr (· * ·) (fun x y z => by simp [mul_left_comm]) 1 s :=
  rfl
#align multiset.prod_eq_foldr Multiset.prod_eq_foldr

@[to_additive]
theorem prod_eq_foldl (s : Multiset α) :
    prod s = foldl (· * ·) (fun x y z => by simp [mul_right_comm]) 1 s :=
  (foldr_swap _ _ _ _).trans (by simp [mul_comm])
#align multiset.prod_eq_foldl Multiset.prod_eq_foldl

@[simp, norm_cast, to_additive]
theorem coe_prod (l : List α) : prod ↑l = l.Prod :=
  prod_eq_foldl _
#align multiset.coe_prod Multiset.coe_prod

@[simp, to_additive]
theorem prod_to_list (s : Multiset α) : s.toList.Prod = s.Prod :=
  by
  conv_rhs => rw [← coe_to_list s]
  rw [coe_prod]
#align multiset.prod_to_list Multiset.prod_to_list

@[simp, to_additive]
theorem prod_zero : @prod α _ 0 = 1 :=
  rfl
#align multiset.prod_zero Multiset.prod_zero

@[simp, to_additive]
theorem prod_cons (a : α) (s) : prod (a ::ₘ s) = a * prod s :=
  foldr_cons _ _ _ _ _
#align multiset.prod_cons Multiset.prod_cons

@[simp, to_additive]
theorem prod_erase [DecidableEq α] (h : a ∈ s) : a * (s.erase a).Prod = s.Prod := by
  rw [← s.coe_to_list, coe_erase, coe_prod, coe_prod, List.prod_erase (mem_to_list.2 h)]
#align multiset.prod_erase Multiset.prod_erase

@[simp, to_additive]
theorem prod_map_erase [DecidableEq ι] {a : ι} (h : a ∈ m) :
    f a * ((m.erase a).map f).Prod = (m.map f).Prod := by
  rw [← m.coe_to_list, coe_erase, coe_map, coe_map, coe_prod, coe_prod,
    List.prod_map_erase f (mem_to_list.2 h)]
#align multiset.prod_map_erase Multiset.prod_map_erase

@[simp, to_additive]
theorem prod_singleton (a : α) : prod {a} = a := by
  simp only [mul_one, prod_cons, ← cons_zero, eq_self_iff_true, prod_zero]
#align multiset.prod_singleton Multiset.prod_singleton

@[to_additive]
theorem prod_pair (a b : α) : ({a, b} : Multiset α).Prod = a * b := by
  rw [insert_eq_cons, prod_cons, prod_singleton]
#align multiset.prod_pair Multiset.prod_pair

@[simp, to_additive]
theorem prod_add (s t : Multiset α) : prod (s + t) = prod s * prod t :=
  (Quotient.induction_on₂ s t) fun l₁ l₂ => by simp
#align multiset.prod_add Multiset.prod_add

theorem prod_nsmul (m : Multiset α) : ∀ n : ℕ, (n • m).Prod = m.Prod ^ n
  | 0 => by
    rw [zero_nsmul, pow_zero]
    rfl
  | n + 1 => by rw [add_nsmul, one_nsmul, pow_add, pow_one, prod_add, prod_nsmul n]
#align multiset.prod_nsmul Multiset.prod_nsmul

@[simp, to_additive]
theorem prod_repeat (a : α) (n : ℕ) : (repeat a n).Prod = a ^ n := by
  simp [repeat, List.prod_repeat]
#align multiset.prod_repeat Multiset.prod_repeat

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (i' «expr ≠ » i) -/
@[to_additive]
theorem prod_map_eq_pow_single [DecidableEq ι] (i : ι)
    (hf : ∀ (i') (_ : i' ≠ i), i' ∈ m → f i' = 1) : (m.map f).Prod = f i ^ m.count i :=
  by
  induction' m using Quotient.induction_on with l
  simp [List.prod_map_eq_pow_single i f hf]
#align multiset.prod_map_eq_pow_single Multiset.prod_map_eq_pow_single

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (a' «expr ≠ » a) -/
@[to_additive]
theorem prod_eq_pow_single [DecidableEq α] (a : α) (h : ∀ (a') (_ : a' ≠ a), a' ∈ s → a' = 1) :
    s.Prod = a ^ s.count a :=
  by
  induction' s using Quotient.induction_on with l
  simp [List.prod_eq_pow_single a h]
#align multiset.prod_eq_pow_single Multiset.prod_eq_pow_single

@[to_additive]
theorem pow_count [DecidableEq α] (a : α) : a ^ s.count a = (s.filter (Eq a)).Prod := by
  rw [filter_eq, prod_repeat]
#align multiset.pow_count Multiset.pow_count

@[to_additive]
theorem prod_hom [CommMonoid β] (s : Multiset α) {F : Type _} [MonoidHomClass F α β] (f : F) :
    (s.map f).Prod = f s.Prod :=
  (Quotient.induction_on s) fun l => by simp only [l.prod_hom f, quot_mk_to_coe, coe_map, coe_prod]
#align multiset.prod_hom Multiset.prod_hom

@[to_additive]
theorem prod_hom' [CommMonoid β] (s : Multiset ι) {F : Type _} [MonoidHomClass F α β] (f : F)
    (g : ι → α) : (s.map fun i => f <| g i).Prod = f (s.map g).Prod :=
  by
  convert (s.map g).prod_hom f
  exact (map_map _ _ _).symm
#align multiset.prod_hom' Multiset.prod_hom'

@[to_additive]
theorem prod_hom₂ [CommMonoid β] [CommMonoid γ] (s : Multiset ι) (f : α → β → γ)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 1) (f₁ : ι → α)
    (f₂ : ι → β) : (s.map fun i => f (f₁ i) (f₂ i)).Prod = f (s.map f₁).Prod (s.map f₂).Prod :=
  (Quotient.induction_on s) fun l => by
    simp only [l.prod_hom₂ f hf hf', quot_mk_to_coe, coe_map, coe_prod]
#align multiset.prod_hom₂ Multiset.prod_hom₂

@[to_additive]
theorem prod_hom_rel [CommMonoid β] (s : Multiset ι) {r : α → β → Prop} {f : ι → α} {g : ι → β}
    (h₁ : r 1 1) (h₂ : ∀ ⦃a b c⦄, r b c → r (f a * b) (g a * c)) :
    r (s.map f).Prod (s.map g).Prod :=
  (Quotient.induction_on s) fun l => by
    simp only [l.prod_hom_rel h₁ h₂, quot_mk_to_coe, coe_map, coe_prod]
#align multiset.prod_hom_rel Multiset.prod_hom_rel

@[to_additive]
theorem prod_map_one : prod (m.map fun i => (1 : α)) = 1 := by rw [map_const, prod_repeat, one_pow]
#align multiset.prod_map_one Multiset.prod_map_one

@[simp, to_additive]
theorem prod_map_mul : (m.map fun i => f i * g i).Prod = (m.map f).Prod * (m.map g).Prod :=
  m.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _
#align multiset.prod_map_mul Multiset.prod_map_mul

@[simp]
theorem prod_map_neg [HasDistribNeg α] (s : Multiset α) :
    (s.map Neg.neg).Prod = (-1) ^ s.card * s.Prod :=
  by
  refine' Quotient.ind _ s
  simp
#align multiset.prod_map_neg Multiset.prod_map_neg

@[to_additive]
theorem prod_map_pow {n : ℕ} : (m.map fun i => f i ^ n).Prod = (m.map f).Prod ^ n :=
  m.prod_hom' (powMonoidHom n : α →* α) f
#align multiset.prod_map_pow Multiset.prod_map_pow

@[to_additive]
theorem prod_map_prod_map (m : Multiset β) (n : Multiset γ) {f : β → γ → α} :
    prod (m.map fun a => Prod <| n.map fun b => f a b) =
      prod (n.map fun b => Prod <| m.map fun a => f a b) :=
  Multiset.induction_on m (by simp) fun a m ih => by simp [ih]
#align multiset.prod_map_prod_map Multiset.prod_map_prod_map

@[to_additive]
theorem prod_induction (p : α → Prop) (s : Multiset α) (p_mul : ∀ a b, p a → p b → p (a * b))
    (p_one : p 1) (p_s : ∀ a ∈ s, p a) : p s.Prod :=
  by
  rw [prod_eq_foldr]
  exact foldr_induction (· * ·) (fun x y z => by simp [mul_left_comm]) 1 p s p_mul p_one p_s
#align multiset.prod_induction Multiset.prod_induction

@[to_additive]
theorem prod_induction_nonempty (p : α → Prop) (p_mul : ∀ a b, p a → p b → p (a * b)) (hs : s ≠ ∅)
    (p_s : ∀ a ∈ s, p a) : p s.Prod := by
  revert s
  refine' Multiset.induction _ _
  · intro h
    exfalso
    simpa using h
  intro a s hs hsa hpsa
  rw [prod_cons]
  by_cases hs_empty : s = ∅
  · simp [hs_empty, hpsa a]
  have hps : ∀ x, x ∈ s → p x := fun x hxs => hpsa x (mem_cons_of_mem hxs)
  exact p_mul a s.prod (hpsa a (mem_cons_self a s)) (hs hs_empty hps)
#align multiset.prod_induction_nonempty Multiset.prod_induction_nonempty

theorem prod_dvd_prod_of_le (h : s ≤ t) : s.Prod ∣ t.Prod :=
  by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  simp only [prod_add, dvd_mul_right]
#align multiset.prod_dvd_prod_of_le Multiset.prod_dvd_prod_of_le

end CommMonoid

theorem prod_dvd_prod_of_dvd [CommMonoid β] {S : Multiset α} (g1 g2 : α → β)
    (h : ∀ a ∈ S, g1 a ∣ g2 a) : (Multiset.map g1 S).Prod ∣ (Multiset.map g2 S).Prod :=
  by
  apply Multiset.induction_on' S; · simp
  intro a T haS _ IH
  simp [mul_dvd_mul (h a haS) IH]
#align multiset.prod_dvd_prod_of_dvd Multiset.prod_dvd_prod_of_dvd

section AddCommMonoid

variable [AddCommMonoid α]

/-- `multiset.sum`, the sum of the elements of a multiset, promoted to a morphism of
`add_comm_monoid`s. -/
def sumAddMonoidHom : Multiset α →+ α where
  toFun := sum
  map_zero' := sum_zero
  map_add' := sum_add
#align multiset.sum_add_monoid_hom Multiset.sumAddMonoidHom

@[simp]
theorem coe_sum_add_monoid_hom : (sumAddMonoidHom : Multiset α → α) = Sum :=
  rfl
#align multiset.coe_sum_add_monoid_hom Multiset.coe_sum_add_monoid_hom

end AddCommMonoid

section CommMonoidWithZero

variable [CommMonoidWithZero α]

theorem prod_eq_zero {s : Multiset α} (h : (0 : α) ∈ s) : s.Prod = 0 :=
  by
  rcases Multiset.exists_cons_of_mem h with ⟨s', hs'⟩
  simp [hs', Multiset.prod_cons]
#align multiset.prod_eq_zero Multiset.prod_eq_zero

variable [NoZeroDivisors α] [Nontrivial α] {s : Multiset α}

theorem prod_eq_zero_iff : s.Prod = 0 ↔ (0 : α) ∈ s :=
  (Quotient.induction_on s) fun l =>
    by
    rw [quot_mk_to_coe, coe_prod]
    exact List.prod_eq_zero_iff
#align multiset.prod_eq_zero_iff Multiset.prod_eq_zero_iff

theorem prod_ne_zero (h : (0 : α) ∉ s) : s.Prod ≠ 0 :=
  mt prod_eq_zero_iff.1 h
#align multiset.prod_ne_zero Multiset.prod_ne_zero

end CommMonoidWithZero

section DivisionCommMonoid

variable [DivisionCommMonoid α] {m : Multiset ι} {f g : ι → α}

@[to_additive]
theorem prod_map_inv' (m : Multiset α) : (m.map Inv.inv).Prod = m.Prod⁻¹ :=
  m.prod_hom (invMonoidHom : α →* α)
#align multiset.prod_map_inv' Multiset.prod_map_inv'

@[simp, to_additive]
theorem prod_map_inv : (m.map fun i => (f i)⁻¹).Prod = (m.map f).Prod⁻¹ :=
  by
  convert (m.map f).prod_map_inv'
  rw [map_map]
#align multiset.prod_map_inv Multiset.prod_map_inv

@[simp, to_additive]
theorem prod_map_div : (m.map fun i => f i / g i).Prod = (m.map f).Prod / (m.map g).Prod :=
  m.prod_hom₂ (· / ·) mul_div_mul_comm (div_one _) _ _
#align multiset.prod_map_div Multiset.prod_map_div

@[to_additive]
theorem prod_map_zpow {n : ℤ} : (m.map fun i => f i ^ n).Prod = (m.map f).Prod ^ n :=
  by
  convert (m.map f).prod_hom (zpowGroupHom _ : α →* α)
  rw [map_map]
  rfl
#align multiset.prod_map_zpow Multiset.prod_map_zpow

end DivisionCommMonoid

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] {a : α} {s : Multiset ι} {f : ι → α}

theorem sum_map_mul_left : sum (s.map fun i => a * f i) = a * sum (s.map f) :=
  Multiset.induction_on s (by simp) fun i s ih => by simp [ih, mul_add]
#align multiset.sum_map_mul_left Multiset.sum_map_mul_left

theorem sum_map_mul_right : sum (s.map fun i => f i * a) = sum (s.map f) * a :=
  Multiset.induction_on s (by simp) fun a s ih => by simp [ih, add_mul]
#align multiset.sum_map_mul_right Multiset.sum_map_mul_right

end NonUnitalNonAssocSemiring

section Semiring

variable [Semiring α]

theorem dvd_sum {a : α} {s : Multiset α} : (∀ x ∈ s, a ∣ x) → a ∣ s.Sum :=
  Multiset.induction_on s (fun _ => dvd_zero _) fun x s ih h =>
    by
    rw [sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun y hy => h _ <| mem_cons.2 <| Or.inr hy)
#align multiset.dvd_sum Multiset.dvd_sum

end Semiring

/-! ### Order -/


section OrderedCommMonoid

variable [OrderedCommMonoid α] {s t : Multiset α} {a : α}

@[to_additive sum_nonneg]
theorem one_le_prod_of_one_le : (∀ x ∈ s, (1 : α) ≤ x) → 1 ≤ s.Prod :=
  (Quotient.induction_on s) fun l hl => by simpa using List.one_le_prod_of_one_le hl
#align multiset.one_le_prod_of_one_le Multiset.one_le_prod_of_one_le

@[to_additive]
theorem single_le_prod : (∀ x ∈ s, (1 : α) ≤ x) → ∀ x ∈ s, x ≤ s.Prod :=
  (Quotient.induction_on s) fun l hl x hx => by simpa using List.single_le_prod hl x hx
#align multiset.single_le_prod Multiset.single_le_prod

@[to_additive sum_le_card_nsmul]
theorem prod_le_pow_card (s : Multiset α) (n : α) (h : ∀ x ∈ s, x ≤ n) : s.Prod ≤ n ^ s.card :=
  by
  induction s using Quotient.induction_on
  simpa using List.prod_le_pow_card _ _ h
#align multiset.prod_le_pow_card Multiset.prod_le_pow_card

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
theorem all_one_of_le_one_le_of_prod_eq_one :
    (∀ x ∈ s, (1 : α) ≤ x) → s.Prod = 1 → ∀ x ∈ s, x = (1 : α) :=
  by
  apply Quotient.induction_on s
  simp only [quot_mk_to_coe, coe_prod, mem_coe]
  exact fun l => List.all_one_of_le_one_le_of_prod_eq_one
#align multiset.all_one_of_le_one_le_of_prod_eq_one Multiset.all_one_of_le_one_le_of_prod_eq_one

@[to_additive]
theorem prod_le_prod_of_rel_le (h : s.Rel (· ≤ ·) t) : s.Prod ≤ t.Prod :=
  by
  induction' h with _ _ _ _ rh _ rt
  · rfl
  · rw [prod_cons, prod_cons]
    exact mul_le_mul' rh rt
#align multiset.prod_le_prod_of_rel_le Multiset.prod_le_prod_of_rel_le

@[to_additive]
theorem prod_map_le_prod_map {s : Multiset ι} (f : ι → α) (g : ι → α) (h : ∀ i, i ∈ s → f i ≤ g i) :
    (s.map f).Prod ≤ (s.map g).Prod :=
  prod_le_prod_of_rel_le <| rel_map.2 <| rel_refl_of_refl_on h
#align multiset.prod_map_le_prod_map Multiset.prod_map_le_prod_map

@[to_additive]
theorem prod_map_le_prod (f : α → α) (h : ∀ x, x ∈ s → f x ≤ x) : (s.map f).Prod ≤ s.Prod :=
  prod_le_prod_of_rel_le <| rel_map_left.2 <| rel_refl_of_refl_on h
#align multiset.prod_map_le_prod Multiset.prod_map_le_prod

@[to_additive]
theorem prod_le_prod_map (f : α → α) (h : ∀ x, x ∈ s → x ≤ f x) : s.Prod ≤ (s.map f).Prod :=
  @prod_map_le_prod αᵒᵈ _ _ f h
#align multiset.prod_le_prod_map Multiset.prod_le_prod_map

@[to_additive card_nsmul_le_sum]
theorem pow_card_le_prod (h : ∀ x ∈ s, a ≤ x) : a ^ s.card ≤ s.Prod :=
  by
  rw [← Multiset.prod_repeat, ← Multiset.map_const]
  exact prod_map_le_prod _ h
#align multiset.pow_card_le_prod Multiset.pow_card_le_prod

end OrderedCommMonoid

theorem prod_nonneg [OrderedCommSemiring α] {m : Multiset α} (h : ∀ a ∈ m, (0 : α) ≤ a) :
    0 ≤ m.Prod := by
  revert h
  refine' m.induction_on _ _
  · rintro -
    rw [prod_zero]
    exact zero_le_one
  intro a s hs ih
  rw [prod_cons]
  exact mul_nonneg (ih _ <| mem_cons_self _ _) (hs fun a ha => ih _ <| mem_cons_of_mem ha)
#align multiset.prod_nonneg Multiset.prod_nonneg

/-- Slightly more general version of `multiset.prod_eq_one_iff` for a non-ordered `monoid` -/
@[to_additive
      "Slightly more general version of `multiset.sum_eq_zero_iff`\n  for a non-ordered `add_monoid`"]
theorem prod_eq_one [CommMonoid α] {m : Multiset α} (h : ∀ x ∈ m, x = (1 : α)) : m.Prod = 1 :=
  by
  induction' m using Quotient.induction_on with l
  simp [List.prod_eq_one h]
#align multiset.prod_eq_one Multiset.prod_eq_one

@[to_additive]
theorem le_prod_of_mem [CanonicallyOrderedMonoid α] {m : Multiset α} {a : α} (h : a ∈ m) :
    a ≤ m.Prod := by
  obtain ⟨m', rfl⟩ := exists_cons_of_mem h
  rw [prod_cons]
  exact _root_.le_mul_right (le_refl a)
#align multiset.le_prod_of_mem Multiset.le_prod_of_mem

@[to_additive le_sum_of_subadditive_on_pred]
theorem le_prod_of_submultiplicative_on_pred [CommMonoid α] [OrderedCommMonoid β] (f : α → β)
    (p : α → Prop) (h_one : f 1 = 1) (hp_one : p 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Multiset α) (hps : ∀ a, a ∈ s → p a) : f s.Prod ≤ (s.map f).Prod :=
  by
  revert s
  refine' Multiset.induction _ _
  · simp [le_of_eq h_one]
  intro a s hs hpsa
  have hps : ∀ x, x ∈ s → p x := fun x hx => hpsa x (mem_cons_of_mem hx)
  have hp_prod : p s.prod := prod_induction p s hp_mul hp_one hps
  rw [prod_cons, map_cons, prod_cons]
  exact (h_mul a s.prod (hpsa a (mem_cons_self a s)) hp_prod).trans (mul_le_mul_left' (hs hps) _)
#align multiset.le_prod_of_submultiplicative_on_pred Multiset.le_prod_of_submultiplicative_on_pred

@[to_additive le_sum_of_subadditive]
theorem le_prod_of_submultiplicative [CommMonoid α] [OrderedCommMonoid β] (f : α → β)
    (h_one : f 1 = 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : Multiset α) :
    f s.Prod ≤ (s.map f).Prod :=
  le_prod_of_submultiplicative_on_pred f (fun i => True) h_one trivial (fun x y _ _ => h_mul x y)
    (by simp) s (by simp)
#align multiset.le_prod_of_submultiplicative Multiset.le_prod_of_submultiplicative

@[to_additive le_sum_nonempty_of_subadditive_on_pred]
theorem le_prod_nonempty_of_submultiplicative_on_pred [CommMonoid α] [OrderedCommMonoid β]
    (f : α → β) (p : α → Prop) (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b)
    (hp_mul : ∀ a b, p a → p b → p (a * b)) (s : Multiset α) (hs_nonempty : s ≠ ∅)
    (hs : ∀ a, a ∈ s → p a) : f s.Prod ≤ (s.map f).Prod :=
  by
  revert s
  refine' Multiset.induction _ _
  · intro h
    exfalso
    exact h rfl
  rintro a s hs hsa_nonempty hsa_prop
  rw [prod_cons, map_cons, prod_cons]
  by_cases hs_empty : s = ∅
  · simp [hs_empty]
  have hsa_restrict : ∀ x, x ∈ s → p x := fun x hx => hsa_prop x (mem_cons_of_mem hx)
  have hp_sup : p s.prod := prod_induction_nonempty p hp_mul hs_empty hsa_restrict
  have hp_a : p a := hsa_prop a (mem_cons_self a s)
  exact (h_mul a _ hp_a hp_sup).trans (mul_le_mul_left' (hs hs_empty hsa_restrict) _)
#align
  multiset.le_prod_nonempty_of_submultiplicative_on_pred Multiset.le_prod_nonempty_of_submultiplicative_on_pred

@[to_additive le_sum_nonempty_of_subadditive]
theorem le_prod_nonempty_of_submultiplicative [CommMonoid α] [OrderedCommMonoid β] (f : α → β)
    (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : Multiset α) (hs_nonempty : s ≠ ∅) :
    f s.Prod ≤ (s.map f).Prod :=
  le_prod_nonempty_of_submultiplicative_on_pred f (fun i => True) (by simp [h_mul]) (by simp) s
    hs_nonempty (by simp)
#align multiset.le_prod_nonempty_of_submultiplicative Multiset.le_prod_nonempty_of_submultiplicative

@[simp]
theorem sum_map_singleton (s : Multiset α) : (s.map fun a => ({a} : Multiset α)).Sum = s :=
  Multiset.induction_on s (by simp) (by simp)
#align multiset.sum_map_singleton Multiset.sum_map_singleton

theorem abs_sum_le_sum_abs [LinearOrderedAddCommGroup α] {s : Multiset α} :
    abs s.Sum ≤ (s.map abs).Sum :=
  le_sum_of_subadditive _ abs_zero abs_add s
#align multiset.abs_sum_le_sum_abs Multiset.abs_sum_le_sum_abs

end Multiset

@[to_additive]
theorem map_multiset_prod [CommMonoid α] [CommMonoid β] {F : Type _} [MonoidHomClass F α β] (f : F)
    (s : Multiset α) : f s.Prod = (s.map f).Prod :=
  (s.prod_hom f).symm
#align map_multiset_prod map_multiset_prod

@[to_additive]
protected theorem MonoidHom.map_multiset_prod [CommMonoid α] [CommMonoid β] (f : α →* β)
    (s : Multiset α) : f s.Prod = (s.map f).Prod :=
  (s.prod_hom f).symm
#align monoid_hom.map_multiset_prod MonoidHom.map_multiset_prod

