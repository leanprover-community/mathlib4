/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Multiset.Basic

#align_import algebra.big_operators.multiset.basic from "leanprover-community/mathlib"@"6c5f73fd6f6cc83122788a80a27cdd54663609f4"

/-!
# Sums and products over multisets

In this file we define products and sums indexed by multisets. This is later used to define products
and sums indexed by finite sets.

## Main declarations

* `Multiset.prod`: `s.prod f` is the product of `f i` over all `i ∈ s`. Not to be mistaken with
  the cartesian product `Multiset.product`.
* `Multiset.sum`: `s.sum f` is the sum of `f i` over all `i ∈ s`.
-/

assert_not_exists MonoidWithZero

variable {F ι α β γ : Type*}

namespace Multiset

section CommMonoid

variable [CommMonoid α] [CommMonoid β] {s t : Multiset α} {a : α} {m : Multiset ι} {f g : ι → α}

/-- Product of a multiset given a commutative monoid structure on `α`.
  `prod {a, b, c} = a * b * c` -/
@[to_additive
      "Sum of a multiset given a commutative additive monoid structure on `α`.
      `sum {a, b, c} = a + b + c`"]
def prod : Multiset α → α :=
  foldr (· * ·) (fun x y z => by simp [mul_left_comm]) 1
#align multiset.prod Multiset.prod
#align multiset.sum Multiset.sum

@[to_additive]
theorem prod_eq_foldr (s : Multiset α) :
    prod s = foldr (· * ·) (fun x y z => by simp [mul_left_comm]) 1 s :=
  rfl
#align multiset.prod_eq_foldr Multiset.prod_eq_foldr
#align multiset.sum_eq_foldr Multiset.sum_eq_foldr

@[to_additive]
theorem prod_eq_foldl (s : Multiset α) :
    prod s = foldl (· * ·) (fun x y z => by simp [mul_right_comm]) 1 s :=
  (foldr_swap _ _ _ _).trans (by simp [mul_comm])
#align multiset.prod_eq_foldl Multiset.prod_eq_foldl
#align multiset.sum_eq_foldl Multiset.sum_eq_foldl

@[to_additive (attr := simp, norm_cast)]
theorem prod_coe (l : List α) : prod ↑l = l.prod :=
  prod_eq_foldl _
#align multiset.coe_prod Multiset.prod_coe
#align multiset.coe_sum Multiset.sum_coe

@[to_additive (attr := simp)]
theorem prod_toList (s : Multiset α) : s.toList.prod = s.prod := by
  conv_rhs => rw [← coe_toList s]
  rw [prod_coe]
#align multiset.prod_to_list Multiset.prod_toList
#align multiset.sum_to_list Multiset.sum_toList

@[to_additive (attr := simp)]
theorem prod_zero : @prod α _ 0 = 1 :=
  rfl
#align multiset.prod_zero Multiset.prod_zero
#align multiset.sum_zero Multiset.sum_zero

@[to_additive (attr := simp)]
theorem prod_cons (a : α) (s) : prod (a ::ₘ s) = a * prod s :=
  foldr_cons _ _ _ _ _
#align multiset.prod_cons Multiset.prod_cons
#align multiset.sum_cons Multiset.sum_cons

@[to_additive (attr := simp)]
theorem prod_erase [DecidableEq α] (h : a ∈ s) : a * (s.erase a).prod = s.prod := by
  rw [← s.coe_toList, coe_erase, prod_coe, prod_coe, List.prod_erase (mem_toList.2 h)]
#align multiset.prod_erase Multiset.prod_erase
#align multiset.sum_erase Multiset.sum_erase

@[to_additive (attr := simp)]
theorem prod_map_erase [DecidableEq ι] {a : ι} (h : a ∈ m) :
    f a * ((m.erase a).map f).prod = (m.map f).prod := by
  rw [← m.coe_toList, coe_erase, map_coe, map_coe, prod_coe, prod_coe,
    List.prod_map_erase f (mem_toList.2 h)]
#align multiset.prod_map_erase Multiset.prod_map_erase
#align multiset.sum_map_erase Multiset.sum_map_erase

@[to_additive (attr := simp)]
theorem prod_singleton (a : α) : prod {a} = a := by
  simp only [mul_one, prod_cons, ← cons_zero, eq_self_iff_true, prod_zero]
#align multiset.prod_singleton Multiset.prod_singleton
#align multiset.sum_singleton Multiset.sum_singleton

@[to_additive]
theorem prod_pair (a b : α) : ({a, b} : Multiset α).prod = a * b := by
  rw [insert_eq_cons, prod_cons, prod_singleton]
#align multiset.prod_pair Multiset.prod_pair
#align multiset.sum_pair Multiset.sum_pair

@[to_additive (attr := simp)]
theorem prod_add (s t : Multiset α) : prod (s + t) = prod s * prod t :=
  Quotient.inductionOn₂ s t fun l₁ l₂ => by simp
#align multiset.prod_add Multiset.prod_add
#align multiset.sum_add Multiset.sum_add

@[to_additive]
theorem prod_nsmul (m : Multiset α) : ∀ n : ℕ, (n • m).prod = m.prod ^ n
  | 0 => by
    rw [zero_nsmul, pow_zero]
    rfl
  | n + 1 => by rw [add_nsmul, one_nsmul, pow_add, pow_one, prod_add, prod_nsmul m n]
#align multiset.prod_nsmul Multiset.prod_nsmul

@[to_additive]
theorem prod_filter_mul_prod_filter_not (p) [DecidablePred p] :
    (s.filter p).prod * (s.filter (fun a ↦ ¬ p a)).prod = s.prod := by
  rw [← prod_add, filter_add_not]

@[to_additive (attr := simp)]
theorem prod_replicate (n : ℕ) (a : α) : (replicate n a).prod = a ^ n := by
  simp [replicate, List.prod_replicate]
#align multiset.prod_replicate Multiset.prod_replicate
#align multiset.sum_replicate Multiset.sum_replicate

@[to_additive]
theorem prod_map_eq_pow_single [DecidableEq ι] (i : ι)
    (hf : ∀ i' ≠ i, i' ∈ m → f i' = 1) : (m.map f).prod = f i ^ m.count i := by
  induction' m using Quotient.inductionOn with l
  simp [List.prod_map_eq_pow_single i f hf]
#align multiset.prod_map_eq_pow_single Multiset.prod_map_eq_pow_single
#align multiset.sum_map_eq_nsmul_single Multiset.sum_map_eq_nsmul_single

@[to_additive]
theorem prod_eq_pow_single [DecidableEq α] (a : α) (h : ∀ a' ≠ a, a' ∈ s → a' = 1) :
    s.prod = a ^ s.count a := by
  induction' s using Quotient.inductionOn with l
  simp [List.prod_eq_pow_single a h]
#align multiset.prod_eq_pow_single Multiset.prod_eq_pow_single
#align multiset.sum_eq_nsmul_single Multiset.sum_eq_nsmul_single

@[to_additive]
lemma prod_eq_one (h : ∀ x ∈ s, x = (1 : α)) : s.prod = 1 := by
  induction' s using Quotient.inductionOn with l; simp [List.prod_eq_one h]
#align multiset.prod_eq_one Multiset.prod_eq_one
#align multiset.sum_eq_zero Multiset.sum_eq_zero

@[to_additive]
theorem pow_count [DecidableEq α] (a : α) : a ^ s.count a = (s.filter (Eq a)).prod := by
  rw [filter_eq, prod_replicate]
#align multiset.pow_count Multiset.pow_count
#align multiset.nsmul_count Multiset.nsmul_count

@[to_additive]
theorem prod_hom [CommMonoid β] (s : Multiset α) {F : Type*} [FunLike F α β]
    [MonoidHomClass F α β] (f : F) :
    (s.map f).prod = f s.prod :=
  Quotient.inductionOn s fun l => by simp only [l.prod_hom f, quot_mk_to_coe, map_coe, prod_coe]
#align multiset.prod_hom Multiset.prod_hom
#align multiset.sum_hom Multiset.sum_hom

@[to_additive]
theorem prod_hom' [CommMonoid β] (s : Multiset ι) {F : Type*} [FunLike F α β]
    [MonoidHomClass F α β] (f : F)
    (g : ι → α) : (s.map fun i => f <| g i).prod = f (s.map g).prod := by
  convert (s.map g).prod_hom f
  exact (map_map _ _ _).symm
#align multiset.prod_hom' Multiset.prod_hom'
#align multiset.sum_hom' Multiset.sum_hom'

@[to_additive]
theorem prod_hom₂ [CommMonoid β] [CommMonoid γ] (s : Multiset ι) (f : α → β → γ)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 1) (f₁ : ι → α)
    (f₂ : ι → β) : (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod :=
  Quotient.inductionOn s fun l => by
    simp only [l.prod_hom₂ f hf hf', quot_mk_to_coe, map_coe, prod_coe]
#align multiset.prod_hom₂ Multiset.prod_hom₂
#align multiset.sum_hom₂ Multiset.sum_hom₂

@[to_additive]
theorem prod_hom_rel [CommMonoid β] (s : Multiset ι) {r : α → β → Prop} {f : ι → α} {g : ι → β}
    (h₁ : r 1 1) (h₂ : ∀ ⦃a b c⦄, r b c → r (f a * b) (g a * c)) :
    r (s.map f).prod (s.map g).prod :=
  Quotient.inductionOn s fun l => by
    simp only [l.prod_hom_rel h₁ h₂, quot_mk_to_coe, map_coe, prod_coe]
#align multiset.prod_hom_rel Multiset.prod_hom_rel
#align multiset.sum_hom_rel Multiset.sum_hom_rel

@[to_additive]
theorem prod_map_one : prod (m.map fun _ => (1 : α)) = 1 := by
  rw [map_const', prod_replicate, one_pow]
#align multiset.prod_map_one Multiset.prod_map_one
#align multiset.sum_map_zero Multiset.sum_map_zero

@[to_additive (attr := simp)]
theorem prod_map_mul : (m.map fun i => f i * g i).prod = (m.map f).prod * (m.map g).prod :=
  m.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _
#align multiset.prod_map_mul Multiset.prod_map_mul
#align multiset.sum_map_add Multiset.sum_map_add

@[to_additive]
theorem prod_map_pow {n : ℕ} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n :=
  m.prod_hom' (powMonoidHom n : α →* α) f
#align multiset.prod_map_pow Multiset.prod_map_pow
#align multiset.sum_map_nsmul Multiset.sum_map_nsmul

@[to_additive]
theorem prod_map_prod_map (m : Multiset β) (n : Multiset γ) {f : β → γ → α} :
    prod (m.map fun a => prod <| n.map fun b => f a b) =
      prod (n.map fun b => prod <| m.map fun a => f a b) :=
  Multiset.induction_on m (by simp) fun a m ih => by simp [ih]
#align multiset.prod_map_prod_map Multiset.prod_map_prod_map
#align multiset.sum_map_sum_map Multiset.sum_map_sum_map

@[to_additive]
theorem prod_induction (p : α → Prop) (s : Multiset α) (p_mul : ∀ a b, p a → p b → p (a * b))
    (p_one : p 1) (p_s : ∀ a ∈ s, p a) : p s.prod := by
  rw [prod_eq_foldr]
  exact foldr_induction (· * ·) (fun x y z => by simp [mul_left_comm]) 1 p s p_mul p_one p_s
#align multiset.prod_induction Multiset.prod_induction
#align multiset.sum_induction Multiset.sum_induction

@[to_additive]
theorem prod_induction_nonempty (p : α → Prop) (p_mul : ∀ a b, p a → p b → p (a * b)) (hs : s ≠ ∅)
    (p_s : ∀ a ∈ s, p a) : p s.prod := by
  -- Porting note: used to be `refine' Multiset.induction _ _`
  induction' s using Multiset.induction_on with a s hsa
  · simp at hs
  rw [prod_cons]
  by_cases hs_empty : s = ∅
  · simp [hs_empty, p_s a]
  have hps : ∀ x, x ∈ s → p x := fun x hxs => p_s x (mem_cons_of_mem hxs)
  exact p_mul a s.prod (p_s a (mem_cons_self a s)) (hsa hs_empty hps)
#align multiset.prod_induction_nonempty Multiset.prod_induction_nonempty
#align multiset.sum_induction_nonempty Multiset.sum_induction_nonempty

theorem prod_dvd_prod_of_le (h : s ≤ t) : s.prod ∣ t.prod := by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  simp only [prod_add, dvd_mul_right]
#align multiset.prod_dvd_prod_of_le Multiset.prod_dvd_prod_of_le

@[to_additive]
lemma _root_.map_multiset_prod [FunLike F α β] [MonoidHomClass F α β] (f : F) (s : Multiset α) :
    f s.prod = (s.map f).prod := (s.prod_hom f).symm
#align map_multiset_prod map_multiset_prod
#align map_multiset_sum map_multiset_sum

@[to_additive]
protected lemma _root_.MonoidHom.map_multiset_prod (f : α →* β) (s : Multiset α) :
    f s.prod = (s.map f).prod := (s.prod_hom f).symm
#align monoid_hom.map_multiset_prod MonoidHom.map_multiset_prod
#align add_monoid_hom.map_multiset_sum AddMonoidHom.map_multiset_sum

lemma dvd_prod : a ∈ s → a ∣ s.prod :=
  Quotient.inductionOn s (fun l a h ↦ by simpa using List.dvd_prod h) a
#align multiset.dvd_prod Multiset.dvd_prod

@[to_additive] lemma fst_prod (s : Multiset (α × β)) : s.prod.1 = (s.map Prod.fst).prod :=
  map_multiset_prod (MonoidHom.fst _ _) _

@[to_additive] lemma snd_prod (s : Multiset (α × β)) : s.prod.2 = (s.map Prod.snd).prod :=
  map_multiset_prod (MonoidHom.snd _ _) _

end CommMonoid

theorem prod_dvd_prod_of_dvd [CommMonoid β] {S : Multiset α} (g1 g2 : α → β)
    (h : ∀ a ∈ S, g1 a ∣ g2 a) : (Multiset.map g1 S).prod ∣ (Multiset.map g2 S).prod := by
  apply Multiset.induction_on' S
  · simp
  intro a T haS _ IH
  simp [mul_dvd_mul (h a haS) IH]
#align multiset.prod_dvd_prod_of_dvd Multiset.prod_dvd_prod_of_dvd

section AddCommMonoid

variable [AddCommMonoid α]

/-- `Multiset.sum`, the sum of the elements of a multiset, promoted to a morphism of
`AddCommMonoid`s. -/
def sumAddMonoidHom : Multiset α →+ α where
  toFun := sum
  map_zero' := sum_zero
  map_add' := sum_add
#align multiset.sum_add_monoid_hom Multiset.sumAddMonoidHom

@[simp]
theorem coe_sumAddMonoidHom : (sumAddMonoidHom : Multiset α → α) = sum :=
  rfl
#align multiset.coe_sum_add_monoid_hom Multiset.coe_sumAddMonoidHom

end AddCommMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α] {m : Multiset ι} {f g : ι → α}

@[to_additive]
theorem prod_map_inv' (m : Multiset α) : (m.map Inv.inv).prod = m.prod⁻¹ :=
  m.prod_hom (invMonoidHom : α →* α)
#align multiset.prod_map_inv' Multiset.prod_map_inv'
#align multiset.sum_map_neg' Multiset.sum_map_neg'

@[to_additive (attr := simp)]
theorem prod_map_inv : (m.map fun i => (f i)⁻¹).prod = (m.map f).prod⁻¹ := by
  -- Porting note: used `convert`
  simp_rw [← (m.map f).prod_map_inv', map_map, Function.comp_apply]
#align multiset.prod_map_inv Multiset.prod_map_inv
#align multiset.sum_map_neg Multiset.sum_map_neg

@[to_additive (attr := simp)]
theorem prod_map_div : (m.map fun i => f i / g i).prod = (m.map f).prod / (m.map g).prod :=
  m.prod_hom₂ (· / ·) mul_div_mul_comm (div_one _) _ _
#align multiset.prod_map_div Multiset.prod_map_div
#align multiset.sum_map_sub Multiset.sum_map_sub

@[to_additive]
theorem prod_map_zpow {n : ℤ} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n := by
  convert (m.map f).prod_hom (zpowGroupHom n : α →* α)
  simp only [map_map, Function.comp_apply, zpowGroupHom_apply]
#align multiset.prod_map_zpow Multiset.prod_map_zpow
#align multiset.sum_map_zsmul Multiset.sum_map_zsmul

end DivisionCommMonoid

@[simp]
theorem sum_map_singleton (s : Multiset α) : (s.map fun a => ({a} : Multiset α)).sum = s :=
  Multiset.induction_on s (by simp) (by simp)
#align multiset.sum_map_singleton Multiset.sum_map_singleton

theorem sum_nat_mod (s : Multiset ℕ) (n : ℕ) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction <;> simp [Nat.add_mod, *]
#align multiset.sum_nat_mod Multiset.sum_nat_mod

theorem prod_nat_mod (s : Multiset ℕ) (n : ℕ) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Nat.mul_mod, *]
#align multiset.prod_nat_mod Multiset.prod_nat_mod

theorem sum_int_mod (s : Multiset ℤ) (n : ℤ) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction <;> simp [Int.add_emod, *]
#align multiset.sum_int_mod Multiset.sum_int_mod

theorem prod_int_mod (s : Multiset ℤ) (n : ℤ) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Int.mul_emod, *]
#align multiset.prod_int_mod Multiset.prod_int_mod

end Multiset
