/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Multiset.Basic

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

variable {F ι α β β' γ : Type*}

namespace Multiset

section CommMonoid

variable [CommMonoid α] [CommMonoid β] {s t : Multiset α} {a : α} {m : Multiset ι} {f g : ι → α}

/-- Product of a multiset given a commutative monoid structure on `α`.
  `prod {a, b, c} = a * b * c` -/
@[to_additive
      "Sum of a multiset given a commutative additive monoid structure on `α`.
      `sum {a, b, c} = a + b + c`"]
def prod : Multiset α → α :=
  foldr (· * ·) 1

@[to_additive]
theorem prod_eq_foldr (s : Multiset α) :
    prod s = foldr (· * ·) 1 s :=
  rfl

@[to_additive]
theorem prod_eq_foldl (s : Multiset α) :
    prod s = foldl (· * ·) 1 s :=
  (foldr_swap _ _ _).trans (by simp [mul_comm])

@[to_additive (attr := simp, norm_cast)]
theorem prod_coe (l : List α) : prod ↑l = l.prod :=
  prod_eq_foldl _

@[to_additive (attr := simp)]
theorem prod_toList (s : Multiset α) : s.toList.prod = s.prod := by
  conv_rhs => rw [← coe_toList s]
  rw [prod_coe]

@[to_additive (attr := simp)]
theorem prod_zero : @prod α _ 0 = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem prod_cons (a : α) (s) : prod (a ::ₘ s) = a * prod s :=
  foldr_cons _ _ _ _

@[to_additive (attr := simp)]
theorem prod_erase [DecidableEq α] (h : a ∈ s) : a * (s.erase a).prod = s.prod := by
  rw [← s.coe_toList, coe_erase, prod_coe, prod_coe, List.prod_erase (mem_toList.2 h)]

@[to_additive (attr := simp)]
theorem prod_map_erase [DecidableEq ι] {a : ι} (h : a ∈ m) :
    f a * ((m.erase a).map f).prod = (m.map f).prod := by
  rw [← m.coe_toList, coe_erase, map_coe, map_coe, prod_coe, prod_coe,
    List.prod_map_erase f (mem_toList.2 h)]

@[to_additive (attr := simp)]
theorem prod_singleton (a : α) : prod {a} = a := by
  simp only [mul_one, prod_cons, ← cons_zero, eq_self_iff_true, prod_zero]

@[to_additive]
theorem prod_pair (a b : α) : ({a, b} : Multiset α).prod = a * b := by
  rw [insert_eq_cons, prod_cons, prod_singleton]

@[to_additive (attr := simp)]
theorem prod_add (s t : Multiset α) : prod (s + t) = prod s * prod t :=
  Quotient.inductionOn₂ s t fun l₁ l₂ => by simp

@[to_additive]
theorem prod_nsmul (m : Multiset α) : ∀ n : ℕ, (n • m).prod = m.prod ^ n
  | 0 => by
    rw [zero_nsmul, pow_zero]
    rfl
  | n + 1 => by rw [add_nsmul, one_nsmul, pow_add, pow_one, prod_add, prod_nsmul m n]

@[to_additive]
theorem prod_filter_mul_prod_filter_not (p) [DecidablePred p] :
    (s.filter p).prod * (s.filter (fun a ↦ ¬ p a)).prod = s.prod := by
  rw [← prod_add, filter_add_not]

@[to_additive (attr := simp)]
theorem prod_replicate (n : ℕ) (a : α) : (replicate n a).prod = a ^ n := by
  simp [replicate, List.prod_replicate]

@[to_additive]
theorem prod_map_eq_pow_single [DecidableEq ι] (i : ι)
    (hf : ∀ i' ≠ i, i' ∈ m → f i' = 1) : (m.map f).prod = f i ^ m.count i := by
  induction m using Quotient.inductionOn
  simp [List.prod_map_eq_pow_single i f hf]

@[to_additive]
theorem prod_eq_pow_single [DecidableEq α] (a : α) (h : ∀ a' ≠ a, a' ∈ s → a' = 1) :
    s.prod = a ^ s.count a := by
  induction s using Quotient.inductionOn; simp [List.prod_eq_pow_single a h]

@[to_additive]
lemma prod_eq_one (h : ∀ x ∈ s, x = (1 : α)) : s.prod = 1 := by
  induction s using Quotient.inductionOn; simp [List.prod_eq_one h]

@[to_additive]
theorem pow_count [DecidableEq α] (a : α) : a ^ s.count a = (s.filter (Eq a)).prod := by
  rw [filter_eq, prod_replicate]

@[to_additive]
theorem prod_hom_ne_zero {s : Multiset α} (hs : s ≠ 0) {F : Type*} [FunLike F α β]
    [MulHomClass F α β] (f : F) :
    (s.map f).prod = f s.prod := by
  induction s using Quot.inductionOn; aesop (add simp List.prod_hom_nonempty)

@[to_additive]
theorem prod_hom (s : Multiset α) {F : Type*} [FunLike F α β]
    [MonoidHomClass F α β] (f : F) :
    (s.map f).prod = f s.prod :=
  Quotient.inductionOn s fun l => by simp only [l.prod_hom f, quot_mk_to_coe, map_coe, prod_coe]

@[to_additive]
theorem prod_hom' (s : Multiset ι) {F : Type*} [FunLike F α β]
    [MonoidHomClass F α β] (f : F)
    (g : ι → α) : (s.map fun i => f <| g i).prod = f (s.map g).prod := by
  convert (s.map g).prod_hom f
  exact (map_map _ _ _).symm

@[to_additive]
theorem prod_hom₂_ne_zero [CommMonoid γ] {s : Multiset ι} (hs : s ≠ 0) (f : α → β → γ)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (f₁ : ι → α) (f₂ : ι → β) :
    (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod := by
  induction s using Quotient.inductionOn; aesop (add simp List.prod_hom₂_nonempty)

@[to_additive]
theorem prod_hom₂ [CommMonoid γ] (s : Multiset ι) (f : α → β → γ)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 1) (f₁ : ι → α)
    (f₂ : ι → β) : (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod :=
  Quotient.inductionOn s fun l => by
    simp only [l.prod_hom₂ f hf hf', quot_mk_to_coe, map_coe, prod_coe]

@[to_additive]
theorem prod_hom_rel (s : Multiset ι) {r : α → β → Prop} {f : ι → α} {g : ι → β}
    (h₁ : r 1 1) (h₂ : ∀ ⦃a b c⦄, r b c → r (f a * b) (g a * c)) :
    r (s.map f).prod (s.map g).prod :=
  Quotient.inductionOn s fun l => by
    simp only [l.prod_hom_rel h₁ h₂, quot_mk_to_coe, map_coe, prod_coe]

@[to_additive]
theorem prod_map_one : prod (m.map fun _ => (1 : α)) = 1 := by
  rw [map_const', prod_replicate, one_pow]

@[to_additive (attr := simp)]
theorem prod_map_mul : (m.map fun i => f i * g i).prod = (m.map f).prod * (m.map g).prod :=
  m.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _

@[to_additive]
theorem prod_map_pow {n : ℕ} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n :=
  m.prod_hom' (powMonoidHom n : α →* α) f

@[to_additive]
theorem prod_map_prod_map (m : Multiset β') (n : Multiset γ) {f : β' → γ → α} :
    prod (m.map fun a => prod <| n.map fun b => f a b) =
      prod (n.map fun b => prod <| m.map fun a => f a b) :=
  Multiset.induction_on m (by simp) fun a m ih => by simp [ih]

@[to_additive]
theorem prod_induction (p : α → Prop) (s : Multiset α) (p_mul : ∀ a b, p a → p b → p (a * b))
    (p_one : p 1) (p_s : ∀ a ∈ s, p a) : p s.prod := by
  rw [prod_eq_foldr]
  exact foldr_induction (· * ·) 1 p s p_mul p_one p_s

@[to_additive]
theorem prod_induction_nonempty (p : α → Prop) (p_mul : ∀ a b, p a → p b → p (a * b)) (hs : s ≠ ∅)
    (p_s : ∀ a ∈ s, p a) : p s.prod := by
  -- Porting note: used to be `refine' Multiset.induction _ _`
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | cons a s hsa =>
    rw [prod_cons]
    by_cases hs_empty : s = ∅
    · simp [hs_empty, p_s a]
    have hps : ∀ x, x ∈ s → p x := fun x hxs => p_s x (mem_cons_of_mem hxs)
    exact p_mul a s.prod (p_s a (mem_cons_self a s)) (hsa hs_empty hps)

theorem prod_dvd_prod_of_le (h : s ≤ t) : s.prod ∣ t.prod := by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  simp only [prod_add, dvd_mul_right]

@[to_additive]
lemma _root_.map_multiset_prod [FunLike F α β] [MonoidHomClass F α β] (f : F) (s : Multiset α) :
    f s.prod = (s.map f).prod := (s.prod_hom f).symm

@[to_additive]
lemma _root_.map_multiset_ne_zero_prod [FunLike F α β] [MulHomClass F α β] (f : F)
    {s : Multiset α} (hs : s ≠ 0):
    f s.prod = (s.map f).prod := (s.prod_hom_ne_zero hs f).symm

@[to_additive]
protected lemma _root_.MonoidHom.map_multiset_prod (f : α →* β) (s : Multiset α) :
    f s.prod = (s.map f).prod := (s.prod_hom f).symm

@[to_additive]
protected lemma _root_.MulHom.map_multiset_ne_zero_prod (f : α →ₙ* β) (s : Multiset α)
    (hs : s ≠ 0) : f s.prod = (s.map f).prod := (s.prod_hom_ne_zero hs f).symm

lemma dvd_prod : a ∈ s → a ∣ s.prod :=
  Quotient.inductionOn s (fun l a h ↦ by simpa using List.dvd_prod h) a

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

section AddCommMonoid

variable [AddCommMonoid α]

/-- `Multiset.sum`, the sum of the elements of a multiset, promoted to a morphism of
`AddCommMonoid`s. -/
def sumAddMonoidHom : Multiset α →+ α where
  toFun := sum
  map_zero' := sum_zero
  map_add' := sum_add

@[simp]
theorem coe_sumAddMonoidHom : (sumAddMonoidHom : Multiset α → α) = sum :=
  rfl

end AddCommMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α] {m : Multiset ι} {f g : ι → α}

@[to_additive]
theorem prod_map_inv' (m : Multiset α) : (m.map Inv.inv).prod = m.prod⁻¹ :=
  m.prod_hom (invMonoidHom : α →* α)

@[to_additive (attr := simp)]
theorem prod_map_inv : (m.map fun i => (f i)⁻¹).prod = (m.map f).prod⁻¹ := by
  -- Porting note: used `convert`
  simp_rw [← (m.map f).prod_map_inv', map_map, Function.comp_apply]

@[to_additive (attr := simp)]
theorem prod_map_div : (m.map fun i => f i / g i).prod = (m.map f).prod / (m.map g).prod :=
  m.prod_hom₂ (· / ·) mul_div_mul_comm (div_one _) _ _

@[to_additive]
theorem prod_map_zpow {n : ℤ} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n := by
  convert (m.map f).prod_hom (zpowGroupHom n : α →* α)
  simp only [map_map, Function.comp_apply, zpowGroupHom_apply]

end DivisionCommMonoid

@[simp]
theorem sum_map_singleton (s : Multiset α) : (s.map fun a => ({a} : Multiset α)).sum = s :=
  Multiset.induction_on s (by simp) (by simp)

theorem sum_nat_mod (s : Multiset ℕ) (n : ℕ) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction <;> simp [Nat.add_mod, *]

theorem prod_nat_mod (s : Multiset ℕ) (n : ℕ) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Nat.mul_mod, *]

theorem sum_int_mod (s : Multiset ℤ) (n : ℤ) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction <;> simp [Int.add_emod, *]

theorem prod_int_mod (s : Multiset ℤ) (n : ℤ) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Int.mul_emod, *]

end Multiset
