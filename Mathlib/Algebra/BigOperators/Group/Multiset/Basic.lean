/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.Order.Sub.Unbundled.Basic

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

variable {F ι κ G M N O : Type*}

namespace Multiset

section CommMonoid

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

@[to_additive (attr := simp)]
theorem prod_erase [DecidableEq M] (h : a ∈ s) : a * (s.erase a).prod = s.prod := by
  rw [← s.coe_toList, coe_erase, prod_coe, prod_coe, List.prod_erase (mem_toList.2 h)]

@[to_additive (attr := simp)]
theorem prod_map_erase [DecidableEq ι] {a : ι} (h : a ∈ m) :
    f a * ((m.erase a).map f).prod = (m.map f).prod := by
  rw [← m.coe_toList, coe_erase, map_coe, map_coe, prod_coe, prod_coe,
    List.prod_map_erase f (mem_toList.2 h)]

@[to_additive (attr := simp, grind =)]
theorem prod_add (s t : Multiset M) : prod (s + t) = prod s * prod t :=
  Quotient.inductionOn₂ s t fun l₁ l₂ => by simp

@[to_additive]
theorem prod_nsmul (m : Multiset M) : ∀ n : ℕ, (n • m).prod = m.prod ^ n
  | 0 => by
    rw [zero_nsmul, pow_zero]
    rfl
  | n + 1 => by rw [add_nsmul, one_nsmul, pow_add, pow_one, prod_add, prod_nsmul m n]

@[to_additive]
theorem prod_filter_mul_prod_filter_not (p) [DecidablePred p] :
    (s.filter p).prod * (s.filter (fun a ↦ ¬ p a)).prod = s.prod := by
  rw [← prod_add, filter_add_not]

@[to_additive]
theorem prod_map_eq_pow_single [DecidableEq ι] (i : ι)
    (hf : ∀ i' ≠ i, i' ∈ m → f i' = 1) : (m.map f).prod = f i ^ m.count i := by
  induction m using Quotient.inductionOn
  simp [List.prod_map_eq_pow_single i f hf]

@[to_additive]
theorem prod_eq_pow_single [DecidableEq M] (a : M) (h : ∀ a' ≠ a, a' ∈ s → a' = 1) :
    s.prod = a ^ s.count a := by
  induction s using Quotient.inductionOn; simp [List.prod_eq_pow_single a h]

@[to_additive]
lemma prod_eq_one (h : ∀ x ∈ s, x = (1 : M)) : s.prod = 1 := by
  induction s using Quotient.inductionOn; simp [List.prod_eq_one h]

@[to_additive]
theorem prod_hom_ne_zero {s : Multiset M} (hs : s ≠ 0) {F : Type*} [FunLike F M N]
    [MulHomClass F M N] (f : F) :
    (s.map f).prod = f s.prod := by
  induction s using Quot.inductionOn; aesop (add simp List.prod_hom_nonempty)

@[to_additive]
theorem prod_hom (s : Multiset M) {F : Type*} [FunLike F M N]
    [MonoidHomClass F M N] (f : F) :
    (s.map f).prod = f s.prod :=
  Quotient.inductionOn s fun l => by simp only [l.prod_hom f, quot_mk_to_coe, map_coe, prod_coe]

@[to_additive]
theorem prod_hom' (s : Multiset ι) {F : Type*} [FunLike F M N]
    [MonoidHomClass F M N] (f : F)
    (g : ι → M) : (s.map fun i => f <| g i).prod = f (s.map g).prod := by
  convert (s.map g).prod_hom f
  exact (map_map _ _ _).symm

@[to_additive]
theorem prod_hom₂_ne_zero [CommMonoid O] {s : Multiset ι} (hs : s ≠ 0) (f : M → N → O)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (f₁ : ι → M) (f₂ : ι → N) :
    (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod := by
  induction s using Quotient.inductionOn; aesop (add simp List.prod_hom₂_nonempty)

@[to_additive]
theorem prod_hom₂ [CommMonoid O] (s : Multiset ι) (f : M → N → O)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 1) (f₁ : ι → M)
    (f₂ : ι → N) : (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod :=
  Quotient.inductionOn s fun l => by
    simp only [l.prod_hom₂ f hf hf', quot_mk_to_coe, map_coe, prod_coe]

@[to_additive (attr := simp)]
theorem prod_map_mul : (m.map fun i => f i * g i).prod = (m.map f).prod * (m.map g).prod :=
  m.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _

@[to_additive]
theorem prod_map_pow {n : ℕ} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n :=
  m.prod_hom' (powMonoidHom n : M →* M) f

@[to_additive]
theorem prod_map_prod_map (m : Multiset ι) (n : Multiset κ) {f : ι → κ → M} :
    prod (m.map fun a => prod <| n.map fun b => f a b) =
      prod (n.map fun b => prod <| m.map fun a => f a b) :=
  Multiset.induction_on m (by simp) fun a m ih => by simp [ih]

theorem prod_dvd_prod_of_le (h : s ≤ t) : s.prod ∣ t.prod := by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  simp only [prod_add, dvd_mul_right]

@[to_additive]
lemma _root_.map_multiset_prod [FunLike F M N] [MonoidHomClass F M N] (f : F) (s : Multiset M) :
    f s.prod = (s.map f).prod := (s.prod_hom f).symm

@[to_additive]
lemma _root_.map_multiset_ne_zero_prod [FunLike F M N] [MulHomClass F M N] (f : F)
    {s : Multiset M} (hs : s ≠ 0) :
    f s.prod = (s.map f).prod := (s.prod_hom_ne_zero hs f).symm

@[to_additive]
protected lemma _root_.MonoidHom.map_multiset_prod (f : M →* N) (s : Multiset M) :
    f s.prod = (s.map f).prod := (s.prod_hom f).symm

@[to_additive]
protected lemma _root_.MulHom.map_multiset_ne_zero_prod (f : M →ₙ* N) (s : Multiset M)
    (hs : s ≠ 0) : f s.prod = (s.map f).prod := (s.prod_hom_ne_zero hs f).symm

lemma dvd_prod : a ∈ s → a ∣ s.prod :=
  Quotient.inductionOn s (fun l a h ↦ by simpa using List.dvd_prod h) a

@[to_additive] lemma fst_prod (s : Multiset (M × N)) : s.prod.1 = (s.map Prod.fst).prod :=
  map_multiset_prod (MonoidHom.fst _ _) _

@[to_additive] lemma snd_prod (s : Multiset (M × N)) : s.prod.2 = (s.map Prod.snd).prod :=
  map_multiset_prod (MonoidHom.snd _ _) _

end CommMonoid

theorem prod_dvd_prod_of_dvd [CommMonoid N] {S : Multiset M} (g1 g2 : M → N)
    (h : ∀ a ∈ S, g1 a ∣ g2 a) : (Multiset.map g1 S).prod ∣ (Multiset.map g2 S).prod := by
  apply Multiset.induction_on' S
  · simp
  intro a T haS _ IH
  simp [mul_dvd_mul (h a haS) IH]

section AddCommMonoid

variable [AddCommMonoid M]

/-- `Multiset.sum`, the sum of the elements of a multiset, promoted to a morphism of
`AddCommMonoid`s. -/
def sumAddMonoidHom : Multiset M →+ M where
  toFun := sum
  map_zero' := sum_zero
  map_add' := sum_add

@[simp]
theorem coe_sumAddMonoidHom : (sumAddMonoidHom : Multiset M → M) = sum :=
  rfl

end AddCommMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid G] {m : Multiset ι} {f g : ι → G}

@[to_additive]
theorem prod_map_inv' (m : Multiset G) : (m.map Inv.inv).prod = m.prod⁻¹ :=
  m.prod_hom (invMonoidHom : G →* G)

@[to_additive (attr := simp)]
theorem prod_map_inv : (m.map fun i => (f i)⁻¹).prod = (m.map f).prod⁻¹ := by
  rw [← (m.map f).prod_map_inv', map_map, Function.comp_def]

@[to_additive (attr := simp)]
theorem prod_map_div : (m.map fun i => f i / g i).prod = (m.map f).prod / (m.map g).prod :=
  m.prod_hom₂ (· / ·) mul_div_mul_comm (div_one _) _ _

@[to_additive]
theorem prod_map_zpow {n : ℤ} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n := by
  convert (m.map f).prod_hom (zpowGroupHom n : G →* G)
  simp only [map_map, Function.comp_apply, zpowGroupHom_apply]

end DivisionCommMonoid

@[simp]
theorem sum_map_singleton (s : Multiset M) : (s.map fun a => ({a} : Multiset M)).sum = s :=
  Multiset.induction_on s (by simp) (by simp)

theorem sum_nat_mod (s : Multiset ℕ) (n : ℕ) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction <;> simp [Nat.add_mod, *]

theorem prod_nat_mod (s : Multiset ℕ) (n : ℕ) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Nat.mul_mod, *]

theorem sum_int_mod (s : Multiset ℤ) (n : ℤ) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction <;> simp [Int.add_emod, *]

theorem prod_int_mod (s : Multiset ℤ) (n : ℤ) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Int.mul_emod, *]

section OrderedSub

theorem sum_map_tsub [AddCommMonoid M] [PartialOrder M] [ExistsAddOfLE M]
    [AddLeftMono M] [AddLeftReflectLE M] [Sub M]
    [OrderedSub M] (l : Multiset ι) {f g : ι → M} (hfg : ∀ x ∈ l, g x ≤ f x) :
    (l.map fun x ↦ f x - g x).sum = (l.map f).sum - (l.map g).sum :=
  eq_tsub_of_add_eq <| by
    rw [← sum_map_add]
    congr 1
    exact map_congr rfl fun x hx => tsub_add_cancel_of_le <| hfg _ hx

end OrderedSub

end Multiset
