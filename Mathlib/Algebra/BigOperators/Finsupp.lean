/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Data.Finsupp.Fin
import Mathlib.Data.Finsupp.Indicator

#align_import algebra.big_operators.finsupp from "leanprover-community/mathlib"@"842328d9df7e96fd90fc424e115679c15fb23a71"

/-!
# Big operators for finsupps

This file contains theorems relevant to big operators in finitely supported functions.
-/


noncomputable section

open Finset Function

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]
variable {t : ι → A → C} (h0 : ∀ i, t i 0 = 0) (h1 : ∀ i x y, t i (x + y) = t i x + t i y)
variable {s : Finset α} {f : α → ι →₀ A} (i : ι)
variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)
variable {β M M' N P G H R S : Type*}

namespace Finsupp

/-!
### Declarations about `Finsupp.sum` and `Finsupp.prod`

In most of this section, the domain `β` is assumed to be an `AddMonoid`.
-/


section SumProd

/-- `prod f g` is the product of `g a (f a)` over the support of `f`. -/
@[to_additive "`sum f g` is the sum of `g a (f a)` over the support of `f`. "]
def prod [Zero M] [CommMonoid N] (f : α →₀ M) (g : α → M → N) : N :=
  ∏ a ∈ f.support, g a (f a)
#align finsupp.prod Finsupp.prod
#align finsupp.sum Finsupp.sum

variable [Zero M] [Zero M'] [CommMonoid N]

@[to_additive]
theorem prod_of_support_subset (f : α →₀ M) {s : Finset α} (hs : f.support ⊆ s) (g : α → M → N)
    (h : ∀ i ∈ s, g i 0 = 1) : f.prod g = ∏ x ∈ s, g x (f x) := by
  refine Finset.prod_subset hs fun x hxs hx => h x hxs ▸ (congr_arg (g x) ?_)
  exact not_mem_support_iff.1 hx
#align finsupp.prod_of_support_subset Finsupp.prod_of_support_subset
#align finsupp.sum_of_support_subset Finsupp.sum_of_support_subset

@[to_additive]
theorem prod_fintype [Fintype α] (f : α →₀ M) (g : α → M → N) (h : ∀ i, g i 0 = 1) :
    f.prod g = ∏ i, g i (f i) :=
  f.prod_of_support_subset (subset_univ _) g fun x _ => h x
#align finsupp.prod_fintype Finsupp.prod_fintype
#align finsupp.sum_fintype Finsupp.sum_fintype

@[to_additive (attr := simp)]
theorem prod_single_index {a : α} {b : M} {h : α → M → N} (h_zero : h a 0 = 1) :
    (single a b).prod h = h a b :=
  calc
    (single a b).prod h = ∏ x ∈ {a}, h x (single a b x) :=
      prod_of_support_subset _ support_single_subset h fun x hx =>
        (mem_singleton.1 hx).symm ▸ h_zero
    _ = h a b := by simp
#align finsupp.prod_single_index Finsupp.prod_single_index
#align finsupp.sum_single_index Finsupp.sum_single_index

@[to_additive]
theorem prod_mapRange_index {f : M → M'} {hf : f 0 = 0} {g : α →₀ M} {h : α → M' → N}
    (h0 : ∀ a, h a 0 = 1) : (mapRange f hf g).prod h = g.prod fun a b => h a (f b) :=
  Finset.prod_subset support_mapRange fun _ _ H => by rw [not_mem_support_iff.1 H, h0]
#align finsupp.prod_map_range_index Finsupp.prod_mapRange_index
#align finsupp.sum_map_range_index Finsupp.sum_mapRange_index

@[to_additive (attr := simp)]
theorem prod_zero_index {h : α → M → N} : (0 : α →₀ M).prod h = 1 :=
  rfl
#align finsupp.prod_zero_index Finsupp.prod_zero_index
#align finsupp.sum_zero_index Finsupp.sum_zero_index

@[to_additive]
theorem prod_comm (f : α →₀ M) (g : β →₀ M') (h : α → M → β → M' → N) :
    (f.prod fun x v => g.prod fun x' v' => h x v x' v') =
      g.prod fun x' v' => f.prod fun x v => h x v x' v' :=
  Finset.prod_comm
#align finsupp.prod_comm Finsupp.prod_comm
#align finsupp.sum_comm Finsupp.sum_comm

@[to_additive (attr := simp)]
theorem prod_ite_eq [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
    (f.prod fun x v => ite (a = x) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 := by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq]
#align finsupp.prod_ite_eq Finsupp.prod_ite_eq
#align finsupp.sum_ite_eq Finsupp.sum_ite_eq

/- Porting note: simpnf linter, added aux lemma below
Left-hand side simplifies from
  Finsupp.sum f fun x v => if a = x then v else 0
to
  if ↑f a = 0 then 0 else ↑f a
-/
-- @[simp]
theorem sum_ite_self_eq [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α →₀ N) (a : α) :
    (f.sum fun x v => ite (a = x) v 0) = f a := by
  classical
    convert f.sum_ite_eq a fun _ => id
    simp [ite_eq_right_iff.2 Eq.symm]
#align finsupp.sum_ite_self_eq Finsupp.sum_ite_self_eq

-- Porting note: Added this thm to replace the simp in the previous one. Need to add [DecidableEq N]
@[simp]
theorem sum_ite_self_eq_aux [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α →₀ N) (a : α) :
    (if a ∈ f.support then f a else 0) = f a := by
  simp only [mem_support_iff, ne_eq, ite_eq_left_iff, not_not]
  exact fun h ↦ h.symm

/-- A restatement of `prod_ite_eq` with the equality test reversed. -/
@[to_additive (attr := simp) "A restatement of `sum_ite_eq` with the equality test reversed."]
theorem prod_ite_eq' [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
    (f.prod fun x v => ite (x = a) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 := by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq']
#align finsupp.prod_ite_eq' Finsupp.prod_ite_eq'
#align finsupp.sum_ite_eq' Finsupp.sum_ite_eq'

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem sum_ite_self_eq' [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α →₀ N) (a : α) :
    (f.sum fun x v => ite (x = a) v 0) = f a := by
  classical
    convert f.sum_ite_eq' a fun _ => id
    simp [ite_eq_right_iff.2 Eq.symm]
#align finsupp.sum_ite_self_eq' Finsupp.sum_ite_self_eq'

@[simp]
theorem prod_pow [Fintype α] (f : α →₀ ℕ) (g : α → N) :
    (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a :=
  f.prod_fintype _ fun _ ↦ pow_zero _
#align finsupp.prod_pow Finsupp.prod_pow

/-- If `g` maps a second argument of 0 to 1, then multiplying it over the
result of `onFinset` is the same as multiplying it over the original `Finset`. -/
@[to_additive
      "If `g` maps a second argument of 0 to 0, summing it over the
      result of `onFinset` is the same as summing it over the original `Finset`."]
theorem onFinset_prod {s : Finset α} {f : α → M} {g : α → M → N} (hf : ∀ a, f a ≠ 0 → a ∈ s)
    (hg : ∀ a, g a 0 = 1) : (onFinset s f hf).prod g = ∏ a ∈ s, g a (f a) :=
  Finset.prod_subset support_onFinset_subset <| by simp (config := { contextual := true }) [*]
#align finsupp.on_finset_prod Finsupp.onFinset_prod
#align finsupp.on_finset_sum Finsupp.onFinset_sum

/-- Taking a product over `f : α →₀ M` is the same as multiplying the value on a single element
`y ∈ f.support` by the product over `erase y f`. -/
@[to_additive
      " Taking a sum over `f : α →₀ M` is the same as adding the value on a
      single element `y ∈ f.support` to the sum over `erase y f`. "]
theorem mul_prod_erase (f : α →₀ M) (y : α) (g : α → M → N) (hyf : y ∈ f.support) :
    g y (f y) * (erase y f).prod g = f.prod g := by
  classical
    rw [Finsupp.prod, Finsupp.prod, ← Finset.mul_prod_erase _ _ hyf, Finsupp.support_erase,
      Finset.prod_congr rfl]
    intro h hx
    rw [Finsupp.erase_ne (ne_of_mem_erase hx)]
#align finsupp.mul_prod_erase Finsupp.mul_prod_erase
#align finsupp.add_sum_erase Finsupp.add_sum_erase

/-- Generalization of `Finsupp.mul_prod_erase`: if `g` maps a second argument of 0 to 1,
then its product over `f : α →₀ M` is the same as multiplying the value on any element
`y : α` by the product over `erase y f`. -/
@[to_additive
      " Generalization of `Finsupp.add_sum_erase`: if `g` maps a second argument of 0
      to 0, then its sum over `f : α →₀ M` is the same as adding the value on any element
      `y : α` to the sum over `erase y f`. "]
theorem mul_prod_erase' (f : α →₀ M) (y : α) (g : α → M → N) (hg : ∀ i : α, g i 0 = 1) :
    g y (f y) * (erase y f).prod g = f.prod g := by
  classical
    by_cases hyf : y ∈ f.support
    · exact Finsupp.mul_prod_erase f y g hyf
    · rw [not_mem_support_iff.mp hyf, hg y, erase_of_not_mem_support hyf, one_mul]
#align finsupp.mul_prod_erase' Finsupp.mul_prod_erase'
#align finsupp.add_sum_erase' Finsupp.add_sum_erase'

@[to_additive]
theorem _root_.SubmonoidClass.finsupp_prod_mem {S : Type*} [SetLike S N] [SubmonoidClass S N]
    (s : S) (f : α →₀ M) (g : α → M → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : f.prod g ∈ s :=
  prod_mem fun _i hi => h _ (Finsupp.mem_support_iff.mp hi)
#align submonoid_class.finsupp_prod_mem SubmonoidClass.finsupp_prod_mem
#align add_submonoid_class.finsupp_sum_mem AddSubmonoidClass.finsupp_sum_mem

@[to_additive]
theorem prod_congr {f : α →₀ M} {g1 g2 : α → M → N} (h : ∀ x ∈ f.support, g1 x (f x) = g2 x (f x)) :
    f.prod g1 = f.prod g2 :=
  Finset.prod_congr rfl h
#align finsupp.prod_congr Finsupp.prod_congr
#align finsupp.sum_congr Finsupp.sum_congr

@[to_additive]
theorem prod_eq_single {f : α →₀ M} (a : α) {g : α → M → N}
    (h₀ : ∀ b, f b ≠ 0 → b ≠ a → g b (f b) = 1) (h₁ : f a = 0 → g a 0 = 1) :
    f.prod g = g a (f a) := by
  refine Finset.prod_eq_single a (fun b hb₁ hb₂ => ?_) (fun h => ?_)
  · exact h₀ b (mem_support_iff.mp hb₁) hb₂
  · simp only [not_mem_support_iff] at h
    rw [h]
    exact h₁ h

end SumProd

section CommMonoidWithZero
variable [Zero α] [CommMonoidWithZero β] [Nontrivial β] [NoZeroDivisors β]
  {f : ι →₀ α} (a : α) {g : ι → α → β}

@[simp]
lemma prod_eq_zero_iff : f.prod g = 0 ↔ ∃ i ∈ f.support, g i (f i) = 0 := Finset.prod_eq_zero_iff
lemma prod_ne_zero_iff : f.prod g ≠ 0 ↔ ∀ i ∈ f.support, g i (f i) ≠ 0 := Finset.prod_ne_zero_iff

end CommMonoidWithZero
end Finsupp

@[to_additive]
theorem map_finsupp_prod [Zero M] [CommMonoid N] [CommMonoid P] {H : Type*}
    [FunLike H N P] [MonoidHomClass H N P]
    (h : H) (f : α →₀ M) (g : α → M → N) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  map_prod h _ _
#align map_finsupp_prod map_finsupp_prod
#align map_finsupp_sum map_finsupp_sum

#align mul_equiv.map_finsupp_prod map_finsupp_prod
#align add_equiv.map_finsupp_sum map_finsupp_sum
#align monoid_hom.map_finsupp_prod map_finsupp_prod
#align add_monoid_hom.map_finsupp_sum map_finsupp_sum
#align ring_hom.map_finsupp_sum map_finsupp_sum
#align ring_hom.map_finsupp_prod map_finsupp_prod

-- Porting note: inserted ⇑ on the rhs
@[to_additive]
theorem MonoidHom.coe_finsupp_prod [Zero β] [Monoid N] [CommMonoid P] (f : α →₀ β)
    (g : α → β → N →* P) : ⇑(f.prod g) = f.prod fun i fi => ⇑(g i fi) :=
  MonoidHom.coe_finset_prod _ _
#align monoid_hom.coe_finsupp_prod MonoidHom.coe_finsupp_prod
#align add_monoid_hom.coe_finsupp_sum AddMonoidHom.coe_finsupp_sum

@[to_additive (attr := simp)]
theorem MonoidHom.finsupp_prod_apply [Zero β] [Monoid N] [CommMonoid P] (f : α →₀ β)
    (g : α → β → N →* P) (x : N) : f.prod g x = f.prod fun i fi => g i fi x :=
  MonoidHom.finset_prod_apply _ _ _
#align monoid_hom.finsupp_prod_apply MonoidHom.finsupp_prod_apply
#align add_monoid_hom.finsupp_sum_apply AddMonoidHom.finsupp_sum_apply

namespace Finsupp

theorem single_multiset_sum [AddCommMonoid M] (s : Multiset M) (a : α) :
    single a s.sum = (s.map (single a)).sum :=
  Multiset.induction_on s (single_zero _) fun a s ih => by
    rw [Multiset.sum_cons, single_add, ih, Multiset.map_cons, Multiset.sum_cons]
#align finsupp.single_multiset_sum Finsupp.single_multiset_sum

theorem single_finset_sum [AddCommMonoid M] (s : Finset ι) (f : ι → M) (a : α) :
    single a (∑ b ∈ s, f b) = ∑ b ∈ s, single a (f b) := by
  trans
  · apply single_multiset_sum
  · rw [Multiset.map_map]
    rfl
#align finsupp.single_finset_sum Finsupp.single_finset_sum

theorem single_sum [Zero M] [AddCommMonoid N] (s : ι →₀ M) (f : ι → M → N) (a : α) :
    single a (s.sum f) = s.sum fun d c => single a (f d c) :=
  single_finset_sum _ _ _
#align finsupp.single_sum Finsupp.single_sum

@[to_additive]
theorem prod_neg_index [AddGroup G] [CommMonoid M] {g : α →₀ G} {h : α → G → M}
    (h0 : ∀ a, h a 0 = 1) : (-g).prod h = g.prod fun a b => h a (-b) :=
  prod_mapRange_index h0
#align finsupp.prod_neg_index Finsupp.prod_neg_index
#align finsupp.sum_neg_index Finsupp.sum_neg_index

end Finsupp

namespace Finsupp

theorem finset_sum_apply [AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N) (a : α) :
    (∑ i ∈ S, f i) a = ∑ i ∈ S, f i a :=
  map_sum (applyAddHom a) _ _
#align finsupp.finset_sum_apply Finsupp.finset_sum_apply

@[simp]
theorem sum_apply [Zero M] [AddCommMonoid N] {f : α →₀ M} {g : α → M → β →₀ N} {a₂ : β} :
    (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂ :=
  finset_sum_apply _ _ _
#align finsupp.sum_apply Finsupp.sum_apply

-- Porting note: inserted ⇑ on the rhs
theorem coe_finset_sum [AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N) :
    ⇑(∑ i ∈ S, f i) = ∑ i ∈ S, ⇑(f i) :=
  map_sum (coeFnAddHom : (α →₀ N) →+ _) _ _
#align finsupp.coe_finset_sum Finsupp.coe_finset_sum

-- Porting note: inserted ⇑ on the rhs
theorem coe_sum [Zero M] [AddCommMonoid N] (f : α →₀ M) (g : α → M → β →₀ N) :
    ⇑(f.sum g) = f.sum fun a₁ b => ⇑(g a₁ b) :=
  coe_finset_sum _ _
#align finsupp.coe_sum Finsupp.coe_sum

theorem support_sum [DecidableEq β] [Zero M] [AddCommMonoid N] {f : α →₀ M} {g : α → M → β →₀ N} :
    (f.sum g).support ⊆ f.support.biUnion fun a => (g a (f a)).support := by
  have : ∀ c, (f.sum fun a b => g a b c) ≠ 0 → ∃ a, f a ≠ 0 ∧ ¬(g a (f a)) c = 0 := fun a₁ h =>
    let ⟨a, ha, ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨a, mem_support_iff.mp ha, ne⟩
  simpa only [Finset.subset_iff, mem_support_iff, Finset.mem_biUnion, sum_apply, exists_prop]
#align finsupp.support_sum Finsupp.support_sum

theorem support_finset_sum [DecidableEq β] [AddCommMonoid M] {s : Finset α} {f : α → β →₀ M} :
    (Finset.sum s f).support ⊆ s.biUnion fun x => (f x).support := by
  rw [← Finset.sup_eq_biUnion]
  induction' s using Finset.cons_induction_on with a s ha ih
  · rfl
  · rw [Finset.sum_cons, Finset.sup_cons]
    exact support_add.trans (Finset.union_subset_union (Finset.Subset.refl _) ih)
#align finsupp.support_finset_sum Finsupp.support_finset_sum

@[simp]
theorem sum_zero [Zero M] [AddCommMonoid N] {f : α →₀ M} : (f.sum fun _ _ => (0 : N)) = 0 :=
  Finset.sum_const_zero
#align finsupp.sum_zero Finsupp.sum_zero

@[to_additive (attr := simp)]
theorem prod_mul [Zero M] [CommMonoid N] {f : α →₀ M} {h₁ h₂ : α → M → N} :
    (f.prod fun a b => h₁ a b * h₂ a b) = f.prod h₁ * f.prod h₂ :=
  Finset.prod_mul_distrib
#align finsupp.prod_mul Finsupp.prod_mul
#align finsupp.sum_add Finsupp.sum_add

@[to_additive (attr := simp)]
theorem prod_inv [Zero M] [CommGroup G] {f : α →₀ M} {h : α → M → G} :
    (f.prod fun a b => (h a b)⁻¹) = (f.prod h)⁻¹ :=
  (map_prod (MonoidHom.id G)⁻¹ _ _).symm
#align finsupp.prod_inv Finsupp.prod_inv
#align finsupp.sum_neg Finsupp.sum_neg

@[simp]
theorem sum_sub [Zero M] [AddCommGroup G] {f : α →₀ M} {h₁ h₂ : α → M → G} :
    (f.sum fun a b => h₁ a b - h₂ a b) = f.sum h₁ - f.sum h₂ :=
  Finset.sum_sub_distrib
#align finsupp.sum_sub Finsupp.sum_sub

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism on the support.
This is a more general version of `Finsupp.prod_add_index'`; the latter has simpler hypotheses. -/
@[to_additive
      "Taking the product under `h` is an additive homomorphism of finsupps,  if `h` is an
      additive homomorphism on the support. This is a more general version of
      `Finsupp.sum_add_index'`; the latter has simpler hypotheses."]
theorem prod_add_index [DecidableEq α] [AddZeroClass M] [CommMonoid N] {f g : α →₀ M}
    {h : α → M → N} (h_zero : ∀ a ∈ f.support ∪ g.support, h a 0 = 1)
    (h_add : ∀ a ∈ f.support ∪ g.support, ∀ (b₁ b₂), h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).prod h = f.prod h * g.prod h := by
  rw [Finsupp.prod_of_support_subset f subset_union_left h h_zero,
    Finsupp.prod_of_support_subset g subset_union_right h h_zero, ←
    Finset.prod_mul_distrib, Finsupp.prod_of_support_subset (f + g) Finsupp.support_add h h_zero]
  exact Finset.prod_congr rfl fun x hx => by apply h_add x hx
#align finsupp.prod_add_index Finsupp.prod_add_index
#align finsupp.sum_add_index Finsupp.sum_add_index

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism.
This is a more specialized version of `Finsupp.prod_add_index` with simpler hypotheses. -/
@[to_additive
      "Taking the sum under `h` is an additive homomorphism of finsupps,if `h` is an additive
      homomorphism. This is a more specific version of `Finsupp.sum_add_index` with simpler
      hypotheses."]
theorem prod_add_index' [AddZeroClass M] [CommMonoid N] {f g : α →₀ M} {h : α → M → N}
    (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).prod h = f.prod h * g.prod h := by
  classical exact prod_add_index (fun a _ => h_zero a) fun a _ => h_add a
#align finsupp.prod_add_index' Finsupp.prod_add_index'
#align finsupp.sum_add_index' Finsupp.sum_add_index'

@[simp]
theorem sum_hom_add_index [AddZeroClass M] [AddCommMonoid N] {f g : α →₀ M} (h : α → M →+ N) :
    ((f + g).sum fun x => h x) = (f.sum fun x => h x) + g.sum fun x => h x :=
  sum_add_index' (fun a => (h a).map_zero) fun a => (h a).map_add
#align finsupp.sum_hom_add_index Finsupp.sum_hom_add_index

@[simp]
theorem prod_hom_add_index [AddZeroClass M] [CommMonoid N] {f g : α →₀ M}
    (h : α → Multiplicative M →* N) :
    ((f + g).prod fun a b => h a (Multiplicative.ofAdd b)) =
      (f.prod fun a b => h a (Multiplicative.ofAdd b)) *
        g.prod fun a b => h a (Multiplicative.ofAdd b) :=
  prod_add_index' (fun a => (h a).map_one) fun a => (h a).map_mul
#align finsupp.prod_hom_add_index Finsupp.prod_hom_add_index

/-- The canonical isomorphism between families of additive monoid homomorphisms `α → (M →+ N)`
and monoid homomorphisms `(α →₀ M) →+ N`. -/
def liftAddHom [AddZeroClass M] [AddCommMonoid N] : (α → M →+ N) ≃+ ((α →₀ M) →+ N) where
  toFun F :=
    { toFun := fun f ↦ f.sum fun x ↦ F x
      map_zero' := Finset.sum_empty
      map_add' := fun _ _ => sum_add_index' (fun x => (F x).map_zero) fun x => (F x).map_add }
  invFun F x := F.comp (singleAddHom x)
  left_inv F := by
    ext
    simp [singleAddHom]
  right_inv F := by
  -- Porting note: This was `ext` and used the wrong lemma
    apply Finsupp.addHom_ext'
    simp [singleAddHom, AddMonoidHom.comp, Function.comp]
  map_add' F G := by
    ext x
    exact sum_add
#align finsupp.lift_add_hom Finsupp.liftAddHom

@[simp]
theorem liftAddHom_apply [AddCommMonoid M] [AddCommMonoid N] (F : α → M →+ N) (f : α →₀ M) :
    (liftAddHom (α := α) (M := M) (N := N)) F f = f.sum fun x => F x :=
  rfl
#align finsupp.lift_add_hom_apply Finsupp.liftAddHom_apply

@[simp]
theorem liftAddHom_symm_apply [AddCommMonoid M] [AddCommMonoid N] (F : (α →₀ M) →+ N) (x : α) :
    (liftAddHom (α := α) (M := M) (N := N)).symm F x = F.comp (singleAddHom x) :=
  rfl
#align finsupp.lift_add_hom_symm_apply Finsupp.liftAddHom_symm_apply

theorem liftAddHom_symm_apply_apply [AddCommMonoid M] [AddCommMonoid N] (F : (α →₀ M) →+ N) (x : α)
    (y : M) : (liftAddHom (α := α) (M := M) (N := N)).symm F x y = F (single x y) :=
  rfl
#align finsupp.lift_add_hom_symm_apply_apply Finsupp.liftAddHom_symm_apply_apply

@[simp]
theorem liftAddHom_singleAddHom [AddCommMonoid M] :
    (liftAddHom (α := α) (M := M) (N := α →₀ M)) (singleAddHom : α → M →+ α →₀ M) =
      AddMonoidHom.id _ :=
  liftAddHom.toEquiv.apply_eq_iff_eq_symm_apply.2 rfl
#align finsupp.lift_add_hom_single_add_hom Finsupp.liftAddHom_singleAddHom

@[simp]
theorem sum_single [AddCommMonoid M] (f : α →₀ M) : f.sum single = f :=
  DFunLike.congr_fun liftAddHom_singleAddHom f
#align finsupp.sum_single Finsupp.sum_single

/-- The `Finsupp` version of `Finset.univ_sum_single` -/
@[simp]
theorem univ_sum_single [Fintype α] [AddCommMonoid M] (f : α →₀ M) :
    ∑ a : α, single a (f a) = f := by
  classical
  refine DFunLike.coe_injective ?_
  simp_rw [coe_finset_sum, single_eq_pi_single, Finset.univ_sum_single]

@[simp]
theorem univ_sum_single_apply [AddCommMonoid M] [Fintype α] (i : α) (m : M) :
    ∑ j : α, single i m j = m := by
  -- Porting note: rewrite due to leaky classical in lean3
  classical rw [single, coe_mk, Finset.sum_pi_single']
  simp
#align finsupp.sum_univ_single Finsupp.univ_sum_single_apply

@[simp]
theorem univ_sum_single_apply' [AddCommMonoid M] [Fintype α] (i : α) (m : M) :
    ∑ j : α, single j m i = m := by
  -- Porting note: rewrite due to leaky classical in lean3
  simp_rw [single, coe_mk]
  classical rw [Finset.sum_pi_single]
  simp
#align finsupp.sum_univ_single' Finsupp.univ_sum_single_apply'


theorem equivFunOnFinite_symm_eq_sum [Fintype α] [AddCommMonoid M] (f : α → M) :
    equivFunOnFinite.symm f = ∑ a, Finsupp.single a (f a) := by
  rw [← univ_sum_single (equivFunOnFinite.symm f)]
  ext
  simp

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem liftAddHom_apply_single [AddCommMonoid M] [AddCommMonoid N] (f : α → M →+ N) (a : α)
    (b : M) : (liftAddHom (α := α) (M := M) (N := N)) f (single a b) = f a b :=
  sum_single_index (f a).map_zero
#align finsupp.lift_add_hom_apply_single Finsupp.liftAddHom_apply_single

@[simp]
theorem liftAddHom_comp_single [AddCommMonoid M] [AddCommMonoid N] (f : α → M →+ N) (a : α) :
    ((liftAddHom (α := α) (M := M) (N := N)) f).comp (singleAddHom a) = f a :=
  AddMonoidHom.ext fun b => liftAddHom_apply_single f a b
#align finsupp.lift_add_hom_comp_single Finsupp.liftAddHom_comp_single

theorem comp_liftAddHom [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] (g : N →+ P)
    (f : α → M →+ N) :
    g.comp ((liftAddHom (α := α) (M := M) (N := N)) f) =
      (liftAddHom (α := α) (M := M) (N := P)) fun a => g.comp (f a) :=
  liftAddHom.symm_apply_eq.1 <|
    funext fun a => by
      rw [liftAddHom_symm_apply, AddMonoidHom.comp_assoc, liftAddHom_comp_single]
#align finsupp.comp_lift_add_hom Finsupp.comp_liftAddHom

theorem sum_sub_index [AddCommGroup β] [AddCommGroup γ] {f g : α →₀ β} {h : α → β → γ}
    (h_sub : ∀ a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) : (f - g).sum h = f.sum h - g.sum h :=
  ((liftAddHom (α := α) (M := β) (N := γ)) fun a =>
    AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g
#align finsupp.sum_sub_index Finsupp.sum_sub_index

@[to_additive]
theorem prod_embDomain [Zero M] [CommMonoid N] {v : α →₀ M} {f : α ↪ β} {g : β → M → N} :
    (v.embDomain f).prod g = v.prod fun a b => g (f a) b := by
  rw [prod, prod, support_embDomain, Finset.prod_map]
  simp_rw [embDomain_apply]
#align finsupp.prod_emb_domain Finsupp.prod_embDomain
#align finsupp.sum_emb_domain Finsupp.sum_embDomain

@[to_additive]
theorem prod_finset_sum_index [AddCommMonoid M] [CommMonoid N] {s : Finset ι} {g : ι → α →₀ M}
    {h : α → M → N} (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (∏ i ∈ s, (g i).prod h) = (∑ i ∈ s, g i).prod h :=
  Finset.cons_induction_on s rfl fun a s has ih => by
    rw [prod_cons, ih, sum_cons, prod_add_index' h_zero h_add]
#align finsupp.prod_finset_sum_index Finsupp.prod_finset_sum_index
#align finsupp.sum_finset_sum_index Finsupp.sum_finset_sum_index

@[to_additive]
theorem prod_sum_index [AddCommMonoid M] [AddCommMonoid N] [CommMonoid P] {f : α →₀ M}
    {g : α → M → β →₀ N} {h : β → N → P} (h_zero : ∀ a, h a 0 = 1)
    (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f.sum g).prod h = f.prod fun a b => (g a b).prod h :=
  (prod_finset_sum_index h_zero h_add).symm
#align finsupp.prod_sum_index Finsupp.prod_sum_index
#align finsupp.sum_sum_index Finsupp.sum_sum_index

theorem multiset_sum_sum_index [AddCommMonoid M] [AddCommMonoid N] (f : Multiset (α →₀ M))
    (h : α → M → N) (h₀ : ∀ a, h a 0 = 0)
    (h₁ : ∀ (a : α) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    f.sum.sum h = (f.map fun g : α →₀ M => g.sum h).sum :=
  Multiset.induction_on f rfl fun a s ih => by
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, sum_add_index' h₀ h₁, ih]
#align finsupp.multiset_sum_sum_index Finsupp.multiset_sum_sum_index

theorem support_sum_eq_biUnion {α : Type*} {ι : Type*} {M : Type*} [DecidableEq α]
    [AddCommMonoid M] {g : ι → α →₀ M} (s : Finset ι)
    (h : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint (g i₁).support (g i₂).support) :
    (∑ i ∈ s, g i).support = s.biUnion fun i => (g i).support := by
  classical
  -- Porting note: apply Finset.induction_on s was not working; refine does.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi
    simp only [hi, sum_insert, not_false_iff, biUnion_insert]
    intro hs
    rw [Finsupp.support_add_eq, hs]
    rw [hs, Finset.disjoint_biUnion_right]
    intro j hj
    exact h _ _ (ne_of_mem_of_not_mem hj hi).symm
#align finsupp.support_sum_eq_bUnion Finsupp.support_sum_eq_biUnion

theorem multiset_map_sum [Zero M] {f : α →₀ M} {m : β → γ} {h : α → M → Multiset β} :
    Multiset.map m (f.sum h) = f.sum fun a b => (h a b).map m :=
  map_sum (Multiset.mapAddMonoidHom m) _ f.support
#align finsupp.multiset_map_sum Finsupp.multiset_map_sum

theorem multiset_sum_sum [Zero M] [AddCommMonoid N] {f : α →₀ M} {h : α → M → Multiset N} :
    Multiset.sum (f.sum h) = f.sum fun a b => Multiset.sum (h a b) :=
  map_sum Multiset.sumAddMonoidHom _ f.support
#align finsupp.multiset_sum_sum Finsupp.multiset_sum_sum

/-- For disjoint `f1` and `f2`, and function `g`, the product of the products of `g`
over `f1` and `f2` equals the product of `g` over `f1 + f2` -/
@[to_additive
      "For disjoint `f1` and `f2`, and function `g`, the sum of the sums of `g`
      over `f1` and `f2` equals the sum of `g` over `f1 + f2`"]
theorem prod_add_index_of_disjoint [AddCommMonoid M] {f1 f2 : α →₀ M}
    (hd : Disjoint f1.support f2.support) {β : Type*} [CommMonoid β] (g : α → M → β) :
    (f1 + f2).prod g = f1.prod g * f2.prod g := by
  have :
    ∀ {f1 f2 : α →₀ M},
      Disjoint f1.support f2.support → (∏ x ∈ f1.support, g x (f1 x + f2 x)) = f1.prod g :=
    fun hd =>
    Finset.prod_congr rfl fun x hx => by
      simp only [not_mem_support_iff.mp (disjoint_left.mp hd hx), add_zero]
  classical simp_rw [← this hd, ← this hd.symm, add_comm (f2 _), Finsupp.prod, support_add_eq hd,
      prod_union hd, add_apply]
#align finsupp.prod_add_index_of_disjoint Finsupp.prod_add_index_of_disjoint
#align finsupp.sum_add_index_of_disjoint Finsupp.sum_add_index_of_disjoint

theorem prod_dvd_prod_of_subset_of_dvd [AddCommMonoid M] [CommMonoid N] {f1 f2 : α →₀ M}
    {g1 g2 : α → M → N} (h1 : f1.support ⊆ f2.support)
    (h2 : ∀ a : α, a ∈ f1.support → g1 a (f1 a) ∣ g2 a (f2 a)) : f1.prod g1 ∣ f2.prod g2 := by
  classical
    simp only [Finsupp.prod, Finsupp.prod_mul]
    rw [← sdiff_union_of_subset h1, prod_union sdiff_disjoint]
    apply dvd_mul_of_dvd_right
    apply prod_dvd_prod_of_dvd
    exact h2
#align finsupp.prod_dvd_prod_of_subset_of_dvd Finsupp.prod_dvd_prod_of_subset_of_dvd

lemma indicator_eq_sum_attach_single [AddCommMonoid M] {s : Finset α} (f : ∀ a ∈ s, M) :
    indicator s f = ∑ x ∈ s.attach, single ↑x (f x x.2) := by
  rw [← sum_single (indicator s f), sum, sum_subset (support_indicator_subset _ _), ← sum_attach]
  · refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [indicator_of_mem]
  · intro i _ hi
    rw [not_mem_support_iff.mp hi, single_zero]
#align finsupp.indicator_eq_sum_single Finsupp.indicator_eq_sum_attach_single

lemma indicator_eq_sum_single [AddCommMonoid M] (s : Finset α) (f : α → M) :
    indicator s (fun x _ ↦ f x) = ∑ x ∈ s, single x (f x) :=
  (indicator_eq_sum_attach_single _).trans <| sum_attach _ fun x ↦ single x (f x)

@[to_additive (attr := simp)]
lemma prod_indicator_index_eq_prod_attach [Zero M] [CommMonoid N]
    {s : Finset α} (f : ∀ a ∈ s, M) {h : α → M → N} (h_zero : ∀ a ∈ s, h a 0 = 1) :
    (indicator s f).prod h = ∏ x ∈ s.attach, h ↑x (f x x.2) := by
  rw [prod_of_support_subset _ (support_indicator_subset _ _) h h_zero, ← prod_attach]
  refine Finset.prod_congr rfl (fun _ _ => ?_)
  rw [indicator_of_mem]
#align finsupp.prod_indicator_index Finsupp.prod_indicator_index_eq_prod_attach
#align finsupp.sum_indicator_index Finsupp.sum_indicator_index_eq_sum_attach

@[to_additive (attr := simp)]
lemma prod_indicator_index [Zero M] [CommMonoid N]
    {s : Finset α} (f : α → M) {h : α → M → N} (h_zero : ∀ a ∈ s, h a 0 = 1) :
    (indicator s (fun x _ ↦ f x)).prod h = ∏ x ∈ s, h x (f x) :=
  (prod_indicator_index_eq_prod_attach _ h_zero).trans <| prod_attach _ fun x ↦ h x (f x)

lemma sum_cons [AddCommMonoid M] (n : ℕ) (σ : Fin n →₀ M) (i : M) :
    (sum (cons i σ) fun _ e ↦ e) = i + sum σ (fun _ e ↦ e) := by
  rw [sum_fintype _ _ (fun _ => rfl), sum_fintype _ _ (fun _ => rfl)]
  exact Fin.sum_cons i σ

lemma sum_cons' [AddCommMonoid M] [AddCommMonoid N] (n : ℕ) (σ : Fin n →₀ M) (i : M)
    (f : Fin (n+1) → M → N) (h : ∀ x, f x 0 = 0) :
    (sum (Finsupp.cons i σ) f) = f 0 i + sum σ (Fin.tail f) := by
  rw [sum_fintype _ _ (fun _ => by apply h), sum_fintype _ _ (fun _ => by apply h)]
  simp_rw [Fin.sum_univ_succ, cons_zero, cons_succ]
  congr

end Finsupp

theorem Finset.sum_apply' : (∑ k ∈ s, f k) i = ∑ k ∈ s, f k i :=
  map_sum (Finsupp.applyAddHom i) f s
#align finset.sum_apply' Finset.sum_apply'

theorem Finsupp.sum_apply' : g.sum k x = g.sum fun i b => k i b x :=
  Finset.sum_apply _ _ _
#align finsupp.sum_apply' Finsupp.sum_apply'

section

open scoped Classical

theorem Finsupp.sum_sum_index' : (∑ x ∈ s, f x).sum t = ∑ x ∈ s, (f x).sum t :=
  Finset.induction_on s rfl fun a s has ih => by
    simp_rw [Finset.sum_insert has, Finsupp.sum_add_index' h0 h1, ih]
#align finsupp.sum_sum_index' Finsupp.sum_sum_index'

end

section

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

theorem Finsupp.sum_mul (b : S) (s : α →₀ R) {f : α → R → S} :
    s.sum f * b = s.sum fun a c => f a c * b := by simp only [Finsupp.sum, Finset.sum_mul]
#align finsupp.sum_mul Finsupp.sum_mul

theorem Finsupp.mul_sum (b : S) (s : α →₀ R) {f : α → R → S} :
    b * s.sum f = s.sum fun a c => b * f a c := by simp only [Finsupp.sum, Finset.mul_sum]
#align finsupp.mul_sum Finsupp.mul_sum

end

namespace Nat

-- Porting note: Needed to replace pow with (· ^ ·)
/-- If `0 : ℕ` is not in the support of `f : ℕ →₀ ℕ` then `0 < ∏ x ∈ f.support, x ^ (f x)`. -/
theorem prod_pow_pos_of_zero_not_mem_support {f : ℕ →₀ ℕ} (hf : 0 ∉ f.support) :
    0 < f.prod (· ^ ·) :=
 Finset.prod_pos fun a ha => pos_iff_ne_zero.mpr (pow_ne_zero _ fun H => by subst H; exact hf ha)
#align nat.prod_pow_pos_of_zero_not_mem_support Nat.prod_pow_pos_of_zero_not_mem_support

end Nat
