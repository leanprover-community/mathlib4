/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Data.Finsupp.Ext
import Mathlib.Data.Finsupp.Indicator

/-!
# Big operators for finsupps

This file contains theorems relevant to big operators in finitely supported functions.
-/

assert_not_exists Field

noncomputable section

open Finset Function

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]
variable {t : ι → A → C}
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
@[to_additive /-- `sum f g` is the sum of `g a (f a)` over the support of `f`. -/]
def prod [Zero M] [CommMonoid N] (f : α →₀ M) (g : α → M → N) : N :=
  ∏ a ∈ f.support, g a (f a)

variable [Zero M] [Zero M'] [CommMonoid N]

@[to_additive]
theorem prod_of_support_subset (f : α →₀ M) {s : Finset α} (hs : f.support ⊆ s) (g : α → M → N)
    (h : ∀ i ∈ s, g i 0 = 1) : f.prod g = ∏ x ∈ s, g x (f x) := by
  refine Finset.prod_subset hs fun x hxs hx => h x hxs ▸ (congr_arg (g x) ?_)
  exact notMem_support_iff.1 hx

@[to_additive]
theorem prod_fintype [Fintype α] (f : α →₀ M) (g : α → M → N) (h : ∀ i, g i 0 = 1) :
    f.prod g = ∏ i, g i (f i) :=
  f.prod_of_support_subset (subset_univ _) g fun x _ => h x

@[to_additive (attr := simp)]
theorem prod_single_index {a : α} {b : M} {h : α → M → N} (h_zero : h a 0 = 1) :
    (single a b).prod h = h a b :=
  calc
    (single a b).prod h = ∏ x ∈ {a}, h x (single a b x) :=
      prod_of_support_subset _ support_single_subset h fun _ hx =>
        (mem_singleton.1 hx).symm ▸ h_zero
    _ = h a b := by simp

@[to_additive]
theorem prod_mapRange_index {f : M → M'} {hf : f 0 = 0} {g : α →₀ M} {h : α → M' → N}
    (h0 : ∀ a, h a 0 = 1) : (mapRange f hf g).prod h = g.prod fun a b => h a (f b) :=
  Finset.prod_subset support_mapRange fun _ _ H => by rw [notMem_support_iff.1 H, h0]

@[to_additive (attr := simp)]
theorem prod_zero_index {h : α → M → N} : (0 : α →₀ M).prod h = 1 :=
  rfl

@[to_additive]
theorem prod_comm (f : α →₀ M) (g : β →₀ M') (h : α → M → β → M' → N) :
    (f.prod fun x v => g.prod fun x' v' => h x v x' v') =
      g.prod fun x' v' => f.prod fun x v => h x v x' v' :=
  Finset.prod_comm

@[to_additive (attr := simp)]
theorem prod_ite_eq [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
    (f.prod fun x v => ite (a = x) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 := by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq]

theorem sum_ite_self_eq [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α →₀ N) (a : α) :
    (f.sum fun x v => ite (a = x) v 0) = f a := by
  simp_all

/--
The left-hand side of `sum_ite_self_eq` simplifies; this is the variant that is useful for `simp`.
-/
@[simp]
theorem if_mem_support [DecidableEq α] {N : Type*} [Zero N] (f : α →₀ N) (a : α) :
    (if a ∈ f.support then f a else 0) = f a := by
  simp only [mem_support_iff, ne_eq, ite_eq_left_iff, not_not]
  exact fun h ↦ h.symm

/-- A restatement of `prod_ite_eq` with the equality test reversed. -/
@[to_additive (attr := simp) /-- A restatement of `sum_ite_eq` with the equality test reversed. -/]
theorem prod_ite_eq' [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
    (f.prod fun x v => ite (x = a) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 := by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq']

/-- A restatement of `sum_ite_self_eq` with the equality test reversed. -/
theorem sum_ite_self_eq' [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α →₀ N) (a : α) :
    (f.sum fun x v => ite (x = a) v 0) = f a := by
  simp

@[to_additive (attr := simp)]
theorem prod_pow [Fintype α] (f : α →₀ ℕ) (g : α → N) :
    (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a :=
  f.prod_fintype _ fun _ ↦ pow_zero _

@[to_additive (attr := simp)]
theorem prod_zpow {N} [DivisionCommMonoid N] [Fintype α] (f : α →₀ ℤ) (g : α → N) :
    (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a :=
  f.prod_fintype _ fun _ ↦ zpow_zero _

/-- If `g` maps a second argument of 0 to 1, then multiplying it over the
result of `onFinset` is the same as multiplying it over the original `Finset`. -/
@[to_additive
      /-- If `g` maps a second argument of 0 to 0, summing it over the
      result of `onFinset` is the same as summing it over the original `Finset`. -/]
theorem onFinset_prod {s : Finset α} {f : α → M} {g : α → M → N} (hf : ∀ a, f a ≠ 0 → a ∈ s)
    (hg : ∀ a, g a 0 = 1) : (onFinset s f hf).prod g = ∏ a ∈ s, g a (f a) :=
  Finset.prod_subset support_onFinset_subset <| by simp +contextual [*]

/-- Taking a product over `f : α →₀ M` is the same as multiplying the value on a single element
`y ∈ f.support` by the product over `erase y f`. -/
@[to_additive
      /-- Taking a sum over `f : α →₀ M` is the same as adding the value on a
      single element `y ∈ f.support` to the sum over `erase y f`. -/]
theorem mul_prod_erase (f : α →₀ M) (y : α) (g : α → M → N) (hyf : y ∈ f.support) :
    g y (f y) * (erase y f).prod g = f.prod g := by
  classical
    rw [Finsupp.prod, Finsupp.prod, ← Finset.mul_prod_erase _ _ hyf, Finsupp.support_erase,
      Finset.prod_congr rfl]
    intro h hx
    rw [Finsupp.erase_ne (ne_of_mem_erase hx)]

/-- Generalization of `Finsupp.mul_prod_erase`: if `g` maps a second argument of 0 to 1,
then its product over `f : α →₀ M` is the same as multiplying the value on any element
`y : α` by the product over `erase y f`. -/
@[to_additive
      /-- Generalization of `Finsupp.add_sum_erase`: if `g` maps a second argument of 0
      to 0, then its sum over `f : α →₀ M` is the same as adding the value on any element
      `y : α` to the sum over `erase y f`. -/]
theorem mul_prod_erase' (f : α →₀ M) (y : α) (g : α → M → N) (hg : ∀ i : α, g i 0 = 1) :
    g y (f y) * (erase y f).prod g = f.prod g := by
  classical
    by_cases hyf : y ∈ f.support
    · exact Finsupp.mul_prod_erase f y g hyf
    · rw [notMem_support_iff.mp hyf, hg y, erase_of_notMem_support hyf, one_mul]

@[to_additive]
theorem _root_.SubmonoidClass.finsuppProd_mem {S : Type*} [SetLike S N] [SubmonoidClass S N]
    (s : S) (f : α →₀ M) (g : α → M → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : f.prod g ∈ s :=
  prod_mem fun _i hi => h _ (Finsupp.mem_support_iff.mp hi)

@[deprecated (since := "2025-04-06")]
alias _root_.SubmonoidClass.finsupp_prod_mem := _root_.SubmonoidClass.finsuppProd_mem

@[to_additive]
theorem prod_congr {f : α →₀ M} {g1 g2 : α → M → N} (h : ∀ x ∈ f.support, g1 x (f x) = g2 x (f x)) :
    f.prod g1 = f.prod g2 :=
  Finset.prod_congr rfl h

@[to_additive]
theorem prod_eq_single {f : α →₀ M} (a : α) {g : α → M → N}
    (h₀ : ∀ b, f b ≠ 0 → b ≠ a → g b (f b) = 1) (h₁ : f a = 0 → g a 0 = 1) :
    f.prod g = g a (f a) := by
  refine Finset.prod_eq_single a (fun b hb₁ hb₂ => ?_) (fun h => ?_)
  · exact h₀ b (mem_support_iff.mp hb₁) hb₂
  · simp only [notMem_support_iff] at h
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
theorem map_finsuppProd [Zero M] [CommMonoid N] [CommMonoid P] {H : Type*}
    [FunLike H N P] [MonoidHomClass H N P]
    (h : H) (f : α →₀ M) (g : α → M → N) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  map_prod h _ _

@[deprecated (since := "2025-04-06")] alias map_finsupp_prod := map_finsuppProd
@[deprecated (since := "2025-04-06")] alias map_finsupp_sum := map_finsuppSum

@[to_additive]
theorem MonoidHom.coe_finsuppProd [Zero β] [MulOneClass N] [CommMonoid P] (f : α →₀ β)
    (g : α → β → N →* P) : ⇑(f.prod g) = f.prod fun i fi => ⇑(g i fi) :=
  MonoidHom.coe_finset_prod _ _

@[deprecated (since := "2025-04-06")] alias MonoidHom.coe_finsupp_prod := MonoidHom.coe_finsuppProd
@[deprecated (since := "2025-04-06")]
alias AddMonoidHom.coe_finsupp_sum := AddMonoidHom.coe_finsuppSum

@[to_additive (attr := simp)]
theorem MonoidHom.finsuppProd_apply [Zero β] [MulOneClass N] [CommMonoid P] (f : α →₀ β)
    (g : α → β → N →* P) (x : N) : f.prod g x = f.prod fun i fi => g i fi x :=
  MonoidHom.finset_prod_apply _ _ _

@[deprecated (since := "2025-04-06")]
alias MonoidHom.finsupp_prod_apply := MonoidHom.finsuppProd_apply
@[deprecated (since := "2025-04-06")]
alias AddMonoidHom.finsupp_sum_apply := AddMonoidHom.finsuppSum_apply

namespace Finsupp

theorem single_multiset_sum [AddCommMonoid M] (s : Multiset M) (a : α) :
    single a s.sum = (s.map (single a)).sum :=
  Multiset.induction_on s (single_zero _) fun a s ih => by
    rw [Multiset.sum_cons, single_add, ih, Multiset.map_cons, Multiset.sum_cons]

theorem single_finset_sum [AddCommMonoid M] (s : Finset ι) (f : ι → M) (a : α) :
    single a (∑ b ∈ s, f b) = ∑ b ∈ s, single a (f b) := by
  trans
  · apply single_multiset_sum
  · rw [Multiset.map_map]
    rfl

theorem single_sum [Zero M] [AddCommMonoid N] (s : ι →₀ M) (f : ι → M → N) (a : α) :
    single a (s.sum f) = s.sum fun d c => single a (f d c) :=
  single_finset_sum _ _ _

@[to_additive]
theorem prod_neg_index [SubtractionMonoid G] [CommMonoid M] {g : α →₀ G} {h : α → G → M}
    (h0 : ∀ a, h a 0 = 1) : (-g).prod h = g.prod fun a b => h a (-b) :=
  prod_mapRange_index h0

end Finsupp

namespace Finsupp

theorem finset_sum_apply [AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N) (a : α) :
    (∑ i ∈ S, f i) a = ∑ i ∈ S, f i a :=
  map_sum (applyAddHom a) _ _

@[simp]
theorem sum_apply [Zero M] [AddCommMonoid N] {f : α →₀ M} {g : α → M → β →₀ N} {a₂ : β} :
    (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂ :=
  finset_sum_apply _ _ _

@[simp, norm_cast] theorem coe_finset_sum [AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N) :
    ⇑(∑ i ∈ S, f i) = ∑ i ∈ S, ⇑(f i) :=
  map_sum (coeFnAddHom : (α →₀ N) →+ _) _ _

@[simp, norm_cast] theorem coe_sum [Zero M] [AddCommMonoid N] (f : α →₀ M) (g : α → M → β →₀ N) :
    ⇑(f.sum g) = f.sum fun a₁ b => ⇑(g a₁ b) :=
  coe_finset_sum _ _

theorem support_sum [DecidableEq β] [Zero M] [AddCommMonoid N] {f : α →₀ M} {g : α → M → β →₀ N} :
    (f.sum g).support ⊆ f.support.biUnion fun a => (g a (f a)).support := by
  have : ∀ c, (f.sum fun a b => g a b c) ≠ 0 → ∃ a, f a ≠ 0 ∧ ¬(g a (f a)) c = 0 := fun a₁ h =>
    let ⟨a, ha, ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨a, mem_support_iff.mp ha, ne⟩
  simpa only [Finset.subset_iff, mem_support_iff, Finset.mem_biUnion, sum_apply, exists_prop]

theorem support_finset_sum [DecidableEq β] [AddCommMonoid M] {s : Finset α} {f : α → β →₀ M} :
    (Finset.sum s f).support ⊆ s.biUnion fun x => (f x).support := by
  rw [← Finset.sup_eq_biUnion]
  induction s using Finset.cons_induction_on with
  | empty => rfl
  | cons _ _ _ ih =>
    rw [Finset.sum_cons, Finset.sup_cons]
    exact support_add.trans (Finset.union_subset_union (Finset.Subset.refl _) ih)

@[simp]
theorem sum_zero [Zero M] [AddCommMonoid N] {f : α →₀ M} : (f.sum fun _ _ => (0 : N)) = 0 :=
  Finset.sum_const_zero

@[to_additive (attr := simp)]
theorem prod_mul [Zero M] [CommMonoid N] {f : α →₀ M} {h₁ h₂ : α → M → N} :
    (f.prod fun a b => h₁ a b * h₂ a b) = f.prod h₁ * f.prod h₂ :=
  Finset.prod_mul_distrib

@[to_additive (attr := simp)]
theorem prod_inv [Zero M] [CommGroup G] {f : α →₀ M} {h : α → M → G} :
    (f.prod fun a b => (h a b)⁻¹) = (f.prod h)⁻¹ :=
  (map_prod (MonoidHom.id G)⁻¹ _ _).symm

@[simp]
theorem sum_sub [Zero M] [SubtractionCommMonoid G] {f : α →₀ M} {h₁ h₂ : α → M → G} :
    (f.sum fun a b => h₁ a b - h₂ a b) = f.sum h₁ - f.sum h₂ :=
  Finset.sum_sub_distrib ..

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism on the support.
This is a more general version of `Finsupp.prod_add_index'`; the latter has simpler hypotheses. -/
@[to_additive
      /-- Taking the product under `h` is an additive homomorphism of finsupps, if `h` is an
      additive homomorphism on the support. This is a more general version of
      `Finsupp.sum_add_index'`; the latter has simpler hypotheses. -/]
theorem prod_add_index [DecidableEq α] [AddZeroClass M] [CommMonoid N] {f g : α →₀ M}
    {h : α → M → N} (h_zero : ∀ a ∈ f.support ∪ g.support, h a 0 = 1)
    (h_add : ∀ a ∈ f.support ∪ g.support, ∀ (b₁ b₂), h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).prod h = f.prod h * g.prod h := by
  rw [Finsupp.prod_of_support_subset f subset_union_left h h_zero,
    Finsupp.prod_of_support_subset g subset_union_right h h_zero, ←
    Finset.prod_mul_distrib, Finsupp.prod_of_support_subset (f + g) Finsupp.support_add h h_zero]
  exact Finset.prod_congr rfl fun x hx => by apply h_add x hx

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism.
This is a more specialized version of `Finsupp.prod_add_index` with simpler hypotheses. -/
@[to_additive
      /-- Taking the sum under `h` is an additive homomorphism of finsupps,if `h` is an additive
      homomorphism. This is a more specific version of `Finsupp.sum_add_index` with simpler
      hypotheses. -/]
theorem prod_add_index' [AddZeroClass M] [CommMonoid N] {f g : α →₀ M} {h : α → M → N}
    (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).prod h = f.prod h * g.prod h := by
  classical exact prod_add_index (fun a _ => h_zero a) fun a _ => h_add a

@[simp]
theorem sum_hom_add_index [AddZeroClass M] [AddCommMonoid N] {f g : α →₀ M} (h : α → M →+ N) :
    ((f + g).sum fun x => h x) = (f.sum fun x => h x) + g.sum fun x => h x :=
  sum_add_index' (fun a => (h a).map_zero) fun a => (h a).map_add

@[simp]
theorem prod_hom_add_index [AddZeroClass M] [CommMonoid N] {f g : α →₀ M}
    (h : α → Multiplicative M →* N) :
    ((f + g).prod fun a b => h a (Multiplicative.ofAdd b)) =
      (f.prod fun a b => h a (Multiplicative.ofAdd b)) *
        g.prod fun a b => h a (Multiplicative.ofAdd b) :=
  prod_add_index' (fun a => (h a).map_one) fun a => (h a).map_mul

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
    ext
    simp [singleAddHom, AddMonoidHom.comp, Function.comp_def]
  map_add' F G := by
    ext x
    exact sum_add

@[simp]
theorem liftAddHom_apply [AddZeroClass M] [AddCommMonoid N] (F : α → M →+ N) (f : α →₀ M) :
    (liftAddHom (α := α) (M := M) (N := N)) F f = f.sum fun x => F x :=
  rfl

@[simp]
theorem liftAddHom_symm_apply [AddZeroClass M] [AddCommMonoid N] (F : (α →₀ M) →+ N) (x : α) :
    (liftAddHom (α := α) (M := M) (N := N)).symm F x = F.comp (singleAddHom x) :=
  rfl

theorem liftAddHom_symm_apply_apply [AddZeroClass M] [AddCommMonoid N] (F : (α →₀ M) →+ N) (x : α)
    (y : M) : (liftAddHom (α := α) (M := M) (N := N)).symm F x y = F (single x y) :=
  rfl

@[simp]
theorem liftAddHom_singleAddHom [AddCommMonoid M] :
    (liftAddHom (α := α) (M := M) (N := α →₀ M)) (singleAddHom : α → M →+ α →₀ M) =
      AddMonoidHom.id _ :=
  liftAddHom.toEquiv.apply_eq_iff_eq_symm_apply.2 rfl

@[simp]
theorem sum_single [AddCommMonoid M] (f : α →₀ M) : f.sum single = f :=
  DFunLike.congr_fun liftAddHom_singleAddHom f

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
  classical rw [single, coe_mk, Finset.sum_pi_single']
  simp

@[simp]
theorem univ_sum_single_apply' [AddCommMonoid M] [Fintype α] (i : α) (m : M) :
    ∑ j : α, single j m i = m := by
  simp_rw [single, coe_mk]
  classical rw [Finset.sum_pi_single]
  simp

lemma sum_single_add_single (f₁ f₂ : ι) (g₁ g₂ : A) (F : ι → A → B) (H : f₁ ≠ f₂)
    (HF : ∀ f, F f 0 = 0) :
    sum (single f₁ g₁ + single f₂ g₂) F = F f₁ g₁ + F f₂ g₂ := by
  classical
  simp +contextual [sum_of_support_subset _ (s := {f₁, f₂}) (support_add.trans _),
    Finset.subset_iff, single_apply, or_imp, H, HF, H.symm]

theorem equivFunOnFinite_symm_eq_sum [Fintype α] [AddCommMonoid M] (f : α → M) :
    equivFunOnFinite.symm f = ∑ a, Finsupp.single a (f a) := by
  rw [← univ_sum_single (equivFunOnFinite.symm f)]
  ext
  simp

theorem liftAddHom_apply_single [AddZeroClass M] [AddCommMonoid N] (f : α → M →+ N) (a : α)
    (b : M) : (liftAddHom (α := α) (M := M) (N := N)) f (single a b) = f a b :=
  sum_single_index (f a).map_zero

@[simp]
theorem liftAddHom_comp_single [AddZeroClass M] [AddCommMonoid N] (f : α → M →+ N) (a : α) :
    ((liftAddHom (α := α) (M := M) (N := N)) f).comp (singleAddHom a) = f a :=
  AddMonoidHom.ext fun b => liftAddHom_apply_single f a b

theorem comp_liftAddHom [AddZeroClass M] [AddCommMonoid N] [AddCommMonoid P] (g : N →+ P)
    (f : α → M →+ N) :
    g.comp ((liftAddHom (α := α) (M := M) (N := N)) f) =
      (liftAddHom (α := α) (M := M) (N := P)) fun a => g.comp (f a) :=
  liftAddHom.symm_apply_eq.1 <|
    funext fun a => by
      rw [liftAddHom_symm_apply, AddMonoidHom.comp_assoc, liftAddHom_comp_single]

theorem sum_sub_index [AddGroup β] [AddCommGroup γ] {f g : α →₀ β} {h : α → β → γ}
    (h_sub : ∀ a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) : (f - g).sum h = f.sum h - g.sum h :=
  ((liftAddHom (α := α) (M := β) (N := γ)) fun a =>
    AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g

@[to_additive]
theorem prod_embDomain [Zero M] [CommMonoid N] {v : α →₀ M} {f : α ↪ β} {g : β → M → N} :
    (v.embDomain f).prod g = v.prod fun a b => g (f a) b := by
  rw [prod, prod, support_embDomain, Finset.prod_map]
  simp_rw [embDomain_apply]

@[to_additive]
theorem prod_finset_sum_index [AddCommMonoid M] [CommMonoid N] {s : Finset ι} {g : ι → α →₀ M}
    {h : α → M → N} (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (∏ i ∈ s, (g i).prod h) = (∑ i ∈ s, g i).prod h :=
  Finset.cons_induction_on s rfl fun a s has ih => by
    rw [prod_cons, ih, sum_cons, prod_add_index' h_zero h_add]

@[to_additive]
theorem prod_sum_index [Zero M] [AddCommMonoid N] [CommMonoid P] {f : α →₀ M}
    {g : α → M → β →₀ N} {h : β → N → P} (h_zero : ∀ a, h a 0 = 1)
    (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f.sum g).prod h = f.prod fun a b => (g a b).prod h :=
  (prod_finset_sum_index h_zero h_add).symm

theorem multiset_sum_sum_index [AddCommMonoid M] [AddCommMonoid N] (f : Multiset (α →₀ M))
    (h : α → M → N) (h₀ : ∀ a, h a 0 = 0)
    (h₁ : ∀ (a : α) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    f.sum.sum h = (f.map fun g : α →₀ M => g.sum h).sum :=
  Multiset.induction_on f rfl fun a s ih => by
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, sum_add_index' h₀ h₁, ih]

theorem support_sum_eq_biUnion {α : Type*} {ι : Type*} {M : Type*} [DecidableEq α]
    [AddCommMonoid M] {g : ι → α →₀ M} (s : Finset ι)
    (h : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint (g i₁).support (g i₂).support) :
    (∑ i ∈ s, g i).support = s.biUnion fun i => (g i).support := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi
    simp only [hi, sum_insert, not_false_iff, biUnion_insert]
    intro hs
    rw [Finsupp.support_add_eq, hs]
    rw [hs, Finset.disjoint_biUnion_right]
    intro j hj
    exact h _ _ (ne_of_mem_of_not_mem hj hi).symm

theorem multiset_map_sum [Zero M] {f : α →₀ M} {m : β → γ} {h : α → M → Multiset β} :
    Multiset.map m (f.sum h) = f.sum fun a b => (h a b).map m :=
  map_sum (Multiset.mapAddMonoidHom m) _ f.support

theorem multiset_sum_sum [Zero M] [AddCommMonoid N] {f : α →₀ M} {h : α → M → Multiset N} :
    Multiset.sum (f.sum h) = f.sum fun a b => Multiset.sum (h a b) :=
  map_sum Multiset.sumAddMonoidHom _ f.support

/-- For disjoint `f1` and `f2`, and function `g`, the product of the products of `g`
over `f1` and `f2` equals the product of `g` over `f1 + f2` -/
@[to_additive
      /-- For disjoint `f1` and `f2`, and function `g`, the sum of the sums of `g`
      over `f1` and `f2` equals the sum of `g` over `f1 + f2` -/]
theorem prod_add_index_of_disjoint [AddCommMonoid M] {f1 f2 : α →₀ M}
    (hd : Disjoint f1.support f2.support) {β : Type*} [CommMonoid β] (g : α → M → β) :
    (f1 + f2).prod g = f1.prod g * f2.prod g := by
  have :
    ∀ {f1 f2 : α →₀ M},
      Disjoint f1.support f2.support → (∏ x ∈ f1.support, g x (f1 x + f2 x)) = f1.prod g :=
    fun hd =>
    Finset.prod_congr rfl fun x hx => by
      simp only [notMem_support_iff.mp (disjoint_left.mp hd hx), add_zero]
  classical simp_rw [← this hd, ← this hd.symm, add_comm (f2 _), Finsupp.prod, support_add_eq hd,
      prod_union hd, add_apply]

theorem prod_dvd_prod_of_subset_of_dvd [Zero M] [CommMonoid N] {f1 f2 : α →₀ M}
    {g1 g2 : α → M → N} (h1 : f1.support ⊆ f2.support)
    (h2 : ∀ a : α, a ∈ f1.support → g1 a (f1 a) ∣ g2 a (f2 a)) : f1.prod g1 ∣ f2.prod g2 := by
  classical
    simp only [Finsupp.prod]
    rw [← sdiff_union_of_subset h1, prod_union sdiff_disjoint]
    apply dvd_mul_of_dvd_right
    apply prod_dvd_prod_of_dvd
    exact h2

lemma indicator_eq_sum_attach_single [AddCommMonoid M] {s : Finset α} (f : ∀ a ∈ s, M) :
    indicator s f = ∑ x ∈ s.attach, single ↑x (f x x.2) := by
  rw [← sum_single (indicator s f), sum, sum_subset (support_indicator_subset _ _), ← sum_attach]
  · refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [indicator_of_mem]
  · intro i _ hi
    rw [notMem_support_iff.mp hi, single_zero]

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

@[to_additive (attr := simp)]
lemma prod_attach_index [CommMonoid N] {s : Finset α} (f : α → M) {h : α → M → N} :
    ∏ x ∈ s.attach, h x (f x) = ∏ x ∈ s, h x (f x) :=
  prod_attach _ fun x ↦ h x (f x)

@[to_additive]
lemma prod_indicator_index [Zero M] [CommMonoid N]
    {s : Finset α} (f : α → M) {h : α → M → N} (h_zero : ∀ a ∈ s, h a 0 = 1) :
    (indicator s (fun x _ ↦ f x)).prod h = ∏ x ∈ s, h x (f x) := by
  simp +contextual [h_zero]

@[to_additive]
lemma prod_mul_eq_prod_mul_of_exists [Zero M] [CommMonoid N]
    {f : α →₀ M} {g : α → M → N} {n₁ n₂ : N}
    (a : α) (ha : a ∈ f.support)
    (h : g a (f a) * n₁ = g a (f a) * n₂) :
    f.prod g * n₁ = f.prod g * n₂ := by
  classical
  exact Finset.prod_mul_eq_prod_mul_of_exists a ha h

end Finsupp

theorem Finset.sum_apply' : (∑ k ∈ s, f k) i = ∑ k ∈ s, f k i :=
  map_sum (Finsupp.applyAddHom i) f s

theorem Finsupp.sum_apply' : g.sum k x = g.sum fun i b => k i b x :=
  Finset.sum_apply _ _ _

/-- Version of `Finsupp.sum_apply'` that applies in large generality to linear combinations
of functions in any `FunLike` type on which addition is defined pointwise.

At the time of writing Mathlib does not have a typeclass to express the condition
that addition on a `FunLike` type is pointwise; hence this is asserted via explicit hypotheses. -/
theorem Finsupp.sum_apply'' {A F : Type*} [AddZeroClass A] [AddCommMonoid F] [FunLike F γ B]
    (g : ι →₀ A) (k : ι → A → F) (x : γ)
    (hg0 : ∀ (i : ι), k i 0 = 0) (hgadd : ∀ (i : ι) (a₁ a₂ : A), k i (a₁ + a₂) = k i a₁ + k i a₂)
    (h0 : (0 : F) x = 0) (hadd : ∀ (f g : F), (f + g : F) x = f x + g x) :
    g.sum k x = g.sum (fun i a ↦ k i a x) := by
  induction g using Finsupp.induction with
  | zero => simp [h0]
  | single_add i a f hf ha ih =>
    rw [Finsupp.sum_add_index' hg0 hgadd, Finsupp.sum_add_index', hadd, ih]
    · congr 1
      rw [Finsupp.sum_single_index (hg0 i), Finsupp.sum_single_index]
      simp [hg0, h0]
    · simp [hg0, h0]
    · simp [hgadd, hadd]

theorem Finsupp.sum_sum_index' (h0 : ∀ i, t i 0 = 0) (h1 : ∀ i x y, t i (x + y) = t i x + t i y) :
    (∑ x ∈ s, f x).sum t = ∑ x ∈ s, (f x).sum t := by
  classical
  exact Finset.induction_on s rfl fun a s has ih => by
    simp_rw [Finset.sum_insert has, Finsupp.sum_add_index' h0 h1, ih]

section

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

theorem Finsupp.sum_mul (b : S) (s : α →₀ R) {f : α → R → S} :
    s.sum f * b = s.sum fun a c => f a c * b := by simp only [Finsupp.sum, Finset.sum_mul]

theorem Finsupp.mul_sum (b : S) (s : α →₀ R) {f : α → R → S} :
    b * s.sum f = s.sum fun a c => b * f a c := by simp only [Finsupp.sum, Finset.mul_sum]

end

@[simp] lemma Multiset.card_finsuppSum [Zero M] (f : ι →₀ M) (g : ι → M → Multiset α) :
    card (f.sum g) = f.sum fun i m ↦ card (g i m) := map_finsuppSum cardHom ..

namespace Nat

/-- If `0 : ℕ` is not in the support of `f : ℕ →₀ ℕ` then `0 < ∏ x ∈ f.support, x ^ (f x)`. -/
theorem prod_pow_pos_of_zero_notMem_support {f : ℕ →₀ ℕ} (nhf : 0 ∉ f.support) :
    0 < f.prod (· ^ ·) :=
  Nat.pos_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun _ hf =>
    pow_ne_zero _ fun H => by subst H; exact nhf hf

@[deprecated (since := "2025-05-23")]
alias prod_pow_pos_of_zero_not_mem_support := prod_pow_pos_of_zero_notMem_support

end Nat
