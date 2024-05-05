/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.DFinsupp.Basic
import Mathlib.GroupTheory.GroupAction.BigOperators
import Mathlib.GroupTheory.Submonoid.Membership

#align_import data.dfinsupp.basic from "leanprover-community/mathlib"@"6623e6af705e97002a9054c1c05a980180276fc1"

/-!
# Dependent functions with finite support

This includes a number of results that need more imports than are available in
`Mathlib.Data.DFinsupp.Basic`.
-/


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

open BigOperators

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

namespace DFinsupp

section Algebra

/-- Evaluation at a point is an `AddMonoidHom`. This is the finitely-supported version of
`Pi.evalAddMonoidHom`. -/
def evalAddMonoidHom [∀ i, AddZeroClass (β i)] (i : ι) : (Π₀ i, β i) →+ β i :=
  (Pi.evalAddMonoidHom β i).comp coeFnAddMonoidHom
#align dfinsupp.eval_add_monoid_hom DFinsupp.evalAddMonoidHom

@[simp, norm_cast]
theorem coe_finset_sum {α} [∀ i, AddCommMonoid (β i)] (s : Finset α) (g : α → Π₀ i, β i) :
    ⇑(∑ a in s, g a) = ∑ a in s, ⇑(g a) :=
  map_sum coeFnAddMonoidHom g s
#align dfinsupp.coe_finset_sum DFinsupp.coe_finset_sum

@[simp]
theorem finset_sum_apply {α} [∀ i, AddCommMonoid (β i)] (s : Finset α) (g : α → Π₀ i, β i) (i : ι) :
    (∑ a in s, g a) i = ∑ a in s, g a i :=
  map_sum (evalAddMonoidHom i) g s
#align dfinsupp.finset_sum_apply DFinsupp.finset_sum_apply

instance isCentralScalar [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)]
    [∀ i, DistribMulAction γᵐᵒᵖ (β i)] [∀ i, IsCentralScalar γ (β i)] :
    IsCentralScalar γ (Π₀ i, β i) where
  op_smul_eq_smul r m := ext fun i => by simp only [smul_apply, op_smul_eq_smul r (m i)]

/-- Dependent functions with finite support inherit a `DistribMulAction` structure from such a
structure on each coordinate. -/
instance distribMulAction [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)] :
    DistribMulAction γ (Π₀ i, β i) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom DFunLike.coe_injective coe_smul

/-- Dependent functions with finite support inherit a module structure from such a structure on
each coordinate. -/
instance module [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)] :
    Module γ (Π₀ i, β i) :=
  { inferInstanceAs (DistribMulAction γ (Π₀ i, β i)) with
    zero_smul := fun c => ext fun i => by simp only [smul_apply, zero_smul, zero_apply]
    add_smul := fun c x y => ext fun i => by simp only [add_apply, smul_apply, add_smul] }
#align dfinsupp.module DFinsupp.module

end Algebra

section FilterAndSubtypeDomain

variable (γ β)

/-- `DFinsupp.filter` as a `LinearMap`. -/
@[simps]
def filterLinearMap [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)] (p : ι → Prop)
    [DecidablePred p] : (Π₀ i, β i) →ₗ[γ] Π₀ i, β i
    where
  toFun := filter p
  map_add' := filter_add p
  map_smul' := filter_smul p
#align dfinsupp.filter_linear_map DFinsupp.filterLinearMap
#align dfinsupp.filter_linear_map_apply DFinsupp.filterLinearMap_apply

/-- `DFinsupp.subtypeDomain` as a `LinearMap`. -/
@[simps]
def subtypeDomainLinearMap [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)]
    (p : ι → Prop) [DecidablePred p] : (Π₀ i, β i) →ₗ[γ] Π₀ i : Subtype p, β i
    where
  toFun := subtypeDomain p
  map_add' := subtypeDomain_add
  map_smul' := subtypeDomain_smul
#align dfinsupp.subtype_domain_linear_map DFinsupp.subtypeDomainLinearMap
#align dfinsupp.subtype_domain_linear_map_apply DFinsupp.subtypeDomainLinearMap_apply

end FilterAndSubtypeDomain

variable [DecidableEq ι]

section AddMonoid

variable [∀ i, AddZeroClass (β i)]

@[simp]
theorem add_closure_iUnion_range_single :
    AddSubmonoid.closure (⋃ i : ι, Set.range (single i : β i → Π₀ i, β i)) = ⊤ :=
  top_unique fun x _ => by
    apply DFinsupp.induction x
    · exact AddSubmonoid.zero_mem _
    exact fun a b f _ _ hf =>
      AddSubmonoid.add_mem _
        (AddSubmonoid.subset_closure <| Set.mem_iUnion.2 ⟨a, Set.mem_range_self _⟩) hf
#align dfinsupp.add_closure_Union_range_single DFinsupp.add_closure_iUnion_range_single

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal. -/
theorem addHom_ext {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀ i, β i) →+ γ⦄
    (H : ∀ (i : ι) (y : β i), f (single i y) = g (single i y)) : f = g := by
  refine' AddMonoidHom.eq_of_eqOn_denseM add_closure_iUnion_range_single fun f hf => _
  simp only [Set.mem_iUnion, Set.mem_range] at hf
  rcases hf with ⟨x, y, rfl⟩
  apply H
#align dfinsupp.add_hom_ext DFinsupp.addHom_ext

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem addHom_ext' {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀ i, β i) →+ γ⦄
    (H : ∀ x, f.comp (singleAddHom β x) = g.comp (singleAddHom β x)) : f = g :=
  addHom_ext fun x => DFunLike.congr_fun (H x)
#align dfinsupp.add_hom_ext' DFinsupp.addHom_ext'

end AddMonoid

theorem support_smul {γ : Type w} [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)]
    [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (b : γ) (v : Π₀ i, β i) :
    (b • v).support ⊆ v.support :=
  support_mapRange
#align dfinsupp.support_smul DFinsupp.support_smul

section Equiv

open Finset

variable {κ : Type*}

section SigmaCurry

variable {α : ι → Type*} {δ : ∀ i, α i → Type v}

instance distribMulAction₂ [Monoid γ] [∀ i j, AddMonoid (δ i j)]
    [∀ i j, DistribMulAction γ (δ i j)] : DistribMulAction γ (Π₀ (i : ι) (j : α i), δ i j) :=
  @DFinsupp.distribMulAction ι _ (fun i => Π₀ j, δ i j) _ _ _
#align dfinsupp.distrib_mul_action₂ DFinsupp.distribMulAction₂

@[simp]
theorem sigmaCurry_smul [Monoid γ] [∀ i j, AddMonoid (δ i j)] [∀ i j, DistribMulAction γ (δ i j)]
    (r : γ) (f : Π₀ (i : Σ _, _), δ i.1 i.2) :
    sigmaCurry (r • f) = r • sigmaCurry f := by
  ext (i j)
  rfl
#align dfinsupp.sigma_curry_smul DFinsupp.sigmaCurry_smul


/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem sigmaUncurry_smul [Monoid γ] [∀ i j, AddMonoid (δ i j)]
    [∀ i, DecidableEq (α i)] [∀ i j (x : δ i j), Decidable (x ≠ 0)]
    [∀ i j, DistribMulAction γ (δ i j)]
    (r : γ) (f : Π₀ (i) (j), δ i j) : sigmaUncurry (r • f) = r • sigmaUncurry f :=
  DFunLike.coe_injective rfl
#align dfinsupp.sigma_uncurry_smul DFinsupp.sigmaUncurry_smul

end SigmaCurry

variable {α : Option ι → Type v}

theorem equivProdDFinsupp_add [∀ i, AddZeroClass (α i)] (f g : Π₀ i, α i) :
    equivProdDFinsupp (f + g) = equivProdDFinsupp f + equivProdDFinsupp g :=
  Prod.ext (add_apply _ _ _) (comapDomain_add _ (Option.some_injective _) _ _)
#align dfinsupp.equiv_prod_dfinsupp_add DFinsupp.equivProdDFinsupp_add

theorem equivProdDFinsupp_smul [Monoid γ] [∀ i, AddMonoid (α i)] [∀ i, DistribMulAction γ (α i)]
    (r : γ) (f : Π₀ i, α i) : equivProdDFinsupp (r • f) = r • equivProdDFinsupp f :=
  Prod.ext (smul_apply _ _ _) (comapDomain_smul _ (Option.some_injective _) _ _)
#align dfinsupp.equiv_prod_dfinsupp_smul DFinsupp.equivProdDFinsupp_smul

end Equiv

section ProdAndSum

/-- `DFinsupp.prod f g` is the product of `g i (f i)` over the support of `f`. -/
@[to_additive "`sum f g` is the sum of `g i (f i)` over the support of `f`."]
def prod [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ] (f : Π₀ i, β i)
    (g : ∀ i, β i → γ) : γ :=
  ∏ i in f.support, g i (f i)
#align dfinsupp.prod DFinsupp.prod
#align dfinsupp.sum DFinsupp.sum

@[to_additive (attr := simp)]
theorem _root_.map_dfinsupp_prod
    {R S H : Type*} [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid R] [CommMonoid S] [FunLike H R S] [MonoidHomClass H R S] (h : H) (f : Π₀ i, β i)
    (g : ∀ i, β i → R) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  map_prod _ _ _

@[to_additive]
theorem prod_mapRange_index {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [∀ i, Zero (β₁ i)]
    [∀ i, Zero (β₂ i)] [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i) (x : β₂ i), Decidable (x ≠ 0)]
    [CommMonoid γ] {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} {h : ∀ i, β₂ i → γ}
    (h0 : ∀ i, h i 0 = 1) : (mapRange f hf g).prod h = g.prod fun i b => h i (f i b) := by
  rw [mapRange_def]
  refine' (Finset.prod_subset support_mk_subset _).trans _
  · intro i h1 h2
    simp only [mem_support_toFun, ne_eq] at h1
    simp only [Finset.coe_sort_coe, mem_support_toFun, mk_apply, ne_eq, h1, not_false_iff,
      dite_eq_ite, ite_true, not_not] at h2
    simp [h2, h0]
  · refine' Finset.prod_congr rfl _
    intro i h1
    simp only [mem_support_toFun, ne_eq] at h1
    simp [h1]
#align dfinsupp.prod_map_range_index DFinsupp.prod_mapRange_index
#align dfinsupp.sum_map_range_index DFinsupp.sum_mapRange_index

@[to_additive]
theorem prod_zero_index [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {h : ∀ i, β i → γ} : (0 : Π₀ i, β i).prod h = 1 :=
  rfl
#align dfinsupp.prod_zero_index DFinsupp.prod_zero_index
#align dfinsupp.sum_zero_index DFinsupp.sum_zero_index

@[to_additive]
theorem prod_single_index [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {i : ι} {b : β i} {h : ∀ i, β i → γ} (h_zero : h i 0 = 1) : (single i b).prod h = h i b := by
  by_cases h : b ≠ 0
  · simp [DFinsupp.prod, support_single_ne_zero h]
  · rw [not_not] at h
    simp [h, prod_zero_index, h_zero]
    rfl
#align dfinsupp.prod_single_index DFinsupp.prod_single_index
#align dfinsupp.sum_single_index DFinsupp.sum_single_index

@[to_additive]
theorem prod_neg_index [∀ i, AddGroup (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {g : Π₀ i, β i} {h : ∀ i, β i → γ} (h0 : ∀ i, h i 0 = 1) :
    (-g).prod h = g.prod fun i b => h i (-b) :=
  prod_mapRange_index h0
#align dfinsupp.prod_neg_index DFinsupp.prod_neg_index
#align dfinsupp.sum_neg_index DFinsupp.sum_neg_index

@[to_additive]
theorem prod_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*} [DecidableEq ι₁]
    [DecidableEq ι₂] [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)] [∀ (i) (x : β₁ i), Decidable (x ≠ 0)]
    [∀ (i) (x : β₂ i), Decidable (x ≠ 0)] [CommMonoid γ] (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i)
    (h : ∀ i, β₁ i → ∀ i, β₂ i → γ) :
    (f₁.prod fun i₁ x₁ => f₂.prod fun i₂ x₂ => h i₁ x₁ i₂ x₂) =
      f₂.prod fun i₂ x₂ => f₁.prod fun i₁ x₁ => h i₁ x₁ i₂ x₂ :=
  Finset.prod_comm
#align dfinsupp.prod_comm DFinsupp.prod_comm
#align dfinsupp.sum_comm DFinsupp.sum_comm

@[simp]
theorem sum_apply {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, Zero (β₁ i₁)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)] {f : Π₀ i₁, β₁ i₁}
    {g : ∀ i₁, β₁ i₁ → Π₀ i, β i} {i₂ : ι} : (f.sum g) i₂ = f.sum fun i₁ b => g i₁ b i₂ :=
  map_sum (evalAddMonoidHom i₂) _ f.support
#align dfinsupp.sum_apply DFinsupp.sum_apply

theorem support_sum {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, Zero (β₁ i₁)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)]
    [∀ (i) (x : β i), Decidable (x ≠ 0)] {f : Π₀ i₁, β₁ i₁} {g : ∀ i₁, β₁ i₁ → Π₀ i, β i} :
    (f.sum g).support ⊆ f.support.biUnion fun i => (g i (f i)).support := by
  have :
    ∀ i₁ : ι,
      (f.sum fun (i : ι₁) (b : β₁ i) => (g i b) i₁) ≠ 0 → ∃ i : ι₁, f i ≠ 0 ∧ ¬(g i (f i)) i₁ = 0 :=
    fun i₁ h =>
    let ⟨i, hi, Ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨i, mem_support_iff.1 hi, Ne⟩
  simpa [Finset.subset_iff, mem_support_iff, Finset.mem_biUnion, sum_apply] using this
#align dfinsupp.support_sum DFinsupp.support_sum

@[to_additive (attr := simp)]
theorem prod_one [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} : (f.prod fun _ _ => (1 : γ)) = 1 :=
  Finset.prod_const_one
#align dfinsupp.prod_one DFinsupp.prod_one
#align dfinsupp.sum_zero DFinsupp.sum_zero

@[to_additive (attr := simp)]
theorem prod_mul [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} {h₁ h₂ : ∀ i, β i → γ} :
    (f.prod fun i b => h₁ i b * h₂ i b) = f.prod h₁ * f.prod h₂ :=
  Finset.prod_mul_distrib
#align dfinsupp.prod_mul DFinsupp.prod_mul
#align dfinsupp.sum_add DFinsupp.sum_add

@[to_additive (attr := simp)]
theorem prod_inv [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommGroup γ]
    {f : Π₀ i, β i} {h : ∀ i, β i → γ} : (f.prod fun i b => (h i b)⁻¹) = (f.prod h)⁻¹ :=
  (map_prod (invMonoidHom : γ →* γ) _ f.support).symm
#align dfinsupp.prod_inv DFinsupp.prod_inv
#align dfinsupp.sum_neg DFinsupp.sum_neg

@[to_additive]
theorem prod_eq_one [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} {h : ∀ i, β i → γ} (hyp : ∀ i, h i (f i) = 1) : f.prod h = 1 :=
  Finset.prod_eq_one fun i _ => hyp i
#align dfinsupp.prod_eq_one DFinsupp.prod_eq_one
#align dfinsupp.sum_eq_zero DFinsupp.sum_eq_zero

theorem smul_sum {α : Type*} [Monoid α] [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [AddCommMonoid γ] [DistribMulAction α γ] {f : Π₀ i, β i} {h : ∀ i, β i → γ} {c : α} :
    c • f.sum h = f.sum fun a b => c • h a b :=
  Finset.smul_sum
#align dfinsupp.smul_sum DFinsupp.smul_sum

@[to_additive]
theorem prod_add_index [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {f g : Π₀ i, β i} {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) : (f + g).prod h = f.prod h * g.prod h :=
  have f_eq : (∏ i in f.support ∪ g.support, h i (f i)) = f.prod h :=
    (Finset.prod_subset (Finset.subset_union_left _ _) <| by
        simp (config := { contextual := true }) [mem_support_iff, h_zero]).symm
  have g_eq : (∏ i in f.support ∪ g.support, h i (g i)) = g.prod h :=
    (Finset.prod_subset (Finset.subset_union_right _ _) <| by
        simp (config := { contextual := true }) [mem_support_iff, h_zero]).symm
  calc
    (∏ i in (f + g).support, h i ((f + g) i)) = ∏ i in f.support ∪ g.support, h i ((f + g) i) :=
      Finset.prod_subset support_add <| by
        simp (config := { contextual := true }) [mem_support_iff, h_zero]
    _ = (∏ i in f.support ∪ g.support, h i (f i)) * ∏ i in f.support ∪ g.support, h i (g i) := by
      { simp [h_add, Finset.prod_mul_distrib] }
    _ = _ := by rw [f_eq, g_eq]
#align dfinsupp.prod_add_index DFinsupp.prod_add_index
#align dfinsupp.sum_add_index DFinsupp.sum_add_index

@[to_additive]
theorem _root_.dfinsupp_prod_mem [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {S : Type*} [SetLike S γ] [SubmonoidClass S γ]
    (s : S) (f : Π₀ i, β i) (g : ∀ i, β i → γ)
    (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : f.prod g ∈ s :=
  prod_mem fun _ hi => h _ <| mem_support_iff.1 hi
#align dfinsupp_prod_mem dfinsupp_prod_mem
#align dfinsupp_sum_mem dfinsupp_sum_mem

@[to_additive (attr := simp)]
theorem prod_eq_prod_fintype [Fintype ι] [∀ i, Zero (β i)] [∀ (i : ι) (x : β i), Decidable (x ≠ 0)]
    -- Porting note: `f` was a typeclass argument
    [CommMonoid γ] (v : Π₀ i, β i) {f : ∀ i, β i → γ} (hf : ∀ i, f i 0 = 1) :
    v.prod f = ∏ i, f i (DFinsupp.equivFunOnFintype v i) := by
  suffices (∏ i in v.support, f i (v i)) = ∏ i, f i (v i) by simp [DFinsupp.prod, this]
  apply Finset.prod_subset v.support.subset_univ
  intro i _ hi
  rw [mem_support_iff, not_not] at hi
  rw [hi, hf]
#align dfinsupp.prod_eq_prod_fintype DFinsupp.prod_eq_prod_fintype
#align dfinsupp.sum_eq_sum_fintype DFinsupp.sum_eq_sum_fintype

section CommMonoidWithZero
variable [Π i, Zero (β i)] [CommMonoidWithZero γ] [Nontrivial γ] [NoZeroDivisors γ]
  [Π i, DecidableEq (β i)] {f : Π₀ i, β i} {g : Π i, β i → γ}

@[simp]
lemma prod_eq_zero_iff : f.prod g = 0 ↔ ∃ i ∈ f.support, g i (f i) = 0 := Finset.prod_eq_zero_iff
lemma prod_ne_zero_iff : f.prod g ≠ 0 ↔ ∀ i ∈ f.support, g i (f i) ≠ 0 := Finset.prod_ne_zero_iff

end CommMonoidWithZero

/--
When summing over an `AddMonoidHom`, the decidability assumption is not needed, and the result is
also an `AddMonoidHom`.
-/
def sumAddHom [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : ∀ i, β i →+ γ) :
    (Π₀ i, β i) →+ γ where
  toFun f :=
    (f.support'.lift fun s => ∑ i in Multiset.toFinset s.1, φ i (f i)) <| by
      rintro ⟨sx, hx⟩ ⟨sy, hy⟩
      dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
      have H1 : sx.toFinset ∩ sy.toFinset ⊆ sx.toFinset := Finset.inter_subset_left _ _
      have H2 : sx.toFinset ∩ sy.toFinset ⊆ sy.toFinset := Finset.inter_subset_right _ _
      refine'
        (Finset.sum_subset H1 _).symm.trans
          ((Finset.sum_congr rfl _).trans (Finset.sum_subset H2 _))
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert AddMonoidHom.map_zero (φ i)
        exact (hy i).resolve_left (mt (And.intro H1) H2)
      · intro i _
        rfl
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert AddMonoidHom.map_zero (φ i)
        exact (hx i).resolve_left (mt (fun H3 => And.intro H3 H1) H2)
  map_add' := by
    rintro ⟨f, sf, hf⟩ ⟨g, sg, hg⟩
    change (∑ i in _, _) = (∑ i in _, _) + ∑ i in _, _
    simp only [coe_add, coe_mk', Subtype.coe_mk, Pi.add_apply, map_add, Finset.sum_add_distrib]
    congr 1
    · refine' (Finset.sum_subset _ _).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inl
      · intro i _ H2
        simp only [Multiset.mem_toFinset, Multiset.mem_add] at H2
        rw [(hf i).resolve_left H2, AddMonoidHom.map_zero]
    · refine' (Finset.sum_subset _ _).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inr
      · intro i _ H2
        simp only [Multiset.mem_toFinset, Multiset.mem_add] at H2
        rw [(hg i).resolve_left H2, AddMonoidHom.map_zero]
  map_zero' := by
    simp only [toFun_eq_coe, coe_zero, Pi.zero_apply, map_zero, Finset.sum_const_zero]; rfl
#align dfinsupp.sum_add_hom DFinsupp.sumAddHom

@[simp]
theorem sumAddHom_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : ∀ i, β i →+ γ) (i)
    (x : β i) : sumAddHom φ (single i x) = φ i x := by
  dsimp [sumAddHom, single, Trunc.lift_mk]
  rw [Multiset.toFinset_singleton, Finset.sum_singleton, Pi.single_eq_same]
#align dfinsupp.sum_add_hom_single DFinsupp.sumAddHom_single

@[simp]
theorem sumAddHom_comp_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) : (sumAddHom f).comp (singleAddHom β i) = f i :=
  AddMonoidHom.ext fun x => sumAddHom_single f i x
#align dfinsupp.sum_add_hom_comp_single DFinsupp.sumAddHom_comp_single

/-- While we didn't need decidable instances to define it, we do to reduce it to a sum -/
theorem sumAddHom_apply [∀ i, AddZeroClass (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [AddCommMonoid γ] (φ : ∀ i, β i →+ γ) (f : Π₀ i, β i) : sumAddHom φ f = f.sum fun x => φ x := by
  rcases f with ⟨f, s, hf⟩
  change (∑ i in _, _) = ∑ i in Finset.filter _ _, _
  rw [Finset.sum_filter, Finset.sum_congr rfl]
  intro i _
  dsimp only [coe_mk', Subtype.coe_mk] at *
  split_ifs with h
  · rfl
  · rw [not_not.mp h, AddMonoidHom.map_zero]
#align dfinsupp.sum_add_hom_apply DFinsupp.sumAddHom_apply

theorem _root_.dfinsupp_sumAddHom_mem [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] {S : Type*}
    [SetLike S γ] [AddSubmonoidClass S γ] (s : S) (f : Π₀ i, β i) (g : ∀ i, β i →+ γ)
    (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : DFinsupp.sumAddHom g f ∈ s := by
  classical
    rw [DFinsupp.sumAddHom_apply]
    exact dfinsupp_sum_mem s f (g ·) h
#align dfinsupp_sum_add_hom_mem dfinsupp_sumAddHom_mem

/-- The supremum of a family of commutative additive submonoids is equal to the range of
`DFinsupp.sumAddHom`; that is, every element in the `iSup` can be produced from taking a finite
number of non-zero elements of `S i`, coercing them to `γ`, and summing them. -/
theorem _root_.AddSubmonoid.iSup_eq_mrange_dfinsupp_sumAddHom
    [AddCommMonoid γ] (S : ι → AddSubmonoid γ) :
    iSup S = AddMonoidHom.mrange (DFinsupp.sumAddHom fun i => (S i).subtype) := by
  apply le_antisymm
  · apply iSup_le _
    intro i y hy
    exact ⟨DFinsupp.single i ⟨y, hy⟩, DFinsupp.sumAddHom_single _ _ _⟩
  · rintro x ⟨v, rfl⟩
    exact dfinsupp_sumAddHom_mem _ v _ fun i _ => (le_iSup S i : S i ≤ _) (v i).prop
#align add_submonoid.supr_eq_mrange_dfinsupp_sum_add_hom AddSubmonoid.iSup_eq_mrange_dfinsupp_sumAddHom

/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`DFinsupp.sumAddHom` composed with `DFinsupp.filterAddMonoidHom`; that is, every element in the
bounded `iSup` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
theorem _root_.AddSubmonoid.bsupr_eq_mrange_dfinsupp_sumAddHom (p : ι → Prop) [DecidablePred p]
    [AddCommMonoid γ] (S : ι → AddSubmonoid γ) :
    ⨆ (i) (_ : p i), S i =
      AddMonoidHom.mrange ((sumAddHom fun i => (S i).subtype).comp (filterAddMonoidHom _ p)) := by
  apply le_antisymm
  · refine' iSup₂_le fun i hi y hy => ⟨DFinsupp.single i ⟨y, hy⟩, _⟩
    rw [AddMonoidHom.comp_apply, filterAddMonoidHom_apply, filter_single_pos _ _ hi]
    exact sumAddHom_single _ _ _
  · rintro x ⟨v, rfl⟩
    refine' dfinsupp_sumAddHom_mem _ _ _ fun i _ => _
    refine' AddSubmonoid.mem_iSup_of_mem i _
    by_cases hp : p i
    · simp [hp]
    · simp [hp]
#align add_submonoid.bsupr_eq_mrange_dfinsupp_sum_add_hom AddSubmonoid.bsupr_eq_mrange_dfinsupp_sumAddHom

theorem _root_.AddSubmonoid.mem_iSup_iff_exists_dfinsupp [AddCommMonoid γ] (S : ι → AddSubmonoid γ)
    (x : γ) : x ∈ iSup S ↔ ∃ f : Π₀ i, S i, DFinsupp.sumAddHom (fun i => (S i).subtype) f = x :=
  SetLike.ext_iff.mp (AddSubmonoid.iSup_eq_mrange_dfinsupp_sumAddHom S) x
#align add_submonoid.mem_supr_iff_exists_dfinsupp AddSubmonoid.mem_iSup_iff_exists_dfinsupp

/-- A variant of `AddSubmonoid.mem_iSup_iff_exists_dfinsupp` with the RHS fully unfolded. -/
theorem _root_.AddSubmonoid.mem_iSup_iff_exists_dfinsupp' [AddCommMonoid γ] (S : ι → AddSubmonoid γ)
    [∀ (i) (x : S i), Decidable (x ≠ 0)] (x : γ) :
    x ∈ iSup S ↔ ∃ f : Π₀ i, S i, (f.sum fun i xi => ↑xi) = x := by
  rw [AddSubmonoid.mem_iSup_iff_exists_dfinsupp]
  simp_rw [sumAddHom_apply]
  rfl
#align add_submonoid.mem_supr_iff_exists_dfinsupp' AddSubmonoid.mem_iSup_iff_exists_dfinsupp'

theorem _root_.AddSubmonoid.mem_bsupr_iff_exists_dfinsupp (p : ι → Prop) [DecidablePred p]
    [AddCommMonoid γ] (S : ι → AddSubmonoid γ) (x : γ) :
    (x ∈ ⨆ (i) (_ : p i), S i) ↔
      ∃ f : Π₀ i, S i, DFinsupp.sumAddHom (fun i => (S i).subtype) (f.filter p) = x :=
  SetLike.ext_iff.mp (AddSubmonoid.bsupr_eq_mrange_dfinsupp_sumAddHom p S) x
#align add_submonoid.mem_bsupr_iff_exists_dfinsupp AddSubmonoid.mem_bsupr_iff_exists_dfinsupp

theorem sumAddHom_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*} {γ : Type*}
    [DecidableEq ι₁] [DecidableEq ι₂] [∀ i, AddZeroClass (β₁ i)] [∀ i, AddZeroClass (β₂ i)]
    [AddCommMonoid γ] (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i) (h : ∀ i j, β₁ i →+ β₂ j →+ γ) :
    sumAddHom (fun i₂ => sumAddHom (fun i₁ => h i₁ i₂) f₁) f₂ =
      sumAddHom (fun i₁ => sumAddHom (fun i₂ => (h i₁ i₂).flip) f₂) f₁ := by
  obtain ⟨⟨f₁, s₁, h₁⟩, ⟨f₂, s₂, h₂⟩⟩ := f₁, f₂
  simp only [sumAddHom, AddMonoidHom.finset_sum_apply, Quotient.liftOn_mk, AddMonoidHom.coe_mk,
    AddMonoidHom.flip_apply, Trunc.lift, toFun_eq_coe, ZeroHom.coe_mk, coe_mk']
  exact Finset.sum_comm
#align dfinsupp.sum_add_hom_comm DFinsupp.sumAddHom_comm

/-- The `DFinsupp` version of `Finsupp.liftAddHom`,-/
@[simps apply symm_apply]
def liftAddHom [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] : (∀ i, β i →+ γ) ≃+ ((Π₀ i, β i) →+ γ)
    where
  toFun := sumAddHom
  invFun F i := F.comp (singleAddHom β i)
  left_inv x := by ext; simp
  right_inv ψ := by ext; simp
  map_add' F G := by ext; simp
#align dfinsupp.lift_add_hom DFinsupp.liftAddHom
#align dfinsupp.lift_add_hom_apply DFinsupp.liftAddHom_apply
#align dfinsupp.lift_add_hom_symm_apply DFinsupp.liftAddHom_symm_apply

-- Porting note: The elaborator is struggling with `liftAddHom`. Passing it `β` explicitly helps.
-- This applies to roughly the remainder of the file.

/-- The `DFinsupp` version of `Finsupp.liftAddHom_singleAddHom`,-/
@[simp, nolint simpNF] -- Porting note: linter claims that simp can prove this, but it can not
theorem liftAddHom_singleAddHom [∀ i, AddCommMonoid (β i)] :
    liftAddHom (β := β) (singleAddHom β) = AddMonoidHom.id (Π₀ i, β i) :=
  (liftAddHom (β := β)).toEquiv.apply_eq_iff_eq_symm_apply.2 rfl
#align dfinsupp.lift_add_hom_single_add_hom DFinsupp.liftAddHom_singleAddHom

/-- The `DFinsupp` version of `Finsupp.liftAddHom_apply_single`,-/
theorem liftAddHom_apply_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) (x : β i) : liftAddHom (β := β) f (single i x) = f i x := by simp
#align dfinsupp.lift_add_hom_apply_single DFinsupp.liftAddHom_apply_single

/-- The `DFinsupp` version of `Finsupp.liftAddHom_comp_single`,-/
theorem liftAddHom_comp_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) : (liftAddHom (β := β) f).comp (singleAddHom β i) = f i := by simp
#align dfinsupp.lift_add_hom_comp_single DFinsupp.liftAddHom_comp_single

/-- The `DFinsupp` version of `Finsupp.comp_liftAddHom`,-/
theorem comp_liftAddHom {δ : Type*} [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] [AddCommMonoid δ]
    (g : γ →+ δ) (f : ∀ i, β i →+ γ) :
    g.comp (liftAddHom (β := β) f) = liftAddHom (β := β) fun a => g.comp (f a) :=
  (liftAddHom (β := β)).symm_apply_eq.1 <|
    funext fun a => by
      rw [liftAddHom_symm_apply, AddMonoidHom.comp_assoc, liftAddHom_comp_single]
#align dfinsupp.comp_lift_add_hom DFinsupp.comp_liftAddHom

@[simp]
theorem sumAddHom_zero [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] :
    (sumAddHom fun i => (0 : β i →+ γ)) = 0 :=
  (liftAddHom (β := β) : (∀ i, β i →+ γ) ≃+ _).map_zero
#align dfinsupp.sum_add_hom_zero DFinsupp.sumAddHom_zero

@[simp]
theorem sumAddHom_add [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (g : ∀ i, β i →+ γ)
    (h : ∀ i, β i →+ γ) : (sumAddHom fun i => g i + h i) = sumAddHom g + sumAddHom h :=
  (liftAddHom (β := β)).map_add _ _
#align dfinsupp.sum_add_hom_add DFinsupp.sumAddHom_add

@[simp]
theorem sumAddHom_singleAddHom [∀ i, AddCommMonoid (β i)] :
    sumAddHom (singleAddHom β) = AddMonoidHom.id _ :=
  liftAddHom_singleAddHom
#align dfinsupp.sum_add_hom_single_add_hom DFinsupp.sumAddHom_singleAddHom

theorem comp_sumAddHom {δ : Type*} [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] [AddCommMonoid δ]
    (g : γ →+ δ) (f : ∀ i, β i →+ γ) : g.comp (sumAddHom f) = sumAddHom fun a => g.comp (f a) :=
  comp_liftAddHom _ _
#align dfinsupp.comp_sum_add_hom DFinsupp.comp_sumAddHom

theorem sum_sub_index [∀ i, AddGroup (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [AddCommGroup γ]
    {f g : Π₀ i, β i} {h : ∀ i, β i → γ} (h_sub : ∀ i b₁ b₂, h i (b₁ - b₂) = h i b₁ - h i b₂) :
    (f - g).sum h = f.sum h - g.sum h := by
  have := (liftAddHom (β := β) fun a => AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g
  rw [liftAddHom_apply, sumAddHom_apply, sumAddHom_apply, sumAddHom_apply] at this
  exact this
#align dfinsupp.sum_sub_index DFinsupp.sum_sub_index

@[to_additive]
theorem prod_finset_sum_index {γ : Type w} {α : Type x} [∀ i, AddCommMonoid (β i)]
    [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ] {s : Finset α} {g : α → Π₀ i, β i}
    {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
    (∏ i in s, (g i).prod h) = (∑ i in s, g i).prod h := by
  classical
  exact Finset.induction_on s (by simp [prod_zero_index])
        (by simp (config := { contextual := true }) [prod_add_index, h_zero, h_add])
#align dfinsupp.prod_finset_sum_index DFinsupp.prod_finset_sum_index
#align dfinsupp.sum_finset_sum_index DFinsupp.sum_finset_sum_index

@[to_additive]
theorem prod_sum_index {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, Zero (β₁ i₁)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)]
    [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ] {f : Π₀ i₁, β₁ i₁}
    {g : ∀ i₁, β₁ i₁ → Π₀ i, β i} {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
    (f.sum g).prod h = f.prod fun i b => (g i b).prod h :=
  (prod_finset_sum_index h_zero h_add).symm
#align dfinsupp.prod_sum_index DFinsupp.prod_sum_index
#align dfinsupp.sum_sum_index DFinsupp.sum_sum_index

@[simp]
theorem sum_single [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] {f : Π₀ i, β i} :
    f.sum single = f := by
  have := DFunLike.congr_fun (liftAddHom_singleAddHom (β := β)) f
  rw [liftAddHom_apply, sumAddHom_apply] at this
  exact this
#align dfinsupp.sum_single DFinsupp.sum_single

@[to_additive]
theorem prod_subtypeDomain_index [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {v : Π₀ i, β i} {p : ι → Prop} [DecidablePred p] {h : ∀ i, β i → γ}
    (hp : ∀ x ∈ v.support, p x) : (v.subtypeDomain p).prod (fun i b => h i b) = v.prod h := by
  refine Finset.prod_bij (fun p _ ↦ p) ?_ ?_ ?_ ?_ <;> aesop
#align dfinsupp.prod_subtype_domain_index DFinsupp.prod_subtypeDomain_index
#align dfinsupp.sum_subtype_domain_index DFinsupp.sum_subtypeDomain_index

theorem subtypeDomain_sum [∀ i, AddCommMonoid (β i)] {s : Finset γ} {h : γ → Π₀ i, β i}
    {p : ι → Prop} [DecidablePred p] :
    (∑ c in s, h c).subtypeDomain p = ∑ c in s, (h c).subtypeDomain p :=
  map_sum (subtypeDomainAddMonoidHom β p) _ s
#align dfinsupp.subtype_domain_sum DFinsupp.subtypeDomain_sum

theorem subtypeDomain_finsupp_sum {δ : γ → Type x} [DecidableEq γ] [∀ c, Zero (δ c)]
    [∀ (c) (x : δ c), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)] {p : ι → Prop} [DecidablePred p]
    {s : Π₀ c, δ c} {h : ∀ c, δ c → Π₀ i, β i} :
    (s.sum h).subtypeDomain p = s.sum fun c d => (h c d).subtypeDomain p :=
  subtypeDomain_sum
#align dfinsupp.subtype_domain_finsupp_sum DFinsupp.subtypeDomain_finsupp_sum

end ProdAndSum

end DFinsupp

/-! ### Product and sum lemmas for bundled morphisms.

In this section, we provide analogues of `AddMonoidHom.map_sum`, `AddMonoidHom.coe_finset_sum`,
and `AddMonoidHom.finset_sum_apply` for `DFinsupp.sum` and `DFinsupp.sumAddHom` instead of
`Finset.sum`.

We provide these for `AddMonoidHom`, `MonoidHom`, `RingHom`, `AddEquiv`, and `MulEquiv`.

Lemmas for `LinearMap` and `LinearEquiv` are in another file.
-/

section

variable [DecidableEq ι]

namespace MonoidHom

variable {R S : Type*}
variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

#align monoid_hom.map_dfinsupp_prod map_dfinsupp_prodₓ
#align add_monoid_hom.map_dfinsupp_sum map_dfinsupp_sumₓ

@[to_additive (attr := simp, norm_cast)]
theorem coe_dfinsupp_prod [Monoid R] [CommMonoid S] (f : Π₀ i, β i) (g : ∀ i, β i → R →* S) :
    ⇑(f.prod g) = f.prod fun a b => ⇑(g a b) :=
  coe_finset_prod _ _
#align monoid_hom.coe_dfinsupp_prod MonoidHom.coe_dfinsupp_prod
#align add_monoid_hom.coe_dfinsupp_sum AddMonoidHom.coe_dfinsupp_sum

@[to_additive]
theorem dfinsupp_prod_apply [Monoid R] [CommMonoid S] (f : Π₀ i, β i) (g : ∀ i, β i → R →* S)
    (r : R) : (f.prod g) r = f.prod fun a b => (g a b) r :=
  finset_prod_apply _ _ _
#align monoid_hom.dfinsupp_prod_apply MonoidHom.dfinsupp_prod_apply
#align add_monoid_hom.dfinsupp_sum_apply AddMonoidHom.dfinsupp_sum_apply

end MonoidHom

#align ring_hom.map_dfinsupp_prod map_dfinsupp_prodₓ
#align ring_hom.map_dfinsupp_sum map_dfinsupp_sumₓ
#align mul_equiv.map_dfinsupp_prod map_dfinsupp_prodₓ
#align add_equiv.map_dfinsupp_sum map_dfinsupp_sumₓ

/-! The above lemmas, repeated for `DFinsupp.sumAddHom`. -/

namespace AddMonoidHom

variable {R S : Type*}

open DFinsupp

@[simp]
theorem map_dfinsupp_sumAddHom [AddCommMonoid R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (h : R →+ S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h g) f
#align add_monoid_hom.map_dfinsupp_sum_add_hom AddMonoidHom.map_dfinsupp_sumAddHom

theorem dfinsupp_sumAddHom_apply [AddZeroClass R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (f : Π₀ i, β i) (g : ∀ i, β i →+ R →+ S) (r : R) :
    (sumAddHom g f) r = sumAddHom (fun i => (eval r).comp (g i)) f :=
  map_dfinsupp_sumAddHom (eval r) f g
#align add_monoid_hom.dfinsupp_sum_add_hom_apply AddMonoidHom.dfinsupp_sumAddHom_apply

@[simp, norm_cast]
theorem coe_dfinsupp_sumAddHom [AddZeroClass R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (f : Π₀ i, β i) (g : ∀ i, β i →+ R →+ S) :
    ⇑(sumAddHom g f) = sumAddHom (fun i => (coeFn R S).comp (g i)) f :=
  map_dfinsupp_sumAddHom (coeFn R S) f g
#align add_monoid_hom.coe_dfinsupp_sum_add_hom AddMonoidHom.coe_dfinsupp_sumAddHom

end AddMonoidHom

namespace RingHom

variable {R S : Type*}

open DFinsupp

@[simp]
theorem map_dfinsupp_sumAddHom [NonAssocSemiring R] [NonAssocSemiring S] [∀ i, AddZeroClass (β i)]
    (h : R →+* S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f
#align ring_hom.map_dfinsupp_sum_add_hom RingHom.map_dfinsupp_sumAddHom

end RingHom

namespace AddEquiv

variable {R S : Type*}

open DFinsupp

@[simp]
theorem map_dfinsupp_sumAddHom [AddCommMonoid R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (h : R ≃+ S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f
#align add_equiv.map_dfinsupp_sum_add_hom AddEquiv.map_dfinsupp_sumAddHom

end AddEquiv

end
