/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Results about pointwise operations on sets and big operators.
-/

public section

namespace Set

open Function
open scoped Pointwise

variable {ι α β F : Type*} [FunLike F α β]

section Monoid

variable [Monoid α] [Monoid β] [MonoidHomClass F α β]

@[to_additive]
theorem image_list_prod (f : F) :
    ∀ l : List (Set α), (f : α → β) '' l.prod = (l.map fun s => f '' s).prod
  | [] => image_one.trans <| congr_arg singleton (map_one f)
  | a :: as => by rw [List.map_cons, List.prod_cons, List.prod_cons, image_mul, image_list_prod _ _]

end Monoid

section CommMonoid

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

@[to_additive]
theorem image_multiset_prod (f : F) :
    ∀ m : Multiset (Set α), (f : α → β) '' m.prod = (m.map fun s => f '' s).prod :=
  Quotient.ind <| by
    simpa only [Multiset.quot_mk_to_coe, Multiset.prod_coe, Multiset.map_coe] using
      image_list_prod f

@[to_additive]
theorem image_finsetProd (f : F) (m : Finset ι) (s : ι → Set α) :
    ((f : α → β) '' ∏ i ∈ m, s i) = ∏ i ∈ m, f '' s i :=
  (image_multiset_prod f _).trans <| congr_arg Multiset.prod <| Multiset.map_map _ _ _

@[deprecated (since := "2026-04-08")] alias image_finset_sum := image_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias image_finset_prod := image_finsetProd

/-- The n-ary version of `Set.mem_mul`. -/
@[to_additive /-- The n-ary version of `Set.mem_add`. -/]
theorem mem_finsetProd (t : Finset ι) (f : ι → Set α) (a : α) :
    (a ∈ ∏ i ∈ t, f i) ↔ ∃ (g : ι → α) (_ : ∀ {i}, i ∈ t → g i ∈ f i), ∏ i ∈ t, g i = a := by
  classical
    induction t using Finset.induction_on generalizing a with
    | empty =>
      simp_rw [Finset.prod_empty, Set.mem_one]
      exact ⟨fun h ↦ ⟨fun _ ↦ a, fun hi ↦ False.elim (Finset.notMem_empty _ hi), h.symm⟩,
        fun ⟨_, _, hf⟩ ↦ hf.symm⟩
    | insert i is hi ih => ?_
    rw [Finset.prod_insert hi, Set.mem_mul]
    simp_rw [Finset.prod_insert hi]
    simp_rw [ih]
    constructor
    · rintro ⟨x, y, hx, ⟨g, hg, rfl⟩, rfl⟩
      refine ⟨Function.update g i x, ?_, ?_⟩
      · intro j hj
        obtain rfl | hj := Finset.mem_insert.mp hj
        · rwa [Function.update_self]
        · rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
          exact hg hj
      · rw [Finset.prod_update_of_notMem hi, Function.update_self]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g i, hg (is.mem_insert_self _), is.prod g,
        ⟨⟨g, fun hi ↦ hg (Finset.mem_insert_of_mem hi), rfl⟩, rfl⟩⟩

@[deprecated (since := "2026-04-08")] alias mem_finset_sum := mem_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias mem_finset_prod := mem_finsetProd

@[to_additive]
lemma mem_pow_iff_prod {n : ℕ} {s : Set α} {a : α} :
    a ∈ s ^ n ↔ ∃ f : Fin n → α, (∀ i, f i ∈ s) ∧ ∏ i, f i = a := by
  simpa using mem_finsetProd (t := .univ) (f := fun _ : Fin n ↦ s) _

/-- A version of `Set.mem_finsetProd` with a simpler RHS for products over a Fintype. -/
@[to_additive /-- A version of `Set.mem_finsetSum` with a simpler RHS for sums over a Fintype. -/]
theorem mem_fintype_prod [Fintype ι] (f : ι → Set α) (a : α) :
    (a ∈ ∏ i, f i) ↔ ∃ (g : ι → α) (_ : ∀ i, g i ∈ f i), ∏ i, g i = a := by
  rw [mem_finsetProd]
  simp

/-- An n-ary version of `Set.mul_mem_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_mem_add`. -/]
theorem list_prod_mem_list_prod (t : List ι) (f : ι → Set α) (g : ι → α) (hg : ∀ i ∈ t, g i ∈ f i) :
    (t.map g).prod ∈ (t.map f).prod := by
  induction t with
  | nil => simp_rw [List.map_nil, List.prod_nil, Set.mem_one]
  | cons h tl ih =>
    simp_rw [List.map_cons, List.prod_cons]
    exact mul_mem_mul (hg h List.mem_cons_self)
      (ih fun i hi ↦ hg i <| List.mem_cons_of_mem _ hi)

/-- An n-ary version of `Set.mul_subset_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_subset_add`. -/]
theorem list_prod_subset_list_prod (t : List ι) (f₁ f₂ : ι → Set α) (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) :
    (t.map f₁).prod ⊆ (t.map f₂).prod := by
  induction t with
  | nil => rfl
  | cons h tl ih =>
    simp_rw [List.map_cons, List.prod_cons]
    exact mul_subset_mul (hf h List.mem_cons_self)
      (ih fun i hi ↦ hf i <| List.mem_cons_of_mem _ hi)

@[to_additive]
theorem list_prod_singleton {M : Type*} [Monoid M] (s : List M) :
    (s.map fun i ↦ ({i} : Set M)).prod = {s.prod} :=
  (map_list_prod (singletonMonoidHom : M →* Set M) _).symm

/-- An n-ary version of `Set.mul_mem_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_mem_add`. -/]
theorem multiset_prod_mem_multiset_prod (t : Multiset ι) (f : ι → Set α) (g : ι → α)
    (hg : ∀ i ∈ t, g i ∈ f i) : (t.map g).prod ∈ (t.map f).prod := by
  induction t using Quotient.inductionOn
  simp_rw [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.prod_coe]
  exact list_prod_mem_list_prod _ _ _ hg

/-- An n-ary version of `Set.mul_subset_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_subset_add`. -/]
theorem multiset_prod_subset_multiset_prod (t : Multiset ι) (f₁ f₂ : ι → Set α)
    (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) : (t.map f₁).prod ⊆ (t.map f₂).prod := by
  induction t using Quotient.inductionOn
  simp_rw [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.prod_coe]
  exact list_prod_subset_list_prod _ _ _ hf

@[to_additive]
theorem multiset_prod_singleton {M : Type*} [CommMonoid M] (s : Multiset M) :
    (s.map fun i ↦ ({i} : Set M)).prod = {s.prod} :=
  (map_multiset_prod (singletonMonoidHom : M →* Set M) _).symm

/-- An n-ary version of `Set.mul_mem_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_mem_add`. -/]
theorem finsetProd_mem_finsetProd (t : Finset ι) (f : ι → Set α) (g : ι → α)
    (hg : ∀ i ∈ t, g i ∈ f i) : (∏ i ∈ t, g i) ∈ ∏ i ∈ t, f i :=
  multiset_prod_mem_multiset_prod _ _ _ hg

@[deprecated (since := "2026-04-08")] alias finset_sum_mem_finset_sum := finsetSum_mem_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_mem_finset_prod := finsetProd_mem_finsetProd

/-- An n-ary version of `Set.mul_subset_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_subset_add`. -/]
theorem finsetProd_subset_finsetProd (t : Finset ι) (f₁ f₂ : ι → Set α)
    (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) : ∏ i ∈ t, f₁ i ⊆ ∏ i ∈ t, f₂ i :=
  multiset_prod_subset_multiset_prod _ _ _ hf

@[deprecated (since := "2026-04-08")]
alias finset_sum_subset_finset_sum := finsetSum_subset_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_subset_finset_prod := finsetProd_subset_finsetProd

@[to_additive]
theorem finsetProd_singleton {M ι : Type*} [CommMonoid M] (s : Finset ι) (I : ι → M) :
    ∏ i ∈ s, ({I i} : Set M) = {∏ i ∈ s, I i} :=
  (map_prod (singletonMonoidHom : M →* Set M) _ _).symm

@[deprecated (since := "2026-04-08")] alias finset_sum_singleton := finsetSum_singleton

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_singleton := finsetProd_singleton

/-- The n-ary version of `Set.image_mul_prod`. -/
@[to_additive /-- The n-ary version of `Set.add_image_prod`. -/]
theorem image_finsetProd_pi (l : Finset ι) (S : ι → Set α) :
    (fun f : ι → α => ∏ i ∈ l, f i) '' (l : Set ι).pi S = ∏ i ∈ l, S i := by
  ext
  simp_rw [mem_finsetProd, mem_image, mem_pi, exists_prop, Finset.mem_coe]

@[deprecated (since := "2026-04-08")] alias image_finset_sum_pi := image_finsetSum_pi

@[to_additive existing, deprecated (since := "2026-04-08")]
alias image_finset_prod_pi := image_finsetProd_pi

/-- A special case of `Set.image_finsetProd_pi` for `Finset.univ`. -/
@[to_additive /-- A special case of `Set.image_finsetSum_pi` for `Finset.univ`. -/]
theorem image_fintype_prod_pi [Fintype ι] (S : ι → Set α) :
    (fun f : ι → α => ∏ i, f i) '' univ.pi S = ∏ i, S i := by
  simpa only [Finset.coe_univ] using image_finsetProd_pi Finset.univ S

end CommMonoid

/-! TODO: define `decidable_mem_finsetProd` and `decidable_mem_finsetSum`. -/


end Set
