/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Set.Pointwise.Basic

#align_import data.set.pointwise.big_operators from "leanprover-community/mathlib"@"fa2cb8a9e2b987db233e4e6eb47645feafba8861"

/-!
# Results about pointwise operations on sets and big operators.
-/


namespace Set

open Pointwise Function

variable {ι α β F : Type*} [FunLike F α β]

section Monoid

variable [Monoid α] [Monoid β] [MonoidHomClass F α β]

@[to_additive]
theorem image_list_prod (f : F) :
    ∀ l : List (Set α), (f : α → β) '' l.prod = (l.map fun s => f '' s).prod
  | [] => image_one.trans <| congr_arg singleton (map_one f)
  | a :: as => by rw [List.map_cons, List.prod_cons, List.prod_cons, image_mul, image_list_prod _ _]
#align set.image_list_prod Set.image_list_prod
#align set.image_list_sum Set.image_list_sum

end Monoid

section CommMonoid

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

@[to_additive]
theorem image_multiset_prod (f : F) :
    ∀ m : Multiset (Set α), (f : α → β) '' m.prod = (m.map fun s => f '' s).prod :=
  Quotient.ind <| by
    simpa only [Multiset.quot_mk_to_coe, Multiset.prod_coe, Multiset.map_coe] using
      image_list_prod f
#align set.image_multiset_prod Set.image_multiset_prod
#align set.image_multiset_sum Set.image_multiset_sum

@[to_additive]
theorem image_finset_prod (f : F) (m : Finset ι) (s : ι → Set α) :
    ((f : α → β) '' ∏ i ∈ m, s i) = ∏ i ∈ m, f '' s i :=
  (image_multiset_prod f _).trans <| congr_arg Multiset.prod <| Multiset.map_map _ _ _
#align set.image_finset_prod Set.image_finset_prod
#align set.image_finset_sum Set.image_finset_sum

/-- The n-ary version of `Set.mem_mul`. -/
@[to_additive " The n-ary version of `Set.mem_add`. "]
theorem mem_finset_prod (t : Finset ι) (f : ι → Set α) (a : α) :
    (a ∈ ∏ i ∈ t, f i) ↔ ∃ (g : ι → α) (_ : ∀ {i}, i ∈ t → g i ∈ f i), ∏ i ∈ t, g i = a := by
  classical
    induction' t using Finset.induction_on with i is hi ih generalizing a
    · simp_rw [Finset.prod_empty, Set.mem_one]
      exact ⟨fun h ↦ ⟨fun _ ↦ a, fun hi ↦ False.elim (Finset.not_mem_empty _ hi), h.symm⟩,
        fun ⟨_, _, hf⟩ ↦ hf.symm⟩
    rw [Finset.prod_insert hi, Set.mem_mul]
    simp_rw [Finset.prod_insert hi]
    simp_rw [ih]
    constructor
    · rintro ⟨x, y, hx, ⟨g, hg, rfl⟩, rfl⟩
      refine ⟨Function.update g i x, ?_, ?_⟩
      · intro j hj
        obtain rfl | hj := Finset.mem_insert.mp hj
        · rwa [Function.update_same]
        · rw [update_noteq (ne_of_mem_of_not_mem hj hi)]
          exact hg hj
      · rw [Finset.prod_update_of_not_mem hi, Function.update_same]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g i, hg (is.mem_insert_self _), is.prod g,
        ⟨⟨g, fun hi ↦ hg (Finset.mem_insert_of_mem hi), rfl⟩, rfl⟩⟩
#align set.mem_finset_prod Set.mem_finset_prod
#align set.mem_finset_sum Set.mem_finset_sum

/-- A version of `Set.mem_finset_prod` with a simpler RHS for products over a Fintype. -/
@[to_additive " A version of `Set.mem_finset_sum` with a simpler RHS for sums over a Fintype. "]
theorem mem_fintype_prod [Fintype ι] (f : ι → Set α) (a : α) :
    (a ∈ ∏ i, f i) ↔ ∃ (g : ι → α) (_ : ∀ i, g i ∈ f i), ∏ i, g i = a := by
  rw [mem_finset_prod]
  simp
#align set.mem_fintype_prod Set.mem_fintype_prod
#align set.mem_fintype_sum Set.mem_fintype_sum

/-- An n-ary version of `Set.mul_mem_mul`. -/
@[to_additive " An n-ary version of `Set.add_mem_add`. "]
theorem list_prod_mem_list_prod (t : List ι) (f : ι → Set α) (g : ι → α) (hg : ∀ i ∈ t, g i ∈ f i) :
    (t.map g).prod ∈ (t.map f).prod := by
  induction' t with h tl ih
  · simp_rw [List.map_nil, List.prod_nil, Set.mem_one]
  · simp_rw [List.map_cons, List.prod_cons]
    exact mul_mem_mul (hg h <| List.mem_cons_self _ _)
      (ih fun i hi ↦ hg i <| List.mem_cons_of_mem _ hi)
#align set.list_prod_mem_list_prod Set.list_prod_mem_list_prod
#align set.list_sum_mem_list_sum Set.list_sum_mem_list_sum

/-- An n-ary version of `Set.mul_subset_mul`. -/
@[to_additive " An n-ary version of `Set.add_subset_add`. "]
theorem list_prod_subset_list_prod (t : List ι) (f₁ f₂ : ι → Set α) (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) :
    (t.map f₁).prod ⊆ (t.map f₂).prod := by
  induction' t with h tl ih
  · rfl
  · simp_rw [List.map_cons, List.prod_cons]
    exact mul_subset_mul (hf h <| List.mem_cons_self _ _)
      (ih fun i hi ↦ hf i <| List.mem_cons_of_mem _ hi)
#align set.list_prod_subset_list_prod Set.list_prod_subset_list_prod
#align set.list_sum_subset_list_sum Set.list_sum_subset_list_sum

@[to_additive]
theorem list_prod_singleton {M : Type*} [CommMonoid M] (s : List M) :
    (s.map fun i ↦ ({i} : Set M)).prod = {s.prod} :=
  (map_list_prod (singletonMonoidHom : M →* Set M) _).symm
#align set.list_prod_singleton Set.list_prod_singleton
#align set.list_sum_singleton Set.list_sum_singleton

/-- An n-ary version of `Set.mul_mem_mul`. -/
@[to_additive " An n-ary version of `Set.add_mem_add`. "]
theorem multiset_prod_mem_multiset_prod (t : Multiset ι) (f : ι → Set α) (g : ι → α)
    (hg : ∀ i ∈ t, g i ∈ f i) : (t.map g).prod ∈ (t.map f).prod := by
  induction t using Quotient.inductionOn
  simp_rw [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.prod_coe]
  exact list_prod_mem_list_prod _ _ _ hg
#align set.multiset_prod_mem_multiset_prod Set.multiset_prod_mem_multiset_prod
#align set.multiset_sum_mem_multiset_sum Set.multiset_sum_mem_multiset_sum

/-- An n-ary version of `Set.mul_subset_mul`. -/
@[to_additive " An n-ary version of `Set.add_subset_add`. "]
theorem multiset_prod_subset_multiset_prod (t : Multiset ι) (f₁ f₂ : ι → Set α)
    (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) : (t.map f₁).prod ⊆ (t.map f₂).prod := by
  induction t using Quotient.inductionOn
  simp_rw [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.prod_coe]
  exact list_prod_subset_list_prod _ _ _ hf
#align set.multiset_prod_subset_multiset_prod Set.multiset_prod_subset_multiset_prod
#align set.multiset_sum_subset_multiset_sum Set.multiset_sum_subset_multiset_sum

@[to_additive]
theorem multiset_prod_singleton {M : Type*} [CommMonoid M] (s : Multiset M) :
    (s.map fun i ↦ ({i} : Set M)).prod = {s.prod} :=
  (map_multiset_prod (singletonMonoidHom : M →* Set M) _).symm
#align set.multiset_prod_singleton Set.multiset_prod_singleton
#align set.multiset_sum_singleton Set.multiset_sum_singleton

/-- An n-ary version of `Set.mul_mem_mul`. -/
@[to_additive " An n-ary version of `Set.add_mem_add`. "]
theorem finset_prod_mem_finset_prod (t : Finset ι) (f : ι → Set α) (g : ι → α)
    (hg : ∀ i ∈ t, g i ∈ f i) : (∏ i ∈ t, g i) ∈ ∏ i ∈ t, f i :=
  multiset_prod_mem_multiset_prod _ _ _ hg
#align set.finset_prod_mem_finset_prod Set.finset_prod_mem_finset_prod
#align set.finset_sum_mem_finset_sum Set.finset_sum_mem_finset_sum

/-- An n-ary version of `Set.mul_subset_mul`. -/
@[to_additive " An n-ary version of `Set.add_subset_add`. "]
theorem finset_prod_subset_finset_prod (t : Finset ι) (f₁ f₂ : ι → Set α)
    (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) : ∏ i ∈ t, f₁ i ⊆ ∏ i ∈ t, f₂ i :=
  multiset_prod_subset_multiset_prod _ _ _ hf
#align set.finset_prod_subset_finset_prod Set.finset_prod_subset_finset_prod
#align set.finset_sum_subset_finset_sum Set.finset_sum_subset_finset_sum

@[to_additive]
theorem finset_prod_singleton {M ι : Type*} [CommMonoid M] (s : Finset ι) (I : ι → M) :
    ∏ i ∈ s, ({I i} : Set M) = {∏ i ∈ s, I i} :=
  (map_prod (singletonMonoidHom : M →* Set M) _ _).symm
#align set.finset_prod_singleton Set.finset_prod_singleton
#align set.finset_sum_singleton Set.finset_sum_singleton

/-- The n-ary version of `Set.image_mul_prod`. -/
@[to_additive "The n-ary version of `Set.add_image_prod`. "]
theorem image_finset_prod_pi (l : Finset ι) (S : ι → Set α) :
    (fun f : ι → α => ∏ i ∈ l, f i) '' (l : Set ι).pi S = ∏ i ∈ l, S i := by
  ext
  simp_rw [mem_finset_prod, mem_image, mem_pi, exists_prop, Finset.mem_coe]
#align set.image_finset_prod_pi Set.image_finset_prod_pi
#align set.image_finset_sum_pi Set.image_finset_sum_pi

/-- A special case of `Set.image_finset_prod_pi` for `Finset.univ`. -/
@[to_additive "A special case of `Set.image_finset_sum_pi` for `Finset.univ`. "]
theorem image_fintype_prod_pi [Fintype ι] (S : ι → Set α) :
    (fun f : ι → α => ∏ i, f i) '' univ.pi S = ∏ i, S i := by
  simpa only [Finset.coe_univ] using image_finset_prod_pi Finset.univ S
#align set.image_fintype_prod_pi Set.image_fintype_prod_pi
#align set.image_fintype_sum_pi Set.image_fintype_sum_pi

end CommMonoid

/-! TODO: define `decidable_mem_finset_prod` and `decidable_mem_finset_sum`. -/


end Set
