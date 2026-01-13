/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

/-!
# Results about pointwise operations on sets and finitely supported functions.
-/

@[expose] public section


namespace Set

open Pointwise Finsupp

variable {α β : Type*} [CommMonoid β]

@[to_additive]
theorem image_pow_eq_image_finsupp_prod {f : α → β} {n} {s : Set α} :
    (f '' s) ^ n = (fun a : α →₀ ℕ ↦ a.prod fun n e ↦ f n ^ e) ''
      {x | x.sum (fun _ ↦ id) = n ∧ ↑x.support ⊆ s} := by
  ext p; simp only [mem_pow_iff_prod, mem_image, mem_setOf_eq]
  refine ⟨fun ⟨g, h, hg⟩ ↦ ?_, fun ⟨x, ⟨x_sum, x_supp⟩, hx⟩ ↦ ?_⟩
  · choose i i_in hi using h
    use ∑ j, single (i j) 1; split_ands
    · simp [← sum_finset_sum_index]
    · classical
      simpa [Set.subset_def, single_apply]
    rw [← prod_finset_sum_index (by simp) (by simp [pow_add]), ← hg]
    simp [← hi]
  let l := x.toMultiset.toList
  have hl : n = l.length := by
    rw [Multiset.length_toList, card_toMultiset, x_sum]
  use fun i ↦ f (l.get (Fin.cast hl i))
  simp only [List.get_eq_getElem, Fin.val_cast]
  refine ⟨fun _ ↦ ⟨_, x_supp ?_, rfl⟩, ?_⟩
  · rw [Finset.mem_coe, ← mem_toMultiset, ← Multiset.mem_toList]
    exact List.getElem_mem ..
  rw [← Fintype.prod_equiv (finCongr (Eq.symm hl)) (fun i ↦ f l[i]) _ (by simp)]
  simp only [Fin.getElem_fin, Fin.prod_univ_fun_getElem, Multiset.prod_map_toList, toMultiset_map,
    prod_toMultiset, l]
  rw [← hx, prod_mapDomain_index (by simp) (by simp [pow_add])]

end Set
