/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Daniel Weber
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Finset.Density

/-!
# Results about big operators with values in a field
-/

open Fintype

variable {ι K : Type*} [DivisionSemiring K]

lemma Multiset.sum_map_div (s : Multiset ι) (f : ι → K) (a : K) :
    (s.map (fun x ↦ f x / a)).sum = (s.map f).sum / a := by
  simp only [div_eq_mul_inv, Multiset.sum_map_mul_right]

lemma Finset.sum_div (s : Finset ι) (f : ι → K) (a : K) :
    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by simp only [div_eq_mul_inv, sum_mul]

-- TODO: Move these to `Algebra.BigOperators.Group.Finset.Basic`, next to the corresponding `card`
-- lemmas, once `Finset.dens` doesn't depend on `Field` anymore.
namespace Finset
variable {α β : Type*} [Fintype β]

@[simp]
lemma dens_disjiUnion (s : Finset α) (t : α → Finset β) (h) :
    (s.disjiUnion t h).dens = ∑ a ∈ s, (t a).dens := by simp [dens, sum_div]

variable {s : Finset α} {t : α → Finset β}

lemma dens_biUnion [DecidableEq β] (h : (s : Set α).PairwiseDisjoint t) :
    (s.biUnion t).dens = ∑ u ∈ s, (t u).dens := by
  simp [dens, card_biUnion h, sum_div]

lemma dens_biUnion_le [DecidableEq β] : (s.biUnion t).dens ≤ ∑ a ∈ s, (t a).dens := by
  simp only [dens, ← sum_div]
  gcongr
  exact mod_cast card_biUnion_le

lemma dens_eq_sum_dens_fiberwise [DecidableEq α] {f : β → α} {t : Finset β}
    (h : (t : Set β).MapsTo f s) : t.dens = ∑ a ∈ s, {b ∈ t | f b = a}.dens := by
  simp [dens, ← sum_div, card_eq_sum_card_fiberwise h]

lemma dens_eq_sum_dens_image [DecidableEq α] (f : β → α) (t : Finset β) :
    t.dens = ∑ a ∈ t.image f, {b ∈ t | f b = a}.dens :=
  dens_eq_sum_dens_fiberwise fun _ ↦ mem_image_of_mem _

end Finset
