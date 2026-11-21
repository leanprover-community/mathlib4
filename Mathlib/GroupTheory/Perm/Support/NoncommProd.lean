/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
module

public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.GroupTheory.Perm.Support.Finset.Basic

/-!
# Support of a non-commutative product of permutations

This file relates `Equiv.Perm.support`, `Equiv.Perm.supportFinset` and `Equiv.Perm.Disjoint` to
`Finset.noncommProd`.

## Main statements

* `Equiv.Perm.disjoint_noncommProd_right`: a permutation disjoint from each factor of a
  `noncommProd` is disjoint from the product.
* `Equiv.Perm.support_noncommProd`, `Equiv.Perm.supportFinset_noncommProd`: the support of a
  `noncommProd` of pairwise disjoint permutations is the union of their supports.
-/

public section

open Function

namespace Equiv.Perm

variable {α ι : Type*}

section Disjoint

theorem disjoint_noncommProd_right {g : Perm α} {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ Commute (k i) (k j))
    (hg : ∀ i ∈ s, g.Disjoint (k i)) :
    g.Disjoint (s.noncommProd k hs) :=
  s.noncommProd_induction k hs g.Disjoint (fun _ _ ↦ Disjoint.mul_right) (disjoint_one_right g) hg

end Disjoint

section Support

theorem mem_support_of_mem_noncommProd_support {s : Finset ι} {k : ι → Perm α}
    {comm : (s : Set ι).Pairwise (Commute on k)} {x : α}
    (hx : x ∈ (s.noncommProd k comm).support) :
    ∃ i ∈ s, x ∈ (k i).support := by
  contrapose! hx
  classical
  revert hx comm s
  apply Finset.induction
  · simp
  · intro i s hi ih comm hs
    rw [Finset.noncommProd_insert_of_notMem s i k comm hi]
    apply mt (Set.mem_of_subset_of_mem (support_mul_subset _ _))
    rw [Set.mem_union, not_or]
    exact ⟨hs i (s.mem_insert_self i), ih (fun j hj ↦ hs j (Finset.mem_insert_of_mem hj))⟩

theorem support_noncommProd {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ (k i).Disjoint (k j)) :
    (s.noncommProd k (hs.imp (fun _ _ ↦ Perm.Disjoint.commute))).support =
      ⋃ i ∈ s, (k i).support := by
  classical
  induction s using Finset.induction_on with
  | empty => ext; simp
  | insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j ↦ (k i).Disjoint (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    have H : (k i).Disjoint (s.noncommProd k _) := disjoint_noncommProd_right
      (hs'.imp (fun _ _ ↦ Perm.Disjoint.commute)) (fun j hj => by
        apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or])
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi, H.support_mul, hrec hs']
    ext; simp

end Support

section SupportFinset

variable [DecidableEq α] [Fintype α]

theorem mem_supportFinset_of_mem_noncommProd_supportFinset {s : Finset ι}
    {k : ι → Perm α} {comm : (s : Set ι).Pairwise (Commute on k)} {x : α}
    (hx : x ∈ (s.noncommProd k comm).supportFinset) :
    ∃ i ∈ s, x ∈ (k i).supportFinset := by
  simpa using mem_support_of_mem_noncommProd_support (by simpa using hx)

theorem supportFinset_noncommProd {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ (k i).Disjoint (k j)) :
    (s.noncommProd k (hs.imp (fun _ _ ↦ Perm.Disjoint.commute))).supportFinset =
      s.biUnion fun i ↦ (k i).supportFinset := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j ↦ (k i).Disjoint (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi, Finset.biUnion_insert]
    rw [Equiv.Perm.Disjoint.supportFinset_mul, hrec hs']
    apply disjoint_noncommProd_right
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]

end SupportFinset

end Equiv.Perm
