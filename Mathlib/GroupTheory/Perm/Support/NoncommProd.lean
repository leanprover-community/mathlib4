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
-/

public section

open Equiv Finset Function

namespace Equiv.Perm

variable {α : Type*} {g : Perm α}

theorem disjoint_noncommProd_right {ι : Type*} {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ Commute (k i) (k j))
    (hg : ∀ i ∈ s, g.Disjoint (k i)) :
    Disjoint g (s.noncommProd k (hs)) :=
  noncommProd_induction s k hs g.Disjoint (fun _ _ ↦ Disjoint.mul_right) (disjoint_one_right g) hg

section supportFinset

variable [DecidableEq α] [Fintype α]

theorem mem_supportFinset_of_mem_noncommProd_supportFinset {α β : Type*} [DecidableEq β] [Fintype β]
    {s : Finset α} {f : α → Perm β}
    {comm : (s : Set α).Pairwise (Commute on f)} {x : β}
        (hx : x ∈ (s.noncommProd f comm).supportFinset) :
    ∃ a ∈ s, x ∈ (f a).supportFinset := by
  contrapose! hx
  classical
  revert hx comm s
  apply Finset.induction
  · simp
  · intro a s ha ih comm hs
    rw [Finset.noncommProd_insert_of_notMem s a f comm ha]
    apply mt (Finset.mem_of_subset (supportFinset_mul_subset _ _))
    rw [Finset.notMem_union]
    exact ⟨hs a (s.mem_insert_self a), ih (fun a ha ↦ hs a (Finset.mem_insert_of_mem ha))⟩

@[deprecated (since := "2026-11-16")] alias mem_support_of_mem_noncommProd_support :=
    mem_supportFinset_of_mem_noncommProd_supportFinset

theorem supportFinset_noncommProd {ι : Type*} {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ Disjoint (k i) (k j)) :
    (s.noncommProd k (hs.imp (fun _ _ ↦ Perm.Disjoint.commute))).supportFinset =
      s.biUnion fun i ↦ (k i).supportFinset := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j ↦ Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi, Finset.biUnion_insert]
    rw [Equiv.Perm.Disjoint.supportFinset_mul, hrec hs']
    apply disjoint_noncommProd_right
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]

@[deprecated (since := "2026-11-16")] alias support_noncommProd := supportFinset_noncommProd

end supportFinset

end Equiv.Perm
