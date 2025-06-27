/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.List.Permutation

/-!

# Fintype instance for nodup lists

The subtype of `{l : List α // l.Nodup}` over a `[Fintype α]`
admits a `Fintype` instance.

## Implementation details
To construct the `Fintype` instance, a function lifting a `Multiset α`
to the `Multiset (List α)` is provided.
This function is applied to the `Finset.powerset` of `Finset.univ`.

-/


variable {α : Type*}
open List

namespace Multiset

/-- Given a `m : Multiset α`, we form the `Multiset` of `l : List α` with the property `⟦l⟧ = m`. -/
def lists : Multiset α → Multiset (List α) := fun s =>
  Quotient.liftOn s (fun l => l.permutations) fun l l' (h : l ~ l') => by
    simp only [mem_permutations, List.mem_toFinset]
    refine coe_eq_coe.mpr ?_
    exact Perm.permutations h

@[simp]
theorem lists_coe (l : List α) : lists (l : Multiset α) = l.permutations :=
  rfl

@[simp]
theorem lists_nodup_finset (l : Finset α) : (lists (l.val)).Nodup := by
  have h_nodup : l.val.Nodup := l.nodup
  rw [← Finset.coe_toList l, Multiset.coe_nodup] at h_nodup
  rw [← Finset.coe_toList l]
  exact nodup_permutations l.val.toList (h_nodup)

@[simp]
theorem mem_lists_iff (s : Multiset α) (l : List α) : l ∈ lists s ↔ s = ⟦l⟧ := by
  induction s using Quotient.inductionOn
  simpa using perm_comm

end Multiset

@[simp]
theorem perm_toList {f₁ f₂ : Finset α} : f₁.toList ~ f₂.toList ↔ f₁ = f₂ :=
  ⟨fun h => Finset.ext_iff.mpr (fun x => by simpa [← Finset.mem_toList] using Perm.mem_iff h),
   fun h ↦ Perm.of_eq <| congrArg Finset.toList h⟩

instance fintypeNodupList [Fintype α] : Fintype { l : List α // l.Nodup } := by
  refine Fintype.ofFinset ?_ ?_
  · let univSubsets := ((Finset.univ : Finset α).powerset.1 : (Multiset (Finset α)))
    let allPerms := Multiset.bind univSubsets (fun s => (Multiset.lists s.1))
    refine ⟨allPerms, Multiset.nodup_bind.mpr ?_⟩
    simp only [Multiset.lists_nodup_finset, implies_true, true_and]
    unfold Multiset.Pairwise
    use ((Finset.univ : Finset α).powerset.toList : (List (Finset α)))
    constructor
    · simp only [Finset.coe_toList]
      rfl
    · convert Finset.nodup_toList (Finset.univ.powerset : Finset (Finset α))
      ext l
      unfold Nodup
      refine Pairwise.iff ?_
      intro m n
      simp only [_root_.Disjoint]
      rw [← m.coe_toList, ← n.coe_toList, Multiset.lists_coe, Multiset.lists_coe]
      have := Multiset.coe_disjoint m.toList.permutations n.toList.permutations
      rw  [_root_.Disjoint] at this
      rw [this]
      simp only [Multiset.coe_disjoint, ne_eq]
      rw [List.disjoint_iff_ne]
      constructor
      · intro h
        by_contra hc
        rw [hc] at h
        contrapose! h
        use n.toList
        simp
      · intro h
        simp only [mem_permutations]
        intro a ha b hb
        by_contra hab
        absurd h
        rw [hab] at ha
        exact perm_toList.mp <| Perm.trans (id (Perm.symm ha)) hb
  · intro l
    simp only [Finset.mem_mk, Multiset.mem_bind, Finset.mem_val, Finset.mem_powerset,
      Finset.subset_univ, Multiset.mem_lists_iff, Multiset.quot_mk_to_coe, true_and]
    constructor
    · intro h
      rcases h with ⟨f, hf⟩
      convert f.nodup
      rw [hf]
      rfl
    · intro h
      exact CanLift.prf _ h
