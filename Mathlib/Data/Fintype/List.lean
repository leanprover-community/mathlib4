/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.List.Permutation

/-!

# Fintype instance for nodup lists

The subtype of `{l : List α // l.Nodup}` over a `[Fintype α]`
admits a `Fintype` instance.

## Implementation details
To construct the `Fintype` instance, a function lifting a `Multiset α`
to the `Multiset (List α)` is provided.
This function is applied to the `Finset.powerset` of `Finset.univ`.

-/

@[expose] public section


variable {α : Type*}
open List

namespace Multiset

/-- Given a `m : Multiset α`, we form the `Multiset` of `l : List α` with the property `⟦l⟧ = m`. -/
def lists : Multiset α → Multiset (List α) := fun s =>
  Quotient.liftOn s (fun l => l.permutations) fun l l' (h : l ~ l') => by
    simp only
    refine coe_eq_coe.mpr ?_
    exact Perm.permutations h

@[simp]
theorem lists_coe (l : List α) : lists (l : Multiset α) = l.permutations :=
  rfl

@[simp]
theorem lists_nodup_finset (l : Finset α) : (lists (l.val)).Nodup := by
  simpa [← Finset.coe_toList] using l.nodup

@[simp]
theorem mem_lists_iff (s : Multiset α) (l : List α) : l ∈ lists s ↔ s = ⟦l⟧ := by
  induction s using Quotient.inductionOn
  simpa using perm_comm

end Multiset

instance fintypeNodupList [Fintype α] : Fintype { l : List α // l.Nodup } := by
  refine Fintype.ofFinset (p := { l : List α | l.Nodup }) ?_ ?_
  · letI univSubsets := ((Finset.univ : Finset α).powerset.1 : (Multiset (Finset α)))
    letI allPerms := Multiset.bind univSubsets (fun s => (Multiset.lists s.1))
    refine ⟨allPerms, Multiset.nodup_bind.mpr ?_⟩
    simp only [Multiset.lists_nodup_finset, implies_true, true_and]
    unfold Multiset.Pairwise
    use ((Finset.univ : Finset α).powerset.toList : (List (Finset α)))
    constructor
    · simp only [Finset.coe_toList, univSubsets]
    · convert Finset.nodup_toList (Finset.univ.powerset : Finset (Finset α))
      ext l
      unfold Nodup
      refine Pairwise.iff ?_
      intro m n
      simp only [Function.onFun]
      rw [← m.coe_toList, ← n.coe_toList, Multiset.lists_coe, Multiset.lists_coe,
        Multiset.coe_disjoint, List.disjoint_iff_ne]
      constructor
      · rintro h rfl
        refine h m.toList ?_ m.toList ?_ ?_ <;> simp
      · simp only [mem_permutations]
        rintro h a ha b hb rfl
        exact h <| Finset.perm_toList.mp <| ha.symm.trans hb
  · simp [← Multiset.coe_nodup, ← Set.mem_range, Multiset.nodup_iff_exists_finset]
