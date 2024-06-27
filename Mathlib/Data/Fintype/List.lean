/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset

#align_import data.fintype.list from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!

# Fintype instance for nodup lists

The subtype of `{l : List α // l.nodup}` over a `[Fintype α]`
admits a `Fintype` instance.

## Implementation details
To construct the `Fintype` instance, a function lifting a `Multiset α`
to the `Finset (List α)` that can construct it is provided.
This function is applied to the `Finset.powerset` of `Finset.univ`.

In general, a `DecidableEq` instance is not necessary to define this function,
but a proof of `(List.permutations l).nodup` is required to avoid it,
which is a TODO.

-/


variable {α : Type*} [DecidableEq α]

open List

namespace Multiset

/-- The `Finset` of `l : List α` that, given `m : Multiset α`, have the property `⟦l⟧ = m`.
-/
def lists : Multiset α → Finset (List α) := fun s =>
  Quotient.liftOn s (fun l => l.permutations.toFinset) fun l l' (h : l ~ l') => by
    ext sl
    simp only [mem_permutations, List.mem_toFinset]
    exact ⟨fun hs => hs.trans h, fun hs => hs.trans h.symm⟩
#align multiset.lists Multiset.lists

@[simp]
theorem lists_coe (l : List α) : lists (l : Multiset α) = l.permutations.toFinset :=
  rfl
#align multiset.lists_coe Multiset.lists_coe

@[simp]
theorem mem_lists_iff (s : Multiset α) (l : List α) : l ∈ lists s ↔ s = ⟦l⟧ := by
  induction s using Quotient.inductionOn
  simpa using perm_comm
#align multiset.mem_lists_iff Multiset.mem_lists_iff

end Multiset

instance fintypeNodupList [Fintype α] : Fintype { l : List α // l.Nodup } :=
  Fintype.subtype ((Finset.univ : Finset α).powerset.biUnion fun s => s.val.lists) fun l => by
    suffices (∃ a : Finset α, a.val = ↑l) ↔ l.Nodup by simpa
    constructor
    · rintro ⟨s, hs⟩
      simpa [← Multiset.coe_nodup, ← hs] using s.nodup
    · intro hl
      refine ⟨⟨↑l, hl⟩, ?_⟩
      simp
#align fintype_nodup_list fintypeNodupList
