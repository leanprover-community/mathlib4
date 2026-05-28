/-
Copyright (c) 2024 Haitian Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haitian Wang, Malvin Gattinger
-/
module

public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Data.Multiset.OrderedMonoid

import Mathlib.Logic.Hydra

/-!
# Dershowitz-Manna ordering

In this file we define the _Dershowitz-Manna ordering_ on multisets. Specifically, for two multisets
`M` and `N` in a partial order `(S, <)`, `M` is smaller than `N` in the Dershowitz-Manna ordering if
`M` can be obtained from `N` by replacing one or more elements in `N` by some finite number of
elements from `S`, each of which is smaller (in the underling ordering over `S`) than one of the
replaced elements from `N`. We prove that, given a well-founded partial order on the underlying set,
the Dershowitz-Manna ordering defined over multisets is also well-founded.

## Main results

- `Multiset.IsDershowitzMannaLT` : the standard definition of the `Dershowitz-Manna ordering`.
- `Multiset.wellFounded_isDershowitzMannaLT` : the main theorem about the
  `Dershowitz-Manna ordering` being well-founded.

## References

* [Wikipedia, Dershowitz–Manna ordering](https://en.wikipedia.org/wiki/Dershowitz%E2%80%93Manna_ordering)

* [CoLoR](https://github.com/fblanqui/color), a Coq library on rewriting theory and termination.
  Our code here is inspired by their formalization and the theorem is called `mOrd_wf` in the file
  [MultisetList.v](https://github.com/fblanqui/color/blob/1.8.5/Util/Multiset/MultisetOrder.v).

-/

@[expose] public section

open Relation

namespace Multiset

variable {α : Type*} [Preorder α] {M N P : Multiset α} {a : α}

/-- The standard Dershowitz–Manna ordering. -/
def IsDershowitzMannaLT (M N : Multiset α) : Prop :=
  ∃ X Y Z,
      Z ≠ ∅
    ∧ M = X + Y
    ∧ N = X + Z
    ∧ ∀ y ∈ Y, ∃ z ∈ Z, y < z

/-- `IsDershowitzMannaLT` is transitive. -/
lemma IsDershowitzMannaLT.trans :
    IsDershowitzMannaLT M N → IsDershowitzMannaLT N P → IsDershowitzMannaLT M P := by
  classical
  rintro ⟨X₁, Y₁, Z₁, -, rfl, rfl, hYZ₁⟩ ⟨X₂, Y₂, Z₂, hZ₂, hXZXY, rfl, hYZ₂⟩
  rw [add_comm X₁, add_comm X₂] at hXZXY
  refine ⟨X₁ ∩ X₂, Y₁ + (Y₂ - Z₁), Z₂ + (Z₁ - Y₂), ?_, ?_, ?_, ?_⟩
  · simpa [-not_and, not_and_or] using .inl hZ₂
  · rwa [← add_assoc, add_right_comm, inter_add_sub_of_add_eq_add]
  · rw [← add_assoc, add_right_comm, add_left_inj, inter_comm, inter_add_sub_of_add_eq_add]
    rwa [eq_comm]
  simp only [mem_add, or_imp, forall_and]
  refine ⟨fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨z, hz, hyz⟩ := hYZ₁ y hy
    by_cases z_in : z ∈ Y₂
    · obtain ⟨w, hw, hzw⟩ := hYZ₂ z z_in
      exact ⟨w, .inl hw, hyz.trans hzw⟩
    · exact ⟨z, .inr <| by rwa [mem_sub, count_eq_zero_of_notMem z_in, count_pos], hyz⟩
  · obtain ⟨z, hz, hyz⟩ := hYZ₂ y <| mem_of_le (Multiset.sub_le_self ..) hy
    exact ⟨z, .inl hz, hyz⟩

private lemma transGen_cutExpand_of_isDershowitzMannaLT :
    IsDershowitzMannaLT M N → TransGen (CutExpand (· < ·)) M N := by
  classical
  rintro ⟨X, Y, Z, hZ, hM, hN, hYZ⟩
  induction Z using Multiset.induction_on generalizing X Y M N with
  | empty => simp at hZ
  | cons z Z ih => ?_
  obtain rfl | hZ := eq_or_ne Z 0
  · subst hM hN
    apply TransGen.single
    rw [cutExpand_add_left]
    exact cutExpand_singleton <| by simpa using hYZ
  let Y' : Multiset α := Y.filter (· < z)
  refine .tail (b := X + Y' + Z) (ih (X + Y') (Y - Y') hZ ?_ rfl fun y hy ↦ ?_) ?_
  · rw [add_add_tsub_cancel (filter_le ..), hM]
  · simp only [sub_filter_eq_filter_not, mem_filter, Y'] at hy
    simpa [hy.2] using hYZ y (by simp_all)
  · subst hN
    rw [add_assoc, cutExpand_add_left, ← singleton_add, cutExpand_add_right]
    exact cutExpand_singleton <| by simp [Y']

private lemma isDershowitzMannaLT_of_transGen_cutExpand (hMN : TransGen (CutExpand (· < ·)) M N) :
    IsDershowitzMannaLT M N := by
  refine hMN.trans_induction_on (fun {a b} hab => ?_) fun _ _ ↦ .trans
  classical
  obtain ⟨s, x, hsx, hxb, hab⟩ := cutExpand_iff.1 hab
  exact ⟨b.erase x, s, {x}, singleton_ne_zero x, hab,
    (add_singleton_eq_iff.2 ⟨hxb, rfl⟩).symm, fun y hy => ⟨x, mem_singleton_self x, hsx y hy⟩⟩

/-- `TransGen (CutExpand (· < ·))` and `IsDershowitzMannaLT` are equivalent. -/
private lemma transGen_cutExpand_eq_isDershowitzMannaLT :
    (TransGen (CutExpand (· < ·)) : Multiset α → Multiset α → Prop) = IsDershowitzMannaLT := by
  ext M N
  exact ⟨isDershowitzMannaLT_of_transGen_cutExpand, transGen_cutExpand_of_isDershowitzMannaLT⟩

/-- Over a well-founded order, the Dershowitz-Manna order on multisets is well-founded. -/
theorem wellFounded_isDershowitzMannaLT [WellFoundedLT α] :
    WellFounded (IsDershowitzMannaLT : Multiset α → Multiset α → Prop) := by
  rw [← transGen_cutExpand_eq_isDershowitzMannaLT]
  exact wellFounded_lt.cutExpand.transGen

instance instWellFoundedIsDershowitzMannaLT [WellFoundedLT α] : WellFoundedRelation (Multiset α) :=
    ⟨IsDershowitzMannaLT, wellFounded_isDershowitzMannaLT⟩

end Multiset
