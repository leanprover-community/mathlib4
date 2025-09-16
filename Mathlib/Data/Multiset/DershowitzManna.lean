/-
Copyright (c) 2024 Haitian Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haitian Wang, Malvin Gattinger
-/
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Data.Multiset.OrderedMonoid

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
  rw [add_comm X₁,add_comm X₂] at hXZXY
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

/-- A special case of `IsDershowitzMannaLT`. The transitive closure of it is used to define
an equivalent (proved later) version of the ordering. -/
private def OneStep (M N : Multiset α) : Prop :=
  ∃ X Y a,
      M = X + Y
    ∧ N = X + {a}
    ∧ ∀ y ∈ Y, y < a

private lemma isDershowitzMannaLT_of_oneStep : OneStep M N → IsDershowitzMannaLT M N := by
  rintro ⟨X, Y, a, M_def, N_def, ys_lt_a⟩
  use X, Y, {a}, by simp, M_def, N_def
  · simpa

private lemma isDershowitzMannaLT_singleton_insert (h : OneStep N (a ::ₘ M)) :
    ∃ M', N = a ::ₘ M' ∧ OneStep M' M ∨ N = M + M' ∧ ∀ x ∈ M', x < a := by
  classical
  obtain ⟨X, Y, b, rfl, h0, h2⟩ := h
  obtain rfl | hab := eq_or_ne a b
  · refine ⟨Y, .inr ⟨?_, h2⟩⟩
    simpa [add_comm _ {a}, singleton_add, eq_comm] using h0
  refine ⟨Y + (M - {b}), .inl ⟨?_, M - {b}, Y, b, add_comm .., ?_, h2⟩⟩
  · rw [← singleton_add, add_comm] at h0
    rw [tsub_eq_tsub_of_add_eq_add h0, add_comm Y, ← singleton_add, ← add_assoc,
      add_tsub_cancel_of_le]
    have : a ∈ X + {b} := by simp [← h0]
    simpa [hab] using this
  · rw [tsub_add_cancel_of_le]
    have : b ∈ a ::ₘ M := by simp [h0]
    simpa [hab.symm] using this

private lemma acc_oneStep_cons_of_acc_lt (ha : Acc LT.lt a) :
    ∀ {M}, Acc OneStep M → Acc OneStep (a ::ₘ M) := by
  induction ha with | _ a _ ha
  rintro M hM
  induction hM with | _ M hM ihM
  refine .intro _ fun N hNM ↦ ?_
  obtain ⟨N, ⟨rfl, hNM'⟩ | ⟨rfl, hN⟩⟩ := isDershowitzMannaLT_singleton_insert hNM
  · exact ihM _ hNM'
  clear hNM
  induction N using Multiset.induction with
  | empty =>
    simpa using .intro _ hM
  | @cons b N ihN =>
    simp only [mem_cons, forall_eq_or_imp, add_cons] at hN ⊢
    obtain ⟨hba, hN⟩ := hN
    exact ha _ hba <| ihN hN

/-- If all elements of a multiset `M` are accessible with `<`, then the multiset `M` is
accessible given the `OneStep` relation. -/
private lemma acc_oneStep_of_acc_lt (hM : ∀ x ∈ M, Acc LT.lt x) : Acc OneStep M := by
  induction M using Multiset.induction_on with
  | empty =>
    constructor
    simp [OneStep, eq_comm (b := _ + _)]
  | cons a M ih =>
    exact acc_oneStep_cons_of_acc_lt (hM _ <| mem_cons_self ..) <| ih fun x hx ↦
      hM _ <| mem_cons_of_mem hx

/-- Over a well-founded order, `OneStep` is well-founded. -/
private lemma isDershowitzMannaLT_singleton_wf [WellFoundedLT α] :
    WellFounded (OneStep : Multiset α → Multiset α → Prop) :=
  ⟨fun _M ↦ acc_oneStep_of_acc_lt fun a _ ↦ WellFoundedLT.apply a⟩

private lemma transGen_oneStep_of_isDershowitzMannaLT :
    IsDershowitzMannaLT M N → TransGen OneStep M N := by
  classical
  rintro ⟨X, Y, Z, hZ, hM, hN, hYZ⟩
  induction Z using Multiset.induction_on generalizing X Y M N with
  | empty => simp at hZ
  | cons z Z ih => ?_
  obtain rfl | hZ := eq_or_ne Z 0
  · exact .single ⟨X, Y, z, hM, hN, by simpa using hYZ⟩
  let Y' : Multiset α := Y.filter (· < z)
  refine .tail (b := X + Y' + Z) (ih (X + Y') (Y - Y') hZ ?_ rfl fun y hy ↦ ?_) <|
    ⟨X + Z, Y', z, add_right_comm .., by simp [hN, add_comm (_ + _)], by simp [Y']⟩
  · rw [add_add_tsub_cancel (filter_le ..), hM]
  · simp only [sub_filter_eq_filter_not, mem_filter, Y'] at hy
    simpa [hy.2] using hYZ y (by simp_all)

private lemma isDershowitzMannaLT_of_transGen_oneStep (hMN : TransGen OneStep M N) :
    IsDershowitzMannaLT M N :=
  hMN.trans_induction_on (by rintro _ _ ⟨X, Y, a, rfl, rfl, hYa⟩; exact ⟨X, Y, {a}, by simpa⟩)
    fun  _ _ ↦ .trans

/-- `TransGen OneStep` and `IsDershowitzMannaLT` are equivalent. -/
private lemma transGen_oneStep_eq_isDershowitzMannaLT :
    (TransGen OneStep : Multiset α → Multiset α → Prop) = IsDershowitzMannaLT := by
  ext M N
  exact ⟨isDershowitzMannaLT_of_transGen_oneStep, transGen_oneStep_of_isDershowitzMannaLT⟩

/-- Over a well-founded order, the Dershowitz-Manna order on multisets is well-founded. -/
theorem wellFounded_isDershowitzMannaLT [WellFoundedLT α] :
    WellFounded (IsDershowitzMannaLT : Multiset α → Multiset α → Prop) := by
  rw [← transGen_oneStep_eq_isDershowitzMannaLT]
  exact isDershowitzMannaLT_singleton_wf.transGen

instance instWellFoundedIsDershowitzMannaLT [WellFoundedLT α] : WellFoundedRelation (Multiset α) :=
    ⟨IsDershowitzMannaLT, wellFounded_isDershowitzMannaLT⟩

end Multiset
