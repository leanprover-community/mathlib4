/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Multiset.Range
import Mathlib.Order.Interval.Set.Defs

/-!
# Finite sets made of a range of elements.

## Main declarations

### Finset constructions

* `Finset.range`: For any `n : ℕ`, `range n` is equal to `{0, 1, ..., n - 1} ⊆ ℕ`.
  This convention is consistent with other languages and normalizes `card (range n) = n`.
  Beware, `n` is not in `range n`.

## Tags

finite sets, finset

-/

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

open Multiset Subtype Function

/-! ### range -/


section Range

open Nat

variable {n m l : ℕ}

/-- `range n` is the set of natural numbers less than `n`. -/
def range (n : ℕ) : Finset ℕ :=
  ⟨_, nodup_range n⟩

@[simp]
theorem range_val (n : ℕ) : (range n).1 = Multiset.range n :=
  rfl

@[simp, grind =]
theorem mem_range : m ∈ range n ↔ m < n :=
  Multiset.mem_range

@[simp, grind =, norm_cast]
theorem coe_range (n : ℕ) : (range n : Set ℕ) = Set.Iio n :=
  Set.ext fun _ => mem_range

@[simp]
theorem range_zero : range 0 = ∅ :=
  rfl

@[simp]
theorem range_one : range 1 = {0} :=
  rfl

theorem range_add_one : range (n + 1) = insert n (range n) := by grind

@[deprecated range_add_one (since := "2025-09-08")]
theorem range_succ : range (succ n) = insert n (range n) := range_add_one

theorem notMem_range_self : n ∉ range n := by grind

@[deprecated (since := "2025-05-23")] alias not_mem_range_self := notMem_range_self

theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) := by grind

@[grind =]
theorem range_subset {n s} : range n ⊆ s ↔ ∀ x, x < n → x ∈ s := by grind

theorem subset_range {s n} : s ⊆ range n ↔ ∀ x, x ∈ s → x < n := by grind

@[simp]
theorem range_subset_range {n m} : range n ⊆ range m ↔ n ≤ m := by grind

theorem range_mono : Monotone range := fun _ _ => range_subset_range.2

@[gcongr] alias ⟨_, _root_.GCongr.finset_range_subset_of_le⟩ := range_subset_range

theorem mem_range_succ_iff {a b : ℕ} : a ∈ range b.succ ↔ a ≤ b := by grind

theorem mem_range_le {n x : ℕ} (hx : x ∈ range n) : x ≤ n := by grind

theorem mem_range_sub_ne_zero {n x : ℕ} (hx : x ∈ range n) : n - x ≠ 0 := by grind

@[simp, grind =]
theorem nonempty_range_iff : (range n).Nonempty ↔ n ≠ 0 :=
  ⟨fun ⟨k, hk⟩ => by grind, fun h => ⟨0, by grind⟩⟩

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Aesop.range_nonempty⟩ := nonempty_range_iff

@[simp]
theorem range_eq_empty_iff : range n = ∅ ↔ n = 0 := by
  grind [nonempty_range_iff]

@[aesop safe apply (rule_sets := [finsetNonempty])]
theorem nonempty_range_add_one : (range <| n + 1).Nonempty :=
  nonempty_range_iff.2 n.succ_ne_zero

@[deprecated nonempty_range_add_one (since := "2025-09-08")]
alias nonempty_range_succ := nonempty_range_add_one

lemma range_nontrivial {n : ℕ} (hn : 1 < n) : (range n).Nontrivial := by
  rw [Finset.Nontrivial, Finset.coe_range]
  exact ⟨0, by grind, 1, hn, Nat.zero_ne_one⟩

theorem exists_nat_subset_range (s : Finset ℕ) : ∃ n : ℕ, s ⊆ range n :=
  s.induction_on (by simp) fun a _ _ ⟨n, hn⟩ => ⟨max (a + 1) n, by grind⟩

end Range

end Finset

open Finset

/-- Equivalence between the set of natural numbers which are `≥ k` and `ℕ`, given by `n → n - k`. -/
def notMemRangeEquiv (k : ℕ) : { n // n ∉ range k } ≃ ℕ where
  toFun i := i.1 - k
  invFun j := ⟨j + k, by simp⟩
  left_inv := by grind
  right_inv := by grind

@[simp]
theorem coe_notMemRangeEquiv (k : ℕ) :
    (notMemRangeEquiv k : { n // n ∉ range k } → ℕ) = fun (i : { n // n ∉ range k }) => i - k :=
  rfl

@[simp]
theorem coe_notMemRangeEquiv_symm (k : ℕ) :
    ((notMemRangeEquiv k).symm : ℕ → { n // n ∉ range k }) = fun j => ⟨j + k, by simp⟩ :=
  rfl
