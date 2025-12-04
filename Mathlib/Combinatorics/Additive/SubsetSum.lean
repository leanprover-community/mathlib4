/-
Copyright (c) 2025 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset

/-!
# Subset sums

This file defines the subset sum of a finite subset of a commutative monoid.

## References

* [Melvyn B. Nathanson, *Inverse theorems for subset sums*][Nathanson1995]
-/

public section

open scoped Pointwise

namespace Finset
variable {M : Type*} [DecidableEq M] [AddCommMonoid M] {A : Finset M} {a : M}

/-- The subset-sum of a finite set `A` in a commutative monoid is the set of all sums
of subsets of `A`. -/
def subsetSum (A : Finset M) : Finset M := A.powerset.image fun S ↦ S.sum id

@[simp]
lemma mem_subsetSum_iff : a ∈ A.subsetSum ↔ ∃ B ⊆ A, ∑ b ∈ B, b = a := by simp [subsetSum]

lemma subsetSum_zero_mem : 0 ∈ A.subsetSum :=
  mem_subsetSum_iff.mpr ⟨∅, empty_subset _, sum_empty⟩

lemma subset_subsetSum : A ⊆ A.subsetSum :=
  fun a ha => mem_subsetSum_iff.mpr ⟨{a}, by simp [ha]⟩

@[gcongr]
lemma subsetSum_mono {B : Finset M} (hAB : A ⊆ B) : A.subsetSum ⊆ B.subsetSum :=
  image_mono _ <| powerset_mono.mpr hAB

@[simp] lemma subsetSum_erase_zero : (A.erase 0).subsetSum = A.subsetSum := by
  refine le_antisymm (subsetSum_mono (erase_subset _ _)) fun x hx => ?_
  obtain ⟨S, hS, rfl⟩ := mem_subsetSum_iff.mp hx
  refine mem_subsetSum_iff.mpr ⟨S.erase 0, ?_, sum_erase _ (by simp)⟩
  exact fun i hi => mem_erase.mpr ⟨(mem_erase.mp hi).1, hS (mem_of_mem_erase hi)⟩

lemma vadd_finset_subsetSum_subset_subsetSum_insert (a_notin_A : a ∉ A) :
    a +ᵥ A.subsetSum ⊆ (insert a A).subsetSum := by
  simp_rw [subset_iff, mem_vadd_finset, mem_subsetSum_iff]
  rintro _ ⟨_, ⟨S, hS, rfl⟩, rfl⟩
  exact ⟨insert a S, by aesop, by rw [sum_insert (fun h => a_notin_A (hS h))]; simp⟩

variable [LinearOrder M] [IsOrderedCancelAddMonoid M]

lemma subsetSum_nonneg_of_nonneg (A_nonneg : ∀ x ∈ A, 0 ≤ x) : ∀ x ∈ A.subsetSum, 0 ≤ x := by
  intro _ hx
  obtain ⟨S, hS, rfl⟩ := mem_subsetSum_iff.mp hx
  exact sum_induction _ (0 ≤ ·) (fun _ _ => add_nonneg) (le_refl 0) fun a ha => A_nonneg a (hS ha)

lemma card_subsetSum_of_pos_insert_max (A_pos : ∀ x ∈ A, 0 < x) (A_lt_a : ∀ x ∈ A, x < a)
    (zero_ls_a : 0 < a) :
    #A + 1 + #A.subsetSum ≤ #(insert a A).subsetSum := by
  -- We show that (insert 0 A) and a +ᵥ A.subsetSum are disjoint subsets
  -- of (insert a A).subsetSum, and their combined cardinality gives the result.

  -- The disjointness
  have disjoint : Disjoint (insert 0 A) (a +ᵥ A.subsetSum) := by
    refine disjoint_insert_left.mpr ⟨?_, disjoint_left.mpr fun x hxA hy => ?_⟩
    · simp only [mem_vadd_finset, vadd_eq_add, not_exists, not_and]
      exact fun b hb h => (add_pos_of_nonneg_of_pos
        (subsetSum_nonneg_of_nonneg (fun x hx => (A_pos x hx).le) b hb) zero_ls_a).ne
        (add_comm a b ▸ h.symm)
    · obtain ⟨b, hb, rfl⟩ := mem_vadd_finset.mp hy
      simp only [vadd_eq_add, add_comm a b] at hxA ⊢
      exact (A_lt_a _ hxA).not_ge (le_add_of_nonneg_left
        (subsetSum_nonneg_of_nonneg (fun x hx => (A_pos x hx).le) b hb))
  -- Both sets are subsets of (insert a A).subsetSum
  have insert_subset : insert 0 A ⊆ (insert a A).subsetSum :=
    insert_subset subsetSum_zero_mem
      (subset_subsetSum.trans (subsetSum_mono (subset_insert a A)))
  have vadd_subset : a +ᵥ A.subsetSum ⊆ (insert a A).subsetSum :=
    vadd_finset_subsetSum_subset_subsetSum_insert fun ha => (A_lt_a a ha).false
  -- Count the sizes
  calc #A + 1 + #A.subsetSum
    _ = #(insert 0 A) + #A.subsetSum := by
        rw [card_insert_of_notMem fun h => (A_pos 0 h).false]
    _ = #(insert 0 A) + #(a +ᵥ A.subsetSum) := by
        simp only [vadd_finset_def, vadd_eq_add, card_image_of_injOn fun _ _ _ _ => add_left_cancel]
    _ = #((insert 0 A) ∪ (a +ᵥ A.subsetSum)) := by rw [card_union_of_disjoint disjoint]
    _ ≤ #(insert a A).subsetSum := card_le_card (union_subset insert_subset vadd_subset)

-- The proof follows Theorem 3 in [Nathanson1995].
theorem card_succ_choose_two_succ_le_card_subsetSum_of_pos (A_pos : ∀ x ∈ A, 0 < x) :
    (#A + 1).choose 2 + 1 ≤ #A.subsetSum := by
  induction A using induction_on_max with
  | h0 => rfl
  | step a A A_lt_a ih =>
    have A_pos' : ∀ x ∈ A, 0 < x := fun x hx => A_pos x (mem_insert_of_mem hx)
    rw [card_insert_of_notMem fun ha => (A_lt_a a ha).false]
    calc ((#A + 1) + 1).choose 2 + 1
      _ = (#A + 1).choose 1 + (#A + 1).choose 2 + 1 := by rw [Nat.choose_succ_left]; omega
      _ = #A + 1 + (#A + 1).choose 2 + 1 := by rw [Nat.choose_one_right]
      _ ≤ #A + 1 + #A.subsetSum := Nat.add_le_add_left (ih A_pos') _
      _ ≤ #(insert a A).subsetSum :=
          card_subsetSum_of_pos_insert_max A_pos' A_lt_a (A_pos a (mem_insert_self a A))

theorem card_choose_two_succ_le_card_subsetSum_of_nonneg (A_pos : ∀ x ∈ A, 0 ≤ x) :
    (#A).choose 2 + 1 ≤ #A.subsetSum := by
  have _ := pred_card_le_card_erase (s := A) (a := 0)
  calc (#A).choose 2 + 1
    _ ≤ (#(A.erase 0) + 1).choose 2 + 1 := Nat.add_le_add_right (Nat.choose_mono 2 (by omega)) 1
    _ ≤ #(A.erase 0).subsetSum :=
        card_succ_choose_two_succ_le_card_subsetSum_of_pos fun x hx =>
          (A_pos x (mem_of_mem_erase hx)).lt_of_ne (ne_of_mem_erase hx).symm
    _ = #A.subsetSum := by rw [subsetSum_erase_zero]

end Finset
