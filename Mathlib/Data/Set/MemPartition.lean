/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Data.Set.Finite

/-!
# Partitions based on membership of a sequence of sets

Let `f : ℕ → Set α` be a sequence of sets. For `n : ℕ`, we can form the set of points that are in
`f 0 ∪ f 1 ∪ ... ∪ f (n-1)`; then the set of points in `(f 0)ᶜ ∪ f 1 ∪ ... ∪ f (n-1)` and so on for
all 2^n choices of a set or its complement. The at most 2^n sets we obtain form a partition
of `univ : Set α`. We call that partition `memPartition f n` (the membership partition of `f`).
For `n = 0` we set `memPartition f 0 = {univ}`.

The partition `memPartition f (n + 1)` is finer than `memPartition f n`.

## Main definitions

* `memPartition f n`: the membership partition of the first `n` sets in `f`.
* `memPartitionSet`: `memPartitionSet f n x` is the set in the partition `memPartition f n` to
  which `x` belongs.

## Main statements

* `disjoint_memPartition`: the sets in `memPartition f n` are disjoint
* `sUnion_memPartition`: the union of the sets in `memPartition f n` is `univ`
* `finite_memPartition`: `memPartition f n` is finite

-/

open Set

variable {α : Type*}

/-- `memPartition f n` is the partition containing at most `2^(n+1)` sets, where each set contains
the points that for all `i` belong to one of `f i` or its complement. -/
def memPartition (f : ℕ → Set α) : ℕ → Set (Set α)
  | 0 => {univ}
  | n + 1 => {s | ∃ u ∈ memPartition f n, s = u ∩ f n ∨ s = u \ f n}

@[simp]
lemma memPartition_zero (f : ℕ → Set α) : memPartition f 0 = {univ} := rfl

lemma memPartition_succ (f : ℕ → Set α) (n : ℕ) :
    memPartition f (n + 1) = {s | ∃ u ∈ memPartition f n, s = u ∩ f n ∨ s = u \ f n} :=
  rfl

lemma disjoint_memPartition (f : ℕ → Set α) (n : ℕ) {u v : Set α}
    (hu : u ∈ memPartition f n) (hv : v ∈ memPartition f n) (huv : u ≠ v) :
    Disjoint u v := by
  revert u v
  induction n with
  | zero =>
    intro u v hu hv huv
    simp only [Nat.zero_eq, memPartition_zero, mem_insert_iff, mem_singleton_iff] at hu hv
    rw [hu, hv] at huv
    exact absurd rfl huv
  | succ n ih =>
    intro u v hu hv huv
    rw [memPartition_succ] at hu hv
    obtain ⟨u', hu', hu'_eq⟩ := hu
    obtain ⟨v', hv', hv'_eq⟩ := hv
    rcases hu'_eq with rfl | rfl <;> rcases hv'_eq with rfl | rfl
    · refine Disjoint.mono (inter_subset_left _ _) (inter_subset_left _ _) (ih hu' hv' ?_)
      exact fun huv' ↦ huv (huv' ▸ rfl)
    · exact Disjoint.mono_left (inter_subset_right _ _) Set.disjoint_sdiff_right
    · exact Disjoint.mono_right (inter_subset_right _ _) Set.disjoint_sdiff_left
    · refine Disjoint.mono (diff_subset _ _) (diff_subset _ _) (ih hu' hv' ?_)
      exact fun huv' ↦ huv (huv' ▸ rfl)

@[simp]
lemma sUnion_memPartition (f : ℕ → Set α) (n : ℕ) : ⋃₀ memPartition f n = univ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [memPartition_succ]
    ext x
    have : x ∈ ⋃₀ memPartition f n := by simp [ih]
    simp only [mem_sUnion, mem_iUnion, mem_insert_iff, mem_singleton_iff, exists_prop, mem_univ,
      iff_true] at this ⊢
    obtain ⟨t, ht, hxt⟩ := this
    by_cases hxf : x ∈ f n
    · exact ⟨t ∩ f n, ⟨t, ht, Or.inl rfl⟩, hxt, hxf⟩
    · exact ⟨t \ f n, ⟨t, ht, Or.inr rfl⟩, hxt, hxf⟩

lemma finite_memPartition (f : ℕ → Set α) (n : ℕ) : Set.Finite (memPartition f n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [memPartition_succ]
    have : Finite (memPartition f n) := Set.finite_coe_iff.mp ih
    rw [← Set.finite_coe_iff]
    simp_rw [setOf_exists, ← exists_prop, setOf_exists, setOf_or]
    refine Finite.Set.finite_biUnion (memPartition f n) _ (fun u _ ↦ ?_)
    rw [Set.finite_coe_iff]
    simp

instance instFinite_memPartition (f : ℕ → Set α) (n : ℕ) : Finite (memPartition f n) :=
  Set.finite_coe_iff.mp (finite_memPartition _ _)

noncomputable
instance instFintype_memPartition (f : ℕ → Set α) (n : ℕ) : Fintype (memPartition f n) :=
  (finite_memPartition f n).fintype

open Classical in
/-- The set in `memPartition f n` to which `a : α` belongs. -/
def memPartitionSet (f : ℕ → Set α) : ℕ → α → Set α
  | 0 => fun _ ↦ univ
  | n + 1 => fun a ↦ if a ∈ f n then memPartitionSet f n a ∩ f n else memPartitionSet f n a \ f n

@[simp]
lemma memPartitionSet_zero (f : ℕ → Set α) (a : α) : memPartitionSet f 0 a = univ := by
  simp [memPartitionSet]

lemma memPartitionSet_succ (f : ℕ → Set α) (n : ℕ) (a : α) [Decidable (a ∈ f n)] :
    memPartitionSet f (n + 1) a
      = if a ∈ f n then memPartitionSet f n a ∩ f n else memPartitionSet f n a \ f n := by
  simp [memPartitionSet]
  congr

lemma memPartitionSet_mem (f : ℕ → Set α) (n : ℕ) (a : α) :
    memPartitionSet f n a ∈ memPartition f n := by
  induction n with
  | zero => simp [memPartitionSet]
  | succ n ih =>
    classical
    rw [memPartitionSet_succ, memPartition_succ]
    refine ⟨memPartitionSet f n a, ?_⟩
    split_ifs <;> simp [ih]

lemma mem_memPartitionSet (f : ℕ → Set α) (n : ℕ) (a : α) : a ∈ memPartitionSet f n a := by
  induction n with
  | zero => simp [memPartitionSet]
  | succ n ih =>
    classical
    rw [memPartitionSet_succ]
    split_ifs with h <;> exact ⟨ih, h⟩

lemma memPartitionSet_eq_iff {f : ℕ → Set α} {n : ℕ} (a : α) {s : Set α}
    (hs : s ∈ memPartition f n) :
    memPartitionSet f n a = s ↔ a ∈ s := by
  refine ⟨fun h ↦ h ▸ mem_memPartitionSet f n a, fun h ↦ ?_⟩
  by_contra h_ne
  have h_disj : Disjoint s (memPartitionSet f n a) :=
    disjoint_memPartition f n hs (memPartitionSet_mem f n a) (Ne.symm h_ne)
  refine absurd h_disj ?_
  rw [not_disjoint_iff_nonempty_inter]
  exact ⟨a, h, mem_memPartitionSet f n a⟩

lemma memPartitionSet_of_mem {f : ℕ → Set α} {n : ℕ} {a : α} {s : Set α}
    (hs : s ∈ memPartition f n) (ha : a ∈ s) :
    memPartitionSet f n a = s :=
  (memPartitionSet_eq_iff a hs).mpr ha
