/-
Copyright (c) 2024 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.SetTheory.ZFC.Basic

/-!
# Ordinal ranks of PSet and ZFSet

In this file, we define the ordinal ranks of `PSet` and `ZFSet`. These ranks are the same as
`IsWellFounded.rank` over `∈`, but are defined in a way that the universe levels of ranks are the
same as the indexing types.

## Definitions

* `PSet.rank`: Ordinal rank of a pre-set.
* `ZFSet.rank`: Ordinal rank of a ZFC set.
-/

@[expose] public section

universe u v

open Ordinal Order

/-! ### PSet rank -/

namespace PSet

/-- The ordinal rank of a pre-set -/
noncomputable def rank : PSet.{u} → Ordinal.{u}
  | ⟨_, A⟩ => ⨆ a, succ (rank (A a))

theorem rank_congr : ∀ {x y : PSet}, Equiv x y → rank x = rank y
  | ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ => by
    apply congr_arg sSup
    ext
    constructor <;> simp only [Set.mem_range, forall_exists_index] <;> intro a h
    · obtain ⟨b, h'⟩ := αβ a
      exists b
      rw [← h, rank_congr h']
    · obtain ⟨b, h'⟩ := βα a
      exists b
      rw [← h, rank_congr h']

theorem rank_lt_of_mem : ∀ {x y : PSet}, y ∈ x → rank y < rank x
  | ⟨_, _⟩, _, ⟨_, h⟩ => by
    rw [rank_congr h, ← succ_le_iff]
    apply Ordinal.le_iSup

theorem rank_le_iff {o : Ordinal} : ∀ {x : PSet}, rank x ≤ o ↔ ∀ ⦃y⦄, y ∈ x → rank y < o
  | ⟨_, A⟩ => by
    refine ⟨fun h _ h' => (rank_lt_of_mem h').trans_le h, fun h ↦ Ordinal.iSup_le fun a ↦ ?_⟩
    rw [succ_le_iff]
    exact h (Mem.mk A a)

theorem lt_rank_iff {o : Ordinal} {x : PSet} : o < rank x ↔ ∃ y ∈ x, o ≤ rank y := by
  contrapose!; exact rank_le_iff

variable {x y : PSet.{u}}

@[gcongr] theorem rank_mono (h : x ⊆ y) : rank x ≤ rank y :=
  rank_le_iff.2 fun _ h₁ => rank_lt_of_mem (mem_of_subset h h₁)

@[simp]
theorem rank_empty : rank ∅ = 0 := by simp [empty_def, rank]

@[simp]
theorem rank_insert (x y : PSet) : rank (insert x y) = max (succ (rank x)) (rank y) := by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_insert_iff]
    rintro _ (h | h)
    · simp [rank_congr h]
    · simp [rank_lt_of_mem h]
  · apply max_le
    · exact (rank_lt_of_mem (mem_insert x y)).succ_le
    · exact rank_mono (subset_iff.2 fun z => mem_insert_of_mem x)

@[simp]
theorem rank_singleton (x : PSet) : rank {x} = succ (rank x) :=
  (rank_insert _ _).trans (by simp)

theorem rank_pair (x y : PSet) : rank {x, y} = max (succ (rank x)) (succ (rank y)) := by
  simp

@[simp]
theorem rank_powerset (x : PSet) : rank (powerset x) = succ (rank x) := by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_powerset, lt_succ_iff]
    intro
    exact rank_mono
  · rw [succ_le_iff]
    apply rank_lt_of_mem
    simp

/-- For the rank of `⋃₀ x`, we only have `rank (⋃₀ x) ≤ rank x ≤ rank (⋃₀ x) + 1`.

This inequality is split into `rank_sUnion_le` and `le_succ_rank_sUnion`. -/
theorem rank_sUnion_le (x : PSet) : rank (⋃₀ x) ≤ rank x := by
  simp_rw [rank_le_iff, mem_sUnion]
  intro _ ⟨_, _, _⟩
  trans <;> apply rank_lt_of_mem <;> assumption

theorem le_succ_rank_sUnion (x : PSet) : rank x ≤ succ (rank (⋃₀ x)) := by
  rw [← rank_powerset]
  apply rank_mono
  rw [subset_iff]
  intro z _
  rw [mem_powerset, subset_iff]
  intro _ _
  rw [mem_sUnion]
  exists z

/-- `PSet.rank` is equal to the `IsWellFounded.rank` over `∈`. -/
theorem rank_eq_wfRank : lift.{u + 1, u} (rank x) = IsWellFounded.rank (α := PSet) (· ∈ ·) x := by
  induction x using mem_wf.induction with | _ x ih
  rw [IsWellFounded.rank_eq]
  simp_rw [← fun y : { y // y ∈ x } => ih y y.2]
  apply (le_of_forall_lt _).antisymm (Ordinal.iSup_le _) <;> intro h
  · rw [lt_lift_iff]
    rintro ⟨o, h, rfl⟩
    simpa [Ordinal.lt_iSup_iff] using lt_rank_iff.1 h
  · simpa using rank_lt_of_mem h.2

end PSet

/-! ### ZFSet rank -/

namespace ZFSet

variable {x y : ZFSet.{u}}

/-- The ordinal rank of a ZFC set -/
noncomputable def rank : ZFSet.{u} → Ordinal.{u} :=
  Quotient.lift _ fun _ _ => PSet.rank_congr

@[simp]
theorem rank_mk (x : PSet) : rank (.mk x) = x.rank :=
  rfl

theorem rank_lt_of_mem : y ∈ x → rank y < rank x :=
  Quotient.inductionOn₂ x y fun _ _ => PSet.rank_lt_of_mem

theorem rank_le_iff {o : Ordinal} : rank x ≤ o ↔ ∀ ⦃y⦄, y ∈ x → rank y < o :=
  ⟨fun h _ h' => (rank_lt_of_mem h').trans_le h,
    Quotient.inductionOn x fun _ h =>
      PSet.rank_le_iff.2 fun y h' => @h ⟦y⟧ h'⟩

theorem lt_rank_iff {o : Ordinal} : o < rank x ↔ ∃ y ∈ x, o ≤ rank y := by
  contrapose!; exact rank_le_iff

@[gcongr] theorem rank_mono (h : x ⊆ y) : rank x ≤ rank y :=
  rank_le_iff.2 fun _ h₁ => rank_lt_of_mem (h h₁)

@[simp]
theorem rank_empty : rank ∅ = 0 := PSet.rank_empty

@[simp]
theorem rank_insert (x y : ZFSet) : rank (insert x y) = max (succ (rank x)) (rank y) :=
  Quotient.inductionOn₂ x y PSet.rank_insert

@[simp]
theorem rank_singleton (x : ZFSet) : rank {x} = succ (rank x) :=
  (rank_insert _ _).trans (by simp)

theorem rank_pair (x y : ZFSet) : rank {x, y} = max (succ (rank x)) (succ (rank y)) := by
  simp

@[simp]
theorem rank_union (x y : ZFSet) : rank (x ∪ y) = max (rank x) (rank y) := by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_union, lt_max_iff]
    intro
    apply Or.imp <;> apply rank_lt_of_mem
  · apply max_le <;> apply rank_mono <;> intro _ h <;> simp [h]

@[simp]
theorem rank_powerset (x : ZFSet) : rank (powerset x) = succ (rank x) :=
  Quotient.inductionOn x PSet.rank_powerset

/-- For the rank of `⋃₀ x`, we only have `rank (⋃₀ x) ≤ rank x ≤ rank (⋃₀ x) + 1`.

This inequality is split into `rank_sUnion_le` and `le_succ_rank_sUnion`. -/
theorem rank_sUnion_le (x : ZFSet) : rank (⋃₀ x) ≤ rank x := by
  simp_rw [rank_le_iff, mem_sUnion]
  intro _ ⟨_, _, _⟩
  trans <;> apply rank_lt_of_mem <;> assumption

theorem le_succ_rank_sUnion (x : ZFSet) : rank x ≤ succ (rank (⋃₀ x)) := by
  rw [← rank_powerset]
  apply rank_mono
  intro z _
  rw [mem_powerset]
  intro _ _
  rw [mem_sUnion]
  exists z

@[simp]
theorem rank_range {α : Type*} [Small.{u} α] (f : α → ZFSet.{u}) :
    rank (range f) = ⨆ i, succ (rank (f i)) := by
  apply (Ordinal.iSup_le _).antisymm'
  · simpa [rank_le_iff, ← add_one_le_iff] using Ordinal.le_iSup _
  · simp [rank_lt_of_mem]

@[simp]
theorem rank_iUnion {α : Type*} [Small.{u} α] (f : α → ZFSet.{u}) :
    rank (⋃ i, f i) = ⨆ i, rank (f i) := by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_iUnion]
    intro y ⟨i, hy⟩
    exact (rank_lt_of_mem hy).trans_le (Ordinal.le_iSup _ _)
  · exact Ordinal.iSup_le fun i => rank_mono (subset_iUnion f i)

/-- `ZFSet.rank` is equal to the `IsWellFounded.rank` over `∈`. -/
theorem rank_eq_wfRank : lift.{u + 1, u} (rank x) = IsWellFounded.rank (α := ZFSet) (· ∈ ·) x := by
  induction x using inductionOn with | _ x ih
  rw [IsWellFounded.rank_eq]
  simp_rw [← fun y : { y // y ∈ x } => ih y y.2]
  apply (le_of_forall_lt _).antisymm (Ordinal.iSup_le _) <;> intro h
  · rw [lt_lift_iff]
    rintro ⟨o, h, rfl⟩
    simpa [Ordinal.lt_iSup_iff] using lt_rank_iff.1 h
  · simpa using rank_lt_of_mem h.2

end ZFSet
