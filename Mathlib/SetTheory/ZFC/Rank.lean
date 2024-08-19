/-
Copyright (c) 2024 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.ZFC.Basic

/-!
# Ordinal ranks of ZFSet

In this file, we define the ordinal ranks of `ZFSet`. This rank is the same as `WellFounded.rank`
over `∈`, but defined as `Quotient.lift` of `PSet.rank` so that the universe level is
`ZFSet.{u} → Ordinal.{u}`.

## Definitions

* `PSet.rank`: Ordinal rank of a pre-set.
* `ZFSet.rank`: Ordinal rank of a ZFC set.
-/

universe u v

open Ordinal

namespace PSet

/-- The ordinal rank of a pre-set -/
noncomputable def rank : PSet.{u} → Ordinal.{u}
  | ⟨_, A⟩ => lsub fun a => rank (A a)

theorem rank_eq_of_equiv : (x y : PSet) → Equiv x y → rank x = rank y
  | ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ =>
    lsub_eq_of_range_eq (by
      ext; constructor <;> simp <;> intro a h
      · obtain ⟨b, h'⟩ := αβ a
        exists b; rw [←h, rank_eq_of_equiv _ _ h']
      · obtain ⟨b, h'⟩ := βα a
        exists b; rw [←h, rank_eq_of_equiv _ _ h'])

theorem rank_lt_of_mem : {x y : PSet} → y ∈ x → rank y < rank x
  | ⟨_, _⟩, _, ⟨_, h⟩ => by
    rw [PSet.rank_eq_of_equiv _ _ h]
    apply lt_lsub

theorem rank_le_of_forall_mem_rank_lt {o : Ordinal} :
    {x : PSet} → (∀ y ∈ x, rank y < o) → rank x ≤ o
  | ⟨_, A⟩, h => lsub_le fun a => h (A a) (Mem.mk A a)

end PSet

namespace ZFSet

variable {x y : ZFSet.{u}}

/-- The ordinal rank of a ZFC set -/
noncomputable def rank : ZFSet.{u} → Ordinal.{u} :=
  Quotient.lift PSet.rank PSet.rank_eq_of_equiv

theorem rank_lt_of_mem : y ∈ x → rank y < rank x :=
  Quotient.inductionOn₂ x y fun _ _ => PSet.rank_lt_of_mem

theorem rank_le_of_forall_mem_rank_lt {o : Ordinal}
    : (∀ y ∈ x, rank y < o) → rank x ≤ o :=
  Quotient.inductionOn x fun _ h =>
    PSet.rank_le_of_forall_mem_rank_lt fun y h' => h ⟦y⟧ h'

theorem rank_le_of_subset (h : x ⊆ y) : rank x ≤ rank y :=
  rank_le_of_forall_mem_rank_lt fun _ h₁ => rank_lt_of_mem (h h₁)

theorem rank_empty : rank ∅ = 0 := by
  rw [←Ordinal.le_zero]; apply rank_le_of_forall_mem_rank_lt; simp

theorem rank_insert : rank (insert x y) = max (rank x + 1) (rank y) := by
  apply le_antisymm
  · apply rank_le_of_forall_mem_rank_lt; simp
    intro _ h; exact Or.inr (rank_lt_of_mem h)
  · simp; constructor
    · apply rank_lt_of_mem; simp
    · apply rank_le_of_subset; intro; apply mem_insert_of_mem

theorem rank_singleton : rank {x} = rank x + 1 :=
  rank_insert.trans (by simp [rank_empty])

theorem rank_pair : rank {x, y} = max (rank x) (rank y) + 1 :=
  rank_insert.trans (by simp [rank_singleton, succ_max])

theorem rank_union : rank (x ∪ y) = max (rank x) (rank y) := by
  apply le_antisymm
  · apply rank_le_of_forall_mem_rank_lt; simp
    intro; exact Or.imp rank_lt_of_mem rank_lt_of_mem
  · simp; constructor <;> apply rank_le_of_subset <;> intro _ h <;> simp [h]

theorem rank_insert : rank (insert x y) = max (rank x + 1) (rank y) := by
  have : insert x y = {x} ∪ y := by ext; simp
  rw [this, rank_union, rank_singleton]

theorem rank_powerset : rank (powerset x) = rank x + 1 := by
  apply le_antisymm
  · apply rank_le_of_forall_mem_rank_lt; simp
    intro; exact rank_le_of_subset
  · simp; apply rank_lt_of_mem; simp

/-- For the rank of `⋃₀ x`, we only have `rank (⋃₀ x) ≤ rank x ≤ rank (⋃₀ x) + 1`.
    This inequality is splitted into `rank_sUnion_le` and `succ_rank_sUnion_ge`. -/
theorem rank_sUnion_le : rank (⋃₀ x : ZFSet) ≤ rank x := by
  apply rank_le_of_forall_mem_rank_lt
  simp; intros; trans <;> apply rank_lt_of_mem <;> assumption

theorem succ_rank_sUnion_ge : rank (⋃₀ x : ZFSet) + 1 ≥ rank x := by
  rw [←rank_powerset]
  apply rank_le_of_subset
  intro z _; simp; intro _ _; simp; exists z

theorem rank_range {α : Type u} {f : α → ZFSet.{max u v}} :
    rank (range f) = lsub fun i => rank (f i) := by
  apply le_antisymm
  · apply rank_le_of_forall_mem_rank_lt; simp; apply lt_lsub
  · apply lsub_le; intro; apply rank_lt_of_mem; simp

/-- `ZFSet.rank` is equal to the `WellFounded.rank` over `∈`. -/
theorem rank_eq_wf_rank : lift.{u+1,u} (rank x) = mem_wf.rank x := by
  induction' x using inductionOn with x ih
  rw [mem_wf.rank_eq]
  simp_rw [←fun y : { y // y ∈ x } => ih y y.2]
  apply le_antisymm
  · apply le_of_forall_lt
    intro _ h
    rw [lt_lift_iff] at h
    rcases h with ⟨o, h₁, h₂⟩
    by_contra h₃; simp [sup_le_iff, ←h₁] at h₃
    exact not_le_of_lt h₂ (rank_le_of_forall_mem_rank_lt h₃)
  · apply Ordinal.sup_le
    intro ⟨_, h⟩; simp; exact rank_lt_of_mem h

end ZFSet
