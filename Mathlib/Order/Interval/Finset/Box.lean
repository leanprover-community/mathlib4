/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Order.Disjointed
import Mathlib.Tactic.AdaptationNote
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Decomposing a locally finite ordered ring into boxes

This file proves that any locally finite ordered ring can be decomposed into "boxes", namely
differences of consecutive intervals.

## Implementation notes

We don't need the full ring structure, only that there is an order embedding `ℤ → `
-/

/-! ### General locally finite ordered ring -/

namespace Finset
variable {α : Type*} [OrderedRing α] [LocallyFiniteOrder α] [DecidableEq α] {n : ℕ}

/-- Hollow box centered at `0 : α` going from `-n` to `n`. -/
def box : ℕ → Finset α := disjointed fun n ↦ Icc (-n : α) n

private lemma Icc_neg_mono : Monotone fun n : ℕ ↦ Icc (-n : α) n := by
  refine fun m n hmn ↦ by apply Icc_subset_Icc <;> simpa using Nat.mono_cast hmn

@[simp] lemma box_zero : (box 0 : Finset α) = {0} := by simp [box]

lemma box_succ_eq_sdiff (n : ℕ) :
    box (n + 1) = Icc (-n.succ : α) n.succ \ Icc (-n) n := Icc_neg_mono.disjointed_succ _

lemma disjoint_box_succ_prod (n : ℕ) : Disjoint (box (n + 1)) (Icc (-n : α) n) := by
  rw [box_succ_eq_sdiff]; exact disjoint_sdiff_self_left

@[simp] lemma box_succ_union_prod (n : ℕ) :
    box (n + 1) ∪ Icc (-n : α) n = Icc (-n.succ : α) n.succ := Icc_neg_mono.disjointed_succ_sup _

lemma box_succ_disjUnion (n : ℕ) :
    (box (n + 1)).disjUnion (Icc (-n : α) n) (disjoint_box_succ_prod _) =
      Icc (-n.succ : α) n.succ := by rw [disjUnion_eq_union, box_succ_union_prod]

@[simp] lemma zero_mem_box : (0 : α) ∈ box n ↔ n = 0 := by cases n <;> simp [box_succ_eq_sdiff]

lemma eq_zero_iff_eq_zero_of_mem_box  {x : α} (hx : x ∈ box n) : x = 0 ↔ n = 0 :=
  ⟨zero_mem_box.mp ∘ (· ▸ hx), fun hn ↦ by rwa [hn, box_zero, mem_singleton] at hx⟩

end Finset

open Finset

/-! ### Product of locally finite ordered rings -/

namespace Prod
variable {α β : Type*} [OrderedRing α] [OrderedRing β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableEq α] [DecidableEq β] [@DecidableRel (α × β) (· ≤ ·)]

@[simp] lemma card_box_succ (n : ℕ) :
    (box (n + 1) : Finset (α × β)).card =
      (Icc (-n.succ : α) n.succ).card * (Icc (-n.succ : β) n.succ).card -
        (Icc (-n : α) n).card * (Icc (-n : β) n).card := by
  rw [box_succ_eq_sdiff, card_sdiff (Icc_neg_mono n.le_succ), Prod.card_Icc, Prod.card_Icc]; rfl

end Prod

/-! ### `ℤ × ℤ` -/

namespace Int
variable {n : ℕ} {x : ℤ × ℤ}

attribute [norm_cast] toNat_ofNat

lemma card_box : ∀ {n}, n ≠ 0 → (box n : Finset (ℤ × ℤ)).card = 8 * n
  | n + 1, _ => by
    simp_rw [Prod.card_box_succ, card_Icc, sub_neg_eq_add]
    norm_cast
    refine tsub_eq_of_eq_add ?_
    zify
    ring

@[simp] lemma mem_box : ∀ {n}, x ∈ box n ↔ max x.1.natAbs x.2.natAbs = n
  | 0 => by simp [Prod.ext_iff]
  | n + 1 => by
    simp [box_succ_eq_sdiff, Prod.le_def]
    #adaptation_note /-- v4.7.0-rc1: `omega` no longer identifies atoms up to defeq.
    (This had become a performance bottleneck.)
    We need a tactic for normalising instances, to avoid the `have`/`simp` dance below: -/
    have : @Nat.cast ℤ instNatCastInt n = @Nat.cast ℤ AddMonoidWithOne.toNatCast n := rfl
    simp only [this]
    omega

-- TODO: Can this be generalised to locally finite archimedean ordered rings?
lemma existsUnique_mem_box (x : ℤ × ℤ) : ∃! n : ℕ, x ∈ box n := by
  use max x.1.natAbs x.2.natAbs; simp only [mem_box, and_self_iff, forall_eq']

end Int
