/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Set unions, intersections, and order

This file contains results connecting indexed unions and intersections of sets with order
structures. It covers intersections of intervals, tails of families indexed by natural numbers,
and the interaction of set unions with complete-lattice suprema and infima.
-/

public section

open Function

variable {α β : Type*} {ι : Sort*} {κ : ι → Sort*}

/-! ### Intervals -/

namespace Set

@[to_dual]
lemma nonempty_iInter_Iic_iff [Preorder α] {f : ι → α} :
    (⋂ i, Iic (f i)).Nonempty ↔ BddBelow (range f) := by
  have : (⋂ (i : ι), Iic (f i)) = lowerBounds (range f) := by
    ext c; simp [lowerBounds]
  simp [this, BddBelow]

variable [CompleteLattice α]

@[to_dual]
theorem Ici_iSup (f : ι → α) : Ici (⨆ i, f i) = ⋂ i, Ici (f i) :=
  ext fun _ => by simp only [mem_Ici, iSup_le_iff, mem_iInter]

@[to_dual]
theorem Ici_iSup₂ (f : ∀ i, κ i → α) : Ici (⨆ (i) (j), f i j) = ⋂ (i) (j), Ici (f i j) := by
  simp_rw [Ici_iSup]

@[to_dual]
theorem Ici_sSup (s : Set α) : Ici (sSup s) = ⋂ a ∈ s, Ici a := by rw [sSup_eq_iSup, Ici_iSup₂]

end Set

namespace Set

theorem iUnion_ge_eq_iUnion_nat_add (u : ℕ → Set α) (n : ℕ) : ⋃ i ≥ n, u i = ⋃ i, u (i + n) :=
  iSup_ge_eq_iSup_nat_add u n

theorem iInter_ge_eq_iInter_nat_add (u : ℕ → Set α) (n : ℕ) : ⋂ i ≥ n, u i = ⋂ i, u (i + n) :=
  iInf_ge_eq_iInf_nat_add u n

theorem _root_.Monotone.iUnion_nat_add {f : ℕ → Set α} (hf : Monotone f) (k : ℕ) :
    ⋃ n, f (n + k) = ⋃ n, f n :=
  hf.iSup_nat_add k

theorem _root_.Antitone.iInter_nat_add {f : ℕ → Set α} (hf : Antitone f) (k : ℕ) :
    ⋂ n, f (n + k) = ⋂ n, f n :=
  hf.iInf_nat_add k

@[simp]
theorem iUnion_iInter_ge_nat_add (f : ℕ → Set α) (k : ℕ) :
    ⋃ n, ⋂ i ≥ n, f (i + k) = ⋃ n, ⋂ i ≥ n, f i :=
  iSup_iInf_ge_nat_add f k

theorem union_iUnion_nat_succ (u : ℕ → Set α) : (u 0 ∪ ⋃ i, u (i + 1)) = ⋃ i, u i :=
  sup_iSup_nat_succ u

theorem inter_iInter_nat_succ (u : ℕ → Set α) : (u 0 ∩ ⋂ i, u (i + 1)) = ⋂ i, u i :=
  inf_iInf_nat_succ u

theorem iUnion_le_nat : ⋃ n : ℕ, {i | i ≤ n} = Set.univ :=
  subset_antisymm (Set.subset_univ _)
    (fun i _ ↦ Set.mem_iUnion_of_mem i (Set.mem_ofPred.mpr (le_refl _)))

end Set

open Set

variable [CompleteLattice β]

@[to_dual]
theorem iSup_iUnion (s : ι → Set α) (f : α → β) : ⨆ a ∈ ⋃ i, s i, f a = ⨆ (i) (a ∈ s i), f a := by
  rw [iSup_comm]
  simp_rw [mem_iUnion, iSup_exists]

@[to_dual]
theorem sSup_iUnion (t : ι → Set β) : sSup (⋃ i, t i) = ⨆ i, sSup (t i) := by
  simp_rw [sSup_eq_iSup, iSup_iUnion]

@[to_dual]
theorem sSup_sUnion (s : Set (Set β)) : sSup (⋃₀ s) = ⨆ t ∈ s, sSup t := by
  simp only [sUnion_eq_biUnion, sSup_eq_iSup, iSup_iUnion]

@[to_dual]
lemma iSup_sUnion (S : Set (Set α)) (f : α → β) :
    (⨆ x ∈ ⋃₀ S, f x) = ⨆ (s ∈ S) (x ∈ s), f x := by
  rw [sUnion_eq_iUnion, iSup_iUnion, ← iSup_subtype'']

lemma forall_sUnion {S : Set (Set α)} {p : α → Prop} :
    (∀ x ∈ ⋃₀ S, p x) ↔ ∀ s ∈ S, ∀ x ∈ s, p x := by
  simp_rw [← iInf_Prop_eq, iInf_sUnion]

lemma exists_sUnion {S : Set (Set α)} {p : α → Prop} :
    (∃ x ∈ ⋃₀ S, p x) ↔ ∃ s ∈ S, ∃ x ∈ s, p x := by
  simp_rw [← exists_prop, ← iSup_Prop_eq, iSup_sUnion]
