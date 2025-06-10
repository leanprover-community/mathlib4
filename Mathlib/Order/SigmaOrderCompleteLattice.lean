/-
Copyright (c) 2025 William Du. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Du
-/
import Mathlib.Order.Lattice
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Set.Countable
import Mathlib.Order.SetNotation
import Mathlib.Order.Bounds.Basic

/-!
TODO: docstring
-/

variable {α : Type*}

-- add boundedness condition
class SigmaOrderCompleteLattice (α : Type*) extends Lattice α, SupSet α, InfSet α where
  protected nSup : (ℕ → α) → α
  protected le_nSup' (s : ℕ → α) (i : ℕ) : s i ≤ nSup s
  protected nSup_le' {s : ℕ → α} {a : α} (h : ∀ (i : ℕ), s i ≤ a) : nSup s ≤ a
  protected sSup_eq_nSup' {s : ℕ → α} : sSup (Set.range s) = nSup s
  protected nInf : (ℕ → α) → α
  protected nInf_le' (s : ℕ → α) (i : ℕ) : nInf s ≤ s i
  protected le_nInf' {s : ℕ → α} {a : α} (h : ∀ (i : ℕ), a ≤ s i) : a ≤ nInf s
  protected sInf_eq_nInf' {s : ℕ → α} : sInf (Set.range s) = nInf s
-- figure out naming
-- partialsup/finset.sup

prefix:110 "⨆i " => SigmaOrderCompleteLattice.nSup
prefix:110 "⨅i " => SigmaOrderCompleteLattice.nInf

variable {l : SigmaOrderCompleteLattice α}

lemma le_nSup (s : ℕ → α) (i : ℕ) : s i ≤ ⨆i s := by
  exact SigmaOrderCompleteLattice.le_nSup' s i

lemma nSup_le {s : ℕ → α} {a : α} (h : ∀ (i : ℕ), s i ≤ a) : ⨆i s ≤ a := by
  exact SigmaOrderCompleteLattice.nSup_le' h

lemma sSup_eq_nSup {s : ℕ → α} : sSup (Set.range s) = ⨆i s := by
  exact SigmaOrderCompleteLattice.sSup_eq_nSup'

lemma nInf_le (s : ℕ → α) (i : ℕ) : ⨅i s ≤ s i := by
  exact SigmaOrderCompleteLattice.nInf_le' s i

lemma le_nInf {s : ℕ → α} {a : α} (h : ∀ (i : ℕ), a ≤ s i) : a ≤ ⨅i s := by
  exact SigmaOrderCompleteLattice.le_nInf' h

lemma sInf_eq_nInf {s : ℕ → α} : sInf (Set.range s) = ⨅i s := by
  exact SigmaOrderCompleteLattice.sInf_eq_nInf'

-- nSup/Inf = iSup/Inf
-- iSup/Inf require Complete(Semi)Lattice, which is too strong

-- lemma nSup_eq_sSup (s : ℕ → α) : ⨆i s = sSup (Set.range s) := by
--   sorry

lemma le_nsSup (s : Set α) (a : α) :
  s.Countable → BddAbove s → a ∈ s → a ≤ sSup s := by
  intro hcountable _ hin_s
  have hne : s.Nonempty := by
    unfold Set.Nonempty
    exists a
  have hexists_eq_range := Set.Countable.exists_eq_range hcountable hne
  obtain ⟨f, hs_eq_range⟩ := hexists_eq_range
  rw [hs_eq_range, Set.mem_range] at hin_s
  obtain ⟨i, heq_a⟩ := hin_s
  rw [hs_eq_range, sSup_eq_nSup, ←heq_a]
  exact le_nSup f i

lemma nsSup_le {s : Set α} {a : α} :
  s.Countable → s.Nonempty → BddAbove s → a ∈ upperBounds s → sSup s ≤ a := by
  intro hcountable hne _ hbounds
  have hexists_eq_range := Set.Countable.exists_eq_range hcountable hne
  obtain ⟨f, hs_eq_range⟩ := hexists_eq_range
  rw [hs_eq_range, sSup_eq_nSup]
  apply nSup_le
  unfold upperBounds at hbounds
  rw [Set.mem_setOf, hs_eq_range] at hbounds
  intro i
  exact hbounds (Set.mem_range_self i)

lemma nsInf_le (s : Set α) (a : α) :
  s.Countable → BddBelow s → a ∈ s → sInf s ≤ a := by
  sorry

lemma le_nsInf {s : Set α} {a : α} :
  s.Countable → s.Nonempty → BddBelow s → a ∈ lowerBounds s → a ≤ sInf s := by
  sorry


lemma nSup_le_iff {s : ℕ → α} {a : α} :
  ⨆i s ≤ a ↔ ∀ (i : ℕ), s i ≤ a := by
  apply Iff.intro
  · intro h i
    exact le_trans (le_nSup s i) h
  · exact nSup_le

lemma le_nInf_iff {s : ℕ → α} {a : α} :
  a ≤ ⨅i s ↔ ∀ (i : ℕ), a ≤ s i := by
  apply Iff.intro
  · intro h i
    exact le_trans h (nInf_le s i)
  · exact le_nInf

lemma nSup_mono {a b : ℕ → α} (hai_le_bj : ∀ (i : ℕ), ∃ (j : ℕ), a i ≤ b j) :
  ⨆i a ≤ ⨆i b := by
  apply nSup_le
  intro i
  specialize hai_le_bj i
  obtain ⟨j, hai_le_bj⟩ := hai_le_bj
  exact le_trans hai_le_bj (le_nSup b j)

lemma nInf_mono {a b : ℕ → α} (hai_le_bj : ∀ (i : ℕ), ∃ (j : ℕ), a j ≤ b i) :
  ⨅i a ≤ ⨅i b := by
  apply le_nInf
  intro i
  specialize hai_le_bj i
  obtain ⟨j, hai_le_bj⟩ := hai_le_bj
  exact le_trans (nInf_le a j) hai_le_bj
