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

-- add inf
class SigmaOrderCompleteBoundedLattice (α : Type*) extends Lattice α, Top α, Bot α where
  protected nSup : (ℕ → α) → α
  protected le_nSup' (s : ℕ → α) (i : ℕ) : s i ≤ nSup s
  protected nSup_le' {s : ℕ → α} {a : α} (h : ∀ i : ℕ, s i ≤ a) : nSup s ≤ a
-- figure out naming
class CSigmaOrderCompleteLattice (α : Type*) extends PartialOrder α, SupSet α, InfSet α where
  protected le_cSup (s : Set α) (a : α) :
    s.Countable → s.Nonempty → BddAbove s → a ∈ s → a ≤ sSup s
  protected cSup_le (s : Set α) (a : α) :
    s.Countable → s.Nonempty → BddAbove s → a ∈ upperBounds s → sSup s ≤ a
-- partialsup/finset.sup

prefix:110 "⨆i " => SigmaOrderCompleteBoundedLattice.nSup

variable {l : SigmaOrderCompleteBoundedLattice α}

lemma le_nSup (s : ℕ → α) (i : ℕ) : s i ≤ ⨆i s := by
  exact SigmaOrderCompleteBoundedLattice.le_nSup' s i

lemma nSup_le {s : ℕ → α} {a : α} (h : ∀ (i : ℕ), s i ≤ a) : ⨆i s ≤ a := by
  exact SigmaOrderCompleteBoundedLattice.nSup_le' h


lemma nSup_le_iff {s : ℕ → α} {a : α} :
  ⨆i s ≤ a ↔ ∀ (i : ℕ), s i ≤ a := by
  apply Iff.intro
  · intro h i
    exact le_trans (le_nSup s i) h
  · exact nSup_le

lemma nSup_mono {a b : ℕ → α} (hai_le_bj : ∀ (i : ℕ), ∃ (j : ℕ), a i ≤ b j) :
  ⨆i a ≤ ⨆i b := by
  apply nSup_le
  intro i
  specialize hai_le_bj i
  obtain ⟨j, hai_le_bj⟩ := hai_le_bj
  exact le_trans hai_le_bj (le_nSup b j)
