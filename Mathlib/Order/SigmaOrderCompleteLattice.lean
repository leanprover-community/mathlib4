/-
Copyright (c) 2025 William Du. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Du
-/
import Mathlib.Order.Lattice

/-!
TODO: docstring
-/

variable {α : Type*}

-- or SigmaOrderComplete
class SigmaOrderCompleteLattice (α : Type*) extends Lattice α where
  protected nSup : (ℕ → α) → α
  protected le_nSup' (s : ℕ → α) (i : ℕ) : s i ≤ nSup s
  protected nSup_le' {s : ℕ → α} {a : α} (h : ∀ i : ℕ, s i ≤ a) : nSup s ≤ a
-- add inf
-- countable <--> Naturals surject the reals

prefix:110 "⨆i " => SigmaOrderCompleteLattice.nSup

variable {l : SigmaOrderCompleteLattice α}

lemma le_nSup (s : ℕ → α) (i : ℕ) : s i ≤ ⨆i s := by
  exact SigmaOrderCompleteLattice.le_nSup' s i

lemma nSup_le {s : ℕ → α} {a : α} (h : ∀ (i : ℕ), s i ≤ a) : ⨆i s ≤ a := by
  exact SigmaOrderCompleteLattice.nSup_le' h


lemma nSup_le_iff [SigmaOrderCompleteLattice α] {s : ℕ → α} {a : α} :
  ⨆i s ≤ a ↔ ∀ (i : ℕ), s i ≤ a := by
  apply Iff.intro
  · intro h i
    exact le_trans (le_nSup s i) h
  · exact nSup_le
