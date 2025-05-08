import Mathlib.Order.Lattice

variable {α : Type*}

-- or SigmaOrderComplete
class SigmaOrderCompleteLattice (α : Type*) extends Lattice α where
  protected nSup : (ℕ → α) → α
  protected le_nSup (s : ℕ → α) (i : ℕ) : s i ≤ nSup s
  protected nSup_le (s : ℕ → α) (a : α) : (∀ i : ℕ, s i ≤ a) → nSup s ≤ a
-- add inf
-- countable <--> Naturals surject the reals

prefix:110 "⨆i " => SigmaOrderCompleteLattice.nSup

lemma nSup_le_iff [SigmaOrderCompleteLattice α] {s : ℕ → α} {a : α} :
  SigmaOrderCompleteLattice.nSup s ≤ a ↔ ∀ (i : ℕ), s i ≤ a := by
  apply Iff.intro
  · intro h i
    apply le_trans (SigmaOrderCompleteLattice.le_nSup s i) h
  · exact SigmaOrderCompleteLattice.nSup_le s a
