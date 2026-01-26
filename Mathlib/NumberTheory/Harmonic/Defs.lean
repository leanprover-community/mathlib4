import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!

This file defines the harmonic numbers.

* `Mathlib/NumberTheory/Harmonic/Int.lean` proves that the `n`th harmonic number is not an integer.
* `Mathlib/NumberTheory/Harmonic/Bounds.lean` provides basic log bounds.

-/

@[expose] public section

/-- The nth-harmonic number defined as a finset sum of consecutive reciprocals. -/
def harmonic : ℕ → ℚ := fun n => ∑ i ∈ Finset.range n, (↑(i + 1))⁻¹

@[simp]
lemma harmonic_zero : harmonic 0 = 0 :=
  rfl

@[simp]
lemma harmonic_succ (n : ℕ) : harmonic (n + 1) = harmonic n + (↑(n + 1))⁻¹ :=
  Finset.sum_range_succ ..
