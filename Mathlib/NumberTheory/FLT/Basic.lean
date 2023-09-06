/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Algebra.GroupPower.Ring

/-!
# Statement of Fermat's Last Theorem

This file states the Fermat Last Theorem. We provide a statement over a general semiring with
specific exponent, along with the usual statement over the naturals.

The goal of this folder is to gather special cases of FLT: `n = 3`, `n = 4`, FLT for regular primes,
FLT over entire functions...
-/

/-- Statement of Fermat's Last Theorem over a given semiring with a specific exponent. -/
def FermatLastTheoremWith (α : Type*) [Semiring α] (n : ℕ) : Prop :=
  ∀ a b c : α, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n ≠ c ^ n

/-- Statement of Fermat's Last Theorem: `a ^ n + b ^ n = c ^ n` has no nontrivial integer solution
when `n ≥ 3`. -/
def FermatLastTheorem : Prop := ∀ n ≥ 3, FermatLastTheoremWith ℕ n

variable {α : Type*} [Semiring α] [NoZeroDivisors α] {m n : ℕ}

lemma FermatLastTheoremWith.mono (hmn : m ∣ n) (hm : FermatLastTheoremWith α m) :
  FermatLastTheoremWith α n := by
  rintro a b c ha hb hc
  obtain ⟨k, rfl⟩ := hmn
  simp_rw [pow_mul']
  refine hm _ _ _ ?_ ?_ ?_ <;> exact pow_ne_zero _ ‹_›
