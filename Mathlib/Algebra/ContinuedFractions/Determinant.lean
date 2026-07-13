/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.Algebra.ContinuedFractions.TerminatedStable
public import Mathlib.Tactic.Ring

/-!
# Determinant Formula for Generalized Continued Fraction

We derive the so-called *determinant formula* for `GenContFract`:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-a₀) * (-a₁) * .. * (-aₙ)`.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction#The_determinant_formula

-/

public section

open GenContFract

variable {K : Type*} [Field K]

namespace GenContFract

variable {g : GenContFract K} {n : ℕ}

/-- The determinant formula `Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-a₀) * (-a₁) * .. * (-aₙ)`. -/
theorem determinant :
    g.nums n * g.dens (n + 1) - g.dens n * g.nums (n + 1) =
      ∏ i ∈ Finset.range (n + 1), - g.partNums! i := by
  induction n with
  | zero =>
    suffices g.h * g.dens 1 - g.nums 1 = -g.partNums! 0 by simpa
    rcases Decidable.em <| g.TerminatedAt 0 with hg | hg
    · simp [dens_stable_of_terminated zero_le_one, nums_stable_of_terminated zero_le_one,
        partNum!_of_terminatedAt, hg]
    · obtain ⟨gp, s_eq⟩ : ∃ gp, g.s.get? 0 = some gp := Option.ne_none_iff_exists'.mp hg
      rw [partNum!_eq_s_a s_eq, first_den_eq s_eq, first_num_eq s_eq,
        mul_comm, sub_add_cancel_left]
  | succ n' ih =>
    rw [Finset.prod_range_succ_comm, ← ih, dens_recurrence!, nums_recurrence!]
    ring

end GenContFract

namespace SimpContFract

variable {s : SimpContFract K} {n : ℕ}

/-- The determinant formula `Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1) ^ (n + 1)` for `SimpContFract`. -/
theorem determinant (not_terminatedAt_n : ¬(↑s : GenContFract K).TerminatedAt n) :
    (↑s : GenContFract K).nums n * (↑s : GenContFract K).dens (n + 1) -
      (↑s : GenContFract K).dens n * (↑s : GenContFract K).nums (n + 1) = (-1) ^ (n + 1) := calc
  _ = ∏ i ∈ Finset.range (n + 1), - ((↑s : GenContFract K).partNums.get? i).getD 0 :=
    (↑s : GenContFract K).determinant
  _ = ∏ i ∈ Finset.range (n + 1), -1 := Finset.prod_congr rfl fun i hi ↦ by
    rw [Finset.mem_range] at hi
    obtain ⟨gp, s_ith_eq⟩ : ∃ gp, (↑s : GenContFract K).s.get? i = some gp :=
      Option.ne_none_iff_exists'.1 <| mt (terminated_stable <| Nat.le_of_succ_le_succ hi) ‹_›
    rw [partNum_eq_s_a s_ith_eq, s.property i gp.a <| partNum_eq_s_a s_ith_eq, Option.getD_some]
  _ = (-1) ^ (n + 1) := by rw [Finset.prod_const, Finset.card_range]

end SimpContFract
