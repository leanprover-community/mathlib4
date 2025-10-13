/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.Algebra.ContinuedFractions.TerminatedStable
import Mathlib.Tactic.Ring

/-!
# Determinant Formula for Simple Continued Fraction

## Summary

We derive the so-called *determinant formula* for `SimpContFract`:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`.

## TODO

Generalize this for `GenContFract` version:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-a₀) * (-a₁) * .. * (-aₙ₊₁)`.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction#The_determinant_formula

-/

open GenContFract

namespace SimpContFract

variable {K : Type*} [Field K] {s : SimpContFract K} {n : ℕ}

theorem determinant_aux (hyp : n = 0 ∨ ¬(↑s : GenContFract K).TerminatedAt (n - 1)) :
    ((↑s : GenContFract K).contsAux n).a * ((↑s : GenContFract K).contsAux (n + 1)).b -
      ((↑s : GenContFract K).contsAux n).b * ((↑s : GenContFract K).contsAux (n + 1)).a =
        (-1) ^ n := by
  induction n with
  | zero => simp [contsAux]
  | succ n IH =>
    -- set up some shorthand notation
    let g := (↑s : GenContFract K)
    let conts := contsAux g (n + 2)
    set pred_conts := contsAux g (n + 1) with pred_conts_eq
    set ppred_conts := contsAux g n with ppred_conts_eq
    let pA := pred_conts.a
    let pB := pred_conts.b
    let ppA := ppred_conts.a
    let ppB := ppred_conts.b
    -- let's change the goal to something more readable
    change pA * conts.b - pB * conts.a = (-1) ^ (n + 1)
    have not_terminated_at_n : ¬TerminatedAt g n := Or.resolve_left hyp n.succ_ne_zero
    obtain ⟨gp, s_nth_eq⟩ : ∃ gp, g.s.get? n = some gp :=
      Option.ne_none_iff_exists'.1 not_terminated_at_n
    -- unfold the recurrence relation for `conts` once and simplify to derive the following
    suffices pA * (ppB + gp.b * pB) - pB * (ppA + gp.b * pA) = (-1) ^ (n + 1) by
      simp only [conts, contsAux_recurrence s_nth_eq ppred_conts_eq pred_conts_eq]
      have gp_a_eq_one : gp.a = 1 := s.property _ _ (partNum_eq_s_a s_nth_eq)
      rw [gp_a_eq_one, this.symm]
      ring
    suffices pA * ppB - pB * ppA = (-1) ^ (n + 1) by grind
    suffices ppA * pB - ppB * pA = (-1) ^ n by grind
    exact IH <| Or.inr <| mt (terminated_stable <| n.sub_le 1) not_terminated_at_n

/-- The determinant formula `Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`. -/
theorem determinant (not_terminatedAt_n : ¬(↑s : GenContFract K).TerminatedAt n) :
    (↑s : GenContFract K).nums n * (↑s : GenContFract K).dens (n + 1) -
      (↑s : GenContFract K).dens n * (↑s : GenContFract K).nums (n + 1) = (-1) ^ (n + 1) :=
  determinant_aux <| Or.inr <| not_terminatedAt_n

end SimpContFract
