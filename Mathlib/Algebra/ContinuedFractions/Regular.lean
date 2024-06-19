/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.Algebra.ContinuedFractions.TerminatedStable
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Monotonicity

/-!
# Property of regular continued fractions (`RCF`)

## Summary

This file proves some properties of regular continued fractions.

## Main Theorems

- `RCF.succ_nth_fib_le_nth_den`: shows that the `n`th denominator
  `Bₙ` is greater than or equal to the `n + 1`th fibonacci number `Nat.fib (n + 1)`.
- `RCF.le_succ_get?_den`: shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is
  the `n`th partial denominator of the continued fraction.

## TODO

Prove that convergents of regular continued fractions is a cauchy sequence.

## References

- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]

-/

open GCF Nat

variable {K : Type*} [LinearOrderedField K] {r : RCF K} {n : ℕ}

namespace RCF

/-!
One of our goals is to show that `bₙ * Bₙ ≤ Bₙ₊₁`. For this, we first show that the partial
denominators `Bₙ` are bounded from below by the fibonacci sequence `Nat.fib`. This then implies that
`0 ≤ Bₙ` and hence `Bₙ₊₂ = bₙ₊₁ * Bₙ₊₁ + Bₙ ≥ bₙ₊₁ * Bₙ₊₁ + 0 = bₙ₊₁ * Bₙ₊₁`.
-/


theorem fib_le_contsAux_b :
    n ≤ 1 ∨ ¬(↑r : GCF K).TerminatedAt (n - 2) → (fib n : K) ≤ ((↑r : GCF K).contsAux n).b :=
  Nat.strong_induction_on n
    (by
      intro n IH hyp
      rcases n with (_ | _ | n)
      · simp [fib_add_two, contsAux] -- case n = 0
      · simp [fib_add_two, contsAux] -- case n = 1
      · let g : GCF K := ↑r -- case 2 ≤ n
        have : ¬n + 2 ≤ 1 := by omega
        have not_terminatedAt_n : ¬g.TerminatedAt n := Or.resolve_left hyp this
        obtain ⟨gp, s_ppred_nth_eq⟩ : ∃ gp, g.s.get? n = some gp :=
          Option.ne_none_iff_exists'.mp not_terminatedAt_n
        set pconts := g.contsAux (n + 1) with pconts_eq
        set ppconts := g.contsAux n with ppconts_eq
        -- use the recurrence of `contsAux`
        simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd]
        suffices (fib n : K) + fib (n + 1) ≤ gp.a * ppconts.b + gp.b * pconts.b by
          simpa [fib_add_two, add_comm, contsAux_recurrence s_ppred_nth_eq ppconts_eq pconts_eq]
        -- make use of the fact that `gp.a = 1`
        suffices (fib n : K) + fib (n + 1) ≤ ppconts.b + gp.b * pconts.b by
          simpa [r.val.property _ _ <| partNum_eq_s_a s_ppred_nth_eq]
        have not_terminatedAt_pred_n : ¬g.TerminatedAt (n - 1) :=
          mt (terminated_stable <| Nat.sub_le n 1) not_terminatedAt_n
        have not_terminatedAt_ppred_n : ¬TerminatedAt g (n - 2) :=
          mt (terminated_stable (n - 1).pred_le) not_terminatedAt_pred_n
        -- use the IH to get the inequalities for `pconts` and `ppconts`
        have ppred_nth_fib_le_ppconts_B : (fib n : K) ≤ ppconts.b :=
          IH n (lt_trans (Nat.lt.base n) <| Nat.lt.base <| n + 1) (Or.inr not_terminatedAt_ppred_n)
        suffices (fib (n + 1) : K) ≤ gp.b * pconts.b by
          solve_by_elim [_root_.add_le_add ppred_nth_fib_le_ppconts_B]
        -- finally use the fact that `1 ≤ gp.b` to solve the goal
        suffices 1 * (fib (n + 1) : K) ≤ gp.b * pconts.b by rwa [one_mul] at this
        have one_le_gp_b : (1 : K) ≤ gp.b := by
          rcases r.property.2 _ _ (partDen_eq_s_b s_ppred_nth_eq) with ⟨m, hm⟩; rw [hm]
          exact_mod_cast Nat.succ_le_of_lt m.pos
        have : (0 : K) ≤ fib (n + 1) := mod_cast (fib (n + 1)).zero_le
        have : (0 : K) ≤ gp.b := le_trans zero_le_one one_le_gp_b
        mono
        · norm_num
        · tauto)
#align generalized_continued_fraction.fib_le_of_continuants_aux_b RCF.fib_le_contsAux_b

/-- Shows that the `n`th denominator is greater than or equal to the `n + 1`th fibonacci number,
that is `Nat.fib (n + 1) ≤ Bₙ`. -/
theorem succ_nth_fib_le_nth_den (hyp : n = 0 ∨ ¬(↑r : GCF K).TerminatedAt (n - 1)) :
    (fib (n + 1) : K) ≤ (↑r : GCF K).dens n := by
  rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  have : n + 1 ≤ 1 ∨ ¬(↑r : GCF K).TerminatedAt (n - 1) := by
    cases n with
    | zero => exact Or.inl <| le_refl 1
    | succ n => exact Or.inr (Or.resolve_left hyp n.succ_ne_zero)
  exact fib_le_contsAux_b this
#align generalized_continued_fraction.succ_nth_fib_le_of_nth_denom RCF.succ_nth_fib_le_nth_den

/-! As a simple consequence, we can now derive that all denominators are nonnegative. -/


theorem zero_le_contsAux_b : 0 ≤ ((↑r : GCF K).contsAux n).b := by
  let g : GCF K := ↑r
  induction n with
  | zero => rfl
  | succ n IH =>
    cases' Decidable.em <| g.TerminatedAt (n - 1) with terminated not_terminated
    · -- terminating case
      cases' n with n
      · simp [succ_eq_add_one, zero_le_one]
      · have : g.contsAux (n + 2) = g.contsAux (n + 1) :=
          contsAux_stable_step_of_terminated terminated
        simp only [this, IH]
    · -- non-terminating case
      calc
        (0 : K) ≤ fib (n + 1) := mod_cast (n + 1).fib.zero_le
        _ ≤ ((↑r : GCF K).contsAux (n + 1)).b := fib_le_contsAux_b (Or.inr not_terminated)
#align generalized_continued_fraction.zero_le_of_continuants_aux_b RCF.zero_le_contsAux_b

/-- Shows that all denominators are nonnegative. -/
theorem zero_le_den : 0 ≤ (↑r : GCF K).dens n := by
  rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]; exact zero_le_contsAux_b
#align generalized_continued_fraction.zero_le_of_denom RCF.zero_le_den

theorem le_succ_succ_get?_contsAux_b {b : K}
    (nth_partDen_eq : (↑r : GCF K).partDens.get? n = some b) :
    b * ((↑r : GCF K).contsAux <| n + 1).b ≤ ((↑r : GCF K).contsAux <| n + 2).b := by
  obtain ⟨gp_n, nth_s_eq, rfl⟩ : ∃ gp_n, (↑r : GCF K).s.get? n = some gp_n ∧ gp_n.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  simp [r.val.property _ _ (partNum_eq_s_a nth_s_eq), zero_le_contsAux_b,
    GCF.contsAux_recurrence nth_s_eq rfl rfl]
#align generalized_continued_fraction.le_of_succ_succ_nth_continuants_aux_b RCF.le_succ_succ_get?_contsAux_b

/-- Shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is the `n`th partial denominator and `Bₙ₊₁` and `Bₙ` are
the `n + 1`th and `n`th denominator of the continued fraction. -/
theorem le_succ_get?_den {b : K}
    (nth_partDenom_eq : (↑r : GCF K).partDens.get? n = some b) :
    b * (↑r : GCF K).dens n ≤ (↑r : GCF K).dens (n + 1) := by
  rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  exact le_succ_succ_get?_contsAux_b nth_partDenom_eq
#align generalized_continued_fraction.le_of_succ_nth_denom RCF.le_succ_get?_den

/-- Shows that the sequence of denominators is monotone, that is `Bₙ ≤ Bₙ₊₁`. -/
theorem den_mono : (↑r : GCF K).dens n ≤ (↑r : GCF K).dens (n + 1) := by
  let g :GCF K := ↑r
  cases' Decidable.em <| g.partDens.TerminatedAt n with terminated not_terminated
  · have : g.partDens.get? n = none := by rwa [Stream'.Seq.TerminatedAt] at terminated
    have : g.TerminatedAt n :=
      terminatedAt_iff_partDen_none.2 (by rwa [Stream'.Seq.TerminatedAt] at terminated)
    have : g.dens (n + 1) = g.dens n :=
      dens_stable_of_terminated n.le_succ this
    rw [this]
  · obtain ⟨b, nth_partDen_eq⟩ : ∃ b, g.partDens.get? n = some b :=
      Option.ne_none_iff_exists'.mp not_terminated
    have : 1 ≤ b := by
          rcases r.property.2 _ _ nth_partDen_eq with ⟨m, hm⟩; rw [hm]
          exact_mod_cast Nat.succ_le_of_lt m.pos
    calc
      g.dens n ≤ b * g.dens n := by
        simpa using mul_le_mul_of_nonneg_right this zero_le_den
      _ ≤ g.dens (n + 1) := le_succ_get?_den nth_partDen_eq
#align generalized_continued_fraction.of_denom_mono RCF.den_mono

end RCF
