/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Translations

#align_import algebra.continued_fractions.continuants_recurrence from "leanprover-community/mathlib"@"5f11361a98ae4acd77f5c1837686f6f0102cdc25"

/-!
# Recurrence Lemmas for the `continuants` Function of Continued Fractions.

## Summary

Given a generalized continued fraction `g`, for all `n ≥ 1`, we prove that the `continuants`
function indeed satisfies the following recurrences:
- `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`, and
- `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`.
-/


namespace GeneralizedContinuedFraction

variable {K : Type*} {g : GeneralizedContinuedFraction K} {n : ℕ} [DivisionRing K]

theorem continuantsAux_recurrence {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some gp)
    (nth_conts_aux_eq : g.continuantsAux n = ppred)
    (succ_nth_conts_aux_eq : g.continuantsAux (n + 1) = pred) :
    g.continuantsAux (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ :=
  by simp [*, continuantsAux, nextContinuants, nextDenominator, nextNumerator]
     -- 🎉 no goals
#align generalized_continued_fraction.continuants_aux_recurrence GeneralizedContinuedFraction.continuantsAux_recurrence

theorem continuants_recurrenceAux {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some gp)
    (nth_conts_aux_eq : g.continuantsAux n = ppred)
    (succ_nth_conts_aux_eq : g.continuantsAux (n + 1) = pred) :
    g.continuants (n + 1) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ := by
  simp [nth_cont_eq_succ_nth_cont_aux,
    continuantsAux_recurrence nth_s_eq nth_conts_aux_eq succ_nth_conts_aux_eq]
#align generalized_continued_fraction.continuants_recurrence_aux GeneralizedContinuedFraction.continuants_recurrenceAux

/-- Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂` and `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`. -/
theorem continuants_recurrence {gp ppred pred : Pair K} (succ_nth_s_eq : g.s.get? (n + 1) = some gp)
    (nth_conts_eq : g.continuants n = ppred) (succ_nth_conts_eq : g.continuants (n + 1) = pred) :
    g.continuants (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ := by
  rw [nth_cont_eq_succ_nth_cont_aux] at nth_conts_eq succ_nth_conts_eq
  -- ⊢ continuants g (n + 2) = { a := gp.b * pred.a + gp.a * ppred.a, b := gp.b * p …
  exact continuants_recurrenceAux succ_nth_s_eq nth_conts_eq succ_nth_conts_eq
  -- 🎉 no goals
#align generalized_continued_fraction.continuants_recurrence GeneralizedContinuedFraction.continuants_recurrence

/-- Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`. -/
theorem numerators_recurrence {gp : Pair K} {ppredA predA : K}
    (succ_nth_s_eq : g.s.get? (n + 1) = some gp) (nth_num_eq : g.numerators n = ppredA)
    (succ_nth_num_eq : g.numerators (n + 1) = predA) :
    g.numerators (n + 2) = gp.b * predA + gp.a * ppredA := by
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : ∃ conts, g.continuants n = conts ∧ conts.a = ppredA
  -- ⊢ ∃ conts, continuants g n = conts ∧ conts.a = ppredA
  exact exists_conts_a_of_num nth_num_eq
  -- ⊢ numerators g (n + 2) = gp.b * predA + gp.a * ppredConts.a
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
    ∃ conts, g.continuants (n + 1) = conts ∧ conts.a = predA
  exact exists_conts_a_of_num succ_nth_num_eq
  -- ⊢ numerators g (n + 2) = gp.b * predConts.a + gp.a * ppredConts.a
  rw [num_eq_conts_a, continuants_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq]
  -- 🎉 no goals
#align generalized_continued_fraction.numerators_recurrence GeneralizedContinuedFraction.numerators_recurrence

/-- Shows that `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`. -/
theorem denominators_recurrence {gp : Pair K} {ppredB predB : K}
    (succ_nth_s_eq : g.s.get? (n + 1) = some gp) (nth_denom_eq : g.denominators n = ppredB)
    (succ_nth_denom_eq : g.denominators (n + 1) = predB) :
    g.denominators (n + 2) = gp.b * predB + gp.a * ppredB := by
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : ∃ conts, g.continuants n = conts ∧ conts.b = ppredB
  -- ⊢ ∃ conts, continuants g n = conts ∧ conts.b = ppredB
  exact exists_conts_b_of_denom nth_denom_eq
  -- ⊢ denominators g (n + 2) = gp.b * predB + gp.a * ppredConts.b
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
    ∃ conts, g.continuants (n + 1) = conts ∧ conts.b = predB
  exact exists_conts_b_of_denom succ_nth_denom_eq
  -- ⊢ denominators g (n + 2) = gp.b * predConts.b + gp.a * ppredConts.b
  rw [denom_eq_conts_b, continuants_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq]
  -- 🎉 no goals
#align generalized_continued_fraction.denominators_recurrence GeneralizedContinuedFraction.denominators_recurrence

end GeneralizedContinuedFraction
