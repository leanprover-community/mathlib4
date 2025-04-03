/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Translations

#align_import algebra.continued_fractions.continuants_recurrence from "leanprover-community/mathlib"@"5f11361a98ae4acd77f5c1837686f6f0102cdc25"

/-!
# Recurrence Lemmas for the Continuants (`conts`) Function of Continued Fractions

## Summary

Given a generalized continued fraction `g`, for all `n ≥ 1`, we prove that the continuants (`conts`)
function indeed satisfies the following recurrences:
- `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`, and
- `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`.
-/


namespace GenContFract

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem contsAux_recurrence {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some gp)
    (nth_contsAux_eq : g.contsAux n = ppred)
    (succ_nth_contsAux_eq : g.contsAux (n + 1) = pred) :
    g.contsAux (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ := by
  simp [*, contsAux, nextConts, nextDen, nextNum]
#align generalized_continued_fraction.continuants_aux_recurrence GenContFract.contsAux_recurrence

theorem conts_recurrenceAux {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some gp)
    (nth_contsAux_eq : g.contsAux n = ppred)
    (succ_nth_contsAux_eq : g.contsAux (n + 1) = pred) :
    g.conts (n + 1) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ := by
  simp [nth_cont_eq_succ_nth_contAux,
    contsAux_recurrence nth_s_eq nth_contsAux_eq succ_nth_contsAux_eq]
#align generalized_continued_fraction.continuants_recurrence_aux GenContFract.conts_recurrenceAux

/-- Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂` and `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`. -/
theorem conts_recurrence {gp ppred pred : Pair K} (succ_nth_s_eq : g.s.get? (n + 1) = some gp)
    (nth_conts_eq : g.conts n = ppred) (succ_nth_conts_eq : g.conts (n + 1) = pred) :
    g.conts (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ := by
  rw [nth_cont_eq_succ_nth_contAux] at nth_conts_eq succ_nth_conts_eq
  exact conts_recurrenceAux succ_nth_s_eq nth_conts_eq succ_nth_conts_eq
#align generalized_continued_fraction.continuants_recurrence GenContFract.conts_recurrence

/-- Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`. -/
theorem nums_recurrence {gp : Pair K} {ppredA predA : K}
    (succ_nth_s_eq : g.s.get? (n + 1) = some gp) (nth_num_eq : g.nums n = ppredA)
    (succ_nth_num_eq : g.nums (n + 1) = predA) :
    g.nums (n + 2) = gp.b * predA + gp.a * ppredA := by
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : ∃ conts, g.conts n = conts ∧ conts.a = ppredA :=
    exists_conts_a_of_num nth_num_eq
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
      ∃ conts, g.conts (n + 1) = conts ∧ conts.a = predA :=
    exists_conts_a_of_num succ_nth_num_eq
  rw [num_eq_conts_a, conts_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq]
#align generalized_continued_fraction.numerators_recurrence GenContFract.nums_recurrence

/-- Shows that `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`. -/
theorem dens_recurrence {gp : Pair K} {ppredB predB : K}
    (succ_nth_s_eq : g.s.get? (n + 1) = some gp) (nth_den_eq : g.dens n = ppredB)
    (succ_nth_den_eq : g.dens (n + 1) = predB) :
    g.dens (n + 2) = gp.b * predB + gp.a * ppredB := by
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : ∃ conts, g.conts n = conts ∧ conts.b = ppredB :=
    exists_conts_b_of_den nth_den_eq
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
      ∃ conts, g.conts (n + 1) = conts ∧ conts.b = predB :=
    exists_conts_b_of_den succ_nth_den_eq
  rw [den_eq_conts_b, conts_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq]
#align generalized_continued_fraction.denominators_recurrence GenContFract.dens_recurrence

end GenContFract
