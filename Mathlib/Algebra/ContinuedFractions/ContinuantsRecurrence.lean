/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.Translations

/-!
# Recurrence Lemmas for the Continuants (`conts`) Function of Continued Fractions

## Summary

Given a generalized continued fraction `g`, for all `n ≥ 1`, we prove that the continuants (`conts`)
function indeed satisfies the following recurrences:
- `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`, and
- `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`.
-/

public section


namespace GenContFract

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem contsAux_recurrence {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some gp)
    (nth_contsAux_eq : g.contsAux n = ppred)
    (succ_nth_contsAux_eq : g.contsAux (n + 1) = pred) :
    g.contsAux (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ := by
  simp [*, contsAux, nextConts, nextDen, nextNum]

theorem contsAux_recurrence! :
    g.contsAux (n + 2) = ⟨
      g.partDens! n * (g.contsAux (n + 1)).a + g.partNums! n * (g.contsAux n).a,
      g.partDens! n * (g.contsAux (n + 1)).b + g.partNums! n * (g.contsAux n).b
    ⟩ := by
  rcases hn : g.s.get? n with _ | ⟨a, b⟩ <;>
  simp [contsAux, partDens!, partDens, partNums!, partNums, nextConts, nextDen, nextNum, hn]

theorem conts_recurrenceAux {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some gp)
    (nth_contsAux_eq : g.contsAux n = ppred)
    (succ_nth_contsAux_eq : g.contsAux (n + 1) = pred) :
    g.conts (n + 1) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ := by
  rw [nth_cont_eq_succ_nth_contAux,
    contsAux_recurrence nth_s_eq nth_contsAux_eq succ_nth_contsAux_eq]

/-- Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂` and `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`. -/
theorem conts_recurrence {gp ppred pred : Pair K} (succ_nth_s_eq : g.s.get? (n + 1) = some gp)
    (nth_conts_eq : g.conts n = ppred) (succ_nth_conts_eq : g.conts (n + 1) = pred) :
    g.conts (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ :=
  contsAux_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq

theorem conts_recurrence! :
    g.conts (n + 2) = ⟨
      g.partDens! (n + 1) * (g.conts (n + 1)).a + g.partNums! (n + 1) * (g.conts n).a,
      g.partDens! (n + 1) * (g.conts (n + 1)).b + g.partNums! (n + 1) * (g.conts n).b
    ⟩ := by
  rw [nth_cont_eq_succ_nth_contAux, contsAux_recurrence!]
  rfl

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

theorem nums_recurrence! :
    g.nums (n + 2) =
      g.partDens! (n + 1) * g.nums (n + 1) + g.partNums! (n + 1) * g.nums n := by
  rw [num_eq_conts_a, conts_recurrence!]
  rfl

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

theorem dens_recurrence! :
    g.dens (n + 2) =
      g.partDens! (n + 1) * g.dens (n + 1) + g.partNums! (n + 1) * g.dens n := by
  rw [den_eq_conts_b, conts_recurrence!]
  rfl

end GenContFract
