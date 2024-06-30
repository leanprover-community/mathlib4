/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Translations

#align_import algebra.continued_fractions.terminated_stable from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Stabilisation of gcf Computations Under Termination

## Summary

We show that the continuants and convergents of a gcf stabilise once the gcf terminates.
-/


namespace GeneralizedContinuedFraction

variable {K : Type*} {g : GeneralizedContinuedFraction K} {n m : ℕ}

/-- If a gcf terminated at position `n`, it also terminated at `m ≥ n`. -/
theorem terminated_stable (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.TerminatedAt m :=
  g.s.terminated_stable n_le_m terminated_at_n
#align generalized_continued_fraction.terminated_stable GeneralizedContinuedFraction.terminated_stable

variable [DivisionRing K]

theorem continuantsAux_stable_step_of_terminated (terminated_at_n : g.TerminatedAt n) :
    g.continuantsAux (n + 2) = g.continuantsAux (n + 1) := by
  rw [terminatedAt_iff_s_none] at terminated_at_n
  simp only [continuantsAux, Nat.add_eq, Nat.add_zero, terminated_at_n]
#align generalized_continued_fraction.continuants_aux_stable_step_of_terminated GeneralizedContinuedFraction.continuantsAux_stable_step_of_terminated

theorem continuantsAux_stable_of_terminated (n_lt_m : n < m) (terminated_at_n : g.TerminatedAt n) :
    g.continuantsAux m = g.continuantsAux (n + 1) := by
  refine Nat.le_induction rfl (fun k hnk hk => ?_) _ n_lt_m
  rcases Nat.exists_eq_add_of_lt hnk with ⟨k, rfl⟩
  refine (continuantsAux_stable_step_of_terminated ?_).trans hk
  exact terminated_stable (Nat.le_add_right _ _) terminated_at_n
#align generalized_continued_fraction.continuants_aux_stable_of_terminated GeneralizedContinuedFraction.continuantsAux_stable_of_terminated

theorem convergents'Aux_stable_step_of_terminated {s : Stream'.Seq <| Pair K}
    (terminated_at_n : s.TerminatedAt n) : convergents'Aux s (n + 1) = convergents'Aux s n := by
  change s.get? n = none at terminated_at_n
  induction n generalizing s with
  | zero => simp only [convergents'Aux, terminated_at_n, Stream'.Seq.head]
  | succ n IH =>
    cases s_head_eq : s.head with
    | none => simp only [convergents'Aux, s_head_eq]
    | some gp_head =>
      have : s.tail.TerminatedAt n := by
        simp only [Stream'.Seq.TerminatedAt, s.get?_tail, terminated_at_n]
      have := IH this
      rw [convergents'Aux] at this
      simp [this, Nat.add_eq, add_zero, convergents'Aux, s_head_eq]
#align generalized_continued_fraction.convergents'_aux_stable_step_of_terminated GeneralizedContinuedFraction.convergents'Aux_stable_step_of_terminated

theorem convergents'Aux_stable_of_terminated {s : Stream'.Seq <| Pair K} (n_le_m : n ≤ m)
    (terminated_at_n : s.TerminatedAt n) : convergents'Aux s m = convergents'Aux s n := by
  induction' n_le_m with m n_le_m IH
  · rfl
  · refine (convergents'Aux_stable_step_of_terminated ?_).trans IH
    exact s.terminated_stable n_le_m terminated_at_n
#align generalized_continued_fraction.convergents'_aux_stable_of_terminated GeneralizedContinuedFraction.convergents'Aux_stable_of_terminated

theorem continuants_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.continuants m = g.continuants n := by
  simp only [nth_cont_eq_succ_nth_cont_aux,
    continuantsAux_stable_of_terminated (Nat.pred_le_iff.mp n_le_m) terminated_at_n]
#align generalized_continued_fraction.continuants_stable_of_terminated GeneralizedContinuedFraction.continuants_stable_of_terminated

theorem numerators_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.numerators m = g.numerators n := by
  simp only [num_eq_conts_a, continuants_stable_of_terminated n_le_m terminated_at_n]
#align generalized_continued_fraction.numerators_stable_of_terminated GeneralizedContinuedFraction.numerators_stable_of_terminated

theorem denominators_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.denominators m = g.denominators n := by
  simp only [denom_eq_conts_b, continuants_stable_of_terminated n_le_m terminated_at_n]
#align generalized_continued_fraction.denominators_stable_of_terminated GeneralizedContinuedFraction.denominators_stable_of_terminated

theorem convergents_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.convergents m = g.convergents n := by
  simp only [convergents, denominators_stable_of_terminated n_le_m terminated_at_n,
    numerators_stable_of_terminated n_le_m terminated_at_n]
#align generalized_continued_fraction.convergents_stable_of_terminated GeneralizedContinuedFraction.convergents_stable_of_terminated

theorem convergents'_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.TerminatedAt n) :
    g.convergents' m = g.convergents' n := by
  simp only [convergents', convergents'Aux_stable_of_terminated n_le_m terminated_at_n]
#align generalized_continued_fraction.convergents'_stable_of_terminated GeneralizedContinuedFraction.convergents'_stable_of_terminated

end GeneralizedContinuedFraction
