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


namespace GenContFract

variable {K : Type*} {g : GenContFract K} {n m : ℕ}

/-- If a gcf terminated at position `n`, it also terminated at `m ≥ n`. -/
theorem terminated_stable (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.TerminatedAt m :=
  g.s.terminated_stable n_le_m terminatedAt_n
#align generalized_continued_fraction.terminated_stable GenContFract.terminated_stable

variable [DivisionRing K]

theorem contsAux_stable_step_of_terminated (terminatedAt_n : g.TerminatedAt n) :
    g.contsAux (n + 2) = g.contsAux (n + 1) := by
  rw [terminatedAt_iff_s_none] at terminatedAt_n
  simp only [contsAux, Nat.add_eq, Nat.add_zero, terminatedAt_n]
#align generalized_continued_fraction.continuants_aux_stable_step_of_terminated GenContFract.contsAux_stable_step_of_terminated

theorem contsAux_stable_of_terminated (n_lt_m : n < m) (terminatedAt_n : g.TerminatedAt n) :
    g.contsAux m = g.contsAux (n + 1) := by
  refine Nat.le_induction rfl (fun k hnk hk => ?_) _ n_lt_m
  rcases Nat.exists_eq_add_of_lt hnk with ⟨k, rfl⟩
  refine (contsAux_stable_step_of_terminated ?_).trans hk
  exact terminated_stable (Nat.le_add_right _ _) terminatedAt_n
#align generalized_continued_fraction.continuants_aux_stable_of_terminated GenContFract.contsAux_stable_of_terminated

theorem convs'Aux_stable_step_of_terminated {s : Stream'.Seq <| Pair K}
    (terminatedAt_n : s.TerminatedAt n) : convs'Aux s (n + 1) = convs'Aux s n := by
  change s.get? n = none at terminatedAt_n
  induction n generalizing s with
  | zero => simp only [convs'Aux, terminatedAt_n, Stream'.Seq.head]
  | succ n IH =>
    cases s_head_eq : s.head with
    | none => simp only [convs'Aux, s_head_eq]
    | some gp_head =>
      have : s.tail.TerminatedAt n := by
        simp only [Stream'.Seq.TerminatedAt, s.get?_tail, terminatedAt_n]
      have := IH this
      rw [convs'Aux] at this
      simp [this, Nat.add_eq, add_zero, convs'Aux, s_head_eq]
#align generalized_continued_fraction.convergents'_aux_stable_step_of_terminated GenContFract.convs'Aux_stable_step_of_terminated

theorem convs'Aux_stable_of_terminated {s : Stream'.Seq <| Pair K} (n_le_m : n ≤ m)
    (terminatedAt_n : s.TerminatedAt n) : convs'Aux s m = convs'Aux s n := by
  induction' n_le_m with m n_le_m IH
  · rfl
  · refine (convs'Aux_stable_step_of_terminated ?_).trans IH
    exact s.terminated_stable n_le_m terminatedAt_n
#align generalized_continued_fraction.convergents'_aux_stable_of_terminated GenContFract.convs'Aux_stable_of_terminated

theorem conts_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.conts m = g.conts n := by
  simp only [nth_cont_eq_succ_nth_contAux,
    contsAux_stable_of_terminated (Nat.pred_le_iff.mp n_le_m) terminatedAt_n]
#align generalized_continued_fraction.continuants_stable_of_terminated GenContFract.conts_stable_of_terminated

theorem nums_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.nums m = g.nums n := by
  simp only [num_eq_conts_a, conts_stable_of_terminated n_le_m terminatedAt_n]
#align generalized_continued_fraction.numerators_stable_of_terminated GenContFract.nums_stable_of_terminated

theorem dens_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.dens m = g.dens n := by
  simp only [den_eq_conts_b, conts_stable_of_terminated n_le_m terminatedAt_n]
#align generalized_continued_fraction.denominators_stable_of_terminated GenContFract.dens_stable_of_terminated

theorem convs_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.convs m = g.convs n := by
  simp only [convs, dens_stable_of_terminated n_le_m terminatedAt_n,
    nums_stable_of_terminated n_le_m terminatedAt_n]
#align generalized_continued_fraction.convergents_stable_of_terminated GenContFract.convs_stable_of_terminated

theorem convs'_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.convs' m = g.convs' n := by
  simp only [convs', convs'Aux_stable_of_terminated n_le_m terminatedAt_n]
#align generalized_continued_fraction.convergents'_stable_of_terminated GenContFract.convs'_stable_of_terminated

end GenContFract
