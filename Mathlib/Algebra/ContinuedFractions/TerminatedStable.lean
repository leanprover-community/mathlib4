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


namespace GCF

variable {K : Type*} {g : GCF K} {n m : ℕ}

#noalign generalized_continued_fraction.terminated_stable

variable [DivisionRing K] [DecidableEq K]

#noalign generalized_continued_fraction.continuants_aux_stable_step_of_terminated

#noalign generalized_continued_fraction.continuants_aux_stable_of_terminated

#noalign generalized_continued_fraction.convergents'_aux_stable_step_of_terminated

#noalign generalized_continued_fraction.convergents'_aux_stable_of_terminated

#noalign generalized_continued_fraction.continuants_stable_of_terminated

#noalign generalized_continued_fraction.numerators_stable_of_terminated

#noalign generalized_continued_fraction.denominators_stable_of_terminated

theorem take_stable (n_le_m : n ≤ m) (terminatedAt_n : g.s.TerminatedAt n) :
    g.take m = g.take n := by
  unfold take
  rw [Seq'.take_stable terminatedAt_n n_le_m]

theorem convergents_stable (n_le_m : n ≤ m) (terminatedAt_n : g.s.TerminatedAt n) :
    g.convergents m = g.convergents n := by
  unfold convergents
  rw [take_stable n_le_m terminatedAt_n]
#align generalized_continued_fraction.convergents_stable_of_terminated GCF.convergents_stable

#noalign generalized_continued_fraction.convergents'_stable_of_terminated

end GCF

namespace SCF

variable {K : Type*} {s : SCF K} {n m : ℕ}

theorem take_stable (n_le_m : n ≤ m) (terminatedAt_n : s.s.TerminatedAt n) :
    s.take m = s.take n := by
  unfold take
  rw [Seq'.take_stable terminatedAt_n n_le_m]

end SCF

namespace CF

variable {K : Type*} {c : CF K} {n m : ℕ}

variable [DivisionRing K]

theorem take_stable (n_le_m : n ≤ m) (terminatedAt_n : c.s.TerminatedAt n) :
    c.take m = c.take n := by
  unfold take
  rw [Seq'.take_stable terminatedAt_n n_le_m]

theorem convergents_stable (n_le_m : n ≤ m) (terminatedAt_n : c.s.TerminatedAt n) :
    c.convergents m = c.convergents n := by
  unfold convergents
  rw [take_stable n_le_m terminatedAt_n]

end CF
