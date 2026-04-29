/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.CauSeq.Completion
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Data.Real.Basic

import all Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean

/-!
# The real numbers as Cauchy completion of the rationals
-/

public section

namespace Real

/-- `Real.equivCauchy` as a ring equivalence. -/
def ringEquivCauchy : ℝ ≃+* CauSeq.Completion.Cauchy (abs : ℚ → ℚ) :=
  { equivCauchy with
    map_add' := Real.cauchy_add
    map_mul' := Real.cauchy_mul }

open CauSeq in
theorem cauSeq_converges (f : CauSeq ℝ abs) : ∃ x, f ≈ const abs x := by
  let s := {x : ℝ | const abs x < f}
  have lb : ∃ x, x ∈ s := exists_lt f
  have ub' : ∀ x, f < const abs x → ∀ y ∈ s, y ≤ x := fun x h y yS =>
    le_of_lt <| const_lt.1 <| CauSeq.lt_trans yS h
  have ub : ∃ x, ∀ y ∈ s, y ≤ x := (exists_gt f).imp ub'
  refine ⟨sSup s, ((lt_total _ _).resolve_left fun h => ?_).resolve_right fun h => ?_⟩
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine (csSup_le lb (ub' _ ?_)).not_gt (sub_lt_self _ (half_pos ε0))
    refine ⟨_, half_pos ε0, i, fun j ij => ?_⟩
    rw [sub_apply, const_apply, sub_right_comm, le_sub_iff_add_le, add_halves]
    exact ih _ ij
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine (le_csSup ub ?_).not_gt ((lt_add_iff_pos_left _).2 (half_pos ε0))
    refine ⟨_, half_pos ε0, i, fun j ij => ?_⟩
    rw [sub_apply, const_apply, add_comm, ← sub_sub, le_sub_iff_add_le, add_halves]
    exact ih _ ij

instance : CauSeq.IsComplete ℝ abs :=
  ⟨cauSeq_converges⟩

/-- Show an underlying Cauchy sequence for real numbers.

The representative chosen is the one passed in the VM to `Quot.mk`, so two Cauchy sequences
converging to the same number may be printed differently.
-/
unsafe instance : Repr ℝ where
  reprPrec r p := Repr.addAppParen ("Real.ofCauchy " ++ repr (ringEquivCauchy r)) p

end Real
