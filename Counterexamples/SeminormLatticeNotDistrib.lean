/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathlib.Analysis.Seminorm

#align_import seminorm_lattice_not_distrib from "leanprover-community/mathlib"@"328375597f2c0dd00522d9c2e5a33b6a6128feeb"

/-!
# The lattice of seminorms is not distributive

We provide an example of three seminorms over the ℝ-vector space ℝ×ℝ which don't satisfy the lattice
distributivity property `(p ⊔ q1) ⊓ (p ⊔ q2) ≤ p ⊔ (q1 ⊓ q2)`.

This proves the lattice `Seminorm ℝ (ℝ × ℝ)` is not distributive.

## References

* https://en.wikipedia.org/wiki/Seminorm#Examples
-/


open Seminorm

open scoped NNReal

namespace Counterexample

namespace SeminormNotDistrib

@[simps!]
noncomputable def p : Seminorm ℝ (ℝ × ℝ) :=
  (normSeminorm ℝ ℝ).comp (LinearMap.fst _ _ _) ⊔ (normSeminorm ℝ ℝ).comp (LinearMap.snd _ _ _)
#align counterexample.seminorm_not_distrib.p Counterexample.SeminormNotDistrib.p

@[simps!]
noncomputable def q1 : Seminorm ℝ (ℝ × ℝ) :=
  (4 : ℝ≥0) • (normSeminorm ℝ ℝ).comp (LinearMap.fst _ _ _)
#align counterexample.seminorm_not_distrib.q1 Counterexample.SeminormNotDistrib.q1

@[simps!]
noncomputable def q2 : Seminorm ℝ (ℝ × ℝ) :=
  (4 : ℝ≥0) • (normSeminorm ℝ ℝ).comp (LinearMap.snd _ _ _)
#align counterexample.seminorm_not_distrib.q2 Counterexample.SeminormNotDistrib.q2

theorem eq_one : (p ⊔ q1 ⊓ q2) (1, 1) = 1 := by
  suffices ⨅ x : ℝ × ℝ, q1 x + q2 (1 - x) ≤ 1 by simpa
  apply ciInf_le_of_le bddBelow_range_add ((0, 1) : ℝ × ℝ); dsimp [q1, q2]
  simp only [abs_zero, smul_zero, sub_self, add_zero, zero_le_one]
#align counterexample.seminorm_not_distrib.eq_one Counterexample.SeminormNotDistrib.eq_one

/-- This is a counterexample to the distributivity of the lattice `Seminorm ℝ (ℝ × ℝ)`. -/
theorem not_distrib : ¬(p ⊔ q1) ⊓ (p ⊔ q2) ≤ p ⊔ q1 ⊓ q2 := by
  intro le_sup_inf
  have c : ¬4 / 3 ≤ (1 : ℝ) := by norm_num
  apply c; nth_rw 1 [← eq_one]
  apply le_trans _ (le_sup_inf _)
  apply le_ciInf; intro x
  rcases le_or_lt x.fst (1 / 3) with h1 | h1
  · rcases le_or_lt x.snd (2 / 3) with h2 | h2
    · calc
        4 / 3 = 4 * (1 - 2 / 3) := by norm_num
        _ ≤ 4 * (1 - x.snd) := by gcongr
        _ ≤ 4 * |1 - x.snd| := by gcongr; apply le_abs_self
        _ = q2 ((1, 1) - x) := by simp; rfl
        _ ≤ (p ⊔ q2) ((1, 1) - x) := le_sup_right
        _ ≤ (p ⊔ q1) x + (p ⊔ q2) ((1, 1) - x) := le_add_of_nonneg_left (apply_nonneg _ _)
    · calc
        4 / 3 = 2 / 3 + (1 - 1 / 3) := by norm_num
        _ ≤ x.snd + (1 - x.fst) := by gcongr
        _ ≤ |x.snd| + |1 - x.fst| := add_le_add (le_abs_self _) (le_abs_self _)
        _ ≤ p x + p ((1, 1) - x) := by exact add_le_add le_sup_right le_sup_left
        _ ≤ (p ⊔ q1) x + (p ⊔ q2) ((1, 1) - x) := add_le_add le_sup_left le_sup_left
  · calc
      4 / 3 = 4 * (1 / 3) := by norm_num
      _ ≤ 4 * x.fst := by gcongr
      _ ≤ 4 * |x.fst| := by gcongr; apply le_abs_self
      _ = q1 x := rfl
      _ ≤ (p ⊔ q1) x := le_sup_right
      _ ≤ (p ⊔ q1) x + (p ⊔ q2) ((1, 1) - x) := le_add_of_nonneg_right (apply_nonneg _ _)
#align counterexample.seminorm_not_distrib.not_distrib Counterexample.SeminormNotDistrib.not_distrib

end SeminormNotDistrib

end Counterexample
