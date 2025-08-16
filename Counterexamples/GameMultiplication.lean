/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import Mathlib.SetTheory.Game.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linter.DeprecatedModule

deprecated_module
  "This module is now at `CombinatorialGames.Counterexamples.Multiplication` in the CGT repo <https://github.com/vihdzp/combinatorial-games>"
  (since := "2025-08-06")

/-!
# Multiplication of pre-games can't be lifted to the quotient

We show that there exist equivalent pregames `x₁ ≈ x₂` and `y` such that `x₁ * y ≉ x₂ * y`. In
particular, we cannot define the multiplication of games in general.

The specific counterexample we use is `x₁ = y = {0 | 0}` and `x₂ = {-1, 0 | 0, 1}`. The first game
is colloquially known as `star`, so we use the name `star'` for the second. We prove that
`star ≈ star'` and `star * star ≈ star`, but `star' * star ≉ star`.
-/

namespace Counterexample

namespace PGame

open SetTheory PGame

/-- The game `{-1, 0 | 0, 1}`, which is equivalent but not identical to `*`. -/
def star' : PGame := ofLists [0, -1] [0, 1]

/-- `*'` is its own negative. -/
theorem neg_star' : -star' = star' := by
  simp [star']

/-- `*'` is equivalent to `*`. -/
theorem star'_equiv_star : star' ≈ star := by
  have le : star' ≤ star := by
    apply PGame.le_of_forall_lf
    · rintro ⟨i⟩
      fin_cases i
      · exact zero_lf_star
      · exact (neg_lt_zero_iff.2 PGame.zero_lt_one).trans_lf zero_lf_star
    · exact fun _ => lf_zero_le.2 ⟨⟨0, Nat.zero_lt_two⟩, le_rfl⟩
  constructor
  case' right => rw [← neg_le_neg_iff, neg_star, neg_star']
  assumption'

/-- The equation `** = *` is an identity, though not a relabelling. -/
theorem star_sq : star * star ≈ star := by
  have le : star * star ≤ star := by
    rw [le_iff_forall_lf]
    constructor <;>
    intro i
    · apply leftMoves_mul_cases i <;>
      intro _ _
      case' hl => rw [mul_moveLeft_inl]
      case' hr => rw [mul_moveLeft_inr]
      all_goals rw [lf_iff_game_lf]; simpa using zero_lf_star
    · refine lf_zero.2 ⟨toRightMovesMul (Sum.inl default), ?_⟩
      rintro (j | j) <;> -- Instance can't be inferred otherwise.
      exact isEmptyElim j
  constructor
  case' right =>
    rw [← neg_le_neg_iff];
    apply (neg_mul _ _).symm.equiv.1.trans;
    rw [neg_star]
  assumption'

/-- `*'* ⧏ *` implies `*'* ≉ *`. -/
theorem star'_mul_star_lf : star' * star ⧏ star := by
  rw [lf_iff_exists_le]
  refine Or.inr ⟨toRightMovesMul (Sum.inr ⟨⟨1, Nat.one_lt_two⟩, default⟩), ?_⟩
  rw [mul_moveRight_inr, le_iff_game_le]
  simp [star']

/-- Pre-game multiplication cannot be lifted to games. -/
theorem mul_not_lift : ∃ x₁ x₂ y : PGame, x₁ ≈ x₂ ∧ ¬ x₁ * y ≈ x₂ * y :=
  ⟨_, _, _, ⟨star'_equiv_star, fun h ↦ (PGame.Equiv.trans h star_sq).ge.not_gf star'_mul_star_lf⟩⟩

end PGame

end Counterexample
