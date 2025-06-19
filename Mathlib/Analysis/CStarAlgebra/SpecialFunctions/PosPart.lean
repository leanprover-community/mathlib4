/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-! # C⋆-algebraic facts about `a⁺` and `a⁻`. -/

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace CStarAlgebra

section SpanNonneg

open Submodule

/-- A C⋆-algebra is spanned by nonnegative elements of norm at most `r` -/
lemma span_nonneg_inter_closedBall {r : ℝ} (hr : 0 < r) :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.closedBall 0 r) = ⊤ := by
  rw [eq_top_iff, ← span_nonneg, span_le]
  intro x hx
  obtain (rfl | hx_pos) := eq_zero_or_norm_pos x
  · exact zero_mem _
  · suffices (r * ‖x‖⁻¹ : ℂ)⁻¹ • ((r * ‖x‖⁻¹ : ℂ) • x) = x by
      rw [← this]
      refine smul_mem _ _ (subset_span <| Set.mem_inter ?_ ?_)
      · norm_cast
        exact smul_nonneg (by positivity) hx
      · simp [mul_smul, norm_smul, abs_of_pos hr, inv_mul_cancel₀ hx_pos.ne']
    apply inv_smul_smul₀
    norm_cast
    positivity

/-- A C⋆-algebra is spanned by nonnegative elements of norm less than `r`. -/
lemma span_nonneg_inter_ball {r : ℝ} (hr : 0 < r) :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.ball 0 r) = ⊤ := by
  rw [eq_top_iff, ← span_nonneg_inter_closedBall (half_pos hr)]
  gcongr
  exact Metric.closedBall_subset_ball <| half_lt_self hr

/-- A C⋆-algebra is spanned by nonnegative contractions. -/
lemma span_nonneg_inter_unitClosedBall :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.closedBall 0 1) = ⊤ :=
  span_nonneg_inter_closedBall zero_lt_one

/-- A C⋆-algebra is spanned by nonnegative strict contractions. -/
lemma span_nonneg_inter_unitBall :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.ball 0 1) = ⊤ :=
  span_nonneg_inter_ball zero_lt_one

end SpanNonneg

open Complex in
lemma exists_sum_four_nonneg {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (a : A) :
    ∃ x : Fin 4 → A, (∀ i, 0 ≤ x i) ∧ (∀ i, ‖x i‖ ≤ ‖a‖) ∧ a = ∑ i : Fin 4, I ^ (i : ℕ) • x i := by
  use ![(realPart a)⁺, (imaginaryPart a)⁺, (realPart a)⁻, (imaginaryPart a)⁻]
  rw [← and_assoc, ← forall_and]
  constructor
  · intro i
    fin_cases i
    all_goals
      constructor
      · simp
        cfc_tac
    · exact CStarAlgebra.norm_posPart_le _ |>.trans <| realPart.norm_le a
    · exact CStarAlgebra.norm_posPart_le _ |>.trans <| imaginaryPart.norm_le a
    · exact CStarAlgebra.norm_negPart_le _ |>.trans <| realPart.norm_le a
    · exact CStarAlgebra.norm_negPart_le _ |>.trans <| imaginaryPart.norm_le a
  · nth_rw 1 [← CStarAlgebra.linear_combination_nonneg a]
    simp only [Fin.sum_univ_four, Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod, I_sq,
      I_pow_three]
    module

end CStarAlgebra
