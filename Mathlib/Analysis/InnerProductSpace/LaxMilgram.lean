/-
Copyright (c) 2022 Daniel Roca González. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Roca González
-/
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.NormedSpace.Banach
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Topology.MetricSpace.Antilipschitz

#align_import analysis.inner_product_space.lax_milgram from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# The Lax-Milgram Theorem

We consider a Hilbert space `V` over `ℝ`
equipped with a bounded bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ`.

Recall that a bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ` is *coercive*
iff `∃ C, (0 < C) ∧ ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u`.
Under the hypothesis that `B` is coercive we prove the Lax-Milgram theorem:
that is, the map `InnerProductSpace.continuousLinearMapOfBilin` from
`Analysis.InnerProductSpace.Dual` can be upgraded to a continuous equivalence
`IsCoercive.continuousLinearEquivOfBilin : V ≃L[ℝ] V`.

## References

* We follow the notes of Peter Howard's Spring 2020 *M612: Partial Differential Equations* lecture,
  see[howard]

## Tags

dual, Lax-Milgram
-/


noncomputable section

open IsROrC LinearMap ContinuousLinearMap InnerProductSpace

open LinearMap (ker range)

open RealInnerProductSpace NNReal

universe u

namespace IsCoercive

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

variable {B : V →L[ℝ] V →L[ℝ] ℝ}

local postfix:1024 "♯" => @continuousLinearMapOfBilin ℝ V _ _ _ _

theorem bounded_below (coercive : IsCoercive B) : ∃ C, 0 < C ∧ ∀ v, C * ‖v‖ ≤ ‖B♯ v‖ := by
  rcases coercive with ⟨C, C_ge_0, coercivity⟩
  -- ⊢ ∃ C, 0 < C ∧ ∀ (v : V), C * ‖v‖ ≤ ‖↑(continuousLinearMapOfBilin B) v‖
  refine' ⟨C, C_ge_0, _⟩
  -- ⊢ ∀ (v : V), C * ‖v‖ ≤ ‖↑(continuousLinearMapOfBilin B) v‖
  intro v
  -- ⊢ C * ‖v‖ ≤ ‖↑(continuousLinearMapOfBilin B) v‖
  by_cases h : 0 < ‖v‖
  -- ⊢ C * ‖v‖ ≤ ‖↑(continuousLinearMapOfBilin B) v‖
  · refine' (mul_le_mul_right h).mp _
    -- ⊢ C * ‖v‖ * ‖v‖ ≤ ‖↑(continuousLinearMapOfBilin B) v‖ * ‖v‖
    calc
      C * ‖v‖ * ‖v‖ ≤ B v v := coercivity v
      _ = ⟪B♯ v, v⟫_ℝ := (continuousLinearMapOfBilin_apply B v v).symm
      _ ≤ ‖B♯ v‖ * ‖v‖ := real_inner_le_norm (B♯ v) v
  · have : v = 0 := by simpa using h
    -- ⊢ C * ‖v‖ ≤ ‖↑(continuousLinearMapOfBilin B) v‖
    simp [this]
    -- 🎉 no goals
#align is_coercive.bounded_below IsCoercive.bounded_below

theorem antilipschitz (coercive : IsCoercive B) : ∃ C : ℝ≥0, 0 < C ∧ AntilipschitzWith C B♯ := by
  rcases coercive.bounded_below with ⟨C, C_pos, below_bound⟩
  -- ⊢ ∃ C, 0 < C ∧ AntilipschitzWith C ↑(continuousLinearMapOfBilin B)
  refine' ⟨C⁻¹.toNNReal, Real.toNNReal_pos.mpr (inv_pos.mpr C_pos), _⟩
  -- ⊢ AntilipschitzWith (Real.toNNReal C⁻¹) ↑(continuousLinearMapOfBilin B)
  refine' ContinuousLinearMap.antilipschitz_of_bound B♯ _
  -- ⊢ ∀ (x : V), ‖x‖ ≤ ↑(Real.toNNReal C⁻¹) * ‖↑(continuousLinearMapOfBilin B) x‖
  simp_rw [Real.coe_toNNReal', max_eq_left_of_lt (inv_pos.mpr C_pos), ←
    inv_mul_le_iff (inv_pos.mpr C_pos)]
  simpa using below_bound
  -- 🎉 no goals
#align is_coercive.antilipschitz IsCoercive.antilipschitz

theorem ker_eq_bot (coercive : IsCoercive B) : ker B♯ = ⊥ := by
  rw [LinearMapClass.ker_eq_bot]
  -- ⊢ Function.Injective ↑(continuousLinearMapOfBilin B)
  rcases coercive.antilipschitz with ⟨_, _, antilipschitz⟩
  -- ⊢ Function.Injective ↑(continuousLinearMapOfBilin B)
  exact antilipschitz.injective
  -- 🎉 no goals
#align is_coercive.ker_eq_bot IsCoercive.ker_eq_bot

theorem closed_range (coercive : IsCoercive B) : IsClosed (range B♯ : Set V) := by
  rcases coercive.antilipschitz with ⟨_, _, antilipschitz⟩
  -- ⊢ IsClosed ↑(range (continuousLinearMapOfBilin B))
  exact antilipschitz.isClosed_range B♯.uniformContinuous
  -- 🎉 no goals
#align is_coercive.closed_range IsCoercive.closed_range

theorem range_eq_top (coercive : IsCoercive B) : range B♯ = ⊤ := by
  haveI := coercive.closed_range.completeSpace_coe
  -- ⊢ range (continuousLinearMapOfBilin B) = ⊤
  rw [← (range B♯).orthogonal_orthogonal]
  -- ⊢ (range (continuousLinearMapOfBilin B))ᗮᗮ = ⊤
  rw [Submodule.eq_top_iff']
  -- ⊢ ∀ (x : V), x ∈ (range (continuousLinearMapOfBilin B))ᗮᗮ
  intro v w mem_w_orthogonal
  -- ⊢ inner w v = 0
  rcases coercive with ⟨C, C_pos, coercivity⟩
  -- ⊢ inner w v = 0
  obtain rfl : w = 0 := by
    rw [← norm_eq_zero, ← mul_self_eq_zero, ← mul_right_inj' C_pos.ne', mul_zero, ←
      mul_assoc]
    apply le_antisymm
    · calc
        C * ‖w‖ * ‖w‖ ≤ B w w := coercivity w
        _ = ⟪B♯ w, w⟫_ℝ := (continuousLinearMapOfBilin_apply B w w).symm
        _ = 0 := mem_w_orthogonal _ ⟨w, rfl⟩
    · exact mul_nonneg (mul_nonneg C_pos.le (norm_nonneg w)) (norm_nonneg w)
  exact inner_zero_left _
  -- 🎉 no goals
#align is_coercive.range_eq_top IsCoercive.range_eq_top

/-- The Lax-Milgram equivalence of a coercive bounded bilinear operator:
for all `v : V`, `continuousLinearEquivOfBilin B v` is the unique element `V`
such that `continuousLinearEquivOfBilin B v, w⟫ = B v w`.
The Lax-Milgram theorem states that this is a continuous equivalence.
-/
def continuousLinearEquivOfBilin (coercive : IsCoercive B) : V ≃L[ℝ] V :=
  ContinuousLinearEquiv.ofBijective B♯ coercive.ker_eq_bot coercive.range_eq_top
#align is_coercive.continuous_linear_equiv_of_bilin IsCoercive.continuousLinearEquivOfBilin

@[simp]
theorem continuousLinearEquivOfBilin_apply (coercive : IsCoercive B) (v w : V) :
    ⟪coercive.continuousLinearEquivOfBilin v, w⟫_ℝ = B v w :=
  continuousLinearMapOfBilin_apply B v w
#align is_coercive.continuous_linear_equiv_of_bilin_apply IsCoercive.continuousLinearEquivOfBilin_apply

theorem unique_continuousLinearEquivOfBilin (coercive : IsCoercive B) {v f : V}
    (is_lax_milgram : ∀ w, ⟪f, w⟫_ℝ = B v w) : f = coercive.continuousLinearEquivOfBilin v :=
  unique_continuousLinearMapOfBilin B is_lax_milgram
#align is_coercive.unique_continuous_linear_equiv_of_bilin IsCoercive.unique_continuousLinearEquivOfBilin

end IsCoercive
