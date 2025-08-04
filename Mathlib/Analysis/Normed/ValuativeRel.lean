/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!

# Nonarchimedean normed fields carry a valuative topology

In this file, we provide a helper instance
for `ValuativeRel R` derived from a `NormedRing R` when `NormMulClass R` and `IsUltrametricDist R`,
so that downstream files can refer to `ValuativeRel R`,
to facilitate a refactor.

-/

variable {R : Type*} [NormedCommRing R] [NormOneClass R]
  [NormMulClass R] [IsUltrametricDist R]

open Filter Set Valuation

open scoped NNReal

namespace NormedField

/-- The valuation on a nonarchimedean normed field `K` defined as `nnnorm`.
Should replace `NormedField.valuation` in the future. -/
def valuation' : Valuation R ℝ≥0 where
  toFun           := nnnorm
  map_zero'       := nnnorm_zero
  map_one'        := nnnorm_one
  map_mul'        := nnnorm_mul
  map_add_le_max' := IsUltrametricDist.norm_add_le_max

@[simp]
theorem valuation'_apply (x : R) : valuation' x = ‖x‖₊ := rfl

/-- A nonarchimedean normed ring carries a valuative relation induced by the norm.
This is a scoped instance. -/
def toValuativeRel : ValuativeRel R := .ofValuation valuation'

open Filter Topology

scoped[NormedField] attribute [instance] NormedField.toValuativeRel

lemma rel_iff_le (x y : R) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := Iff.rfl

lemma norm_pos_posSubmonoid (x : (ValuativeRel.posSubmonoid R)) :
    0 < ‖(x : R)‖ := by
  simp

instance : (valuation' (R := R)).Compatible := .ofValuation _

instance : ValuativeRel.IsRankLeOne R :=
  .of_compatible_mulArchimedean (valuation' (R := R))

instance {K : Type*} [NormedField K] [IsUltrametricDist K] :
    IsValuativeTopology K := by
  have he : valuation'.IsEquiv (ValuativeRel.valuation K) := ValuativeRel.isEquiv _ _
  refine .of_hasBasis (Metric.nhds_basis_ball.to_hasBasis' ?_ ?_)
  · intro ε hε
    simp only [true_and]
    rcases discreteTopology_or_nontriviallyNormedField K with _|⟨⟨⟨_, rfl⟩⟩⟩
    · use 1
      intro x
      rcases eq_or_ne x 0 with rfl | hx
      · simp [hε]
      -- this is where we need DivisionRing as opposed to NormedCommRing with
      --`‖x * y‖ = ‖x‖ * ‖y‖`, because we need to be able to have an element `x` of `‖x‖ < 1`
      rw [← NormedDivisionRing.norm_eq_one_iff_ne_zero_of_discrete] at hx
      simp [hx, ← he.lt_one_iff_lt_one, ← NNReal.coe_lt_one]
    · obtain ⟨x, hx, hx'⟩ := exists_norm_lt K hε
      refine ⟨Units.mk0 (ValuativeRel.valuation K x) ?_, ?_⟩
      · rw [← he.ne_zero]
        simpa using hx
      · intro y
        simp only [Units.val_mk0, ← he.lt_iff_lt, valuation'_apply, ← NNReal.coe_lt_coe,
          coe_nnnorm, mem_setOf_eq, Metric.mem_ball, dist_zero_right]
        order
  · intro γ _
    obtain ⟨r, s, hr⟩ := ValuativeRel.valuation_surjective γ.val
    simp_rw [← hr, ← Valuation.map_div, ← he.lt_iff_lt]
    simp only [valuation'_apply, map_div₀, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_div]
    simp_rw [← dist_zero_right]
    rcases eq_or_ne r 0 with rfl | hr
    · simp [eq_comm] at hr
    refine Metric.ball_mem_nhds _ ?_
    simp [hr]

end NormedField
