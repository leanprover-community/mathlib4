/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Ultra
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

def toValuativeRel : ValuativeRel R := .ofValuation valuation'

open Filter Topology

scoped[NormedField] attribute [instance] NormedField.toValuativeRel

lemma rel_iff_le (x y : R) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := Iff.rfl

@[simp]
lemma coe_posSubmonoid_ne_zero (x : (ValuativeRel.posSubmonoid R)) :
    (x : R) ≠ 0 := by
  have := x.prop
  rw [ValuativeRel.posSubmonoid_def] at this
  simpa [rel_iff_le] using this

lemma norm_pos_posSubmonoid (x : (ValuativeRel.posSubmonoid R)) :
    0 < ‖(x : R)‖ := by
  simp

instance : (valuation' (R := R)).Compatible := .ofValuation _

/-- Norm lifted from the ValueGroupWithZero. -/
noncomputable
def ofValueGroupWithZero : ValuativeRel.ValueGroupWithZero R →*₀ ℝ≥0 :=
  ⟨⟨ValuativeRel.ValueGroupWithZero.lift (fun r s ↦ ‖r‖₊ / ‖(s : R)‖₊) <| by
    intro x y r s
    simp only [rel_iff_le]
    intro h h'
    rw [div_eq_div_iff]
    · simp only [norm_mul, NNReal.val_eq_coe, ← NNReal.coe_inj, NNReal.coe_mul,
      coe_nnnorm] at h h' ⊢
      linarith
    · simp
    · simp, by simp⟩, by simp, by
      intros
      simp only
      apply ValuativeRel.ValueGroupWithZero.lift_mul
      field_simp⟩

lemma ofValueGroupWithZero_strictMono : StrictMono (ofValueGroupWithZero (R := R)) := by
  intro a b h
  simp only [ofValueGroupWithZero]
  induction a using ValuativeRel.ValueGroupWithZero.ind with | mk a r
  induction b using ValuativeRel.ValueGroupWithZero.ind with | mk b s
  simp only [ValuativeRel.ValueGroupWithZero.mk_lt_mk, rel_iff_le, norm_mul, not_le,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, ValuativeRel.ValueGroupWithZero.lift_mk] at h ⊢
  rw [div_lt_div_iff₀]
  · exact h.right
  · simp
  · simp

instance : ValuativeRel.IsRankLeOne R where
  nonempty := ⟨ofValueGroupWithZero, ofValueGroupWithZero_strictMono⟩

-- TODO:
-- instance : ValuativeTopology R where
--   mem_nhds_iff s := by
--     simp only [Metric.mem_nhds_iff, gt_iff_lt]
--     constructor
--     · rintro ⟨ε, ⟨hε, hs⟩⟩
--       by_cases h : ∃ γ : (ValuativeRel.ValueGroupWithZero R)ˣ, ofValueGroupWithZero γ.val ≤ ε
--       · refine h.imp ?_
--         intro γ hγ
--         refine hs.trans' ?_
--         intro
--         simp only [Metric.mem_ball, dist_zero_right, ← ofValueGroupWithZero_strictMono.lt_iff_lt,
--           mem_setOf_eq]
--         intro h
--         simpa [ofValueGroupWithZero] using hγ.trans_lt' h
--       · push_neg at h
--         sorry
--     · rintro ⟨γ, hs⟩
--       refine ⟨ofValueGroupWithZero γ.val, by simp [zero_lt_iff], hs.trans' ?_⟩
--       intro
--       simp only [Metric.mem_ball, dist_zero_right, ← ofValueGroupWithZero_strictMono.lt_iff_lt,
--         mem_setOf_eq]
--       apply lt_of_le_of_lt
--       simp [ofValueGroupWithZero]

end NormedField
