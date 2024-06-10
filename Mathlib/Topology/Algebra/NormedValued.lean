/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valuation

/-!
# Correspondence between nontrivial nonarchimedean norms and rank one valuations

Nontrivial nonarchimedean norms correspond to rank one valuations.

## Main Definitions
* `NormedField.toValued` : the valued field structure on a nonarchimedean normed field `K`,
  determined by the norm.
* `Valued.toNormedField` : the normed field structure determined by a rank one valuation.

## Tags

norm, nonarchimedean, nontrivial, valuation, rank one
-/


noncomputable section

open Filter Set Valuation

open scoped NNReal

variable {K : Type*} [hK : NormedField K] (h : IsNonarchimedean (norm : K → ℝ))

namespace NormedField

/-- The valuation on a nonarchimedean normed field `K` defined as `nnnorm`. -/
def valuation : Valuation K ℝ≥0 where
  toFun           := nnnorm
  map_zero'       := nnnorm_zero
  map_one'        := nnnorm_one
  map_mul'        := nnnorm_mul
  map_add_le_max' := h

theorem valuation_apply (x : K) : valuation h x = ‖x‖₊ := rfl

/-- The valued field structure on a nonarchimedean normed field `K`, determined by the norm. -/
def toValued : Valued K ℝ≥0 :=
  { hK.toUniformSpace,
    @NonUnitalNormedRing.toNormedAddCommGroup K _ with
    v := valuation h
    is_topological_valuation := fun U => by
      rw [Metric.mem_nhds_iff]
      exact ⟨fun ⟨ε, hε, h⟩  =>
          ⟨Units.mk0 ⟨ε, le_of_lt hε⟩ (ne_of_gt hε), fun x hx ↦ h (mem_ball_zero_iff.mpr hx)⟩,
        fun ⟨ε, hε⟩ => ⟨(ε : ℝ), NNReal.coe_pos.mpr (Units.zero_lt _),
          fun x hx ↦ hε (mem_ball_zero_iff.mp hx)⟩⟩ }

end NormedField

namespace Valued

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [val : Valued L Γ₀] [hv : RankOne val.v]

/-- The norm function determined by a rank one valuation on a field `L`. -/
def norm : L → ℝ := fun x : L => hv.hom (Valued.v x)

theorem norm_nonneg (x : L) : 0 ≤ norm x := by simp only [norm, NNReal.zero_le_coe]

theorem norm_add_le (x y : L) : norm (x + y) ≤ max (norm x) (norm y) := by
  simp only [norm, NNReal.coe_le_coe, le_max_iff, StrictMono.le_iff_le hv.strictMono]
  exact le_max_iff.mp (Valuation.map_add_le_max' val.v _ _)

theorem norm_eq_zero {x : L} (hx : norm x = 0) : x = 0 := by
  simpa [norm, NNReal.coe_eq_zero, RankOne.hom_eq_zero_iff, zero_iff] using hx

variable (L) (Γ₀)

/-- The normed field structure determined by a rank one valuation. -/
def toNormedField : NormedField L :=
  { (inferInstance : Field L) with
    norm := norm
    dist := fun x y => norm (x - y)
    dist_self := fun x => by
      simp only [sub_self, norm, Valuation.map_zero, hv.hom.map_zero, NNReal.coe_zero]
    dist_comm := fun x y => by simp only [norm]; rw [← neg_sub, Valuation.map_neg]
    dist_triangle := fun x y z => by
      simp only [← sub_add_sub_cancel x y z]
      exact le_trans (norm_add_le _ _)
        (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _))
    edist_dist := fun x y => by simp only [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
    eq_of_dist_eq_zero := fun hxy => eq_of_sub_eq_zero (norm_eq_zero hxy)
    dist_eq := fun x y => rfl
    norm_mul' := fun x y => by simp only [norm, ← NNReal.coe_mul, _root_.map_mul]
    toUniformSpace := Valued.toUniformSpace
    uniformity_dist := by
      haveI : Nonempty { ε : ℝ // ε > 0 } := nonempty_Ioi_subtype
      ext U
      rw [hasBasis_iff.mp (Valued.hasBasis_uniformity L Γ₀), iInf_subtype', mem_iInf_of_directed]
      · simp only [exists_true_left, mem_principal, Subtype.exists, gt_iff_lt,
          Subtype.coe_mk, exists_prop, true_and_iff]
        refine ⟨fun ⟨ε, hε⟩ => ?_, fun ⟨r, hr_pos, hr⟩ => ?_⟩
        · set δ : ℝ≥0 := hv.hom ε with hδ
          have hδ_pos : 0 < δ := by
            rw [hδ, ← _root_.map_zero hv.hom]
            exact hv.strictMono (Units.zero_lt ε)
          use δ, hδ_pos
          apply subset_trans _ hε
          intro x hx
          simp only [mem_setOf_eq, norm, hδ, NNReal.val_eq_coe, NNReal.coe_lt_coe] at hx
          rw [mem_setOf, ← neg_sub, Valuation.map_neg]
          exact (RankOne.strictMono Valued.v).lt_iff_lt.mp hx
        · haveI : Nontrivial Γ₀ˣ := (nontrivial_iff_exists_ne (1 : Γ₀ˣ)).mpr
            ⟨RankOne.unit val.v, RankOne.unit_ne_one val.v⟩
          obtain ⟨u, hu⟩ := Real.exists_lt_of_strictMono hv.strictMono hr_pos
          use u
          apply subset_trans _ hr
          intro x hx
          simp only [norm, mem_setOf_eq]
          apply lt_trans _ hu
          rw [NNReal.coe_lt_coe, ← neg_sub, Valuation.map_neg]
          exact (RankOne.strictMono Valued.v).lt_iff_lt.mpr hx
      · simp only [gt_iff_lt, ge_iff_le, Directed]
        intro x y
        use min x y
        simp only [le_principal_iff, mem_principal, setOf_subset_setOf, Prod.forall]
        exact ⟨fun a b hab => lt_of_lt_of_le hab (min_le_left _ _), fun a b hab =>
            lt_of_lt_of_le hab (min_le_right _ _)⟩ }

end Valued
