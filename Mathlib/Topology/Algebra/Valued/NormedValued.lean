/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Correspondence between nonarchimedean norms and valuations of rank at most one

Nonarchimedean norms correspond to valuations of rank ≤ 1,
and nontrivial such norms to valuations of rank 1

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

section

variable {K : Type*} [hK : NormedField K] [IsUltrametricDist K]

namespace NormedField

/-- The valuation on a nonarchimedean normed field `K` defined as `nnnorm`. -/
def valuation : Valuation K ℝ≥0 where
  toFun           := nnnorm
  map_zero'       := nnnorm_zero
  map_one'        := nnnorm_one
  map_mul'        := nnnorm_mul
  map_add_le_max' := IsUltrametricDist.norm_add_le_max

@[simp]
theorem valuation_apply (x : K) : valuation x = ‖x‖₊ := rfl

/-- The valuation of a normed field has rank at most one -/
instance : RankLeOne (valuation (K := K)) where
  hom := MonoidWithZeroHom.id _
  strictMono' _ _ h := h

/-- The valued field structure on a nonarchimedean normed field `K`, determined by the norm. -/
def toValued : Valued K ℝ≥0 :=
  { hK.toUniformSpace,
    inferInstanceAs (IsUniformAddGroup K) with
    v := valuation
    is_topological_valuation := fun U => by
      rw [Metric.mem_nhds_iff]
      constructor
      · intro ⟨ε, hε, hU⟩
        rcases RankLeOne.exists_val_lt (valuation (K := K)) with H | H
           -- isTriviallyValued_or_exists h hε with (H | ⟨x, hpos, h_lt⟩)
        · refine ⟨1, one_mem _, one_ne_zero, ?_⟩
          intro x hx
          simp only [Units.val_one, mem_setOf_eq] at hx
          suffices x = 0 by
            apply hU
            simp only [this, Metric.mem_ball, dist_self, hε]
          by_cases hx' : valuation (K := K)  x = 0
          · exact nnnorm_eq_zero.mp hx'
          · exfalso
            apply not_le.mpr hx
            apply le_of_eq
            symm
            have : IsUnit (⟨valuation x, valuation.mem_rangeGroup₀⟩ : valuation.rangeGroup₀) := by
              rw [isUnit_iff_ne_zero, ne_eq, ← Subtype.coe_inj,
                MonoidHomWithZero.range₀_coe_zero]
              exact hx'
            simpa only [Units.ext_iff, this.unit_spec, Units.val_one,
              Submonoid.mk_eq_one] using H.elim this.unit 1
        · obtain ⟨x, hx, hxy⟩ := H (γ := ⟨ε, le_of_lt hε⟩) (pos_iff_ne_zero.mp hε)
          use valuation x, valuation.mem_rangeGroup₀,
            (ne_zero_iff valuation).mpr hx
          intro y hy
          apply hU
          simp only [Metric.mem_ball, dist_zero_right]
          simp only [Units.val_mk0, mem_setOf_eq] at hy
          exact lt_trans hy hxy
      · rintro ⟨γ, _, hγ, hU⟩
        use (γ : ℝ), NNReal.coe_pos.mpr (pos_of_ne_zero hγ)
        intro x hx
        apply hU
        simpa only [Metric.mem_ball, dist_zero_right, mem_setOf_eq] using hx }

instance {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] :
    Valuation.RankOne (valuation (K := K)) where
  hom := .id _
  strictMono' := strictMono_id
  nontrivial' := (exists_one_lt_norm K).imp fun x h ↦ by
    have h' : x ≠ 0 := norm_eq_zero.not.mp (h.gt.trans' (by simp)).ne'
    simp [valuation_apply, ← NNReal.coe_inj, h.ne', h']

end NormedField

end

namespace Valued

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [val : Valued L Γ₀] [hv : RankLeOne val.v]

/-- The norm function determined by a rank one valuation on a field `L`. -/
def norm : L → ℝ := fun x : L => hv.hom (Valued.v x)

theorem norm_def {x : L} : Valued.norm x = hv.hom (Valued.v x) := rfl

theorem norm_nonneg (x : L) : 0 ≤ norm x := by simp only [norm, NNReal.zero_le_coe]

theorem norm_add_le (x y : L) : norm (x + y) ≤ max (norm x) (norm y) := by
  simp only [norm, NNReal.coe_le_coe, le_max_iff, StrictMono.le_iff_le hv.strictMono]
  exact le_max_iff.mp (Valuation.map_add_le_max' val.v _ _)

theorem norm_eq_zero {x : L} (hx : norm x = 0) : x = 0 := by
  simpa [norm, NNReal.coe_eq_zero, RankLeOne.hom_eq_zero_iff, zero_iff] using hx

theorem norm_pos_iff_valuation_pos {x : L} : 0 < Valued.norm x ↔ (0 : Γ₀) < v x := by
  rw [norm_def, ← NNReal.coe_zero, NNReal.coe_lt_coe,
    ← map_zero (RankLeOne.hom (v (R := L))), StrictMono.lt_iff_lt]
  exact RankLeOne.strictMono v

variable (L) (Γ₀)

/-- The normed field structure determined by a rank ≤ one valuation. -/
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
    eq_of_dist_eq_zero := fun hxy => eq_of_sub_eq_zero (norm_eq_zero hxy)
    dist_eq := fun x y => rfl
    norm_mul := fun x y => by simp only [norm, ← NNReal.coe_mul, map_mul]
    toUniformSpace := Valued.toUniformSpace
    uniformity_dist := by
      haveI : Nonempty { ε : ℝ // ε > 0 } := nonempty_Ioi_subtype
      ext U
      rw [hasBasis_iff.mp (Valued.hasBasis_uniformity L Γ₀), iInf_subtype', mem_iInf_of_directed]
      · simp only [true_and, mem_principal, Subtype.exists, gt_iff_lt, exists_prop]
        constructor
        · rintro ⟨a, H⟩
          use hv.hom a
          constructor
          · suffices (0 : ℝ) = hv.hom 0 by
              rw [this]
              apply hv.strictMono
              rw [zero_lt_iff]
              have := a.ne_zero
              rwa [ne_eq, ← Subtype.coe_inj] at this
            simp
          · intro p hp
            apply H
            simp only [mem_setOf_eq] at hp ⊢
            rw [← StrictMono.lt_iff_lt hv.strictMono]
            rwa [norm, NNReal.coe_lt_coe, map_sub_swap] at hp
        · rintro ⟨a, ha, H⟩
          rcases hv.exists_val_lt with (h | h)
          · use 1
            apply subset_trans _ H
            simp only [Units.val_one, setOf_subset_setOf, Prod.forall]
            intro x y hxy
            convert ha
            suffices v (x - y) = 0 by
              simp [norm, this]
            rw [map_sub_swap]
            by_contra hxy'
            apply ne_of_lt hxy
            simp only [map_one, Units.val_one]
            have hu : IsUnit (⟨v (y - x), v.mem_rangeGroup₀⟩ : v.rangeGroup₀) := by
              rwa [isUnit_iff_ne_zero, ne_eq, ← Subtype.coe_inj,
                MonoidHomWithZero.range₀_coe_zero]
            simpa [Units.ext_iff] using h.elim hu.unit 1
          · obtain ⟨x, hx, h⟩ := h (γ := ⟨a, le_of_lt ha⟩) (pos_iff_ne_zero.mp ha )
            have hx' : IsUnit (⟨v x, v.mem_rangeGroup₀⟩ : v.rangeGroup₀) := by
              simpa [isUnit_iff_ne_zero, ne_eq, ← Subtype.coe_inj] using hx
            use hx'.unit
            apply subset_trans _ H
            simp only [Units.val_mk0, setOf_subset_setOf, Prod.forall]
            intro y z hyz
            rw [map_sub_swap] at hyz
            rw [← StrictMono.lt_iff_lt hv.strictMono] at hyz
            exact lt_trans hyz h
      · simp only [Directed]
        intro x y
        use min x y
        simp only [le_principal_iff, mem_principal, setOf_subset_setOf, Prod.forall]
        exact ⟨fun a b hab => lt_of_lt_of_le hab (min_le_left _ _), fun a b hab =>
            lt_of_lt_of_le hab (min_le_right _ _)⟩
      }

-- When a field is valued, one inherits a `NormedField`.
-- Scoped instance to avoid a typeclass loop or non-defeq topology or norms.
scoped[Valued] attribute [instance] Valued.toNormedField
scoped[NormedField] attribute [instance] NormedField.toValued

section NormedField

open scoped Valued

protected lemma isNonarchimedean_norm : IsNonarchimedean ((‖·‖): L → ℝ) := Valued.norm_add_le

instance : IsUltrametricDist L :=
  ⟨fun x y z ↦ by
    refine (Valued.norm_add_le (x - y) (y - z)).trans_eq' ?_
    simp only [sub_add_sub_cancel]
    rfl ⟩

lemma coe_valuation_eq_rankOne_hom_comp_valuation : ⇑NormedField.valuation = hv.hom ∘ val.v := rfl

end NormedField

variable {L} {Γ₀}

namespace toNormedField

variable {x x' : L}

@[simp]
theorem norm_le_iff : ‖x‖ ≤ ‖x'‖ ↔ val.v x ≤ val.v x' :=
  (Valuation.RankLeOne.strictMono val.v).le_iff_le

@[simp]
theorem norm_lt_iff : ‖x‖ < ‖x'‖ ↔ val.v x < val.v x' :=
  (Valuation.RankLeOne.strictMono val.v).lt_iff_lt

@[simp]
theorem norm_le_one_iff : ‖x‖ ≤ 1 ↔ val.v x ≤ 1 := by
  simpa only [map_one] using (Valuation.RankLeOne.strictMono val.v).le_iff_le (b := 1)

@[simp]
theorem norm_lt_one_iff : ‖x‖ < 1 ↔ val.v x < 1 := by
  simpa only [map_one] using (Valuation.RankLeOne.strictMono val.v).lt_iff_lt (b := 1)

@[simp]
theorem one_le_norm_iff : 1 ≤ ‖x‖ ↔ 1 ≤ val.v x := by
  simpa only [map_one] using (Valuation.RankLeOne.strictMono val.v).le_iff_le (a := 1)

@[simp]
theorem one_lt_norm_iff : 1 < ‖x‖ ↔ 1 < val.v x := by
  simpa only [map_one] using (Valuation.RankLeOne.strictMono val.v).lt_iff_lt (a := 1)

end toNormedField

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [val : Valued L Γ₀] [hv : RankOne val.v]

/--
The nontrivially normed field structure determined by a rank one valuation.
-/
def toNontriviallyNormedField: NontriviallyNormedField L := {
  val.toNormedField with
  non_trivial := by
    obtain ⟨x, hx⟩ := Valuation.RankOne.nontrivial val.v
    rcases Valuation.val_le_one_or_val_inv_le_one val.v x with h | h
    · use x⁻¹
      simp only [toNormedField.one_lt_norm_iff, map_inv₀, one_lt_inv₀ (zero_lt_iff.mpr hx.1),
          lt_of_le_of_ne h hx.2]
    · use x
      simp only [map_inv₀, inv_le_one₀ <| zero_lt_iff.mpr hx.1] at h
      simp only [toNormedField.one_lt_norm_iff, lt_of_le_of_ne h hx.2.symm]
}

scoped[Valued] attribute [instance] Valued.toNontriviallyNormedField

end Valued
