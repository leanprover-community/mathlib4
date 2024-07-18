/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valued.ValuationTopology

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


/- NB. Si (valuation h).rangeGroup était `LinearOrderedCommGroupWith Zero`,
on peurrait plutôt appliquer `NNReal.exists_lt_of_strictMono`
*FAE* Je l'ai rajouté, reste à voir si ça marche...-/

theorem isTriviallyValued_or_exists' {ε : ℝ} (hε : 0 < ε):
    (valuation h).rangeGroup = ⊥ ∨ (∃ (x : K), ‖x‖₊ ≠ 0 ∧ ‖x‖₊ < ε) := by
  rw [Classical.or_iff_not_imp_left]
  intro H
  have _ : Nontrivial ((valuation h).rangeGroup) :=
    (Subgroup.nontrivial_iff_ne_bot (valuation h).rangeGroup).mpr H
  -- have := @NNReal.exists_lt_of_strictMono (valuation h).rangeGroupWithZero _
  sorry

theorem isTriviallyValued_or_exists {ε : ℝ} (hε : 0 < ε):
    (valuation h).rangeGroup = ⊥ ∨ (∃ (x : K), ‖x‖₊ ≠ 0 ∧ ‖x‖₊ < ε) := by
  rw [Classical.or_iff_not_imp_right]
  push_neg
  intro H
  rw [eq_bot_iff]
  simp only [rangeGroup]
  simp only [le_bot_iff, Subgroup.closure_eq_bot_iff, subset_singleton_iff, mem_preimage, mem_range,
    forall_exists_index]
  intro γ x hx
  have hγ' : ∀ (n : ℤ), ε ≤ γ ^ n := fun n ↦ by
    rw [← NNReal.coe_zpow, ← hx, valuation_apply, ← nnnorm_zpow]
    apply H
    apply ne_zero_of_lt (b := 0)
    rw [nnnorm_zpow, ← valuation_apply, hx]
    apply zpow_pos_of_pos
    apply NNReal.coe_unit_pos
  rcases lt_trichotomy (γ : ℝ) 1 with (h1 | h2 | h3)
  · exfalso
    have h1' : 1 < ((γ⁻¹ : ℝ≥0ˣ) : ℝ) := by
      rw [Units.val_inv_eq_inv_val, NNReal.coe_inv]
      refine one_lt_inv (NNReal.coe_unit_pos γ) h1
    obtain ⟨n, hn⟩ := exists_mem_Ioc_zpow hε h1'
    simp only [mem_Ioc, ← not_le] at hn
    apply hn.1
    rw [Units.val_inv_eq_inv_val, NNReal.coe_inv, inv_zpow']
    apply hγ'
  · rw [← Units.eq_iff, ← NNReal.coe_inj, h2, Units.val_one, NNReal.coe_one]
  · exfalso
    obtain ⟨n, hn⟩ := exists_mem_Ioc_zpow hε h3
    simp only [mem_Ioc, ← not_le] at hn
    exact hn.1 (hγ' n)

/-- The valued field structure on a nonarchimedean normed field `K`, determined by the norm. -/
def toValued : Valued K ℝ≥0 :=
  { hK.toUniformSpace,
    @NonUnitalNormedRing.toNormedAddCommGroup K _ with
    v := valuation h
    is_topological_valuation := fun U => by
      rw [Metric.mem_nhds_iff]
      constructor
      · intro ⟨ε, hε, hU⟩
        rcases isTriviallyValued_or_exists h hε with (H | ⟨x, hpos, h_lt⟩)
        · use 1, one_mem _
          intro x hx
          simp only [Units.val_one, mem_setOf_eq] at hx
          suffices x = 0 by
            apply hU
            simp only [this, Metric.mem_ball, dist_self, hε]
          by_cases hx' : valuation h x = 0
          · by_contra hx_ne
            have : valuation h 1 = 1 := Valuation.map_one (valuation h)
            rw [← CommGroupWithZero.mul_inv_cancel x hx_ne] at this
            simp only [_root_.map_mul, map_inv₀, hx', zero_mul] at this
            apply zero_ne_one this
          · exfalso
            apply not_le.mpr hx
            apply le_of_eq
            symm
            rw [← Units.val_mk0 hx', ← Units.val_one, Units.eq_iff,
              ← Subgroup.mem_bot, ← H]
            exact mem_rangeGroup _ rfl
        · use Units.mk0 _ hpos, mem_rangeGroup _ rfl
          intro y
          simp only [Units.val_mk0, mem_setOf_eq]
          intro hy
          apply hU
          simp only [Metric.mem_ball, dist_zero_right]
          exact lt_trans hy h_lt

      · rintro ⟨γ, _, hU⟩
        use (γ : ℝ), NNReal.coe_unit_pos γ
        intro x hx
        apply hU
        simpa only [Metric.mem_ball, dist_zero_right, mem_setOf_eq] using hx

/-       exact ⟨fun ⟨ε, hε, h⟩  =>
          ⟨Units.mk0 ⟨ε, le_of_lt hε⟩ (ne_of_gt hε), fun x hx ↦ h (mem_ball_zero_iff.mpr hx)⟩,
        fun ⟨ε, hε⟩ => ⟨(ε : ℝ), NNReal.coe_pos.mpr (Units.zero_lt _),
          fun x hx ↦ hε (mem_ball_zero_iff.mp hx)⟩⟩  -/

          }

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
          apply subset_trans _ hε.2
          intro x hx
          simp only [mem_setOf_eq, norm, hδ, NNReal.val_eq_coe, NNReal.coe_lt_coe] at hx
          rw [mem_setOf, ← neg_sub, Valuation.map_neg]
          exact (RankOne.strictMono Valued.v).lt_iff_lt.mp hx
        · -- ici, il faut raffiner l'argument
          have : Nontrivial Γ₀ˣ := (nontrivial_iff_exists_ne (1 : Γ₀ˣ)).mpr
            ⟨RankOne.unit val.v, RankOne.unit_ne_one val.v⟩

          have bar : ∃ w : Γ₀ˣ, RankOne.hom (R := L) v (w : Γ₀) < r := Real.exists_lt_of_strictMono hv.strictMono hr_pos

          have foo : ∃ u : rangeGroup (R := L) v, RankOne.hom (R := L) v u.1 < r := by sorry

          obtain ⟨⟨u, mem_u⟩, hu⟩ := foo
          refine ⟨u, ⟨mem_u, ?_⟩⟩
          apply subset_trans _ hr
          intro x hx
          simp only [norm, mem_setOf_eq]
          apply lt_trans _ hu
          rw [NNReal.coe_lt_coe, ← neg_sub, Valuation.map_neg]
          exact (RankOne.strictMono Valued.v).lt_iff_lt.mpr hx
      · simp only [gt_iff_lt, Directed]
        intro x y
        use min x y
        simp only [le_principal_iff, mem_principal, setOf_subset_setOf, Prod.forall]
        exact ⟨fun a b hab => lt_of_lt_of_le hab (min_le_left _ _), fun a b hab =>
            lt_of_lt_of_le hab (min_le_right _ _)⟩
      }

end Valued
