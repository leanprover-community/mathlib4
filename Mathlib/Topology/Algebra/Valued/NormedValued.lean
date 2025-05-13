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

instance : RankLeOne (valuation h) where
  hom := MonoidWithZeroHom.id _
  strictMono' _ _ h := h

/-
/- NB. Si (valuation h).rangeGroup était `LinearOrderedCommGroupWithZero`,
on pourrait plutôt appliquer `NNReal.exists_lt_of_strictMono`
*FAE* Je l'ai rajouté, reste à voir si ça marche...-/

theorem isTriviallyValued_or_exists' {ε : ℝ} (hε : 0 < ε):
    (valuation h).rangeGroup = ⊥ ∨ (∃ (x : K), ‖x‖₊ ≠ 0 ∧ ‖x‖₊ < ε) := by
  rw [Classical.or_iff_not_imp_left]
  push_neg
  intro H
  have this : Nontrivial ((valuation h).rangeGroup) :=
    (Subgroup.nontrivial_iff_ne_bot (valuation h).rangeGroup).mpr H
  have this' : Nontrivial (valuation h).rangeGroup₀ˣ := sorry
  -- have := @NNReal.exists_lt_of_strictMono (valuation h).rangeGroup₀
  sorry

#check NNReal.exists_lt_of_strictMono

#check RankOne
theorem exists_val_lt {L : Type*} [Field L] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [val : Valued L Γ₀] [hv : RankOne val.v]
    (γ : Γ₀ˣ) :
    (∃ (x : L), x ≠ 0 ∧ val.v x < γ) := by
  set u : ℝ≥0 := if γ < 1 then hv.hom γ else hv.hom c⁻¹ with hu
  set y : L := if c < 1 then x else x⁻¹ with hy
  have hu_lt1 : u < 1 := by
    rw [hu]
    split_ifs with h
    · rw [← hv.hom.map_one, StrictMono.lt_iff_lt hv.strictMono]
      exact h
    · rw [not_lt] at h
      rw [eq_comm] at hγ
      rw [map_inv₀, inv_lt_one₀ ?_]
      rw [← hv.hom.map_one, StrictMono.lt_iff_lt hv.strictMono]
      apply lt_of_le_of_ne h hγ
      apply ne_of_gt
      rw [← hv.hom.map_zero, StrictMono.lt_iff_lt hv.strictMono]
      exact c.zero_lt
  have hy' : RankLeOne.hom val.v (Valued.v y) = u := by
    rw [hu, hy, apply_ite (f := Valued.v), apply_ite (f := RankLeOne.hom Valued.v), map_inv₀, hx]
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ?_ hu_lt1
  use y ^ n
  simp only [pow_eq_zero_iff', ne_eq, not_and, Decidable.not_not, norm_pow]
  constructor
  · intro hy0
    exfalso
    apply u.ne_zero
    rwa [hy0, _root_.map_zero, eq_comm] at hy'
  · simp only [NNReal.val_eq_coe, ← hy'] at hn
    exact lt_of_lt_of_le hn (min_le_left _ _)

theorem isTriviallyValued_or_exists'' {ε : ℝ} (hε : 0 < ε):
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
-/

/-- The valued field structure on a nonarchimedean normed field `K`, determined by the norm. -/
def toValued : Valued K ℝ≥0 :=
  { hK.toUniformSpace,
    inferInstanceAs (IsUniformAddGroup K) with
    v := valuation
    is_topological_valuation := fun U => by
      rw [Metric.mem_nhds_iff]
      constructor
      · intro ⟨ε, hε, hU⟩
        rcases RankLeOne.exists_val_lt (valuation h) with (H | H)
           -- isTriviallyValued_or_exists h hε with (H | ⟨x, hpos, h_lt⟩)
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
        · obtain ⟨x, hx, hxy⟩ := H (γ := ⟨ε, le_of_lt hε⟩) (pos_iff_ne_zero.mp hε)
          use Units.mk0 (nnnorm x) (nnnorm_ne_zero_iff.mpr hx), mem_rangeGroup _ rfl
          intro y hy
          apply hU
          simp only [Metric.mem_ball, dist_zero_right]
          simp only [Units.val_mk0, mem_setOf_eq] at hy
          exact lt_trans hy hxy
      · rintro ⟨γ, _, hU⟩
        use (γ : ℝ), NNReal.coe_unit_pos γ
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
  rw [norm_def, ← NNReal.coe_zero, NNReal.coe_lt_coe, ← map_zero (RankOne.hom (v (R := L))),
    StrictMono.lt_iff_lt]
  exact RankOne.strictMono v

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
        · rintro ⟨a, ha, H⟩
          use hv.hom a
          constructor
          · suffices (0 : ℝ) = hv.hom 0 by
              rw [this]
              exact hv.strictMono a.zero_lt
            simp
          · intro p hp
            apply H
            simp only [mem_setOf_eq] at hp ⊢
            rw [← StrictMono.lt_iff_lt hv.strictMono]
            rwa [norm, NNReal.coe_lt_coe, map_sub_swap] at hp
        · rintro ⟨a, ha, H⟩
          rcases hv.exists_val_lt with (h | h)
          · use 1, one_mem _
            apply subset_trans _ H
            simp only [Units.val_one, setOf_subset_setOf, Prod.forall]
            intro x y hxy
            convert ha
            suffices v (x - y) = 0 by
              simp [norm, this]
            by_contra hxy'
            apply ne_of_lt hxy
            let u := Units.mk0 _ hxy'
            have : Units.mk0 _ hxy' ∈ v.rangeGroup := mem_rangeGroup v rfl
            simpa only [map_sub_swap, h, Subgroup.mem_bot, ← Units.eq_iff] using this
          · obtain ⟨x, hx, h⟩ := h (γ := ⟨a, le_of_lt ha⟩) (pos_iff_ne_zero.mp ha )
            use Units.mk0 (v x) ((ne_zero_iff v).mpr hx)
            refine ⟨mem_rangeGroup v rfl, ?_⟩
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
  (Valuation.RankOne.strictMono val.v).le_iff_le

@[simp]
theorem norm_lt_iff : ‖x‖ < ‖x'‖ ↔ val.v x < val.v x' :=
  (Valuation.RankOne.strictMono val.v).lt_iff_lt

@[simp]
theorem norm_le_one_iff : ‖x‖ ≤ 1 ↔ val.v x ≤ 1 := by
  simpa only [map_one] using (Valuation.RankOne.strictMono val.v).le_iff_le (b := 1)

@[simp]
theorem norm_lt_one_iff : ‖x‖ < 1 ↔ val.v x < 1 := by
  simpa only [map_one] using (Valuation.RankOne.strictMono val.v).lt_iff_lt (b := 1)

@[simp]
theorem one_le_norm_iff : 1 ≤ ‖x‖ ↔ 1 ≤ val.v x := by
  simpa only [map_one] using (Valuation.RankOne.strictMono val.v).le_iff_le (a := 1)

@[simp]
theorem one_lt_norm_iff : 1 < ‖x‖ ↔ 1 < val.v x := by
  simpa only [map_one] using (Valuation.RankOne.strictMono val.v).lt_iff_lt (a := 1)

end toNormedField

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
