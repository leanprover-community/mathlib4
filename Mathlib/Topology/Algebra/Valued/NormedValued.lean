/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.Valuation.RankOne
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# Correspondence between nontrivial nonarchimedean norms and rank one valuations

Nontrivial nonarchimedean norms correspond to rank one valuations.

## Main Definitions
* `NormedField.toValued` : the valued field structure on a nonarchimedean normed field `K`,
  determined by the norm.
* `Valued.toNormedField` : the normed field structure determined by a rank one valuation.

## Main Results
* The valuation of a normed field has rank at most one.

## Tags

norm, nonarchimedean, nontrivial, valuation, rank one
-/

@[expose] public section


noncomputable section

open Filter Set Valuation MonoidWithZeroHom

open scoped NNReal Topology

section

variable {K : Type*} [hK : NormedField K] [IsUltrametricDist K]

namespace NormedField

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The valuation on a nonarchimedean normed field `K` defined as `nnnorm`. -/
def valuation : Valuation K ℝ≥0 where
  toFun           := nnnorm
  map_zero'       := nnnorm_zero
  map_one'        := nnnorm_one
  map_mul'        := nnnorm_mul
  map_add_le_max' := IsUltrametricDist.norm_add_le_max

@[simp]
theorem valuation_apply (x : K) : valuation x = ‖x‖₊ := rfl

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

/-- The valuation of a normed field has rank at most one -/
instance : RankLeOne (valuation (K := K)) where
  hom' := embedding
  strictMono' := embedding_strictMono

/-- The neighbourhoods of `0` in a nonarchimedean normed field `K` have a basis given by the
open balls of the valuation `NormedField.valuation`. -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : K)).HasBasis (fun _ ↦ True)
      fun γ : (ValueGroup₀ (.ofClass (valuation (K := K))))ˣ ↦
        { x | valuation.restrict x < γ } := by
  refine Metric.nhds_basis_ball.to_hasBasis (fun ε hε ↦ ?_) fun γ _ ↦ ?_
  · obtain ⟨γ, hγ⟩ := Real.exists_forall_lt_of_strictMono
      (embedding_strictMono (f := .ofClass (valuation (K := K)))) hε
    exact ⟨γ, trivial, fun x hx ↦ mem_ball_zero_iff.2 (by simpa using hγ _ hx)⟩
  · refine ⟨(embedding γ.1 : ℝ≥0), ?_, fun x hx ↦ ?_⟩
    · exact NNReal.coe_pos.mpr <| embedding_strictMono.lt_iff_lt.mpr γ.zero_lt
    · simpa [restrict_lt_iff_lt_embedding] using! mem_ball_zero_iff.1 hx

/-- The valued field structure on a nonarchimedean normed field `K`, determined by the norm. -/
@[instance_reducible]
def toValued : Valued K ℝ≥0 :=
  { hK.toUniformSpace,
    (inferInstance : IsUniformAddGroup K) with
    v := valuation
    is_topological_valuation := fun s ↦ by simpa only [true_and] using hasBasis_nhds_zero.mem_iff }

instance {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] :
    Valuation.RankOne (valuation (K := K)) where
  hom' := ValueGroup₀.embedding
  strictMono' := ValueGroup₀.embedding_strictMono
  exists_val_nontrivial := (exists_one_lt_norm K).imp fun x h ↦ by
    have h' : x ≠ 0 := norm_eq_zero.not.mp (h.gt.trans' (by simp)).ne'
    simp [valuation_apply, ← NNReal.coe_inj, h.ne', h']

end NormedField

end


namespace Valuation

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀) [hv : RankOne v]

/-- The norm function determined by a rank one valuation on a field `L`. -/
def norm : L → ℝ := fun x : L => hv.hom _ (v.restrict x)

theorem norm_def {x : L} : v.norm x = hv.hom _ (v.restrict x) := rfl

theorem norm_nonneg (x : L) : 0 ≤ v.norm x := by simp only [norm, NNReal.zero_le_coe]

theorem norm_add_le (x y : L) : v.norm (x + y) ≤ max (v.norm x) (v.norm y) := by
  simp only [norm, NNReal.coe_le_coe, le_max_iff, StrictMono.le_iff_le hv.strictMono]
  exact le_max_iff.mp (Valuation.map_add_le_max' v.restrict _ _)

theorem norm_eq_zero {x : L} (hx : v.norm x = 0) : x = 0 := by
  simpa [v.restrict_def, norm, NNReal.coe_eq_zero, RankOne.hom_eq_zero_iff, zero_iff] using hx

theorem norm_pos_iff_valuation_pos {x : L} : 0 < v.norm x ↔ (0 : Γ₀) < v x := by
  rw [norm_def, ← NNReal.coe_zero, NNReal.coe_lt_coe, ← map_zero (RankOne.hom v),
    StrictMono.lt_iff_lt (RankOne.strictMono v)]
  rw [v.restrict_pos_iff]

end Valuation

namespace Valued

variable (L : Type*) [Field L] (Γ₀ : Type*) [LinearOrderedCommGroupWithZero Γ₀]
  [val : Valued L Γ₀] [hv : RankOne val.v]

open Valuation

/-- The normed field structure determined by a rank one valuation. -/
@[instance_reducible]
def toNormedField : NormedField L :=
  { (inferInstance : Field L) with
    norm := val.v.norm
    dist := fun x y => val.v.norm (x - y)
    dist_self := fun x => by
      simp only [sub_self, Valuation.norm, Valuation.map_zero, hv.hom.map_zero, NNReal.coe_zero]
    dist_comm := fun x y => by simp only [Valuation.norm]; rw [← neg_sub, Valuation.map_neg]
    dist_triangle := fun x y z => by
      simp only [← sub_add_sub_cancel x y z]
      exact le_trans (val.v.norm_add_le _ _)
        (max_le_add_of_nonneg (val.v.norm_nonneg _) (val.v.norm_nonneg _))
    eq_of_dist_eq_zero := fun hxy => eq_of_sub_eq_zero (val.v.norm_eq_zero hxy)
    dist_eq := fun x y => by
      simp only [Valuation.norm]
      rw [← v.restrict.map_neg, neg_sub, sub_eq_add_neg, add_comm]
    norm_mul := fun x y => by simp only [Valuation.norm, ← NNReal.coe_mul, map_mul]
    toUniformSpace := Valued.toUniformSpace
    uniformity_dist := by
      have : Nonempty { ε : ℝ // ε > 0 } := nonempty_Ioi_subtype
      ext U
      rw [hasBasis_iff.mp (Valued.hasBasis_uniformity L Γ₀), iInf_subtype', mem_iInf_of_directed]
      · simp only [true_and, mem_principal, Subtype.exists, gt_iff_lt, exists_prop]
        refine ⟨fun ⟨ε, hε⟩ => ?_, fun ⟨r, hr_pos, hr⟩ => ?_⟩
        · set δ : ℝ≥0 := hv.hom _ ε with hδ
          have hδ_pos : 0 < δ := by
            rw [hδ, ← map_zero hv.hom]
            exact hv.strictMono _ (Units.zero_lt ε)
          use δ, hδ_pos
          apply subset_trans _ hε
          intro x hx
          simp only [mem_ofPred_eq, Valuation.norm, hδ, NNReal.coe_lt_coe] at hx
          rw [mem_ofPred, ← neg_sub, Valuation.map_neg]
          exact (RankOne.strictMono Valued.v).lt_iff_lt.mp hx
        · have : Nontrivial Γ₀ˣ := (nontrivial_iff_exists_ne (1 : Γ₀ˣ)).mpr
            ⟨RankOne.unit val.v, RankOne.unit_ne_one val.v⟩
          obtain ⟨u, hu⟩ := Real.exists_lt_of_strictMono hv.strictMono hr_pos
          use u
          apply subset_trans _ hr
          intro x hx
          simp only [Valuation.norm, mem_ofPred_eq]
          apply lt_trans _ hu
          rw [NNReal.coe_lt_coe, ← neg_sub, Valuation.map_neg]
          exact (RankOne.strictMono Valued.v).lt_iff_lt.mpr hx
      · simp only [Directed]
        intro x y
        use min x y
        simp only [le_principal_iff, mem_principal, ofPred_subset_ofPred, Prod.forall]
        exact ⟨fun a b hab => lt_of_lt_of_le hab (min_le_left _ _), fun a b hab =>
            lt_of_lt_of_le hab (min_le_right _ _)⟩ }

-- When a field is valued, one inherits a `NormedField`.
-- Scoped instance to avoid a typeclass loop or non-defeq topology or norms.
scoped[Valued] attribute [instance] Valued.toNormedField
scoped[NormedField] attribute [instance] NormedField.toValued

section NormedField

open scoped Valued

protected lemma isNonarchimedean_norm : IsNonarchimedean ((‖·‖) : L → ℝ) :=
  Valuation.norm_add_le _

instance : IsUltrametricDist L :=
  ⟨fun x y z ↦ by
    refine (Valuation.norm_add_le _ (x - y) (y - z)).trans_eq' ?_
    simp only [sub_add_sub_cancel]
    rfl ⟩

lemma coe_valuation_eq_rankOne_hom_comp_valuation :
    ⇑NormedField.valuation = hv.hom ∘ val.v.restrict := rfl

end NormedField
namespace toNormedField

variable {L Γ₀}

variable {x x' : L}

theorem norm_def : ‖x‖ = hv.hom _ (Valued.v.restrict x) := rfl

@[simp]
theorem norm_le_iff : ‖x‖ ≤ ‖x'‖ ↔ val.v x ≤ val.v x' := by
  rw [← v.restrict_le_iff, ← (Valuation.RankOne.strictMono val.v).le_iff_le]
  rfl

@[simp]
theorem norm_lt_iff : ‖x‖ < ‖x'‖ ↔ val.v x < val.v x' := by
  rw [← v.restrict_lt_iff, ← (Valuation.RankOne.strictMono val.v).lt_iff_lt]
  rfl

@[simp]
theorem norm_le_one_iff : ‖x‖ ≤ 1 ↔ val.v x ≤ 1 := by
  rw [← map_one val.v, ← v.restrict_le_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).le_iff_le (b := 1)

@[simp]
theorem norm_lt_one_iff : ‖x‖ < 1 ↔ val.v x < 1 := by
  rw [← map_one val.v, ← v.restrict_lt_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).lt_iff_lt (b := 1)

@[simp]
theorem one_le_norm_iff : 1 ≤ ‖x‖ ↔ 1 ≤ val.v x := by
  rw [← map_one val.v, ← v.restrict_le_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).le_iff_le (a := 1)

@[simp]
theorem one_lt_norm_iff : 1 < ‖x‖ ↔ 1 < val.v x := by
  rw [← map_one val.v, ← v.restrict_lt_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).lt_iff_lt (a := 1)

lemma setOfPred_mem_integer_eq_closedBall :
    { x : L | x ∈ Valued.v.integer } = Metric.closedBall 0 1 := by
  ext x
  simp [mem_integer_iff]

@[deprecated (since := "2026-07-09")]
alias setOf_mem_integer_eq_closedBall := setOfPred_mem_integer_eq_closedBall

end toNormedField

/--
The nontrivially normed field structure determined by a rank one valuation.
-/
@[instance_reducible]
def toNontriviallyNormedField : NontriviallyNormedField L := {
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
