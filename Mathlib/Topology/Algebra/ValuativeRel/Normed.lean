/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# Correspondence between nonarchimedean norms and valuations of rank at most one

In this file we relate nonarchimedean normed fields and fields equipped with a valuation
of rank at most one.

## Main Definitions
* `NormedField.toValuativeRel` : the valuative relation on a nonarchimedean normed field `K`,
  determined by the norm.
* `NormedField.isValuativeTopology` : the topology on a nonarchimedean normed field `K` is the
  topology induced by the valuative relation determined by the norm.
* `ValuativeRel.toNormedField` : the normed field structure determined by a valuative
  relation of rank at most one.
* `IsValuativeTopology.toNontriviallyNormedField` : the nontrivially normed field structure
  determined by a rank one valuation.
-/

@[expose] public section

noncomputable section

open Filter Set Valuation ValuativeRel

open scoped NNReal Topology Uniformity

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

namespace NormedField

/-- The valuative relation on a nonarchimedean normed field `K`, determined by the norm. -/
@[instance_reducible]
def toValuativeRel : ValuativeRel K := .ofValuation valuation

/-- The topology on a nonarchimedean normed field `K` is the topology induced by the
valuative relation `NormedField.toValuativeRel`. -/
instance isValuativeTopology :
    letI := toValuativeRel (K := K)
    IsValuativeTopology K :=
  letI := toValuativeRel (K := K)
  haveI : (valuation (K := K)).Compatible := .ofValuation _
  .of_mem_nhds_zero_iff_vle valuation fun {s} ↦ by
    simpa only [true_and] using hasBasis_nhds_zero.mem_iff

/-- The valuation `NormedField.valuation` is compatible with `NormedField.toValuativeRel`. -/
instance valuation_compatible :
    letI := toValuativeRel (K := K)
    (valuation (K := K)).Compatible :=
  Valuation.Compatible.ofValuation _

/-- The valuative relation on a nonarchimedean normed field has rank at most one. -/
instance isRankLeOne :
    letI := toValuativeRel (K := K)
    IsRankLeOne K :=
  letI := toValuativeRel (K := K)
  have := valuation_compatible (K := K)
  .of_compatible_mulArchimedean valuation

/-- The valuative relation on a nontrivially normed nonarchimedean field is nontrivial. -/
instance isNontrivial {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] :
    letI := toValuativeRel (K := K)
    IsNontrivial K :=
  letI := toValuativeRel (K := K)
  haveI := valuation_compatible (K := K)
  (isNontrivial_iff_isNontrivial valuation).2 inferInstance

end NormedField

-- When a field is nonarchimedean normed, one inherits a valuative relation inducing its topology.
-- Scoped instances to avoid a typeclass loop or non-defeq topology or norms.
scoped[NormedField] attribute [instance] NormedField.toValuativeRel

end NormedField

namespace IsValuativeTopology

variable (R : Type*) [Ring R] [ValuativeRel R] [UniformSpace R] [IsUniformAddGroup R]
  [IsValuativeTopology R]

theorem hasBasis_uniformity :
    (𝓤 R).HasBasis (fun _ ↦ True)
      fun γ : (ValueGroupWithZero R)ˣ ↦ { p : R × R | valuation R (p.2 - p.1) < γ } := by
  rw [uniformity_eq_comap_nhds_zero]
  exact (hasBasis_nhds_zero R).comap _

end IsValuativeTopology

namespace ValuativeRel

variable {L : Type*} [Field L] [ValuativeRel L] [IsRankLeOne L] {x y : L}

/-- The real absolute value on a field `L` with a valuative relation, determined by an embedding
`e` of the value group of `L` into `ℝ≥0`. -/
def absoluteValue : AbsoluteValue L ℝ :=
  (valuation L).absoluteValue

theorem absoluteValue_apply (x : L) : absoluteValue x = (valuation L).norm x := rfl

@[simp]
theorem absoluteValue_le_absoluteValue_iff : absoluteValue x ≤ absoluteValue y ↔ x ≤ᵥ y := by
  simp [absoluteValue_apply, norm_def, (valuation L).vle_iff_le]

@[simp]
theorem absoluteValue_lt_absoluteValue_iff : absoluteValue x < absoluteValue y ↔ x <ᵥ y := by
  simpa only [not_le, not_vle] using absoluteValue_le_absoluteValue_iff (x := y) (y := x).not

@[simp]
theorem absoluteValue_eq_absoluteValue_iff : absoluteValue x = absoluteValue y ↔ x =ᵥ y := by
  rw [le_antisymm_iff, veq_def]
  exact Iff.and absoluteValue_le_absoluteValue_iff absoluteValue_le_absoluteValue_iff

@[simp]
theorem absoluteValue_le_one_iff : absoluteValue x ≤ 1 ↔ x ≤ᵥ 1 := by
  simpa using absoluteValue_le_absoluteValue_iff (x := x) (y := 1)

@[simp]
theorem absoluteValue_lt_one_iff : absoluteValue x < 1 ↔ x <ᵥ 1 := by
  simpa using absoluteValue_lt_absoluteValue_iff (x := x) (y := 1)

@[simp]
theorem absoluteValue_eq_one_iff : absoluteValue x = 1 ↔ x =ᵥ 1 := by
  simpa using absoluteValue_eq_absoluteValue_iff (x := x) (y := 1)

@[simp]
theorem one_le_absoluteValue_iff : 1 ≤ absoluteValue x ↔ 1 ≤ᵥ x := by
  simpa using absoluteValue_le_absoluteValue_iff (x := 1) (y := x)

@[simp]
theorem one_lt_absoluteValue_iff : 1 < absoluteValue x ↔ 1 <ᵥ x := by
  simpa using absoluteValue_lt_absoluteValue_iff (x := 1) (y := x)

theorem isNonarchimedean_absoluteValue : IsNonarchimedean (absoluteValue (L := L)) :=
  fun x y ↦ le_sup_iff.2 <| (vle_add_cases x y).imp absoluteValue_le_absoluteValue_iff.2
    absoluteValue_le_absoluteValue_iff.2

theorem exists_one_lt_absoluteValue [IsNontrivial L] : ∃ x : L, 1 < absoluteValue x := by
  obtain ⟨γ, hγ₀, hγ₁⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := L)
  obtain ⟨x, hx⟩ := valuation_surjective γ⁻¹
  exact ⟨x, one_lt_absoluteValue_iff.2 <| (valuation L).one_vlt_iff.2 <|
    hx ▸ (one_lt_inv₀ hγ₀).2 hγ₁⟩

section UniformSpace

variable [UniformSpace L] [IsUniformAddGroup L] [IsValuativeTopology L]

theorem hasBasis_uniformity : (𝓤 L).HasBasis (fun ε : ℝ ↦ 0 < ε)
    fun ε ↦ { p : L × L | absoluteValue (p.1 - p.2) < ε } := by
  refine (valuation L).hasBasis_uniformity.to_hasBasis (fun γ _ ↦ ?_) fun ε hε ↦ ?_
  · refine ⟨RankLeOne.hom' (valuation L) γ, by simp [← NNReal.coe_zero], fun p hp ↦ ?_⟩
    simpa [(valuation L).restrict.map_sub_swap, absoluteValue_apply, norm_def] using hp
  · obtain ⟨γ, hγ⟩ := Real.exists_forall_lt_of_strictMono
      (RankLeOne.strictMono' (v := valuation L)) hε
    exact ⟨γ, trivial, fun p hp ↦ (absoluteValue.map_sub _ _).trans_lt (hγ _ hp)⟩

theorem uniformity_eq : 𝓤 L = 𝓤[absoluteValue.toNormedField.toUniformSpace] :=
  hasBasis_uniformity.eq_of_same_basis <| by
    let := absoluteValue.toNormedField (K := L)
    have := Metric.uniformity_basis_dist (α := L)
    convert this
    rw [dist_comm]
    congr
    abel

/-- The normed field structure on `L` determined by an embedding `e` of the value group of `L`
into `ℝ≥0`, whose uniform structure is the given one. -/
@[instance_reducible]
def toNormedField : NormedField L where
  __ := absoluteValue.toNormedField
  toMetricSpace := absoluteValue.toNormedField.toMetricSpace.replaceUniformity uniformity_eq

/-- The nontrivially normed field structure on `L` determined by an embedding `e` of the value
group of `L` into `ℝ≥0`, whose uniform structure is the given one. -/
@[instance_reducible]
def toNontriviallyNormedField [IsNontrivial L] : NontriviallyNormedField L where
  __ := toNormedField
  non_trivial := exists_one_lt_absoluteValue

-- When a field has a valuative topology of rank at most one, one inherits a `NormedField`.
-- Scoped instances to avoid a typeclass loop or non-defeq topology or norms.
scoped[ValuativeRel] attribute [instance] ValuativeRel.toNormedField
  ValuativeRel.toNontriviallyNormedField

section toNormedField

protected theorem isNonarchimedean_norm : IsNonarchimedean ((‖·‖) : L → ℝ) :=
  isNonarchimedean_absoluteValue

instance isUltrametricDist_toNormedField :
    letI := toNormedField (L := L)
    IsUltrametricDist L :=
  letI := toNormedField (L := L)
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm ValuativeRel.isNonarchimedean_norm

theorem norm_def : ‖x‖ = RankLeOne.hom' (valuation L) ((valuation L).restrict x) := rfl

theorem nnnorm_def : ‖x‖₊ = RankLeOne.hom' (valuation L) ((valuation L).restrict x) := rfl

@[simp]
theorem norm_le_iff : ‖x‖ ≤ ‖y‖ ↔ x ≤ᵥ y :=
  absoluteValue_le_absoluteValue_iff

@[simp]
theorem norm_lt_iff : ‖x‖ < ‖y‖ ↔ x <ᵥ y :=
  absoluteValue_lt_absoluteValue_iff

@[simp]
theorem norm_eq_iff : ‖x‖ = ‖y‖ ↔ x =ᵥ y :=
  absoluteValue_eq_absoluteValue_iff

@[simp]
theorem norm_le_one_iff : ‖x‖ ≤ 1 ↔ x ≤ᵥ 1 :=
  absoluteValue_le_one_iff

@[simp]
theorem norm_lt_one_iff : ‖x‖ < 1 ↔ x <ᵥ 1 :=
  absoluteValue_lt_one_iff

@[simp]
theorem norm_eq_one_iff : ‖x‖ = 1 ↔ x =ᵥ 1 :=
  absoluteValue_eq_one_iff

@[simp]
theorem one_le_norm_iff : 1 ≤ ‖x‖ ↔ 1 ≤ᵥ x :=
  one_le_absoluteValue_iff

@[simp]
theorem one_lt_norm_iff : 1 < ‖x‖ ↔ 1 <ᵥ x :=
  one_lt_absoluteValue_iff

theorem setOfPred_mem_integer_eq_closedBall :
    { x : L | x ∈ (valuation L).integer } = Metric.closedBall 0 1 := by
  ext x
  simp [mem_integer_iff, (valuation L).vle_one_iff]

/-- The valuation `NormedField.valuation` of the normed field structure
`ValuativeRel.toNormedField` is compatible with the valuative relation. -/
instance : (NormedField.valuation (K := L)).Compatible where
  vle_iff_le x y := by
    rw [NormedField.valuation_apply, NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm,
      coe_nnnorm, norm_le_iff]

/-- The valuative relation determined by the norm of `ValuativeRel.toNormedField` is the
original valuative relation. -/
theorem toValuativeRel_toNormedField : NormedField.toValuativeRel = ‹ValuativeRel L› := by
  ext x y
  exact NormedField.valuation.vle_iff_le.symm

end toNormedField

end UniformSpace

end ValuativeRel
