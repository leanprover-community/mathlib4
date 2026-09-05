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
* `IsValuativeTopology.toNormedField` : the normed field structure determined by a valuative
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

namespace ValuativeRel.RankLeOneStruct

variable {L : Type*} [Field L] [ValuativeRel L] (e : RankLeOneStruct L) {x y : L}

/-- The real absolute value on a field `L` with a valuative relation, determined by an embedding
`e` of the value group of `L` into `ℝ≥0`. -/
def absoluteValue : AbsoluteValue L ℝ where
  toFun x := e.emb (valuation L x)
  map_mul' x y := by simp
  nonneg' _ := NNReal.coe_nonneg _
  eq_zero' x := by
    rw [NNReal.coe_eq_zero, ← map_zero e.emb, e.strictMono.injective.eq_iff, (valuation L).zero_iff]
  add_le' x y := by
    refine le_trans ?_ (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
    simp only [le_max_iff, NNReal.coe_le_coe, e.strictMono.le_iff_le]
    exact le_max_iff.1 ((valuation L).map_add x y)

@[simp]
theorem absoluteValue_apply (x : L) : e.absoluteValue x = e.emb (valuation L x) := rfl

theorem absoluteValue_le_absoluteValue_iff : e.absoluteValue x ≤ e.absoluteValue y ↔ x ≤ᵥ y := by
  rw [absoluteValue_apply, absoluteValue_apply, NNReal.coe_le_coe, e.strictMono.le_iff_le,
    (valuation L).vle_iff_le]

theorem absoluteValue_lt_absoluteValue_iff : e.absoluteValue x < e.absoluteValue y ↔ x <ᵥ y := by
  rw [absoluteValue_apply, absoluteValue_apply, NNReal.coe_lt_coe, e.strictMono.lt_iff_lt,
    (valuation L).vlt_iff_lt]

theorem absoluteValue_lt_emb_iff {γ : ValueGroupWithZero L} :
    e.absoluteValue x < e.emb γ ↔ valuation L x < γ := by
  rw [absoluteValue_apply, NNReal.coe_lt_coe, e.strictMono.lt_iff_lt]

theorem absoluteValue_le_one_iff : e.absoluteValue x ≤ 1 ↔ x ≤ᵥ 1 := by
  simpa using e.absoluteValue_le_absoluteValue_iff (x := x) (y := 1)

theorem absoluteValue_lt_one_iff : e.absoluteValue x < 1 ↔ x <ᵥ 1 := by
  simpa using e.absoluteValue_lt_absoluteValue_iff (x := x) (y := 1)

theorem one_le_absoluteValue_iff : 1 ≤ e.absoluteValue x ↔ 1 ≤ᵥ x := by
  simpa using e.absoluteValue_le_absoluteValue_iff (x := 1) (y := x)

theorem one_lt_absoluteValue_iff : 1 < e.absoluteValue x ↔ 1 <ᵥ x := by
  simpa using e.absoluteValue_lt_absoluteValue_iff (x := 1) (y := x)

theorem absoluteValue_pos_iff : 0 < e.absoluteValue x ↔ 0 <ᵥ x := by
  simpa using e.absoluteValue_lt_absoluteValue_iff (x := 0) (y := x)

theorem isNonarchimedean_absoluteValue : IsNonarchimedean e.absoluteValue := fun x y ↦
  le_sup_iff.2 <| (vle_add_cases x y).imp e.absoluteValue_le_absoluteValue_iff.2
    e.absoluteValue_le_absoluteValue_iff.2

theorem exists_one_lt_absoluteValue [IsNontrivial L] : ∃ x : L, 1 < e.absoluteValue x := by
  obtain ⟨γ, hγ₀, hγ₁⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := L)
  obtain ⟨x, hx⟩ := valuation_surjective γ⁻¹
  exact ⟨x, e.one_lt_absoluteValue_iff.2 <| (valuation L).one_vlt_iff.2 <|
    hx ▸ (one_lt_inv₀ hγ₀).2 hγ₁⟩

section UniformSpace

variable [UniformSpace L] [IsUniformAddGroup L] [IsValuativeTopology L]

theorem hasBasis_uniformity : (𝓤 L).HasBasis (fun ε : ℝ ↦ 0 < ε)
    fun ε ↦ { p : L × L | e.absoluteValue (p.1 - p.2) < ε } := by
  refine (IsValuativeTopology.hasBasis_uniformity L).to_hasBasis (fun γ _ ↦ ?_) fun ε hε ↦ ?_
  · refine ⟨e.emb γ, by simpa using e.strictMono γ.zero_lt, fun p hp ↦ ?_⟩
    rw [mem_ofPred, (valuation L).map_sub_swap]
    exact e.absoluteValue_lt_emb_iff.1 hp
  · obtain ⟨γ, hγ⟩ := Real.exists_forall_lt_of_strictMono e.strictMono hε
    exact ⟨γ, trivial, fun p hp ↦ (e.absoluteValue.map_sub _ _).trans_lt (hγ _ hp)⟩

theorem uniformity_eq : 𝓤 L = 𝓤[e.absoluteValue.toNormedField.toUniformSpace] :=
  e.hasBasis_uniformity.eq_of_same_basis <| by
    let := e.absoluteValue.toNormedField
    have := Metric.uniformity_basis_dist (α := L)
    simp only [dist_eq_norm] at this
    exact this

/-- The normed field structure on `L` determined by an embedding `e` of the value group of `L`
into `ℝ≥0`, whose uniform structure is the given one. -/
@[instance_reducible]
def toNormedField : NormedField L where
  __ := e.absoluteValue.toNormedField
  toMetricSpace := e.absoluteValue.toNormedField.toMetricSpace.replaceUniformity e.uniformity_eq

instance isUltrametricDist_toNormedField :
    letI := e.toNormedField
    IsUltrametricDist L :=
  letI := e.toNormedField
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm e.isNonarchimedean_absoluteValue

/-- The nontrivially normed field structure on `L` determined by an embedding `e` of the value
group of `L` into `ℝ≥0`, whose uniform structure is the given one. -/
@[instance_reducible]
def toNontriviallyNormedField [IsNontrivial L] : NontriviallyNormedField L where
  __ := e.toNormedField
  non_trivial := e.exists_one_lt_absoluteValue

end UniformSpace

end ValuativeRel.RankLeOneStruct

namespace IsValuativeTopology

variable (L : Type*) [Field L] [ValuativeRel L] [IsRankLeOne L] [UniformSpace L]
  [IsUniformAddGroup L] [IsValuativeTopology L]

/-- The normed field structure determined by a valuative relation of rank at most one, whose
uniform structure is the given one. -/
@[instance_reducible]
def toNormedField : NormedField L := (IsRankLeOne.nonempty (R := L)).some.toNormedField

/-- The nontrivially normed field structure determined by a rank one valuation, whose uniform
structure is the given one. -/
@[instance_reducible]
def toNontriviallyNormedField [IsNontrivial L] : NontriviallyNormedField L :=
  (IsRankLeOne.nonempty (R := L)).some.toNontriviallyNormedField

end IsValuativeTopology

-- When a field has a valuative topology of rank at most one, one inherits a `NormedField`.
-- Scoped instances to avoid a typeclass loop or non-defeq topology or norms.
scoped[IsValuativeTopology] attribute [instance] IsValuativeTopology.toNormedField
  IsValuativeTopology.toNontriviallyNormedField

namespace IsValuativeTopology

open scoped IsValuativeTopology

variable {L : Type*} [Field L] [ValuativeRel L] [IsRankLeOne L] [UniformSpace L]
  [IsUniformAddGroup L] [IsValuativeTopology L] {x y : L}

protected theorem isNonarchimedean_norm : IsNonarchimedean ((‖·‖) : L → ℝ) :=
  (IsRankLeOne.nonempty (R := L)).some.isNonarchimedean_absoluteValue

namespace toNormedField

theorem norm_def : ‖x‖ = (IsRankLeOne.nonempty (R := L)).some.emb (valuation L x) := rfl

theorem nnnorm_def : ‖x‖₊ = (IsRankLeOne.nonempty (R := L)).some.emb (valuation L x) := rfl

@[simp]
theorem norm_le_iff : ‖x‖ ≤ ‖y‖ ↔ x ≤ᵥ y :=
  (IsRankLeOne.nonempty (R := L)).some.absoluteValue_le_absoluteValue_iff

@[simp]
theorem norm_lt_iff : ‖x‖ < ‖y‖ ↔ x <ᵥ y :=
  (IsRankLeOne.nonempty (R := L)).some.absoluteValue_lt_absoluteValue_iff

@[simp]
theorem norm_le_one_iff : ‖x‖ ≤ 1 ↔ x ≤ᵥ 1 :=
  (IsRankLeOne.nonempty (R := L)).some.absoluteValue_le_one_iff

@[simp]
theorem norm_lt_one_iff : ‖x‖ < 1 ↔ x <ᵥ 1 :=
  (IsRankLeOne.nonempty (R := L)).some.absoluteValue_lt_one_iff

@[simp]
theorem one_le_norm_iff : 1 ≤ ‖x‖ ↔ 1 ≤ᵥ x :=
  (IsRankLeOne.nonempty (R := L)).some.one_le_absoluteValue_iff

@[simp]
theorem one_lt_norm_iff : 1 < ‖x‖ ↔ 1 <ᵥ x :=
  (IsRankLeOne.nonempty (R := L)).some.one_lt_absoluteValue_iff

theorem setOfPred_mem_integer_eq_closedBall :
    { x : L | x ∈ (valuation L).integer } = Metric.closedBall 0 1 := by
  ext x
  simp [mem_integer_iff, (valuation L).vle_one_iff]

end toNormedField

/-- The valuation `NormedField.valuation` of the normed field structure
`IsValuativeTopology.toNormedField` is compatible with the valuative relation. -/
instance : (NormedField.valuation (K := L)).Compatible where
  vle_iff_le x y := by
    rw [NormedField.valuation_apply, NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm,
      coe_nnnorm, toNormedField.norm_le_iff]

/-- The valuative relation determined by the norm of `IsValuativeTopology.toNormedField` is the
original valuative relation. -/
theorem toValuativeRel_eq : NormedField.toValuativeRel = ‹ValuativeRel L› := by
  ext x y
  exact NormedField.valuation.vle_iff_le.symm

end IsValuativeTopology
