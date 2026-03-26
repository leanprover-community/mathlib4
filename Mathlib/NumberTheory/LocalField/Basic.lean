/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Valuation.DiscreteValuativeRel
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!

# Definition of (Non-archimedean) local fields

Given a topological field `K` equipped with an equivalence class of valuations (a `ValuativeRel`),
we say that it is a non-archimedean local field if the topology comes from the given valuation,
and it is locally compact and non-discrete.

-/

@[expose] public section

/--
Given a topological field `K` equipped with an equivalence class of valuations (a `ValuativeRel`),
we say that it is a non-archimedean local field if the topology comes from the given valuation,
and it is locally compact and non-discrete.

This implies the following typeclasses via `inferInstance`
- `IsValuativeTopology K`
- `LocallyCompactSpace K`
- `IsTopologicalDivisionRing K`
- `ValuativeRel.IsNontrivial K`
- `ValuativeRel.IsRankLeOne K`
- `ValuativeRel.IsDiscrete K`
- `IsDiscreteValuationRing 𝒪[K]`
- `Finite 𝓀[K]`

Assuming we have a compatible `UniformSpace K` instance
(e.g. via `IsTopologicalAddGroup.toUniformSpace` and `isUniformAddGroup_of_addCommGroup`) then
- `CompleteSpace K`
- `CompleteSpace 𝒪[K]`
-/
class IsNonarchimedeanLocalField
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] : Prop extends
  IsValuativeTopology K,
  LocallyCompactSpace K,
  ValuativeRel.IsNontrivial K

open ValuativeRel Valued.integer

open scoped WithZero

namespace IsNonarchimedeanLocalField

section TopologicalSpace

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

attribute [local simp] zero_lt_iff

instance : IsTopologicalDivisionRing K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

lemma isCompact_closedBall (γ : ValueGroupWithZero K) : IsCompact { x | valuation K x ≤ γ } := by
  obtain ⟨γ, rfl⟩ := ValuativeRel.valuation_surjective γ
  by_cases hγ : γ = 0
  · simp [hγ]
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  obtain ⟨s, hs, -, hs'⟩ := LocallyCompactSpace.local_compact_nhds (0 : K) .univ Filter.univ_mem
  obtain ⟨r, hr, hr1, H⟩ :
      ∃ r', r' ≠ 0 ∧ valuation K r' < 1 ∧ { x | valuation K x ≤ valuation K r' } ⊆ s := by
    obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' K).mem_iff.mp hs
    obtain ⟨r', hr', hr⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
    simp only [ne_eq] at hr'
    obtain hr1 | hr1 := lt_or_ge r 1
    · obtain ⟨r, rfl⟩ := ValuativeRel.valuation_surjective r
      simp only [ne_eq, map_eq_zero] at hr
      refine ⟨r ^ 2, by simpa using hr, by simpa [pow_two], fun x hx ↦ hrs ?_⟩
      simp only [map_pow, Set.mem_setOf_eq] at hx ⊢
      exact hx.trans_lt (by simpa [pow_two, hr])
    · refine ⟨r', hr', hr, .trans ?_ hrs⟩
      intro x hx
      dsimp at hx ⊢
      exact hx.trans_lt (hr.trans_le hr1)
  simp_rw [← (valuation K).restrict_le_iff] at H ⊢
  convert (hs'.of_isClosed_subset (Valued.isClosed_closedBall K _) H).image
    (Homeomorph.mulLeft₀ (γ / r) (by simp [hr, div_eq_zero_iff, hγ])).continuous using 1
  refine .trans ?_ (Equiv.image_eq_preimage_symm _ _).symm
  ext x
  simp only [Set.mem_setOf_eq, Homeomorph.coe_symm_toEquiv, Homeomorph.mulLeft₀_symm_apply, inv_div,
    Set.preimage_setOf_eq, map_mul, map_div₀, Valuation.restrict_le_iff]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by simp [hγ])]
  simp only [IsValuativeTopology.v_eq_valuation, ← map_mul, Valuation.restrict_le_iff]
  simp [hr]

instance : CompactSpace 𝒪[K] := isCompact_iff_compactSpace.mp (isCompact_closedBall K 1)

instance (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsValuativeTopology K] : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).Compatible :=
  inferInstanceAs (valuation K).Compatible

instance : IsDiscreteValuationRing 𝒪[K] :=
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI : CompactSpace (Valued.integer K) := inferInstanceAs (CompactSpace 𝒪[K])
  Valued.integer.isDiscreteValuationRing_of_compactSpace

/-- The value group of a local field is (uniquely) isomorphic to `ℤᵐ⁰`. -/
noncomputable
def valueGroupWithZeroIsoInt : ValueGroupWithZero K ≃*o ℤᵐ⁰ := by
  apply Nonempty.some
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  obtain ⟨_⟩ := Valued.integer.locallyFiniteOrder_units_mrange_of_isCompact_integer
    (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[K]))
  let e : (MonoidHom.mrange (valuation K)) ≃*o ValueGroupWithZero K :=
    ⟨.ofBijective (MonoidHom.mrange (valuation K)).subtype ⟨Subtype.val_injective, fun x ↦
      ⟨⟨x, ValuativeRel.valuation_surjective x⟩, rfl⟩⟩, .rfl⟩
  have : Nontrivial (ValueGroupWithZero K)ˣ := isNontrivial_iff_nontrivial_units.mp inferInstance
  have : Nontrivial (↥(MonoidHom.mrange (valuation K)))ˣ :=
    (Units.map_injective (f := e.symm.toMonoidHom) e.symm.injective).nontrivial
  exact ⟨e.symm.trans (LocallyFiniteOrder.orderMonoidWithZeroEquiv _)⟩

instance : ValuativeRel.IsDiscrete K :=
  (ValuativeRel.nonempty_orderIso_withZeroMul_int_iff.mp ⟨valueGroupWithZeroIsoInt K⟩).1

instance : ValuativeRel.IsRankLeOne K :=
  ValuativeRel.isRankLeOne_iff_mulArchimedean.mpr
    (.comap (valueGroupWithZeroIsoInt K).toMonoidHom (valueGroupWithZeroIsoInt K).strictMono)

instance : Finite 𝓀[K] :=
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstanceAs (CompactSpace 𝒪[K]))).2.2

proof_wanted isAdicComplete : IsAdicComplete 𝓂[K] 𝒪[K]

end TopologicalSpace

section UniformSpace

variable (K : Type*) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

instance : CompleteSpace K :=
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp
    inferInstance).1

instance : CompleteSpace 𝒪[K] :=
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstanceAs (CompactSpace 𝒪[K]))).1

end UniformSpace

end IsNonarchimedeanLocalField
