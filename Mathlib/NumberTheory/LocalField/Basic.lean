/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

import Mathlib.RingTheory.Valuation.DiscreteValuativeRel
import Mathlib.Topology.Algebra.Module.Compact

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
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

lemma isCompact_closedBall (γ : ValueGroupWithZero K) : IsCompact { x | valuation K x ≤ γ } := by
  obtain ⟨γ, rfl⟩ := ValuativeRel.valuation_surjective γ
  by_cases hγ : γ = 0
  · simp [hγ]
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
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
      simp only [map_pow, Set.mem_ofPred_eq] at hx ⊢
      exact hx.trans_lt (by simpa [pow_two, hr])
    · refine ⟨r', hr', hr, .trans ?_ hrs⟩
      intro x hx
      dsimp at hx ⊢
      exact hx.trans_lt (hr.trans_le hr1)
  simp_rw [← (valuation K).restrict_le_iff] at H ⊢
  convert
    (hs'.of_isClosed_subset (Valued.isClosed_closedBall K _) H).image
      (Homeomorph.mulLeft₀ (γ / r) (by simp [hr, div_eq_zero_iff, hγ])).continuous using 1
  refine .trans ?_ (Equiv.image_eq_preimage_symm _ _).symm
  ext x
  simp only [Set.mem_ofPred_eq, Homeomorph.coe_symm_toEquiv, Homeomorph.mulLeft₀_symm_apply,
    inv_div, Set.preimage_ofPred_eq, map_mul, map_div₀, Valuation.restrict_le_iff]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by simp [hγ])]
  simp only [IsValuativeTopology.v_eq_valuation, ← map_mul, Valuation.restrict_le_iff]
  simp [hr]

lemma isCompact_vle (y : K) : IsCompact { x | x ≤ᵥ y } := by
  by_cases hy : y = 0
  · simp [hy]
  have hy' : 0 <ᵥ y := by simpa using hy
  obtain ⟨s, hs, -, hcompact⟩ :=
    LocallyCompactSpace.local_compact_nhds (0 : K) .univ Filter.univ_mem
  rw [IsValuativeTopology.mem_nhds_iff_exists_image_vlt_subset'] at hs
  obtain ⟨z, hz0, hz⟩ := hs
  simp only [zero_add, Set.image_id'] at hz
  obtain ⟨w, hw0, hw1, hw⟩ : ∃ w ≠ 0, w <ᵥ 1 ∧ {x | x ≤ᵥ w} ⊆ s := by
    obtain ⟨v, hv0, hv1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := K)
    obtain ⟨w, rfl⟩ := ValuativeRel.valuation_surjective v
    have hw0 : w ≠ 0 := by simpa using hv0
    have hw1 : w <ᵥ 1 := by simpa [(valuation K).vlt_iff_lt] using hv1
    by_cases hw : z ≤ᵥ w
    · refine ⟨z * w, by simp [hz0, hw0], ?_, ?_⟩
      · simpa using ValuativeRel.mul_vlt_mul (hw.trans_vlt hw1) hw1
      · apply hz.trans'
        intro x hx
        apply ValuativeRel.vle.trans_vlt hx
        simpa using ValuativeRel.mul_vlt_mul_of_vle_of_vlt (vle_refl z) hw1 (by simpa using hz0)
    · use w, hw0, hw1, Set.Subset.trans (fun x hx ↦ ValuativeRel.vle.trans_vlt hx hw) hz
  rw [← (Homeomorph.mulLeft₀ (y / w) (by simp [hy, hw0])).isCompact_preimage]
  suffices IsCompact {x | y / w * x ≤ᵥ y} by simpa
  convert_to IsCompact {x | x ≤ᵥ w}
  · ext x
    simp only [Set.mem_ofPred_eq]
    conv_rhs => rw [← ValuativeRel.mul_vle_mul_iff_right hy', ← ValuativeRel.div_vle_iff hw0,
      mul_div_right_comm]
  exact .of_isClosed_subset hcompact (IsValuativeTopology.isClosed_vle w) hw

instance : CompactSpace 𝒪[K] := isCompact_iff_compactSpace.mp (isCompact_vle K 1)

instance (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsValuativeTopology K] : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).Compatible :=
  inferInstanceAs (valuation K).Compatible

section Stuff

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]

lemma ValuativeRel.integer.isPrincipalIdealRing_of_compactSpace [hc : CompactSpace 𝒪[K]] :
    IsPrincipalIdealRing 𝒪[K] := by
  have hc : IsCompact (X := K) 𝒪[K] := isCompact_iff_compactSpace.mpr hc
  --obtain ⟨_⟩ := locallyFiniteOrder_units_mrange_of_isCompact_integer hc
  /- -- The strategy to show that we have a PIR is by contradiction,
  -- assuming that the range of the valuation is densely ordered.
  have hi : Valuation.Integers (R := K) Valued.v 𝒪[K] := Valuation.integer.integers v
  have hc : IsCompact (X := K) 𝒪[K] := isCompact_iff_compactSpace.mpr hc
  -- We can also construct that it has a locally finite order, by compactness
  -- which leads to a contradiction.
  obtain ⟨_⟩ := locallyFiniteOrder_units_mrange_of_isCompact_integer hc
  have hm := mulArchimedean_mrange_of_isCompact_integer hc
  -- The key result is that a valuation ring that maps into a `MulArchimedean` value group
  -- is a PIR iff the value group is not densely ordered.
  refine hi.isPrincipalIdealRing_iff_not_denselyOrdered_mrange.mpr fun _ ↦ ?_
  -- since we are densely ordered, we necessarily are nontrivial
  exact not_subsingleton (MonoidHom.mrange (v : Valuation K Γ₀))ˣ
    (LocallyFiniteOrder.denselyOrdered_iff_subsingleton.mp inferInstance)-/
  sorry


theorem ValuativeRel.integer.isDiscreteValuationRing_of_compactSpace [CompactSpace 𝒪[K]]
    [ValuativeRel.IsNontrivial K] :
    IsDiscreteValuationRing 𝒪[K] where
  -- To prove we have a DVR, we need to show it is
  -- a local ring (instance is directly inferred) and a PIR and not a field.
  __ := ValuativeRel.integer.isPrincipalIdealRing_of_compactSpace
  not_a_field' := sorry

end Stuff

instance : IsDiscreteValuationRing 𝒪[K] :=
  ValuativeRel.integer.isDiscreteValuationRing_of_compactSpace

/-- The value group of a local field is (uniquely) isomorphic to `ℤᵐ⁰`. -/
noncomputable
def valueGroupWithZeroIsoInt : ValueGroupWithZero K ≃*o ℤᵐ⁰ := by
  apply Nonempty.some
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  have : CompactSpace 𝒪[K] := inferInstance
  rw [← valuationInteger_valuation_eq_integer] at this
  obtain ⟨_⟩ := Valued.integer.locallyFiniteOrder_units_mrange_of_isCompact_integer
    (isCompact_iff_compactSpace.mpr this)
  let e : (MonoidHom.mrange (valuation K)) ≃*o ValueGroupWithZero K :=
    ⟨.ofBijective (MonoidHom.mrange (valuation K)).subtype ⟨Subtype.val_injective, fun x ↦
      ⟨⟨x, ValuativeRel.valuation_surjective x⟩, rfl⟩⟩, .rfl⟩
  have : Nontrivial (ValueGroupWithZero K)ˣ := isNontrivial_iff_nontrivial_units.mp inferInstance
  have : Nontrivial (↥(MonoidHom.mrange (valuation K)))ˣ :=
    (Units.map_injective (f := e.symm.toMonoidHom) e.symm.injective).nontrivial
  exact ⟨e.symm.trans (LocallyFiniteOrder.orderMonoidWithZeroEquiv _)⟩

instance : IsCyclic (ValueGroupWithZero K)ˣ :=
  (Units.mapEquiv (valueGroupWithZeroIsoInt K).toMulEquiv).isCyclic.mpr inferInstance

instance : ValuativeRel.IsDiscrete K :=
  (ValuativeRel.ValueGroupWithZero.nonempty_orderMonoidIso_withZeroMulInt_iff.mp
    ⟨valueGroupWithZeroIsoInt K⟩).1

instance : ValuativeRel.IsRankLeOne K :=
  ValuativeRel.isRankLeOne_iff_mulArchimedean.mpr
    (.comap (valueGroupWithZeroIsoInt K).toMonoidHom (valueGroupWithZeroIsoInt K).strictMono)

instance : Finite 𝓀[K] := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  sorry
  /-rw [← integer_valuation_eq_integer]
  exact (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstanceAs (CompactSpace (Valued.integer K)))).2.2-/

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
  sorry
  /-(compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstanceAs (Valued.integer K))).1-/

open scoped Pointwise in
instance : IsAdicComplete 𝓂[K] 𝒪[K] where
  prec' f hf := by
    let S n : Set 𝒪[K] := f n +ᵥ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
    have hS n : S (n + 1) ⊆ S n := by
      apply (Set.vadd_set_subset_vadd_set_iff.mpr (Ideal.pow_le_pow_right n.le_succ)).trans
      simpa [S] using (hf n.le_succ).symm
    have h n : IsClosed (S n) := (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ n)).vadd (f n)
    obtain ⟨L, hL⟩ := (h 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hS
      (by simp [S]) h
    refine ⟨L, fun n ↦ ?_⟩
    obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.mp hL n
    simpa [SModEq.sub_mem] using hy

end UniformSpace

end IsNonarchimedeanLocalField
