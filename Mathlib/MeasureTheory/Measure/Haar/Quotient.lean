/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth

! This file was ported from Lean 3 source module measure_theory.measure.haar.quotient
! leanprover-community/mathlib commit fd5edc43dc4f10b85abfe544b88f82cf13c5f844
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Algebra.Group.Opposite
import Mathlib.MeasureTheory.Constructions.Polish

/-!
# Haar quotient measure

In this file, we consider properties of fundamental domains and measures for the action of a
subgroup of a group `G` on `G` itself.

## Main results

* `MeasureTheory.IsFundamentalDomain.smulInvariantMeasure_map `: given a subgroup `Γ` of a
  topological group `G`, the pushforward to the coset space `G ⧸ Γ` of the restriction of a both
  left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure
  on `G ⧸ Γ`.

* `MeasureTheory.IsFundamentalDomain.isMulLeftInvariant_map `: given a normal subgroup `Γ` of
  a topological group `G`, the pushforward to the quotient group `G ⧸ Γ` of the restriction of
  a both left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a left-invariant
  measure on `G ⧸ Γ`.

Note that a group `G` with Haar measure that is both left and right invariant is called
**unimodular**.
-/


open Set MeasureTheory TopologicalSpace MeasureTheory.Measure


open scoped Pointwise NNReal

section

variable {G : Type _} [Group G] [MeasurableSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {Γ : Subgroup G} [PolishSpace G] [T2Space (G ⧸ Γ)]
  [SecondCountableTopology (G ⧸ Γ)]

--- TODO: move to `measure_theory.constructions.polish`
instance CosetSpace.borelSpace {G : Type _} [TopologicalSpace G] [PolishSpace G]
    [Group G] [MeasurableSpace G] [BorelSpace G] {N : Subgroup G} [T2Space (G ⧸ N)]
    [SecondCountableTopology (G ⧸ N)] : BorelSpace (G ⧸ N) := Quotient.borelSpace

/-- Measurability of the action of the topological group `G` on the left-coset space `G / Γ`. -/
--@[to_additive "Measurability of the action of the additive topological group `G` on the left-coset
--  space `G / Γ`."]
instance QuotientGroup.measurableSMul [PolishSpace G] [T2Space (G ⧸ Γ)]
    [SecondCountableTopology (G ⧸ Γ)] : MeasurableSMul G (G ⧸ Γ) where
  measurable_const_smul g := (continuous_const_smul g).measurable
  measurable_smul_const x := (QuotientGroup.continuous_smul₁ x).measurable
#align quotient_group.has_measurable_smul QuotientGroup.measurableSMul
--#align quotient_add_group.has_measurable_vadd QuotientAddGroup.measurableVAdd

end

section smulInvariantMeasure

variable {G : Type _} [Group G] [MeasureSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {Γ : Subgroup G} [PolishSpace G] [T2Space (G ⧸ Γ)]
  [SecondCountableTopology (G ⧸ Γ)]

--variable {𝓕 : Set G} (h𝓕 : IsFundamentalDomain (Subgroup.opposite Γ) 𝓕 μ)

variable {μ : Measure (G ⧸ Γ)}

local notation "π" => @QuotientGroup.mk G _ Γ

-- set_option linter.unusedVariables false in
-- class QuotientVolumeEqVolumePreimage' [MeasureSpace (G ⧸ Γ)] : Prop where
--   projection_respects_measure : ∀ (t : Set G)
--   (fund_dom_t : IsFundamentalDomain (Subgroup.opposite Γ) t)
--     (meas_t : MeasurableSet t) (U : Set (G ⧸ Γ)) (meas_U : MeasurableSet U),
--     volume U = volume (π ⁻¹' U ∩ t)


variable [Countable Γ] --[MeasureSpace G] -- [MeasureSpace (G ⧸ Γ)]
  [QuotientVolumeEqVolumePreimage (Subgroup.opposite Γ) G μ]
--[BorelSpace (G ⧸ Γ)]


-- more beautiful theorem: if you have ameasure speace downstairs and the downstairs one is smul invariant
-- then fund dom independent

/-- The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and right-
  invariant measure on `G` to is a `G`-invariant measure on `G ⧸ Γ`. -/
-- @[to_additive "The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and
--   right-invariant measure on an additive topological group `G` to a fundamental domain `𝓕` is a
--   `G`-invariant measure on `G ⧸ Γ`."]
instance MeasureTheory.QuotientVolumeEqVolumePreimage.smulInvariantMeasure_quotient
    [IsMulLeftInvariant (volume : Measure G)] [IsMulRightInvariant (volume : Measure G)]
    [hasFun : HasFundamentalDomain (Subgroup.opposite Γ) G] :
    SMulInvariantMeasure G (G ⧸ Γ) μ where
  measure_preimage_smul g A hA := by
    have meas_π : Measurable π := continuous_quotient_mk'.measurable
    have meas_πA : MeasurableSet (π ⁻¹' A) := measurableSet_preimage meas_π hA
    obtain ⟨𝓕, h𝓕, meas_𝓕⟩ := hasFun.has_fundamental_domain_characterization
    have meas_g𝓕 : MeasurableSet (g • 𝓕)
    · rw [← preimage_smul_inv]
      exact (@measurable_const_smul G G _ _ _ _ (g⁻¹)) meas_𝓕
    have h𝓕_translate_fundom : IsFundamentalDomain (Subgroup.opposite Γ) (g • 𝓕) volume :=
      h𝓕.smul_of_comm g
    rw [QuotientVolumeEqVolumePreimage.projection_respects_measure 𝓕 h𝓕 meas_𝓕 _
      (meas_π (measurableSet_preimage (measurable_const_smul g) hA)),
      QuotientVolumeEqVolumePreimage.projection_respects_measure _ h𝓕_translate_fundom meas_g𝓕 _
      hA]
    change volume ((π ⁻¹' _) ∩ _) = _
    set π_preA := π ⁻¹' A
    have : π ⁻¹' ((fun x : G ⧸ Γ => g • x) ⁻¹' A) = (g * ·) ⁻¹' π_preA := by ext1; simp
    rw [this]
    have : volume ((g * ·) ⁻¹' π_preA ∩ 𝓕) = volume (π_preA ∩ (g⁻¹ * ·) ⁻¹' 𝓕)
    · trans volume ((g * ·) ⁻¹' (π_preA ∩ (g⁻¹ * ·) ⁻¹' 𝓕))
      · rw [preimage_inter]
        congr 2
        simp [Set.preimage]
      rw [measure_preimage_mul]
    rw [this, ← preimage_smul_inv]; rfl

end smulInvariantMeasure

section mulInvariantMeasure


variable {G : Type _} [Group G] [MeasureSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {Γ : Subgroup G} [PolishSpace G] [T2Space (G ⧸ Γ)]
  [SecondCountableTopology (G ⧸ Γ)] {μ : Measure (G ⧸ Γ)}
  [Countable Γ] [QuotientVolumeEqVolumePreimage (Subgroup.opposite Γ) G μ]

/-- Assuming `Γ` is a normal subgroup of a topological group `G`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of a both left- and right-invariant measure on `G` to a
  fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`. -/
-- @[to_additive "Assuming `Γ` is a normal subgroup of an additive topological group `G`, the
--   pushforward to the quotient group `G ⧸ Γ` of the restriction of a both left- and right-invariant
--   measure on `G` to a fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`."]
instance MeasureTheory.QuotientVolumeEqVolumePreimage.MulInvariantMeasure_quotient
    [Subgroup.Normal Γ] [IsMulLeftInvariant (volume : Measure G)]
    [IsMulRightInvariant (volume : Measure G)]
    [hasFun : HasFundamentalDomain (Subgroup.opposite Γ) G]  :
    μ.IsMulLeftInvariant where
  map_mul_left_eq_self x := by
    apply Measure.ext
    intro A hA
    obtain ⟨x₁, h⟩ := @Quotient.exists_rep _ (QuotientGroup.leftRel Γ) x
    --haveI := h𝓕.smulInvariantMeasure_map
    convert measure_preimage_smul x₁ μ A using 1
    rw [← h, Measure.map_apply]
    · rfl
    · exact measurable_const_mul _
    · exact hA

---- the quotient measure is finite, assuming the covolume is finite
theorem MeasureTheory.QuotientVolumeEqVolumePreimage.Finite_quotient
    [Subgroup.Normal Γ] [IsMulLeftInvariant (volume : Measure G)]
    [IsMulRightInvariant (volume : Measure G)]
    [hasFun : HasFundamentalDomain (Subgroup.opposite Γ) G]
    (h : covolume (Subgroup.opposite Γ) G < ⊤) :
    IsFiniteMeasure μ := by
  obtain ⟨𝓕, h𝓕, meas_𝓕⟩ := hasFun.has_fundamental_domain_characterization
  have 𝓕meas : NullMeasurableSet 𝓕 volume := h𝓕.nullMeasurableSet
  rw [@QuotientVolumeEqVolumePreimage.eq_map_restrict (s := 𝓕) (G := Subgroup.opposite Γ) _
    _ _ _ _ _ _ meas_𝓕 h𝓕 μ _]
  haveI : Fact (volume 𝓕 < ⊤) := by
    apply Fact.mk
    convert h
    rw [covolume_eq_volume]
    exact h𝓕
  exact inferInstance

end mulInvariantMeasure

section QuotientIsHaar

variable {G : Type _} [Group G] [MeasureSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {Γ : Subgroup G} [PolishSpace G] [i : T2Space (G ⧸ Γ)]
  [ii : SecondCountableTopology (G ⧸ Γ)] {μ : Measure (G ⧸ Γ)}
  [Countable Γ] [QuotientVolumeEqVolumePreimage (Subgroup.opposite Γ) G μ]

variable [T2Space (G ⧸ Γ)] [SecondCountableTopology (G ⧸ Γ)] (K : PositiveCompacts (G ⧸ Γ))


/-- Given a normal cofinite subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is
  also right-invariant, and a measure `μ` on `G ⧸ Γ` which is compatible under the quotient map
  with the volume on `G`, that measure `μ` is a multiple of Haar measure on `G ⧸ Γ`. -/
theorem MeasureTheory.QuotientVolumeEqVolumePreimage.quotient_is_haar [Subgroup.Normal Γ]
    [MeasureTheory.Measure.IsHaarMeasure (volume : Measure G)]
    [HasFundamentalDomain (Subgroup.opposite Γ) G] [IsMulRightInvariant (volume : Measure G)]
    (h : covolume (Subgroup.opposite Γ) G < ⊤) :
    μ = μ K • MeasureTheory.Measure.haarMeasure K := by
  haveI : IsFiniteMeasure μ := QuotientVolumeEqVolumePreimage.Finite_quotient h
  rw [Measure.haarMeasure_unique μ K, Measure.smul_apply, Measure.haarMeasure_self]
  simp


/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ` is
  measure-preserving between appropriate multiples of Haar measure on `G` and `G ⧸ Γ`. -/
theorem MeasurePreservingQuotientGroup.mk' [Subgroup.Normal Γ]
    [MeasureTheory.Measure.IsHaarMeasure (volume : Measure G)]
    [IsMulRightInvariant (volume : Measure G)]
    (𝓕 : Set G)
    (h𝓕 : IsFundamentalDomain (Subgroup.opposite Γ) 𝓕)
    (meas_𝓕 : MeasurableSet 𝓕)
    (h𝓕_finite : volume 𝓕 < ⊤)
    (c : ℝ≥0)
    (h : volume ((QuotientGroup.mk' Γ ⁻¹' (K : Set (G ⧸ Γ))) ∩ 𝓕) = c) :
    MeasurePreserving (QuotientGroup.mk' Γ) (volume.restrict 𝓕)
      (c • MeasureTheory.Measure.haarMeasure K) where
  measurable := continuous_quotient_mk'.measurable
  map_eq := by
    haveI : HasFundamentalDomain (Subgroup.opposite Γ) G := ⟨𝓕, h𝓕, meas_𝓕⟩
    let μ := Measure.map (QuotientGroup.mk' Γ) (volume.restrict 𝓕)
    haveI : QuotientVolumeEqVolumePreimage (Subgroup.opposite Γ) G μ :=
      quotientVolumeEqVolumePreimage_map_restrict (Subgroup.opposite Γ) G 𝓕 meas_𝓕 h𝓕
    convert QuotientVolumeEqVolumePreimage.quotient_is_haar K _ (μ := μ) using 1
    trans (c : ENNReal) • haarMeasure K
    · norm_cast
    · rw [QuotientVolumeEqVolumePreimage.projection_respects_measure 𝓕 h𝓕 meas_𝓕, ← h]
      · rfl
      · haveI : T2Space (Quotient (MulAction.orbitRel (Subgroup.opposite Γ) G)) := i
        haveI : SecondCountableTopology (Quotient (MulAction.orbitRel (Subgroup.opposite Γ) G)) :=
          ii
        haveI : BorelSpace (Quotient (MulAction.orbitRel (Subgroup.opposite Γ) G)) := Quotient.borelSpace
        apply IsCompact.measurableSet
        exact PositiveCompacts.isCompact K
    · convert h𝓕_finite using 1
      rw [covolume_eq_volume]
      exact h𝓕
-- #align measure_preserving_quotient_group.mk' MeasurePreservingQuotientGroup.mk'
-- #align measure_preserving_quotient_add_group.mk' MeasurePreservingQuotientAddGroup.mk'

end QuotientIsHaar
