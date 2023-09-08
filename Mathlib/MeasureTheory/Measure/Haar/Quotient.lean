/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Algebra.Group.Opposite
import Mathlib.MeasureTheory.Constructions.Polish

#align_import measure_theory.measure.haar.quotient from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

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

-- TODO : make additive version of the below

/-- Measurability of the action of the topological group `G` on the left-coset space `G / Γ`. -/
--@[to_additive "Measurability of the action of the additive topological group `G` on the left-coset
--  space `G / Γ`."]
instance QuotientGroup.measurableSMul [PolishSpace G] [T2Space (G ⧸ Γ)]
    [SecondCountableTopology (G ⧸ Γ)] : MeasurableSMul G (G ⧸ Γ) where
  measurable_const_smul g := (continuous_const_smul g).measurable
  measurable_smul_const x := (QuotientGroup.continuous_smul₁ x).measurable
#align quotient_group.has_measurable_smul QuotientGroup.measurableSMul
--#align quotient_add_group.has_measurable_vadd QuotientAddGroup.measurableVAdd


/-- Any map on the zero measures is `MeasurePreserving` -/
theorem MeasurePreserving.zero {X Y : Type _} {f : X → Y} [MeasurableSpace X] [MeasurableSpace Y]
    (hf : Measurable f) : MeasurePreserving f 0 0 where
      measurable := hf
      map_eq := Measure.map_zero f

/-- Move somewhere -/
theorem QuotientGroup.sound [Subgroup.Normal Γ] (U : Set (G ⧸ Γ)) (g : (Subgroup.opposite Γ)) :
    g • (QuotientGroup.mk' Γ) ⁻¹' U = (QuotientGroup.mk' Γ) ⁻¹' U := by
  rw [QuotientGroup.coe_mk']
  ext x
  simp only [mem_preimage]
  have := @Set.mem_inv_smul_set_iff (x := x) (A := (mk' Γ) ⁻¹' U) (a := g⁻¹) _ _
  simp only [inv_inv, coe_mk', mem_preimage] at this
  convert this using 2
  apply @Quotient.sound (a := x) (s := (QuotientGroup.leftRel Γ)) (b := g⁻¹ • x)
  use g
  simp

end

section smulInvariantMeasure

variable {G : Type _} [Group G] [MeasureSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] [PolishSpace G] {Γ : Subgroup G} [Countable Γ] [T2Space (G ⧸ Γ)]
  [SecondCountableTopology (G ⧸ Γ)] {μ : Measure (G ⧸ Γ)}
  [QuotientVolumeEqVolumePreimage μ]

local notation "π" => @QuotientGroup.mk G _ Γ

-- more beautiful theorem: if you have a measure speace downstairs and the downstairs one is smul invariant
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
    rw [projection_respects_measure h𝓕 meas_𝓕
      (meas_π (measurableSet_preimage (measurable_const_smul g) hA)),
      projection_respects_measure h𝓕_translate_fundom meas_g𝓕 hA]
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

/-- Given a subgroup `Γ` of a topological group `G` with Haar measure `volume`, with a measure 'μ'
  on the quotient `G ⧸ Γ` satisfying `QuotientVolumeEqVolumePreimage`, the restriction of `volume`
  to a fundamental domain is measure-preserving with respect to `μ`. -/
theorem measurePreserving_quotientGroup_mk_of_quotientVolumeEqVolumePreimage
    [IsMulLeftInvariant (volume : Measure G)] [IsMulRightInvariant (volume : Measure G)]
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain (Subgroup.opposite Γ) 𝓕)
    (meas_𝓕 : MeasurableSet 𝓕) (μ : Measure (G ⧸ Γ))
    [QuotientVolumeEqVolumePreimage μ] :
    MeasurePreserving (@QuotientGroup.mk G _ Γ) (volume.restrict 𝓕) μ :=
  measurePreserving_quotient_mk_of_quotientVolumeEqVolumePreimage h𝓕 meas_𝓕 μ

/-- The quotient measure is finite, assuming the covolume is finite -/
theorem MeasureTheory.QuotientVolumeEqVolumePreimage.Finite_quotient
    [IsMulRightInvariant (volume : Measure G)]
    [hasFun : HasFundamentalDomain (Subgroup.opposite Γ) G] (h : hasFun.covolume ≠ ⊤) :
    IsFiniteMeasure μ := by
  obtain ⟨𝓕, h𝓕, meas_𝓕⟩ := hasFun.has_fundamental_domain_characterization
  rw [QuotientVolumeEqVolumePreimage.eq_quotientMeasure h𝓕 meas_𝓕 μ,
    meas_𝓕.quotientMeasure_eq_map_restrict]
  have : Fact (volume 𝓕 < ⊤) := by
    apply Fact.mk
    convert Ne.lt_top h
    rw [h𝓕.covolume_eq_volume meas_𝓕]
  exact inferInstance

end smulInvariantMeasure

section mulInvariantMeasure

variable {G : Type _} [Group G] [MeasureSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {Γ : Subgroup G} [PolishSpace G] [T2Space (G ⧸ Γ)]
  [SecondCountableTopology (G ⧸ Γ)] {μ : Measure (G ⧸ Γ)}
  [Countable Γ] [QuotientVolumeEqVolumePreimage μ]

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
    convert measure_preimage_smul x₁ μ A using 1
    rw [← h, Measure.map_apply (measurable_const_mul _) hA]
    rfl

end mulInvariantMeasure

section HaarIsQuotientVolumeEqVolumePreimage

variable {G : Type _} [Group G] [MeasureSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {Γ : Subgroup G} [PolishSpace G] [T2Space (G ⧸ Γ)]
  [SecondCountableTopology (G ⧸ Γ)] [Countable Γ] [Subgroup.Normal Γ]
  [IsMulLeftInvariant (volume : Measure G)] [IsMulRightInvariant (volume : Measure G)]
  {μ : Measure (G ⧸ Γ)} [IsMulLeftInvariant μ] [SigmaFinite μ]
  -- Note: couldn't get uniqueness without sigma finiteness

local notation "π" => @QuotientGroup.mk G _ Γ

/-- Assume that a measure `μ` is `IsHaarMeasure`, that the action of `Γ` on `G` has a measurable
fundamental domain `s` with positive finite volume, and that there is a single measurable set
`V ⊆ G ⧸ Γ` along which the pullback of `μ` and `volume` agree (so the scaling is right). Then `μ`
satisfies `QuotientVolumeEqVolumePreimage`. The main tool of the proof is the uniqueness of left
invariant measures, if normalized by a single positive finite-measured set. -/
theorem MeasureTheory.HaarIsQuotientVolumeEqVolumePreimage_ofSet
    {s : Set G} (fund_dom_s : IsFundamentalDomain (Subgroup.opposite Γ) s)
    (meas_s : MeasurableSet s) (finiteVol : volume s ≠ ⊤)
    {V : Set (G ⧸ Γ)} (meas_V : MeasurableSet V) (neZeroV : μ V ≠ 0)
    (hV : μ V = volume (π ⁻¹' V ∩ s)) : QuotientVolumeEqVolumePreimage μ := by
  apply fund_dom_s.QuotientVolumeEqVolumePreimage meas_s
  intro U meas_U
  let μ' : Measure (G ⧸ Γ) := meas_s.quotientMeasure (Subgroup.opposite Γ) volume
  haveI has_fund : HasFundamentalDomain (Subgroup.opposite Γ) G := ⟨⟨s, fund_dom_s, meas_s⟩⟩
  have fin_coVol : has_fund.covolume ≠ ⊤ := by
    rw [fund_dom_s.covolume_eq_volume meas_s]
    exact finiteVol
  have : QuotientVolumeEqVolumePreimage μ' :=
    fund_dom_s.QuotientVolumeEqVolumePreimage_quotientMeasure meas_s
  have : μ'.IsMulLeftInvariant :=
    MeasureTheory.QuotientVolumeEqVolumePreimage.MulInvariantMeasure_quotient
  have : IsFiniteMeasure μ' :=
    QuotientVolumeEqVolumePreimage.Finite_quotient fin_coVol
  have neTopV : μ V ≠ ⊤
  · contrapose! finiteVol
    rw [hV] at finiteVol
    refine top_unique (trans finiteVol.symm ?_)
    exact measure_mono (Set.inter_subset_right _ _)
  suffices : μ = μ'
  · rw [this, MeasurableSet.quotientMeasure_apply]
    exact meas_U
  · rw [@measure_eq_div_smul (μ := μ') (ν := μ) (s := V) _ _ _ _ _ _ _ _ meas_V neZeroV neTopV, hV]
    symm
    convert one_smul ENNReal μ
    rw [meas_s.quotientMeasure_apply _ meas_V]
    convert ENNReal.div_self ..
    · exact trans hV.symm neZeroV
    · exact trans hV.symm neTopV

/-- If a measure `μ` is `IsHaarMeasure` and satisfies the right scaling condition, then it
  satisfies `QuotientVolumeEqVolumePreimage`. -/
theorem MeasureTheory.HaarIsQuotientVolumeEqVolumePreimage
    [hasFun : HasFundamentalDomain (Subgroup.opposite Γ) G]
    (h : hasFun.covolume = μ univ) (finiteCovol : hasFun.covolume ≠ ⊤) :
    QuotientVolumeEqVolumePreimage μ := by
  obtain ⟨s, fund_dom_s, meas_s⟩ := hasFun.has_fundamental_domain_characterization
  rw [fund_dom_s.covolume_eq_volume meas_s] at finiteCovol h
  by_cases meas_s_ne_zero : volume s = 0
  · convert fund_dom_s.QuotientVolumeEqVolumePreimage_of_volume_zero meas_s meas_s_ne_zero
    rw [← @measure_univ_eq_zero, ←h, meas_s_ne_zero]
  apply MeasureTheory.HaarIsQuotientVolumeEqVolumePreimage_ofSet (s := s) (fund_dom_s := fund_dom_s)
    (meas_s := meas_s) (finiteVol := finiteCovol) (meas_V := MeasurableSet.univ)
  · rw [← h]
    exact meas_s_ne_zero
  · rw [← h]
    simp

end HaarIsQuotientVolumeEqVolumePreimage

section QuotientIsHaar

variable {G : Type _} [Group G] [MeasureSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {Γ : Subgroup G} [PolishSpace G] [i : T2Space (G ⧸ Γ)]
  [ii : SecondCountableTopology (G ⧸ Γ)] {μ : Measure (G ⧸ Γ)}
  [Countable Γ] [QuotientVolumeEqVolumePreimage μ]

variable [T2Space (G ⧸ Γ)] [SecondCountableTopology (G ⧸ Γ)] (K : PositiveCompacts (G ⧸ Γ))

/-- Given a normal cofinite subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is
  also right-invariant, and a measure `μ` on `G ⧸ Γ` which is compatible under the quotient map
  with the volume on `G`, that measure `μ` is a multiple of Haar measure on `G ⧸ Γ`. -/
theorem MeasureTheory.QuotientVolumeEqVolumePreimage.quotient_is_haar [Subgroup.Normal Γ]
    [MeasureTheory.Measure.IsHaarMeasure (volume : Measure G)]
    [IsMulRightInvariant (volume : Measure G)]
    [hasFun : HasFundamentalDomain (Subgroup.opposite Γ) G]
    (h : hasFun.covolume < ⊤) :
    μ = μ K • MeasureTheory.Measure.haarMeasure K := by
  have : IsFiniteMeasure μ := QuotientVolumeEqVolumePreimage.Finite_quotient h.ne
  rw [Measure.haarMeasure_unique μ K, Measure.smul_apply, Measure.haarMeasure_self]
  simp


--- 7/21/23
-- Need a lemma about our magic typeclass:
-- Lemma: behavior under scaling


/- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
  properly normalized, satisfies `QuotientVolumeEqVolumePreimage`. -/
theorem IsFundamentalDomain.QuotientVolumeEqVolumePreimage_HaarMeasure [Subgroup.Normal Γ]
    [MeasureTheory.Measure.IsHaarMeasure (volume : Measure G)] [T2Space (G ⧸ Γ)]
    [BorelSpace (G ⧸ Γ)] [IsMulRightInvariant (volume : Measure G)] {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain (Subgroup.opposite Γ) 𝓕)
    (meas_𝓕 : MeasurableSet 𝓕) (h𝓕_finite : volume 𝓕 ≠ ⊤)
    (μ : Measure (G ⧸ Γ)) [IsMulLeftInvariant μ] [SigmaFinite μ]
    {V : Set (G ⧸ Γ)} (hV : (interior V).Nonempty) (meas_V : MeasurableSet V)
    (hμK : μ V = volume ((QuotientGroup.mk' Γ ⁻¹' V) ∩ 𝓕)) :
    QuotientVolumeEqVolumePreimage μ := by
  apply MeasureTheory.HaarIsQuotientVolumeEqVolumePreimage_ofSet (fund_dom_s := h𝓕)
    (meas_s := meas_𝓕) (finiteVol := h𝓕_finite) (meas_V := meas_V)
  · intro c_eq_zero
    apply Measure.IsOpenPosMeasure.open_pos (interior (QuotientGroup.mk' Γ ⁻¹' V)) (μ := volume)
    · simp
    · apply Set.Nonempty.mono (preimage_interior_subset_interior_preimage continuous_coinduced_rng)
      apply hV.preimage'
      simp
    · apply measure_mono_null (h := interior_subset)
      apply h𝓕.measure_zero_of_invariant (ht := fun g ↦ QuotientGroup.sound _ _)
      rw [← hμK]
      exact c_eq_zero
  · exact hμK

/- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
  properly normalized, satisfies `QuotientVolumeEqVolumePreimage`. -/
theorem IsFundamentalDomain.QuotientVolumeEqVolumePreimage_bubHaarMeasure [Subgroup.Normal Γ]
    [MeasureTheory.Measure.IsHaarMeasure (volume : Measure G)] [T2Space (G ⧸ Γ)]
    [BorelSpace (G ⧸ Γ)] [IsMulRightInvariant (volume : Measure G)] {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain (Subgroup.opposite Γ) 𝓕)
    (meas_𝓕 : MeasurableSet 𝓕) (h𝓕_finite : volume 𝓕 ≠ ⊤) :
    QuotientVolumeEqVolumePreimage
      ((volume ((QuotientGroup.mk' Γ ⁻¹' (K : Set (G ⧸ Γ))) ∩ 𝓕)) • Measure.haarMeasure K) := by
  set c := volume ((QuotientGroup.mk' Γ ⁻¹' (K : Set (G ⧸ Γ))) ∩ 𝓕)
  have c_ne_top : c ≠ ⊤
  · contrapose! h𝓕_finite
    have : volume (↑(QuotientGroup.mk' Γ) ⁻¹' ↑K ∩ 𝓕) ≤ volume 𝓕 :=
      measure_mono (Set.inter_subset_right _ _)
    rw [h𝓕_finite] at this
    exact top_unique this
  set μ := c • haarMeasure K
  have hμK : μ K = c := by simp [Measure.haarMeasure_self]
  haveI : IsMulLeftInvariant μ := isMulLeftInvariant_smul _
  haveI : SigmaFinite μ := by
    clear_value c
    lift c to NNReal using c_ne_top
    exact SMul.sigmaFinite c
  apply IsFundamentalDomain.QuotientVolumeEqVolumePreimage_HaarMeasure (h𝓕 := h𝓕)
    (meas_𝓕 := meas_𝓕) (h𝓕_finite := h𝓕_finite) (meas_V := K.isCompact.measurableSet) (μ := μ)
  · exact K.interior_nonempty
  · exact hμK

/- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ` is
  measure-preserving between appropriate multiples of Haar measure on `G` and `G ⧸ Γ`. -/
theorem MeasurePreserving_QuotientGroup.TestCase2 [Subgroup.Normal Γ]
    [MeasureTheory.Measure.IsHaarMeasure (volume : Measure G)] [T2Space (G ⧸ Γ)]
    [BorelSpace (G ⧸ Γ)] [IsMulRightInvariant (volume : Measure G)] {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain (Subgroup.opposite Γ) 𝓕)
    (meas_𝓕 : MeasurableSet 𝓕) (h𝓕_finite : volume 𝓕 ≠ ⊤) :
    MeasurePreserving (QuotientGroup.mk' Γ) (volume.restrict 𝓕)
      ((volume ((QuotientGroup.mk' Γ ⁻¹' (K : Set (G ⧸ Γ))) ∩ 𝓕)) •
      MeasureTheory.Measure.haarMeasure K) := by
  haveI := IsFundamentalDomain.QuotientVolumeEqVolumePreimage_bubHaarMeasure
    K h𝓕 meas_𝓕 h𝓕_finite
  apply measurePreserving_quotientGroup_mk_of_quotientVolumeEqVolumePreimage h𝓕 meas_𝓕

end QuotientIsHaar
