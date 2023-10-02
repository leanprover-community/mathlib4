/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Algebra.Group.Opposite
import Mathlib.MeasureTheory.Constructions.Polish

#align_import measure_theory.measure.haar.quotient from "leanprover-community/mathlib"@"3b52265189f3fb43aa631edffce5d060fafaf82f"

/-!
# Haar quotient measure

In this file, we consider properties of fundamental domains and measures for the action of a
subgroup `Γ` of a topological group `G` on `G` itself. Let `μ` be a measure on `G ⧸ Γ`.

## Main results

* `MeasureTheory.QuotientVolumeEqVolumePreimage.smulInvariantMeasure_quotient`: If `μ` satisfies
  `QuotientVolumeEqVolumePreimage` relative to a both left- and right-invariant measure on `G`, then
  it is a `G` invariant measure on `G ⧸ Γ`.

The next two results assume that `Γ` is normal, and that `G` is equipped with a left- and
right-invariant measure.

* `MeasureTheory.QuotientVolumeEqVolumePreimage.MulInvariantMeasure_quotient`: If `μ` satisfies
  `QuotientVolumeEqVolumePreimage`, then `μ` is a left-invariant measure.

* `MeasureTheory.LeftInvariantIsQuotientVolumeEqVolumePreimage`: If `μ` is left-invariant, and the
  action of `Γ` on `G` has finite covolume, and `μ` satisfies the right scaling condition, then it
  satisfies `QuotientVolumeEqVolumePreimage`. This is a converse to
  `MeasureTheory.QuotientVolumeEqVolumePreimage.MulInvariantMeasure_quotient`.

The last result assumes that `G` is locally compact, that `Γ` is countable and normal, that its
action on `G` has a fundamental domain, and that `μ` is a finite measure. We also assume that `G` is
equipped with a sigma-finite Haar measure.

* `MeasureTheory.QuotientVolumeEqVolumePreimage.haarMeasure_quotient`: If `μ` satisfies
  `QuotientVolumeEqVolumePreimage`, then it is itself Haar. This is a variant of
  `MeasureTheory.QuotientVolumeEqVolumePreimage.MulInvariantMeasure_quotient`.

Note that a group `G` with Haar measure that is both left and right invariant is called
**unimodular**.
-/

open Set MeasureTheory TopologicalSpace MeasureTheory.Measure

open scoped Pointwise NNReal ENNReal

section

/-- Measurability of the action of the topological group `G` on the left-coset space `G / Γ`. -/
@[to_additive "Measurability of the action of the additive topological group `G` on the left-coset
  space `G / Γ`."]
instance QuotientGroup.measurableSMul {G : Type*} [Group G] {Γ : Subgroup G} [MeasurableSpace G]
    [TopologicalSpace G] [TopologicalGroup G] [BorelSpace G] [BorelSpace (G ⧸ Γ)] :
    MeasurableSMul G (G ⧸ Γ) where
  measurable_const_smul g := Continuous.measurable (continuous_const_smul g)
  measurable_smul_const x := (QuotientGroup.continuous_smul₁ x).measurable
#align quotient_group.has_measurable_smul QuotientGroup.measurableSMul
#align quotient_add_group.has_measurable_vadd QuotientAddGroup.measurableVAdd

end

section smulInvariantMeasure

section additive

variable {G : Type*} [AddGroup G] [MeasureSpace G] [TopologicalSpace G] [TopologicalAddGroup G]
  [BorelSpace G] [PolishSpace G] {Γ : AddSubgroup G} [Countable Γ] [T2Space (G ⧸ Γ)]
  [SecondCountableTopology (G ⧸ Γ)] {μ : Measure (G ⧸ Γ)}
  [AddQuotientVolumeEqVolumePreimage μ]

---- should not need this!!!?
variable [MeasurableVAdd G (G ⧸ Γ)]

local notation "π" => @QuotientAddGroup.mk G _ Γ

/-- If `μ` satisfies `AddQuotientVolumeEqVolumePreimage` relative to a both left- and right-
  invariant measure on `G`, then it is a `G` invariant measure on `G ⧸ Γ`. -/
instance MeasureTheory.AddQuotientVolumeEqVolumePreimage.vaddInvariantMeasure_quotient
    [IsAddLeftInvariant (volume : Measure G)] [IsAddRightInvariant (volume : Measure G)]
    [hasFun : HasAddFundamentalDomain (AddSubgroup.opposite Γ) G] :
    VAddInvariantMeasure G (G ⧸ Γ) μ where
  measure_preimage_vadd g A hA := by
    have meas_π : Measurable π := continuous_quotient_mk'.measurable
    have meas_πA : MeasurableSet (π ⁻¹' A) := measurableSet_preimage meas_π hA
    obtain ⟨𝓕, h𝓕⟩ := hasFun.has_add_fundamental_domain_characterization
    have h𝓕_translate_fundom : IsAddFundamentalDomain (AddSubgroup.opposite Γ) (g +ᵥ 𝓕) volume :=
      h𝓕.vadd_of_comm g
    rw [add_projection_respects_measure h𝓕
      (meas_π (measurableSet_preimage (measurable_const_vadd g) hA)),
      add_projection_respects_measure h𝓕_translate_fundom hA]
    change volume ((π ⁻¹' _) ∩ _) = _
    set π_preA := π ⁻¹' A
    have : π ⁻¹' ((fun x : G ⧸ Γ => g +ᵥ x) ⁻¹' A) = (g + ·) ⁻¹' π_preA := by ext1; simp
    rw [this]
    have : volume ((g + ·) ⁻¹' π_preA ∩ 𝓕) = volume (π_preA ∩ ((-g) + ·) ⁻¹' 𝓕)
    · trans volume ((g + ·) ⁻¹' (π_preA ∩ ((-g) + ·) ⁻¹' 𝓕))
      · rw [preimage_inter]
        congr 2
        simp [Set.preimage]
      rw [measure_preimage_add]
    rw [this, ← preimage_vadd_neg]; rfl

end additive

variable {G : Type*} [Group G] [MeasureSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] [PolishSpace G] {Γ : Subgroup G} [Countable Γ] [T2Space (G ⧸ Γ)]
  [SecondCountableTopology (G ⧸ Γ)] {μ : Measure (G ⧸ Γ)}
  [QuotientVolumeEqVolumePreimage μ]

local notation "π" => @QuotientGroup.mk G _ Γ

/-- If `μ` satisfies `QuotientVolumeEqVolumePreimage` relative to a both left- and right-
  invariant measure on `G`, then it is a `G` invariant measure on `G ⧸ Γ`. -/
instance MeasureTheory.QuotientVolumeEqVolumePreimage.smulInvariantMeasure_quotient
    [IsMulLeftInvariant (volume : Measure G)] [IsMulRightInvariant (volume : Measure G)]
    [hasFun : HasFundamentalDomain (Subgroup.opposite Γ) G] :
    SMulInvariantMeasure G (G ⧸ Γ) μ where
  measure_preimage_smul g A hA := by
    have meas_π : Measurable π := continuous_quotient_mk'.measurable
    have meas_πA : MeasurableSet (π ⁻¹' A) := measurableSet_preimage meas_π hA
    obtain ⟨𝓕, h𝓕⟩ := hasFun.has_fundamental_domain_characterization
    have h𝓕_translate_fundom : IsFundamentalDomain (Subgroup.opposite Γ) (g • 𝓕) volume :=
      h𝓕.smul_of_comm g
    rw [projection_respects_measure h𝓕
      (meas_π (measurableSet_preimage (measurable_const_smul g) hA)),
      projection_respects_measure h𝓕_translate_fundom hA]
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

attribute [to_additive existing]
  MeasureTheory.QuotientVolumeEqVolumePreimage.smulInvariantMeasure_quotient

-- We restate the `SigmaFinite` instance. For some reason, this is needed for typeclass inference
@[to_additive] instance [SigmaFinite (volume : Measure G)]
    [IsMulRightInvariant (volume : Measure G)] [HasFundamentalDomain (Subgroup.opposite Γ) G]
    (μ : Measure (G ⧸ Γ)) [QuotientVolumeEqVolumePreimage μ] : SigmaFinite μ :=
  instSigmaFiniteQuotientOrbitRelInstMeasurableSpaceToMeasurableSpace μ

/-- Given a subgroup `Γ` of a topological group `G` with right-invariant measure `volume`, with a
  measure 'μ' on the quotient `G ⧸ Γ` satisfying `QuotientVolumeEqVolumePreimage`, the restriction
  of `volume` to a fundamental domain is measure-preserving with respect to `μ`. -/
@[to_additive measurePreserving_addQuotientGroup_mk_of_addQuotientVolumeEqVolumePreimage]
theorem measurePreserving_quotientGroup_mk_of_quotientVolumeEqVolumePreimage
    [IsMulRightInvariant (volume : Measure G)] {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain (Subgroup.opposite Γ) 𝓕) (μ : Measure (G ⧸ Γ))
    [QuotientVolumeEqVolumePreimage μ] :
    MeasurePreserving (@QuotientGroup.mk G _ Γ) (volume.restrict 𝓕) μ :=
  h𝓕.measurePreserving_quotient_mk μ

end smulInvariantMeasure

section normal

section additive
variable {G : Type*} [AddGroup G] [MeasureSpace G] [TopologicalSpace G] [TopologicalAddGroup G]
  [BorelSpace G] [PolishSpace G] {Γ : AddSubgroup G} [Countable Γ] [AddSubgroup.Normal Γ]
  [T2Space (G ⧸ Γ)] [SecondCountableTopology (G ⧸ Γ)] {μ : Measure (G ⧸ Γ)}
  [IsAddLeftInvariant (volume : Measure G)] [IsAddRightInvariant (volume : Measure G)]
  [SigmaFinite (volume : Measure G)]

section addInvariantMeasure

-- should not be needed??? Why can't it figure this out?
variable [MeasurableAdd (G ⧸ Γ)] [MeasurableVAdd G (G ⧸ Γ)]

/-- If `μ` on `G ⧸ Γ` satisfies `AddQuotientVolumeEqVolumePreimage` relative to a both left- and
right-invariant measure on `G` and `Γ` is a normal subgroup, then `μ` is a left-invariant measure.-/
instance MeasureTheory.AddQuotientVolumeEqVolumePreimage.addInvariantMeasure_quotient
    [hasFun : HasAddFundamentalDomain (AddSubgroup.opposite Γ) G]
    [AddQuotientVolumeEqVolumePreimage μ] : μ.IsAddLeftInvariant where
  map_add_left_eq_self x := by
    apply Measure.ext
    intro A hA
    obtain ⟨x₁, h⟩ := @Quotient.exists_rep _ (QuotientAddGroup.leftRel Γ) x
    convert measure_preimage_vadd x₁ μ A using 1
    rw [← h, Measure.map_apply (measurable_const_add _) hA]
    rfl

variable [IsAddLeftInvariant μ] [SigmaFinite μ]

--- should not need this!!!
variable [MeasurableAdd₂ (G ⧸ Γ)] [MeasurableNeg (G ⧸ Γ)]

local notation "π" => @QuotientAddGroup.mk G _ Γ

/-- Assume that a measure `μ` is `IsAddLeftInvariant`, that the action of `Γ` on `G` has a
measurable fundamental domain `s` with positive finite volume, and that there is a single measurable
set `V ⊆ G ⧸ Γ` along which the pullback of `μ` and `volume` agree (so the scaling is right). Then
`μ` satisfies `AddQuotientVolumeEqVolumePreimage`. The main tool of the proof is the uniqueness of
left invariant measures, if normalized by a single positive finite-measured set. -/
theorem MeasureTheory.Measure.IsAddLeftInvariant.addQuotientVolumeEqVolumePreimage_of_set
    {s : Set G} (fund_dom_s : IsAddFundamentalDomain (AddSubgroup.opposite Γ) s) {V : Set (G ⧸ Γ)}
    (meas_V : MeasurableSet V) (neZeroV : μ V ≠ 0) (hV : μ V = volume (π ⁻¹' V ∩ s))
    (neTopV : μ V ≠ ⊤) : AddQuotientVolumeEqVolumePreimage μ := by
  apply fund_dom_s.addQuotientVolumeEqVolumePreimage
  intro U meas_U
  let μ' : Measure (G ⧸ Γ) := fund_dom_s.nullMeasurableSet.addQuotientMeasure
    (AddSubgroup.opposite Γ) volume
  haveI has_fund : HasAddFundamentalDomain (AddSubgroup.opposite Γ) G := ⟨⟨s, fund_dom_s⟩⟩
  have : AddQuotientVolumeEqVolumePreimage μ' :=
    fund_dom_s.addQuotientVolumeEqVolumePreimage_addQuotientMeasure
  have : μ'.IsAddLeftInvariant :=
    MeasureTheory.AddQuotientVolumeEqVolumePreimage.addInvariantMeasure_quotient
  suffices : μ = μ'
  · rw [this, NullMeasurableSet.addQuotientMeasure_apply]
    exact meas_U
  · rw [measure_eq_sub_vadd μ' μ meas_V neZeroV neTopV, hV]
    symm
    convert one_smul ENNReal μ
    rw [fund_dom_s.nullMeasurableSet.addQuotientMeasure_apply _ meas_V]
    convert ENNReal.div_self ..
    · exact trans hV.symm neZeroV
    · exact trans hV.symm neTopV

/-- If a measure `μ` is left-invariant and satisfies the right scaling condition, then it
  satisfies `QuotientVolumeEqVolumePreimage`. -/
theorem MeasureTheory.LeftInvariantIsAddQuotientVolumeEqVolumePreimage
    [IsFiniteMeasure μ] [hasFun : HasAddFundamentalDomain (AddSubgroup.opposite Γ) G]
    (h : addCovolume (AddSubgroup.opposite Γ) G = μ univ) :
    AddQuotientVolumeEqVolumePreimage μ := by
  obtain ⟨s, fund_dom_s⟩ := hasFun.has_add_fundamental_domain_characterization
  have finiteCovol : μ univ < ⊤ := measure_lt_top μ univ
  rw [fund_dom_s.covolume_eq_volume] at h
  by_cases meas_s_ne_zero : volume s = 0
  · convert fund_dom_s.AddQuotientVolumeEqVolumePreimage_of_volume_zero meas_s_ne_zero
    rw [← @measure_univ_eq_zero, ←h, meas_s_ne_zero]
  apply IsAddLeftInvariant.addQuotientVolumeEqVolumePreimage_of_set (fund_dom_s := fund_dom_s)
    (meas_V := MeasurableSet.univ)
  · rw [← h]
    exact meas_s_ne_zero
  · rw [← h]
    simp
  · rw [← h]
    convert finiteCovol.ne

end addInvariantMeasure

section addHaarMeasure

variable [SigmaFinite (volume : Measure G)] [IsAddHaarMeasure (volume : Measure G)]
  [IsAddRightInvariant (volume : Measure G)]

---should not be needed???
variable [BorelSpace (G ⧸ Γ)]

local notation "π" => @QuotientAddGroup.mk G _ Γ

/-- If a measure `μ` on the quotient `G ⧸ Γ` of an additive group `G` by a discrete normal subgroup
`Γ` having fundamental domain, satisfies `AddQuotientVolumeEqVolumePreimage` relative to a
standardized choice of Haar measure on `G`, and assuming `μ` is finite, then `μ` is itself Haar.
TODO: Is it possible to drop the assumption that `μ` is finite? -/
instance MeasureTheory.AddQuotientVolumeEqVolumePreimage.addHaarMeasure_quotient
    [LocallyCompactSpace G] [AddQuotientVolumeEqVolumePreimage μ]
    [i : HasAddFundamentalDomain (AddSubgroup.opposite Γ) G] [IsFiniteMeasure μ] :
    IsAddHaarMeasure μ := by
  obtain ⟨K⟩ := PositiveCompacts.nonempty' (α := G)
  let K' : PositiveCompacts (G ⧸ Γ) :=
    K.map π continuous_coinduced_rng (QuotientAddGroup.isOpenMap_coe Γ)
  rw [addHaarMeasure_unique μ K']
  have finiteCovol : addCovolume (AddSubgroup.opposite Γ) G ≠ ⊤ :=
    AddQuotientVolumeEqVolumePreimage.covolume_ne_top (μ := μ)
  obtain ⟨s, fund_dom_s⟩ := i
  rw [fund_dom_s.covolume_eq_volume] at finiteCovol
  rw [add_projection_respects_measure fund_dom_s K'.isCompact.measurableSet]
  apply IsAddHaarMeasure.smul
  · intro h
    haveI i' : IsOpenPosMeasure (volume : Measure G) := inferInstance
    apply IsOpenPosMeasure.open_pos (interior K) (μ := volume) (self := i')
    · exact isOpen_interior
    · exact K.interior_nonempty
    rw [←le_zero_iff, ←fund_dom_s.measure_zero_of_invariant _
      (fun g ↦ QuotientAddGroup.sound _ _ g) h]
    apply measure_mono
    refine interior_subset.trans ?_
    show (K : Set G) ⊆ π ⁻¹' (π '' K)
    exact subset_preimage_image π K
  · show volume (π ⁻¹' (π '' K) ∩ s) ≠ ⊤
    apply ne_of_lt
    refine lt_of_le_of_lt ?_ finiteCovol.lt_top
    apply measure_mono
    exact inter_subset_right _ s

/- Given a normal subgroup `Γ` of a topological additive group `G` with Haar measure `μ`, which is
  also right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
  properly normalized, satisfies `AddQuotientVolumeEqVolumePreimage`. -/
theorem IsAddFundamentalDomain.AddQuotientVolumeEqVolumePreimage_HaarMeasure {𝓕 : Set G}
    (h𝓕 : IsAddFundamentalDomain (AddSubgroup.opposite Γ) 𝓕) [IsAddLeftInvariant μ] [SigmaFinite μ]
    {V : Set (G ⧸ Γ)} (hV : (interior V).Nonempty) (meas_V : MeasurableSet V)
    (hμK : μ V = volume ((π ⁻¹' V) ∩ 𝓕)) (neTopV : μ V ≠ ⊤) :
    AddQuotientVolumeEqVolumePreimage μ := by
  apply IsAddLeftInvariant.addQuotientVolumeEqVolumePreimage_of_set (fund_dom_s := h𝓕)
    (meas_V := meas_V)
  · rw [hμK]
    intro c_eq_zero
    apply IsOpenPosMeasure.open_pos (interior (π ⁻¹' V)) (μ := volume)
    · simp
    · apply Set.Nonempty.mono (preimage_interior_subset_interior_preimage continuous_coinduced_rng)
      apply hV.preimage'
      simp
    · apply measure_mono_null (h := interior_subset)
      apply h𝓕.measure_zero_of_invariant (ht := fun g ↦ QuotientGroup.sound _ _ g)
      exact c_eq_zero
  · exact hμK
  · exact neTopV

variable (K : PositiveCompacts (G ⧸ Γ))

/- Given a normal subgroup `Γ` of a topological additive group `G` with Haar measure `μ`, which is
  also right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
  properly normalized, satisfies `AddQuotientVolumeEqVolumePreimage`. -/
theorem IsAddFundamentalDomain.AddQuotientVolumeEqVolumePreimage_bubHaarMeasure {𝓕 : Set G}
    (h𝓕 : IsAddFundamentalDomain (AddSubgroup.opposite Γ) 𝓕) (h𝓕_finite : volume 𝓕 ≠ ⊤) :
    AddQuotientVolumeEqVolumePreimage
      ((volume ((π ⁻¹' (K : Set (G ⧸ Γ))) ∩ 𝓕)) • addHaarMeasure K) := by
  set c := volume ((π ⁻¹' (K : Set (G ⧸ Γ))) ∩ 𝓕)
  have c_ne_top : c ≠ ⊤
  · contrapose! h𝓕_finite
    have : volume (π ⁻¹' ↑K ∩ 𝓕) ≤ volume 𝓕 := measure_mono (Set.inter_subset_right _ _)
    rw [h𝓕_finite] at this
    exact top_unique this
  set μ := c • addHaarMeasure K
  have hμK : μ K = c := by simp [addHaarMeasure_self]
  haveI : SigmaFinite μ := by
    clear_value c
    lift c to NNReal using c_ne_top
    exact SMul.sigmaFinite c
  apply IsAddFundamentalDomain.AddQuotientVolumeEqVolumePreimage_HaarMeasure (h𝓕 := h𝓕)
    (meas_V := K.isCompact.measurableSet) (μ := μ)
  · exact K.interior_nonempty
  · exact hμK
  · rw [hμK]
    exact c_ne_top

end addHaarMeasure

end additive

variable {G : Type*} [Group G] [MeasureSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] [PolishSpace G]
  {Γ : Subgroup G} [Countable Γ] [Subgroup.Normal Γ]
  [T2Space (G ⧸ Γ)]
  [SecondCountableTopology (G ⧸ Γ)] {μ : Measure (G ⧸ Γ)}

section mulInvariantMeasure

variable
  [IsMulLeftInvariant (volume : Measure G)] [IsMulRightInvariant (volume : Measure G)]
  [SigmaFinite (volume : Measure G)]

/-- If `μ` on `G ⧸ Γ` satisfies `QuotientVolumeEqVolumePreimage` relative to a both left- and right-
  invariant measure on `G` and `Γ` is a normal subgroup, then `μ` is a left-invariant measure.-/
instance MeasureTheory.QuotientVolumeEqVolumePreimage.mulInvariantMeasure_quotient
    [hasFun : HasFundamentalDomain (Subgroup.opposite Γ) G] [QuotientVolumeEqVolumePreimage μ] :
    μ.IsMulLeftInvariant where
  map_mul_left_eq_self x := by
    apply Measure.ext
    intro A hA
    obtain ⟨x₁, h⟩ := @Quotient.exists_rep _ (QuotientGroup.leftRel Γ) x
    convert measure_preimage_smul x₁ μ A using 1
    rw [← h, Measure.map_apply (measurable_const_mul _) hA]
    rfl

attribute [to_additive existing]
  MeasureTheory.QuotientVolumeEqVolumePreimage.mulInvariantMeasure_quotient

variable [IsMulLeftInvariant μ] [SigmaFinite μ]

local notation "π" => @QuotientGroup.mk G _ Γ

/-- Assume that a measure `μ` is `IsMulLeftInvariant`, that the action of `Γ` on `G` has a
measurable fundamental domain `s` with positive finite volume, and that there is a single measurable
set `V ⊆ G ⧸ Γ` along which the pullback of `μ` and `volume` agree (so the scaling is right). Then
`μ` satisfies `QuotientVolumeEqVolumePreimage`. The main tool of the proof is the uniqueness of left
invariant measures, if normalized by a single positive finite-measured set. -/
theorem MeasureTheory.Measure.IsMulLeftInvariant.quotientVolumeEqVolumePreimage_of_set {s : Set G}
    (fund_dom_s : IsFundamentalDomain (Subgroup.opposite Γ) s) {V : Set (G ⧸ Γ)}
    (meas_V : MeasurableSet V) (neZeroV : μ V ≠ 0) (hV : μ V = volume (π ⁻¹' V ∩ s))
    (neTopV : μ V ≠ ⊤) : QuotientVolumeEqVolumePreimage μ := by
  apply fund_dom_s.quotientVolumeEqVolumePreimage
  intro U meas_U
  let μ' : Measure (G ⧸ Γ) := fund_dom_s.nullMeasurableSet.quotientMeasure
    (Subgroup.opposite Γ) volume
  haveI has_fund : HasFundamentalDomain (Subgroup.opposite Γ) G := ⟨⟨s, fund_dom_s⟩⟩
  have : QuotientVolumeEqVolumePreimage μ' :=
    fund_dom_s.quotientVolumeEqVolumePreimage_quotientMeasure
  have : μ'.IsMulLeftInvariant :=
    MeasureTheory.QuotientVolumeEqVolumePreimage.mulInvariantMeasure_quotient
  suffices : μ = μ'
  · rw [this, NullMeasurableSet.quotientMeasure_apply]
    exact meas_U
  · rw [measure_eq_div_smul μ' μ meas_V neZeroV neTopV, hV]
    symm
    convert one_smul ENNReal μ
    rw [fund_dom_s.nullMeasurableSet.quotientMeasure_apply _ meas_V]
    convert ENNReal.div_self ..
    · exact trans hV.symm neZeroV
    · exact trans hV.symm neTopV

attribute [to_additive existing
  MeasureTheory.Measure.IsAddLeftInvariant.addQuotientVolumeEqVolumePreimage_of_set]
  MeasureTheory.Measure.IsMulLeftInvariant.quotientVolumeEqVolumePreimage_of_set

/-- If a measure `μ` is left-invariant and satisfies the right scaling condition, then it
  satisfies `QuotientVolumeEqVolumePreimage`. -/
theorem MeasureTheory.LeftInvariantIsQuotientVolumeEqVolumePreimage [IsFiniteMeasure μ]
    [hasFun : HasFundamentalDomain (Subgroup.opposite Γ) G]
    (h : covolume (Subgroup.opposite Γ) G = μ univ) : QuotientVolumeEqVolumePreimage μ := by
  obtain ⟨s, fund_dom_s⟩ := hasFun.has_fundamental_domain_characterization
  have finiteCovol : μ univ < ⊤ := measure_lt_top μ univ
  rw [fund_dom_s.covolume_eq_volume] at h
  by_cases meas_s_ne_zero : volume s = 0
  · convert fund_dom_s.QuotientVolumeEqVolumePreimage_of_volume_zero meas_s_ne_zero
    rw [← @measure_univ_eq_zero, ←h, meas_s_ne_zero]
  apply IsMulLeftInvariant.quotientVolumeEqVolumePreimage_of_set (fund_dom_s := fund_dom_s)
    (meas_V := MeasurableSet.univ)
  · rw [← h]
    exact meas_s_ne_zero
  · rw [← h]
    simp
  · rw [← h]
    convert finiteCovol.ne

attribute [to_additive existing MeasureTheory.LeftInvariantIsAddQuotientVolumeEqVolumePreimage]
  MeasureTheory.LeftInvariantIsQuotientVolumeEqVolumePreimage

end mulInvariantMeasure

section haarMeasure

variable [SigmaFinite (volume : Measure G)] [IsHaarMeasure (volume : Measure G)]
  [IsMulRightInvariant (volume : Measure G)]

local notation "π" => @QuotientGroup.mk G _ Γ

/-- If a measure `μ` on the quotient `G ⧸ Γ` of a group `G` by a discrete normal subgroup `Γ` having
fundamental domain, satisfies `QuotientVolumeEqVolumePreimage` relative to a standardized choice of
Haar measure on `G`, and assuming `μ` is finite, then `μ` is itself Haar.
TODO: Is it possible to drop the assumption that `μ` is finite? -/
instance MeasureTheory.QuotientVolumeEqVolumePreimage.haarMeasure_quotient [LocallyCompactSpace G]
    [QuotientVolumeEqVolumePreimage μ] [i : HasFundamentalDomain (Subgroup.opposite Γ) G]
    [IsFiniteMeasure μ] : IsHaarMeasure μ := by
  obtain ⟨K⟩ := PositiveCompacts.nonempty' (α := G)
  let K' : PositiveCompacts (G ⧸ Γ) :=
    K.map π continuous_coinduced_rng (QuotientGroup.isOpenMap_coe Γ)
  rw [haarMeasure_unique μ K']
  have finiteCovol : covolume (Subgroup.opposite Γ) G ≠ ⊤ :=
    QuotientVolumeEqVolumePreimage.covolume_ne_top (μ := μ)
  obtain ⟨s, fund_dom_s⟩ := i
  rw [fund_dom_s.covolume_eq_volume] at finiteCovol
  rw [projection_respects_measure fund_dom_s K'.isCompact.measurableSet]
  apply IsHaarMeasure.smul
  · intro h
    haveI i' : IsOpenPosMeasure (volume : Measure G) := inferInstance
    apply IsOpenPosMeasure.open_pos (interior K) (μ := volume) (self := i')
    · exact isOpen_interior
    · exact K.interior_nonempty
    rw [←le_zero_iff, ←fund_dom_s.measure_zero_of_invariant _ (fun g ↦ QuotientGroup.sound _ _ g) h]
    apply measure_mono
    refine interior_subset.trans ?_
    show (K : Set G) ⊆ π ⁻¹' (π '' K)
    exact subset_preimage_image π K
  · show volume (π ⁻¹' (π '' K) ∩ s) ≠ ⊤
    apply ne_of_lt
    refine lt_of_le_of_lt ?_ finiteCovol.lt_top
    apply measure_mono
    exact inter_subset_right _ s

attribute [to_additive existing]
  MeasureTheory.QuotientVolumeEqVolumePreimage.haarMeasure_quotient

/- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
  properly normalized, satisfies `QuotientVolumeEqVolumePreimage`. -/
theorem IsFundamentalDomain.QuotientVolumeEqVolumePreimage_HaarMeasure {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain (Subgroup.opposite Γ) 𝓕) [IsMulLeftInvariant μ] [SigmaFinite μ]
    {V : Set (G ⧸ Γ)} (hV : (interior V).Nonempty) (meas_V : MeasurableSet V)
    (hμK : μ V = volume ((π ⁻¹' V) ∩ 𝓕)) (neTopV : μ V ≠ ⊤) :
    QuotientVolumeEqVolumePreimage μ := by
  apply IsMulLeftInvariant.quotientVolumeEqVolumePreimage_of_set (fund_dom_s := h𝓕)
    (meas_V := meas_V)
  · rw [hμK]
    intro c_eq_zero
    apply IsOpenPosMeasure.open_pos (interior (π ⁻¹' V)) (μ := volume)
    · simp
    · apply Set.Nonempty.mono (preimage_interior_subset_interior_preimage continuous_coinduced_rng)
      apply hV.preimage'
      simp
    · apply measure_mono_null (h := interior_subset)
      apply h𝓕.measure_zero_of_invariant (ht := fun g ↦ QuotientGroup.sound _ _ g)
      exact c_eq_zero
  · exact hμK
  · exact neTopV

attribute [to_additive existing
  IsAddFundamentalDomain.AddQuotientVolumeEqVolumePreimage_HaarMeasure]
  IsFundamentalDomain.QuotientVolumeEqVolumePreimage_HaarMeasure

variable (K : PositiveCompacts (G ⧸ Γ))

/- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
  properly normalized, satisfies `QuotientVolumeEqVolumePreimage`. -/
theorem IsFundamentalDomain.QuotientVolumeEqVolumePreimage_bubHaarMeasure {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain (Subgroup.opposite Γ) 𝓕) (h𝓕_finite : volume 𝓕 ≠ ⊤) :
    QuotientVolumeEqVolumePreimage
      ((volume ((π ⁻¹' (K : Set (G ⧸ Γ))) ∩ 𝓕)) • haarMeasure K) := by
  set c := volume ((π ⁻¹' (K : Set (G ⧸ Γ))) ∩ 𝓕)
  have c_ne_top : c ≠ ⊤
  · contrapose! h𝓕_finite
    have : volume (π ⁻¹' ↑K ∩ 𝓕) ≤ volume 𝓕 := measure_mono (Set.inter_subset_right _ _)
    rw [h𝓕_finite] at this
    exact top_unique this
  set μ := c • haarMeasure K
  have hμK : μ K = c := by simp [haarMeasure_self]
  haveI : SigmaFinite μ := by
    clear_value c
    lift c to NNReal using c_ne_top
    exact SMul.sigmaFinite c
  apply IsFundamentalDomain.QuotientVolumeEqVolumePreimage_HaarMeasure (h𝓕 := h𝓕)
    (meas_V := K.isCompact.measurableSet) (μ := μ)
  · exact K.interior_nonempty
  · exact hμK
  · rw [hμK]
    exact c_ne_top

attribute [to_additive existing
  IsAddFundamentalDomain.AddQuotientVolumeEqVolumePreimage_bubHaarMeasure]
  IsFundamentalDomain.QuotientVolumeEqVolumePreimage_bubHaarMeasure

end haarMeasure

end normal
