/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Haar quotient measure

In this file, we consider properties of fundamental domains and measures for the action of a
subgroup `Γ` of a topological group `G` on `G` itself. Let `μ` be a measure on `G ⧸ Γ`.

## Main results

* `MeasureTheory.QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient`: If `μ` satisfies
  `QuotientMeasureEqMeasurePreimage` relative to a both left- and right-invariant measure on `G`,
  then it is a `G` invariant measure on `G ⧸ Γ`.

The next two results assume that `Γ` is normal, and that `G` is equipped with a left- and
right-invariant measure.

* `MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient`: If `μ` satisfies
  `QuotientMeasureEqMeasurePreimage`, then `μ` is a left-invariant measure.

* `MeasureTheory.leftInvariantIsQuotientMeasureEqMeasurePreimage`: If `μ` is left-invariant, and
  the action of `Γ` on `G` has finite covolume, and `μ` satisfies the right scaling condition, then
  it satisfies `QuotientMeasureEqMeasurePreimage`. This is a converse to
  `MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient`.

The last result assumes that `G` is locally compact, that `Γ` is countable and normal, that its
action on `G` has a fundamental domain, and that `μ` is a finite measure. We also assume that `G`
is equipped with a sigma-finite Haar measure.

* `MeasureTheory.QuotientMeasureEqMeasurePreimage.haarMeasure_quotient`: If `μ` satisfies
  `QuotientMeasureEqMeasurePreimage`, then it is itself Haar. This is a variant of
  `MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient`.

Note that a group `G` with Haar measure that is both left and right invariant is called
**unimodular**.
-/

@[expose] public section

open Set MeasureTheory TopologicalSpace MeasureTheory.Measure

open scoped Pointwise NNReal ENNReal

section

/-- Measurability of the action of the topological group `G` on the left-coset space `G / Γ`. -/
@[to_additive /-- Measurability of the action of the additive topological group `G` on the
  left-coset space `G / Γ`. -/]
instance QuotientGroup.measurableSMul {G : Type*} [Group G] {Γ : Subgroup G} [MeasurableSpace G]
    [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [BorelSpace (G ⧸ Γ)] :
    MeasurableSMul G (G ⧸ Γ) where
  measurable_const_smul g := (continuous_const_smul g).measurable
  measurable_smul_const _ := (continuous_id.smul continuous_const).measurable

end

section smulInvariantMeasure

variable {G : Type*} [Group G] [MeasurableSpace G] (ν : Measure G) {Γ : Subgroup G}
  {μ : Measure (G ⧸ Γ)}
  [QuotientMeasureEqMeasurePreimage ν μ]

/-- Given a subgroup `Γ` of a topological group `G` with measure `ν`, and a measure 'μ' on the
  quotient `G ⧸ Γ` satisfying `QuotientMeasureEqMeasurePreimage`, the restriction
  of `ν` to a fundamental domain is measure-preserving with respect to `μ`. -/
@[to_additive]
theorem measurePreserving_quotientGroup_mk_of_QuotientMeasureEqMeasurePreimage
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ.op 𝓕 ν) (μ : Measure (G ⧸ Γ))
    [QuotientMeasureEqMeasurePreimage ν μ] :
    MeasurePreserving (@QuotientGroup.mk G _ Γ) (ν.restrict 𝓕) μ :=
  h𝓕.measurePreserving_quotient_mk μ

local notation "π" => @QuotientGroup.mk G _ Γ

variable [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [PolishSpace G]
  [T2Space (G ⧸ Γ)] [SecondCountableTopology (G ⧸ Γ)]

/-- If `μ` satisfies `QuotientMeasureEqMeasurePreimage` relative to a both left- and right-
  invariant measure `ν` on `G`, then it is a `G` invariant measure on `G ⧸ Γ`. -/
@[to_additive]
lemma MeasureTheory.QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient
    [IsMulLeftInvariant ν] [hasFun : HasFundamentalDomain Γ.op G ν] :
    SMulInvariantMeasure G (G ⧸ Γ) μ where
  measure_preimage_smul g A hA := by
    have meas_π : Measurable π := continuous_quotient_mk'.measurable
    obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
    have h𝓕_translate_fundom : IsFundamentalDomain Γ.op (g • 𝓕) ν := h𝓕.smul_of_comm g
    -- TODO: why `rw` fails with both of these rewrites?
    erw [h𝓕.projection_respects_measure_apply (μ := μ)
      (meas_π (measurableSet_preimage (measurable_const_smul g) hA)),
      h𝓕_translate_fundom.projection_respects_measure_apply (μ := μ) hA]
    change ν ((π ⁻¹' _) ∩ _) = ν ((π ⁻¹' _) ∩ _)
    set π_preA := π ⁻¹' A
    have : π ⁻¹' ((fun x : G ⧸ Γ => g • x) ⁻¹' A) = (g * ·) ⁻¹' π_preA := by ext1; simp [π_preA]
    rw [this]
    have : ν ((g * ·) ⁻¹' π_preA ∩ 𝓕) = ν (π_preA ∩ (g⁻¹ * ·) ⁻¹' 𝓕) := by
      trans ν ((g * ·) ⁻¹' (π_preA ∩ (g⁻¹ * ·) ⁻¹' 𝓕))
      · rw [preimage_inter]
        congr 2
        simp [Set.preimage]
      rw [measure_preimage_mul]
    rw [this, ← preimage_smul_inv]; rfl

end smulInvariantMeasure

section normal

variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [PolishSpace G] {Γ : Subgroup G} [Subgroup.Normal Γ]
  [T2Space (G ⧸ Γ)] [SecondCountableTopology (G ⧸ Γ)] {μ : Measure (G ⧸ Γ)}

section mulInvariantMeasure

variable (ν : Measure G) [IsMulLeftInvariant ν]

/-- If `μ` on `G ⧸ Γ` satisfies `QuotientMeasureEqMeasurePreimage` relative to a both left- and
  right-invariant measure on `G` and `Γ` is a normal subgroup, then `μ` is a left-invariant
  measure. -/
@[to_additive /-- If `μ` on `G ⧸ Γ` satisfies `AddQuotientMeasureEqMeasurePreimage` relative to a
  both left- and right-invariant measure on `G` and `Γ` is a normal subgroup, then `μ` is a
  left-invariant measure. -/]
lemma MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient
    [hasFun : HasFundamentalDomain Γ.op G ν] [QuotientMeasureEqMeasurePreimage ν μ] :
    μ.IsMulLeftInvariant where
  map_mul_left_eq_self x := by
    ext A hA
    obtain ⟨x₁, h⟩ := @Quotient.exists_rep _ (QuotientGroup.leftRel Γ) x
    convert measure_preimage_smul μ x₁ A using 1
    · rw [← h, Measure.map_apply (measurable_const_mul _) hA]
      simp [← MulAction.Quotient.coe_smul_out, ← Quotient.mk''_eq_mk]
    exact smulInvariantMeasure_quotient ν

variable [Countable Γ] [IsMulRightInvariant ν] [SigmaFinite ν]
  [IsMulLeftInvariant μ] [SigmaFinite μ]

local notation "π" => @QuotientGroup.mk G _ Γ

/-- Assume that a measure `μ` is `IsMulLeftInvariant`, that the action of `Γ` on `G` has a
measurable fundamental domain `s` with positive finite volume, and that there is a single measurable
set `V ⊆ G ⧸ Γ` along which the pullback of `μ` and `ν` agree (so the scaling is right). Then
`μ` satisfies `QuotientMeasureEqMeasurePreimage`. The main tool of the proof is the uniqueness of
left invariant measures, if normalized by a single positive finite-measured set. -/
@[to_additive
/-- Assume that a measure `μ` is `IsAddLeftInvariant`, that the action of `Γ` on `G` has a
measurable fundamental domain `s` with positive finite volume, and that there is a single measurable
set `V ⊆ G ⧸ Γ` along which the pullback of `μ` and `ν` agree (so the scaling is right). Then
`μ` satisfies `AddQuotientMeasureEqMeasurePreimage`. The main tool of the proof is the uniqueness of
left invariant measures, if normalized by a single positive finite-measured set. -/]
theorem MeasureTheory.Measure.IsMulLeftInvariant.quotientMeasureEqMeasurePreimage_of_set {s : Set G}
    (fund_dom_s : IsFundamentalDomain Γ.op s ν) {V : Set (G ⧸ Γ)}
    (meas_V : MeasurableSet V) (neZeroV : μ V ≠ 0) (hV : μ V = ν (π ⁻¹' V ∩ s))
    (neTopV : μ V ≠ ⊤) : QuotientMeasureEqMeasurePreimage ν μ := by
  apply fund_dom_s.quotientMeasureEqMeasurePreimage
  ext U _
  have meas_π : Measurable (QuotientGroup.mk : G → G ⧸ Γ) := continuous_quotient_mk'.measurable
  let μ' : Measure (G ⧸ Γ) := (ν.restrict s).map π
  haveI has_fund : HasFundamentalDomain Γ.op G ν := ⟨⟨s, fund_dom_s⟩⟩
  have i : QuotientMeasureEqMeasurePreimage ν μ' :=
    fund_dom_s.quotientMeasureEqMeasurePreimage_quotientMeasure
  have : μ'.IsMulLeftInvariant :=
    MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient ν
  suffices μ = μ' by
    rw [this]
    rfl
  have : SigmaFinite μ' := i.sigmaFiniteQuotient
  rw [measure_eq_div_smul μ' μ neZeroV neTopV, hV]
  symm
  suffices (μ' V / ν (QuotientGroup.mk ⁻¹' V ∩ s)) = 1 by rw [this, one_smul]
  rw [Measure.map_apply meas_π meas_V, Measure.restrict_apply]
  · convert ENNReal.div_self ..
    · exact trans hV.symm neZeroV
    · exact trans hV.symm neTopV
  exact measurableSet_quotient.mp meas_V

/-- If a measure `μ` is left-invariant and satisfies the right scaling condition, then it
  satisfies `QuotientMeasureEqMeasurePreimage`. -/
@[to_additive /-- If a measure `μ` is
left-invariant and satisfies the right scaling condition, then it satisfies
`AddQuotientMeasureEqMeasurePreimage`. -/]
theorem MeasureTheory.leftInvariantIsQuotientMeasureEqMeasurePreimage [IsFiniteMeasure μ]
    [hasFun : HasFundamentalDomain Γ.op G ν]
    (h : covolume Γ.op G ν = μ univ) : QuotientMeasureEqMeasurePreimage ν μ := by
  obtain ⟨s, fund_dom_s⟩ := hasFun.ExistsIsFundamentalDomain
  have finiteCovol : μ univ < ⊤ := measure_lt_top μ univ
  rw [fund_dom_s.covolume_eq_volume] at h
  by_cases meas_s_ne_zero : ν s = 0
  · convert fund_dom_s.quotientMeasureEqMeasurePreimage_of_zero meas_s_ne_zero
    rw [← @measure_univ_eq_zero, ← h, meas_s_ne_zero]
  apply IsMulLeftInvariant.quotientMeasureEqMeasurePreimage_of_set (fund_dom_s := fund_dom_s)
    (meas_V := MeasurableSet.univ)
  · rw [← h]
    exact meas_s_ne_zero
  · rw [← h]
    simp
  · rw [← h]
    convert finiteCovol.ne

end mulInvariantMeasure

section haarMeasure

variable [Countable Γ] (ν : Measure G) [IsHaarMeasure ν] [IsMulRightInvariant ν]

local notation "π" => @QuotientGroup.mk G _ Γ

/-- If a measure `μ` on the quotient `G ⧸ Γ` of a group `G` by a discrete normal subgroup `Γ` having
fundamental domain, satisfies `QuotientMeasureEqMeasurePreimage` relative to a standardized choice
of Haar measure on `G`, and assuming `μ` is finite, then `μ` is itself Haar.
TODO: Is it possible to drop the assumption that `μ` is finite? -/
@[to_additive /-- If a measure `μ` on the quotient `G ⧸ Γ` of an additive group `G` by a discrete
normal subgroup `Γ` having fundamental domain, satisfies `AddQuotientMeasureEqMeasurePreimage`
relative to a standardized choice of Haar measure on `G`, and assuming `μ` is finite, then `μ` is
itself Haar. -/]
theorem MeasureTheory.QuotientMeasureEqMeasurePreimage.haarMeasure_quotient [LocallyCompactSpace G]
    [QuotientMeasureEqMeasurePreimage ν μ] [i : HasFundamentalDomain Γ.op G ν]
    [IsFiniteMeasure μ] : IsHaarMeasure μ := by
  obtain ⟨K⟩ := PositiveCompacts.nonempty' (α := G)
  let K' : PositiveCompacts (G ⧸ Γ) :=
    K.map π QuotientGroup.continuous_mk QuotientGroup.isOpenMap_coe
  haveI : IsMulLeftInvariant μ :=
    MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient ν
  rw [haarMeasure_unique μ K']
  have finiteCovol : covolume Γ.op G ν ≠ ⊤ :=
    ne_top_of_lt <| QuotientMeasureEqMeasurePreimage.covolume_ne_top μ (ν := ν)
  obtain ⟨s, fund_dom_s⟩ := i
  rw [fund_dom_s.covolume_eq_volume] at finiteCovol
  -- TODO: why `rw` fails?
  erw [fund_dom_s.projection_respects_measure_apply μ K'.isCompact.measurableSet]
  apply IsHaarMeasure.smul
  · intro h
    have i' : IsOpenPosMeasure (ν : Measure G) := inferInstance
    apply IsOpenPosMeasure.open_pos (interior K) (μ := ν) (self := i')
    · exact isOpen_interior
    · exact K.interior_nonempty
    refine measure_mono_null (interior_subset.trans ?_) <|
      fund_dom_s.measure_zero_of_invariant _ (fun g ↦ QuotientGroup.sound _ _ g) h
    rw [QuotientGroup.coe_mk']
    change (K : Set G) ⊆ π ⁻¹' (π '' K)
    exact subset_preimage_image π K
  · change ν (π ⁻¹' (π '' K) ∩ s) ≠ ⊤
    apply ne_of_lt
    refine lt_of_le_of_lt ?_ finiteCovol.lt_top
    apply measure_mono
    exact inter_subset_right

variable [SigmaFinite ν]

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
  properly normalized, satisfies `QuotientMeasureEqMeasurePreimage`. -/
@[to_additive /-- Given a normal
subgroup `Γ` of an additive topological group `G` with Haar measure `μ`, which is also
right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
properly normalized, satisfies `AddQuotientMeasureEqMeasurePreimage`. -/]
theorem IsFundamentalDomain.QuotientMeasureEqMeasurePreimage_HaarMeasure {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ.op 𝓕 ν) [IsMulLeftInvariant μ] [SigmaFinite μ]
    {V : Set (G ⧸ Γ)} (hV : (interior V).Nonempty) (meas_V : MeasurableSet V)
    (hμK : μ V = ν ((π ⁻¹' V) ∩ 𝓕)) (neTopV : μ V ≠ ⊤) :
    QuotientMeasureEqMeasurePreimage ν μ := by
  apply IsMulLeftInvariant.quotientMeasureEqMeasurePreimage_of_set (fund_dom_s := h𝓕)
    (meas_V := meas_V)
  · rw [hμK]
    intro c_eq_zero
    apply IsOpenPosMeasure.open_pos (interior (π ⁻¹' V)) (μ := ν)
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

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
  properly normalized, satisfies `QuotientMeasureEqMeasurePreimage`. -/
@[to_additive /-- Given a
normal subgroup `Γ` of an additive topological group `G` with Haar measure `μ`, which is also
right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
properly normalized, satisfies `AddQuotientMeasureEqMeasurePreimage`. -/]
theorem IsFundamentalDomain.QuotientMeasureEqMeasurePreimage_smulHaarMeasure {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ.op 𝓕 ν) (h𝓕_finite : ν 𝓕 ≠ ⊤) :
    QuotientMeasureEqMeasurePreimage ν
      ((ν ((π ⁻¹' (K : Set (G ⧸ Γ))) ∩ 𝓕)) • haarMeasure K) := by
  set c := ν ((π ⁻¹' (K : Set (G ⧸ Γ))) ∩ 𝓕)
  have c_ne_top : c ≠ ∞ := by
    contrapose! h𝓕_finite
    have : c ≤ ν 𝓕 := measure_mono (Set.inter_subset_right)
    rw [h𝓕_finite] at this
    exact top_unique this
  set μ := c • haarMeasure K
  have hμK : μ K = c := by simp [μ, haarMeasure_self]
  haveI : SigmaFinite μ := by
    clear_value c
    lift c to NNReal using c_ne_top
    exact SMul.sigmaFinite c
  apply IsFundamentalDomain.QuotientMeasureEqMeasurePreimage_HaarMeasure (h𝓕 := h𝓕)
    (meas_V := K.isCompact.measurableSet) (μ := μ)
  · exact K.interior_nonempty
  · exact hμK
  · rw [hμK]
    exact c_ne_top

end haarMeasure

end normal

section UnfoldingTrick

variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] {μ : Measure G} {Γ : Subgroup G}

variable {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ.op 𝓕 μ)
include h𝓕

variable [Countable Γ] [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

local notation "μ_𝓕" => Measure.map (@QuotientGroup.mk G _ Γ) (μ.restrict 𝓕)

/-- The `essSup` of a function `g` on the quotient space `G ⧸ Γ` with respect to the pushforward
  of the restriction, `μ_𝓕`, of a right-invariant measure `μ` to a fundamental domain `𝓕`, is the
  same as the `essSup` of `g`'s lift to the universal cover `G` with respect to `μ`. -/
@[to_additive /-- The `essSup` of a function `g` on the additive quotient space `G ⧸ Γ` with respect
  to the pushforward of the restriction, `μ_𝓕`, of a right-invariant measure `μ` to a fundamental
  domain `𝓕`, is the same as the `essSup` of `g`'s lift to the universal cover `G` with respect
  to `μ`. -/]
lemma essSup_comp_quotientGroup_mk [μ.IsMulRightInvariant] {g : G ⧸ Γ → ℝ≥0∞}
    (g_ae_measurable : AEMeasurable g μ_𝓕) : essSup g μ_𝓕 = essSup (fun (x : G) ↦ g x) μ := by
  have hπ : Measurable (QuotientGroup.mk : G → G ⧸ Γ) := continuous_quotient_mk'.measurable
  rw [essSup_map_measure g_ae_measurable hπ.aemeasurable]
  refine h𝓕.essSup_measure_restrict ?_
  intro ⟨γ, hγ⟩ x
  dsimp
  congr 1
  exact QuotientGroup.mk_mul_of_mem x hγ

/-- Given a quotient space `G ⧸ Γ` where `Γ` is `Countable`, and the restriction,
  `μ_𝓕`, of a right-invariant measure `μ` on `G` to a fundamental domain `𝓕`, a set
  in the quotient which has `μ_𝓕`-measure zero, also has measure zero under the
  folding of `μ` under the quotient. Note that, if `Γ` is infinite, then the folded map
  will take the value `∞` on any open set in the quotient! -/
@[to_additive /-- Given an additive quotient space `G ⧸ Γ` where `Γ` is `Countable`, and the
  restriction, `μ_𝓕`, of a right-invariant measure `μ` on `G` to a fundamental domain `𝓕`, a set
  in the quotient which has `μ_𝓕`-measure zero, also has measure zero under the
  folding of `μ` under the quotient. Note that, if `Γ` is infinite, then the folded map
  will take the value `∞` on any open set in the quotient! -/]
lemma _root_.MeasureTheory.IsFundamentalDomain.absolutelyContinuous_map
    [μ.IsMulRightInvariant] :
    map (QuotientGroup.mk : G → G ⧸ Γ) μ ≪ map (QuotientGroup.mk : G → G ⧸ Γ) (μ.restrict 𝓕) := by
  set π : G → G ⧸ Γ := QuotientGroup.mk
  have meas_π : Measurable π := continuous_quotient_mk'.measurable
  apply AbsolutelyContinuous.mk
  intro s s_meas hs
  rw [map_apply meas_π s_meas] at hs ⊢
  rw [Measure.restrict_apply] at hs
  · apply h𝓕.measure_zero_of_invariant _ _ hs
    intro γ
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem, mem_preimage, mem_preimage]
    congr! 1
    convert QuotientGroup.mk_mul_of_mem g (γ⁻¹).2 using 1
  exact MeasurableSet.preimage s_meas meas_π

attribute [-instance] Quotient.instMeasurableSpace

/-- This is a simple version of the **Unfolding Trick**: Given a subgroup `Γ` of a group `G`, the
  integral of a function `f` on `G` with respect to a right-invariant measure `μ` is equal to the
  integral over the quotient `G ⧸ Γ` of the automorphization of `f`. -/
@[to_additive /-- This is a simple version of the **Unfolding Trick**: Given a subgroup `Γ` of an
  additive group `G`, the integral of a function `f` on `G` with respect to a right-invariant
  measure `μ` is equal to the integral over the quotient `G ⧸ Γ` of the automorphization of `f`. -/]
lemma QuotientGroup.integral_eq_integral_automorphize {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [μ.IsMulRightInvariant] {f : G → E}
    (hf₁ : Integrable f μ) (hf₂ : AEStronglyMeasurable (automorphize f) μ_𝓕) :
    ∫ x : G, f x ∂μ = ∫ x : G ⧸ Γ, automorphize f x ∂μ_𝓕 := by
  calc ∫ x : G, f x ∂μ = ∑' γ : Γ.op, ∫ x in 𝓕, f (γ • x) ∂μ :=
    h𝓕.integral_eq_tsum'' f hf₁
    _ = ∫ x in 𝓕, ∑' γ : Γ.op, f (γ • x) ∂μ := ?_
    _ = ∫ x : G ⧸ Γ, automorphize f x ∂μ_𝓕 :=
      (integral_map continuous_quotient_mk'.aemeasurable hf₂).symm
  rw [integral_tsum]
  · exact fun i ↦ (hf₁.1.comp_quasiMeasurePreserving
      (measurePreserving_smul i μ).quasiMeasurePreserving).restrict
  · rw [← h𝓕.lintegral_eq_tsum'' (‖f ·‖ₑ)]
    exact ne_of_lt hf₁.2

-- we can't use `to_additive`, because it tries to translate `*` into `+`
/-- This is the **Unfolding Trick**: Given a subgroup `Γ` of a group `G`, the integral of a
  function `f` on `G` times the lift to `G` of a function `g` on the quotient `G ⧸ Γ` with respect
  to a right-invariant measure `μ` on `G`, is equal to the integral over the quotient of the
  automorphization of `f` times `g`. -/
lemma QuotientGroup.integral_mul_eq_integral_automorphize_mul {K : Type*} [NormedField K]
    [NormedSpace ℝ K] [μ.IsMulRightInvariant] {f : G → K}
    (f_ℒ_1 : Integrable f μ) {g : G ⧸ Γ → K} (hg : AEStronglyMeasurable g μ_𝓕)
    (g_ℒ_infinity : essSup (fun x ↦ ↑‖g x‖ₑ) μ_𝓕 ≠ ∞)
    (F_ae_measurable : AEStronglyMeasurable (QuotientGroup.automorphize f) μ_𝓕) :
    ∫ x : G, g (x : G ⧸ Γ) * (f x) ∂μ
      = ∫ x : G ⧸ Γ, g x * (QuotientGroup.automorphize f x) ∂μ_𝓕 := by
  let π : G → G ⧸ Γ := QuotientGroup.mk
  have meas_π : Measurable π := continuous_quotient_mk'.measurable
  have H₀ : QuotientGroup.automorphize ((g ∘ π) * f) = g * (QuotientGroup.automorphize f) := by
    exact QuotientGroup.automorphize_smul_left f g
  calc ∫ (x : G), g (π x) * (f x) ∂μ =
        ∫ (x : G ⧸ Γ), QuotientGroup.automorphize ((g ∘ π) * f) x ∂μ_𝓕 := ?_
    _ = ∫ (x : G ⧸ Γ), g x * (QuotientGroup.automorphize f x) ∂μ_𝓕 := by simp [H₀]
  have H₁ : Integrable ((g ∘ π) * f) μ := by
    have : AEStronglyMeasurable (fun (x : G) ↦ g (x : (G ⧸ Γ))) μ :=
      (hg.mono_ac h𝓕.absolutelyContinuous_map).comp_measurable meas_π
    refine Integrable.essSup_smul f_ℒ_1 this ?_
    have hg' : AEStronglyMeasurable (‖g ·‖ₑ) μ_𝓕 := continuous_enorm.comp_aestronglyMeasurable hg
    rw [← essSup_comp_quotientGroup_mk h𝓕 hg'.aemeasurable]
    exact g_ℒ_infinity
  have H₂ : AEStronglyMeasurable (QuotientGroup.automorphize ((g ∘ π) * f)) μ_𝓕 := by
    simp_rw [H₀]
    exact hg.mul F_ae_measurable
  apply QuotientGroup.integral_eq_integral_automorphize h𝓕 H₁ H₂

end UnfoldingTrick

section

variable {G' : Type*} [AddGroup G'] [MeasurableSpace G'] [TopologicalSpace G']
  [IsTopologicalAddGroup G'] [BorelSpace G'] {μ' : Measure G'} {Γ' : AddSubgroup G'}
  {𝓕' : Set G'} (h𝓕 : IsAddFundamentalDomain Γ'.op 𝓕' μ')
  [Countable Γ'] [MeasurableSpace (G' ⧸ Γ')] [BorelSpace (G' ⧸ Γ')]
include h𝓕

local notation "μ_𝓕" => Measure.map (@QuotientAddGroup.mk G' _ Γ') (μ'.restrict 𝓕')

/-- This is the **Unfolding Trick**: Given an additive subgroup `Γ'` of an additive group `G'`, the
  integral of a function `f` on `G'` times the lift to `G'` of a function `g` on the quotient
  `G' ⧸ Γ'` with respect to a right-invariant measure `μ` on `G'`, is equal to the integral over
  the quotient of the automorphization of `f` times `g`. -/
lemma QuotientAddGroup.integral_mul_eq_integral_automorphize_mul {K : Type*} [NormedField K]
    [NormedSpace ℝ K] [μ'.IsAddRightInvariant] {f : G' → K}
    (f_ℒ_1 : Integrable f μ') {g : G' ⧸ Γ' → K} (hg : AEStronglyMeasurable g μ_𝓕)
    (g_ℒ_infinity : essSup (‖g ·‖ₑ) μ_𝓕 ≠ ∞)
    (F_ae_measurable : AEStronglyMeasurable (QuotientAddGroup.automorphize f) μ_𝓕) :
    ∫ x : G', g (x : G' ⧸ Γ') * (f x) ∂μ'
      = ∫ x : G' ⧸ Γ', g x * (QuotientAddGroup.automorphize f x) ∂μ_𝓕 := by
  let π : G' → G' ⧸ Γ' := QuotientAddGroup.mk
  have meas_π : Measurable π := continuous_quotient_mk'.measurable
  have H₀ : QuotientAddGroup.automorphize ((g ∘ π) * f) = g * (QuotientAddGroup.automorphize f) :=
    by exact QuotientAddGroup.automorphize_smul_left f g
  calc ∫ (x : G'), g (π x) * f x ∂μ' =
    ∫ (x : G' ⧸ Γ'), QuotientAddGroup.automorphize ((g ∘ π) * f) x ∂μ_𝓕 := ?_
    _ = ∫ (x : G' ⧸ Γ'), g x * (QuotientAddGroup.automorphize f x) ∂μ_𝓕 := by simp [H₀]
  have H₁ : Integrable ((g ∘ π) * f) μ' := by
    have : AEStronglyMeasurable (fun (x : G') ↦ g (x : (G' ⧸ Γ'))) μ' :=
      (hg.mono_ac h𝓕.absolutelyContinuous_map).comp_measurable meas_π
    refine Integrable.essSup_smul f_ℒ_1 this ?_
    have hg' : AEStronglyMeasurable (‖g ·‖ₑ) μ_𝓕 := continuous_enorm.comp_aestronglyMeasurable hg
    rw [← essSup_comp_quotientAddGroup_mk h𝓕 hg'.aemeasurable]
    exact g_ℒ_infinity
  have H₂ : AEStronglyMeasurable (QuotientAddGroup.automorphize ((g ∘ π) * f)) μ_𝓕 := by
    simp_rw [H₀]
    exact hg.mul F_ae_measurable
  apply QuotientAddGroup.integral_eq_integral_automorphize h𝓕 H₁ H₂

end

structure TopologicalGroup.IsSES {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] (φ : A →* B) (ψ : B →* C) where
  isClosedEmbedding : Topology.IsClosedEmbedding φ
  isOpenQuotientMap : IsOpenQuotientMap ψ
  exact : φ.range = ψ.ker

variable {A B C E : Type*} [Group A] [Group B] [Group C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [BorelSpace A] [BorelSpace B] [BorelSpace C]
  [LocallyCompactSpace B]
  (φ : A →* B) (ψ : B →* C) (H : TopologicalGroup.IsSES φ ψ)
  (μA : Measure A) (μC : Measure C) (hμA : IsHaarMeasure μA) (hμC : IsHaarMeasure μC)
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def average₀ (f : B → E) (b : B) : E :=
  ∫ a, f (b * φ a) ∂μA

variable {φ ψ}

noncomputable def twist (f : CompactlySupportedContinuousMap B E) (b : B) :
    CompactlySupportedContinuousMap A E where
  toFun a := f (b * φ a)
  hasCompactSupport' := by
    have h := f.hasCompactSupport
    rw [← exists_compact_iff_hasCompactSupport] at h ⊢
    obtain ⟨K, hK, hf⟩ := h
    refine ⟨φ ⁻¹' (b⁻¹ • K), H.isClosedEmbedding.isCompact_preimage (hK.smul b⁻¹), fun x hx ↦ hf _ ?_⟩
    contrapose! hx
    simpa [mem_smul_set_iff_inv_smul_mem]
  continuous_toFun := by
    have : Continuous φ := H.isClosedEmbedding.continuous
    fun_prop

noncomputable def average₀_eq (f : B → E) {b₁ b₂ : B} (h : ψ b₁ = ψ b₂) :
    average₀ φ μA f b₁ = average₀ φ μA f b₂ := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul] at h
  obtain ⟨a, ha⟩ := H.exact.ge h
  rw [eq_inv_mul_iff_mul_eq] at ha
  simp_rw [← ha, average₀, mul_assoc, ← map_mul]
  exact (integral_mul_left_eq_self _ a).symm

noncomputable def average₀_add (f g : CompactlySupportedContinuousMap B E) :
    average₀ φ μA (f + g) = average₀ φ μA f + average₀ φ μA g := by
  ext b
  simp only [average₀, Pi.add_apply]
  apply integral_add
  · exact (twist H f b).integrable
  · exact (twist H g b).integrable

noncomputable def average₀_smul (x : ℝ) (f : B → E) :
    average₀ φ μA (x • f) = x • average₀ φ μA f := by
  ext b
  simp only [average₀, Pi.smul_apply]
  apply integral_smul

noncomputable def average₀_mono (f g : CompactlySupportedContinuousMap B ℝ) (h : f ≤ g) :
    average₀ φ μA f ≤ average₀ φ μA g := by
  rw [Pi.le_def]
  intro b
  simp only [average₀]
  apply integral_mono
  · exact (twist H f b).integrable
  · exact (twist H g b).integrable
  · rw [Pi.le_def]
    intro a
    apply h

-- upgrade to linear map?
noncomputable def average (f : CompactlySupportedContinuousMap B E) :
    CompactlySupportedContinuousMap C E where
  toFun := fun c ↦ average₀ φ μA f (Function.invFun ψ c)
  hasCompactSupport' := by
    have h := f.hasCompactSupport
    rw [← exists_compact_iff_hasCompactSupport] at h ⊢
    obtain ⟨K, hK, hf⟩ := h
    refine ⟨ψ '' K, hK.image H.isOpenQuotientMap.continuous, fun x hx ↦ ?_⟩
    simp only [average₀]
    suffices ∀ a : A, f (Function.invFun ψ x * φ a) = 0 by simp [this]
    intro a
    apply hf
    contrapose! hx
    refine ⟨_, hx, ?_⟩
    rw [map_mul]
    rw [Function.rightInverse_invFun H.isOpenQuotientMap.surjective, mul_eq_left]
    apply H.exact.le
    use a
  continuous_toFun := by
    have average_apply (f : B → E) (b : B) :
        average₀ φ μA f (Function.invFun ψ (ψ b)) = average₀ φ μA f b :=
      average₀_eq H μA hμA f Function.apply_invFun_apply
    rw [← H.isOpenQuotientMap.continuous_comp_iff]
    change Continuous fun c ↦ _
    simp only [Function.comp_apply, average_apply]
    simp only [average₀]
    let p₀ : B → A → E := fun b a ↦ f (b * φ a)
    have hp₀ (b : B) : MemLp (p₀ b) 1 μA := by
      apply Continuous.memLp_of_hasCompactSupport
      · exact (twist H f b).continuous
      · exact (twist H f b).hasCompactSupport
    let p : B → Lp E 1 μA := fun b ↦ MemLp.toLp (p₀ b) (hp₀ b)
    have key (b : B) : ∫ a, p b a ∂μA = ∫ a, f (b * φ a) ∂μA :=
      integral_congr_ae (hp₀ b).coeFn_toLp
    simp only [← key]
    suffices Continuous p by
      exact continuous_integral.comp this
    simp only [p, p₀]
    let := IsTopologicalGroup.rightUniformSpace B -- or perhaps left
    have ha := f.hasCompactSupport.uniformContinuous_of_continuous f.continuous
    rw [UniformContinuous, Filter.tendsto_iff_forall_eventually_mem] at ha
    rw [Metric.continuous_iff']
    intro b ε hε
    obtain ⟨U₀, hU₀, hb⟩ := exists_compact_mem_nhds b
    have hf₀ := f.hasCompactSupport
    rw [← exists_compact_iff_hasCompactSupport] at hf₀
    obtain ⟨K, hK, hf₀⟩ := hf₀
    let prod : Set B := U₀⁻¹ * K
    let preim : Set A := φ ⁻¹' prod
    have hpreim : IsCompact preim := H.isClosedEmbedding.isCompact_preimage (hU₀.inv.mul hK)
    let V₀ := μA preim
    have hV₀' : V₀ < ⊤ := hpreim.measure_lt_top
    let v : ℝ := if V₀ = 0 then 1 else (ε / ENNReal.toReal (μA preim)) / 2
    have hv : 0 < v := by
      simp only [v]
      split_ifs with h
      · exact one_pos
      · exact div_pos (div_pos hε (ENNReal.toReal_pos h hV₀'.ne)) two_pos
    simp only [dist_eq_norm_sub, ← MemLp.toLp_sub, MeasureTheory.Lp.norm_toLp]
    specialize ha _ (Metric.dist_mem_uniformity hv)
    simp only [Filter.eventually_iff] at ha ⊢
    change _ ∈ Filter.comap _ _ at ha
    rw [Filter.mem_comap] at ha
    obtain ⟨U, hU, hf⟩ := ha
    simp [Set.subset_def] at hf
    replace hU := inv_mem_nhds_one B hU
    have hU' := mul_singleton_mem_nhds_of_nhds_one b hU
    replace hU' := Filter.inter_mem hU' hb
    refine Filter.mem_of_superset hU' ?_
    rintro - ⟨⟨c, d, e, rfl, g, rfl⟩, hm⟩
    have : ∀ a : A, dist (f (c * e * φ a)) (f (e * φ a)) < v := by
      intro a
      simp only [Set.mem_inv] at d
      specialize hf (c * e * φ a) (e * φ a)
      simpa [d] using hf
    dsimp
    apply ENNReal.toReal_lt_of_lt_ofReal
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
    rw [← MeasureTheory.setLIntegral_eq_of_support_subset (s := preim)]
    · have : ∀ x : A, ‖((fun a ↦ f (c * e * φ a)) - fun a ↦ f (e * φ a)) x‖ₑ ≤ ENNReal.ofReal v := by
        intro x
        simp only [dist_eq_norm_sub] at this
        simp
        rw [← ofReal_norm_eq_enorm]
        apply ENNReal.ofReal_le_ofReal
        exact (this x).le
      refine (MeasureTheory.lintegral_mono (g := fun _ ↦ ENNReal.ofReal v) ?_).trans_lt ?_
      · intro x
        exact this x
      · rw [lintegral_const]
        simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter]
        simp only [v]
        split_ifs with h
        · simp only [V₀] at h
          simpa [h]
        · change _ * V₀ < _
          rw [← ENNReal.ofReal_toReal hV₀'.ne, ← ENNReal.ofReal_mul (by positivity)]
          rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
          simp only [V₀]
          field_simp
          grw [div_self_le_one]
          norm_num
    · intro x hx
      have : f (c * e * φ x) ≠ 0 ∨ f (e * φ x) ≠ 0 := by
        contrapose! hx
        simp [hx.1, hx.2]
      rcases this with h | h
      · have : c * e * φ x ∈ K := by
          contrapose! h
          apply hf₀ _ h
        -- c * e * φ x ∈ K
        change φ x ∈ U₀⁻¹ * K
        have h : φ x = (c * e)⁻¹ * (c * e * φ x) := by group
        rw [h]
        apply Set.mul_mem_mul
        · rwa [Set.inv_mem_inv]
        · exact this
      · have : e * φ x ∈ K := by
          contrapose! h
          apply hf₀ _ h
        change φ x ∈ U₀⁻¹ * K
        have h : φ x = e⁻¹ * (e * φ x) := by simp
        rw [h]
        apply Set.mul_mem_mul
        · rw [Set.inv_mem_inv]
          exact mem_of_mem_nhds hb
        · exact this

noncomputable def average_zero :
    average H μA hμA (0 : CompactlySupportedContinuousMap B E) = 0 := by
  ext
  simp [average, average₀]

noncomputable def average_add (f g : CompactlySupportedContinuousMap B E) :
    average H μA hμA (f + g) = average H μA hμA f + average H μA hμA g := by
  ext c
  simp only [average, Pi.add_apply, average₀_add H]
  simp

noncomputable def average_mono (f g : CompactlySupportedContinuousMap B ℝ) (h : f ≤ g) :
    average H μA hμA f ≤ average H μA hμA g := by
  exact fun _ ↦ average₀_mono H μA hμA f g h _

noncomputable def average_smul (x : ℝ) (f : CompactlySupportedContinuousMap B E) :
    average H μA hμA (x • f) = x • average H μA hμA f := by
  ext c
  simp [average, average₀_smul]

include H hμA in
theorem average_apply (f : CompactlySupportedContinuousMap B E) (b : B) :
    average H μA hμA f (ψ b) = average₀ φ μA f b :=
  average₀_eq H μA hμA f Function.apply_invFun_apply

open Filter

include hμA hμC H in
theorem average_integrable (f : CompactlySupportedContinuousMap B E) :
    Integrable (average H μA hμA f) μC := by
  change Integrable (fun c ↦ average H μA hμA f c) μC
  have hc : Continuous (fun c ↦ average H μA hμA f c) := (average H μA hμA f).continuous
  have hs : HasCompactSupport (fun c ↦ average H μA hμA f c) :=
    (average H μA hμA f).hasCompactSupport
  exact hc.integrable_of_hasCompactSupport hs

-- upgrade to linear map?
noncomputable def integrate (f : CompactlySupportedContinuousMap B E) : E :=
  ∫ c, average H μA hμA f c ∂μC

include H hμA hμC in
theorem integrate_add (f g : CompactlySupportedContinuousMap B E) :
    integrate H μA μC hμA (f + g) =
      integrate H μA μC hμA f + integrate H μA μC hμA g := by
  simp only [integrate, average_add H]
  apply integral_add
  · exact average_integrable H μA μC hμA hμC f
  · exact average_integrable H μA μC hμA hμC g

theorem integrate_smul (x : ℝ) (f : CompactlySupportedContinuousMap B E) :
    integrate H μA μC hμA (x • f) = x • integrate H μA μC hμA f := by
  simp only [integrate, Pi.smul_apply, average_smul]
  apply integral_smul

include H hμA hμC in
theorem integrate_mono (f g : CompactlySupportedContinuousMap B ℝ) (h : f ≤ g) :
    integrate H μA μC hμA f ≤ integrate H μA μC hμA g := by
  simp only [integrate]
  apply integral_mono
  · exact average_integrable H μA μC hμA hμC f
  · exact average_integrable H μA μC hμA hμC g
  · exact average_mono H μA hμA f g h

noncomputable def map : CompactlySupportedContinuousMap B ℝ →ₚ[ℝ] ℝ where
  toFun f := integrate H μA μC hμA f
  map_add' f g := integrate_add H μA μC hμA hμC f g
  map_smul' x f := integrate_smul H μA μC hμA x f
  monotone' f g h := integrate_mono H μA μC hμA hμC f g h

variable [T2Space B]

noncomputable def inducedMeasure : Measure B :=
  RealRMK.rieszMeasure (map H μA μC hμA hμC)

instance inducedMeasure_regular :
    (inducedMeasure H μA μC hμA hμC).Regular :=
  RealRMK.regular_rieszMeasure (map H μA μC hμA hμC)


theorem integral_inducedMeasure (f : CompactlySupportedContinuousMap B ℝ) :
    ∫ b : B, f b ∂(inducedMeasure H μA μC hμA hμC) = integrate H μA μC hμA f := by
  apply RealRMK.integral_rieszMeasure

theorem isHaarMeasure_inducedMeasure :
    IsHaarMeasure (inducedMeasure H μA μC hμA hμC) where
  lt_top_of_isCompact := by
    intro K hK
    let U : Set B := Set.univ
    have hU : IsOpen U := isOpen_univ
    have hKU : K ⊆ U := K.subset_univ
    obtain ⟨f, hf1, hf2, hf3, hf4⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
    exact lt_of_le_of_lt (RealRMK.rieszMeasure_le_of_eq_one (map H μA μC hμA hμC)
      (f := ⟨f, hf2⟩) (fun x ↦ (hf4 x).1) hK (fun x hx ↦ hf1 hx)) ENNReal.ofReal_lt_top
  map_mul_left_eq_self := by
    intro b
    have : ((inducedMeasure H μA μC hμA hμC).map (fun x ↦ b * x)).Regular :=
      Regular.map (Homeomorph.mulLeft b)
    apply MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (by fun_prop) (by fun_prop)]
    have key : ∀ x : B, f (b * x) = f.comp (Homeomorph.mulLeft b).toCocompactMap x := by simp
    simp only [integral_inducedMeasure, key, integrate]
    rw [← integral_mul_left_eq_self _ (ψ b)⁻¹]
    congr
    ext c
    simp [average, average₀, ← mul_assoc]
    apply average₀_eq H μA hμA
    rw [map_mul, Function.rightInverse_invFun H.isOpenQuotientMap.surjective, mul_inv_cancel_left,
      Function.rightInverse_invFun H.isOpenQuotientMap.surjective]
  open_pos := by
    rintro U hU ⟨b, hb⟩
    obtain ⟨K, hK, hb, hKU⟩ := exists_compact_subset hU hb
    replace hb : b ∈ K := interior_subset hb
    obtain ⟨f, hf1, hf2, hf3, hf4⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
    have hf0 : 0 ≤ f := fun x ↦ (hf4 x).1
    have hf0' := average_mono H μA hμA 0 ⟨f, hf2⟩ hf0
    rw [average_zero] at hf0'
    refine (lt_of_lt_of_le ?_ (RealRMK.le_rieszMeasure_tsupport_subset
      (map H μA μC hμA hμC) (f := ⟨f, hf2⟩) hf4 hf3)).ne'
    rw [ENNReal.ofReal_pos]
    suffices (0 : ℝ) < average H μA hμA ⟨f, hf2⟩ (ψ b) from
      Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
        (average H μA hμA ⟨f, hf2⟩).continuous
        (average H μA hμA ⟨f, hf2⟩).hasCompactSupport
        hf0' this.ne'
    have : (Function.invFun ψ (ψ b))⁻¹ * b ∈ φ.range := by
      apply H.exact.ge
      simp [Function.apply_invFun_apply]
    obtain ⟨a, ha⟩ := this
    apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (twist H ⟨f, hf2⟩ _).continuous
      (twist H ⟨f, hf2⟩ _).hasCompactSupport
      (fun x ↦ (hf4 _).1)
    simp only [twist, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk, ne_eq]
    rw [ha]
    simp [hf1 hb]

-- upgrade exists_continuousMap_one_of_isCompact_subset_isOpen
-- upgrade Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero

theorem main₀ (U : Set B) (hU : IsOpen U) [DiscreteTopology A]
    (h : μC Set.univ * μA {1} < inducedMeasure H μA μC hμA hμC U) :
    ¬ U.InjOn ψ := by
  have ho : 0 < μA {1} := (isOpen_discrete {1}).measure_pos _ (singleton_nonempty 1)
  have ht : μA {1} < ⊤ := isCompact_singleton.measure_lt_top
  obtain ⟨K, hKU, hK, h⟩ := Regular.innerRegular hU _ h
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  have : μC Set.univ * μA {1} < ENNReal.ofReal (∫ c : C, average H μA hμA ⟨f, hf2⟩ c ∂μC) :=
    lt_of_lt_of_le h
      ((RealRMK.rieszMeasure_le_of_eq_one (map H μA μC hμA hμC)
        (f := ⟨f, hf2⟩) (fun x ↦ (hf4 x).1) hK (fun x hx ↦ hf1 hx)))
  have : ∃ c : C, (μA {1}).toReal < average H μA hμA ⟨f, hf2⟩ c := by
    contrapose! this
    rcases eq_top_or_lt_top (μC Set.univ) with h | h
    · rw [h, ENNReal.top_mul ho.ne']
      exact le_top
    have hC : IsFiniteMeasure μC := ⟨h⟩
    rw [← ENNReal.ofReal_toReal h.ne, ← ENNReal.ofReal_toReal ht.ne, ← ENNReal.ofReal_mul]
    apply ENNReal.ofReal_le_ofReal
    rw [← Measure.real_def, ← smul_eq_mul, ← integral_indicator_const, indicator_univ]
    apply integral_mono_of_nonneg
    · apply Filter.Eventually.of_forall
      have key := average_mono H μA hμA 0 ⟨f, hf2⟩ (fun x ↦ (hf4 x).1)
      rwa [average_zero] at key
    · apply MeasureTheory.integrable_const
    · apply Filter.Eventually.of_forall
      exact this
    · exact MeasurableSet.univ
    · exact ENNReal.toReal_nonneg
  obtain ⟨c, hc⟩ := this
  contrapose! hc
  by_cases h : ∀ a, f (Function.invFun ψ c * φ a) = 0
  · simp [average, average₀, h]
  push_neg at h
  obtain ⟨a₀, ha₀⟩ := h
  replace hc : Function.support (fun a ↦ f (Function.invFun ψ c * φ a)) = {a₀} := by
    rw [Set.eq_singleton_iff_unique_mem]
    use ha₀
    intro a ha
    replace ha := hf3 (subset_tsupport _ ha)
    replace ha₀ := hf3 (subset_tsupport _ ha₀)
    have : ∀ a, ψ (φ a) = 1 := by
      intro a
      apply H.exact.le
      exact ⟨a, rfl⟩
    have key := hc ha ha₀ (by simp [this])
    simpa [H.isClosedEmbedding.injective.eq_iff] using key
  simp only [average, average₀]
  simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk, ge_iff_le]
  rw [← MeasureTheory.setIntegral_support, hc, integral_singleton, smul_eq_mul,
    real_def, haar_singleton]
  rw [mul_le_iff_le_one_right]
  · exact (hf4 _).2
  · apply ENNReal.toReal_pos ho.ne' ht.ne
