/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import Mathlib.Algebra.Group.Opposite
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.Basic

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

open Set MeasureTheory TopologicalSpace MeasureTheory.Measure

open scoped Pointwise NNReal ENNReal

section

/-- Measurability of the action of the topological group `G` on the left-coset space `G / Γ`. -/
@[to_additive "Measurability of the action of the additive topological group `G` on the left-coset
  space `G / Γ`."]
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
@[to_additive "If `μ` on `G ⧸ Γ` satisfies `AddQuotientMeasureEqMeasurePreimage` relative to a both
  left- and right-invariant measure on `G` and `Γ` is a normal subgroup, then `μ` is a
  left-invariant measure."]
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
"Assume that a measure `μ` is `IsAddLeftInvariant`, that the action of `Γ` on `G` has a
measurable fundamental domain `s` with positive finite volume, and that there is a single measurable
set `V ⊆ G ⧸ Γ` along which the pullback of `μ` and `ν` agree (so the scaling is right). Then
`μ` satisfies `AddQuotientMeasureEqMeasurePreimage`. The main tool of the proof is the uniqueness of
left invariant measures, if normalized by a single positive finite-measured set."]
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
@[to_additive "If a measure `μ` is
left-invariant and satisfies the right scaling condition, then it satisfies
`AddQuotientMeasureEqMeasurePreimage`."]
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
@[to_additive "If a measure `μ` on the quotient `G ⧸ Γ` of an additive group `G` by a discrete
normal subgroup `Γ` having fundamental domain, satisfies `AddQuotientMeasureEqMeasurePreimage`
relative to a standardized choice of Haar measure on `G`, and assuming `μ` is finite, then `μ` is
itself Haar."]
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
    haveI i' : IsOpenPosMeasure (ν : Measure G) := inferInstance
    apply IsOpenPosMeasure.open_pos (interior K) (μ := ν) (self := i')
    · exact isOpen_interior
    · exact K.interior_nonempty
    rw [← le_zero_iff,
      ← fund_dom_s.measure_zero_of_invariant _ (fun g ↦ QuotientGroup.sound _ _ g) h]
    apply measure_mono
    refine interior_subset.trans ?_
    rw [QuotientGroup.coe_mk']
    show (K : Set G) ⊆ π ⁻¹' (π '' K)
    exact subset_preimage_image π K
  · show ν (π ⁻¹' (π '' K) ∩ s) ≠ ⊤
    apply ne_of_lt
    refine lt_of_le_of_lt ?_ finiteCovol.lt_top
    apply measure_mono
    exact inter_subset_right

variable [SigmaFinite ν]

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
  properly normalized, satisfies `QuotientMeasureEqMeasurePreimage`. -/
@[to_additive "Given a normal
subgroup `Γ` of an additive topological group `G` with Haar measure `μ`, which is also
right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
properly normalized, satisfies `AddQuotientMeasureEqMeasurePreimage`."]
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
@[to_additive "Given a
normal subgroup `Γ` of an additive topological group `G` with Haar measure `μ`, which is also
right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
properly normalized, satisfies `AddQuotientMeasureEqMeasurePreimage`."]
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
@[to_additive "The `essSup` of a function `g` on the additive quotient space `G ⧸ Γ` with respect
  to the pushforward of the restriction, `μ_𝓕`, of a right-invariant measure `μ` to a fundamental
  domain `𝓕`, is the same as the `essSup` of `g`'s lift to the universal cover `G` with respect
  to `μ`."]
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
@[to_additive "Given an additive quotient space `G ⧸ Γ` where `Γ` is `Countable`, and the
  restriction, `μ_𝓕`, of a right-invariant measure `μ` on `G` to a fundamental domain `𝓕`, a set
  in the quotient which has `μ_𝓕`-measure zero, also has measure zero under the
  folding of `μ` under the quotient. Note that, if `Γ` is infinite, then the folded map
  will take the value `∞` on any open set in the quotient!"]
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
@[to_additive "This is a simple version of the **Unfolding Trick**: Given a subgroup `Γ` of an
  additive group `G`, the integral of a function `f` on `G` with respect to a right-invariant
  measure `μ` is equal to the integral over the quotient `G ⧸ Γ` of the automorphization of `f`."]
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
