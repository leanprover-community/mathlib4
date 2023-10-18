/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Algebra.Group.Opposite

#align_import measure_theory.measure.haar.quotient from "leanprover-community/mathlib"@"3b52265189f3fb43aa631edffce5d060fafaf82f"

/-!
# Haar quotient measure

In this file, we consider properties of fundamental domains and measures for the action of a
subgroup of a group `G` on `G` itself.

## Main results

* `MeasureTheory.IsFundamentalDomain.smulInvariantMeasure_map`: given a subgroup `Γ` of a
  topological group `G`, the pushforward to the coset space `G ⧸ Γ` of the restriction of a both
  left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure
  on `G ⧸ Γ`.

* `MeasureTheory.IsFundamentalDomain.isMulLeftInvariant_map`: given a normal subgroup `Γ` of
  a topological group `G`, the pushforward to the quotient group `G ⧸ Γ` of the restriction of
  a both left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a left-invariant
  measure on `G ⧸ Γ`.

Note that a group `G` with Haar measure that is both left and right invariant is called
**unimodular**.
-/


open Set MeasureTheory TopologicalSpace MeasureTheory.Measure

open scoped Pointwise NNReal ENNReal

variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {μ : Measure G} {Γ : Subgroup G}

/-- Measurability of the action of the topological group `G` on the left-coset space `G/Γ`. -/
@[to_additive "Measurability of the action of the additive topological group `G` on the left-coset
  space `G/Γ`."]
instance QuotientGroup.measurableSMul [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)] :
    MeasurableSMul G (G ⧸ Γ) where
  measurable_const_smul g := (continuous_const_smul g).measurable
  measurable_smul_const x := (QuotientGroup.continuous_smul₁ x).measurable
#align quotient_group.has_measurable_smul QuotientGroup.measurableSMul
#align quotient_add_group.has_measurable_vadd QuotientAddGroup.measurableVAdd

variable {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ.op 𝓕 μ)

variable [Countable Γ] [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

/-- The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and right-
  invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure on `G ⧸ Γ`. -/
@[to_additive "The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and
  right-invariant measure on an additive topological group `G` to a fundamental domain `𝓕` is a
  `G`-invariant measure on `G ⧸ Γ`."]
theorem MeasureTheory.IsFundamentalDomain.smulInvariantMeasure_map [μ.IsMulLeftInvariant]
    [μ.IsMulRightInvariant] :
    SMulInvariantMeasure G (G ⧸ Γ) (Measure.map QuotientGroup.mk (μ.restrict 𝓕)) where
  measure_preimage_smul g A hA := by
    let π : G → G ⧸ Γ := QuotientGroup.mk
    have meas_π : Measurable π := continuous_quotient_mk'.measurable
    have 𝓕meas : NullMeasurableSet 𝓕 μ := h𝓕.nullMeasurableSet
    have meas_πA : MeasurableSet (π ⁻¹' A) := measurableSet_preimage meas_π hA
    rw [Measure.map_apply meas_π hA,
      Measure.map_apply meas_π (measurableSet_preimage (measurable_const_smul g) hA),
      Measure.restrict_apply₀' 𝓕meas, Measure.restrict_apply₀' 𝓕meas]
    set π_preA := π ⁻¹' A
    have : π ⁻¹' ((fun x : G ⧸ Γ => g • x) ⁻¹' A) = (g * ·) ⁻¹' π_preA := by
      ext1; simp
    rw [this]
    have : μ ((g * ·) ⁻¹' π_preA ∩ 𝓕) = μ (π_preA ∩ (g⁻¹ * ·) ⁻¹' 𝓕) := by
      trans μ ((g * ·) ⁻¹' (π_preA ∩ (g⁻¹ * ·) ⁻¹' 𝓕))
      · rw [preimage_inter]
        congr 2
        simp [Set.preimage]
      rw [measure_preimage_mul]
    rw [this]
    have h𝓕_translate_fundom : IsFundamentalDomain Γ.op (g • 𝓕) μ :=
      h𝓕.smul_of_comm g
    rw [h𝓕.measure_set_eq h𝓕_translate_fundom meas_πA, ← preimage_smul_inv]; rfl
    rintro ⟨γ, γ_in_Γ⟩
    ext x
    have : π (x * MulOpposite.unop γ) = π x := by simpa [QuotientGroup.eq'] using γ_in_Γ
    simp only [(· • ·), ← this, mem_preimage]
    rfl
#align measure_theory.is_fundamental_domain.smul_invariant_measure_map MeasureTheory.IsFundamentalDomain.smulInvariantMeasure_map
#align measure_theory.is_add_fundamental_domain.vadd_invariant_measure_map MeasureTheory.IsAddFundamentalDomain.vaddInvariantMeasure_map

/-- Assuming `Γ` is a normal subgroup of a topological group `G`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of a both left- and right-invariant measure on `G` to a
  fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`. -/
@[to_additive "Assuming `Γ` is a normal subgroup of an additive topological group `G`, the
  pushforward to the quotient group `G ⧸ Γ` of the restriction of a both left- and right-invariant
  measure on `G` to a fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`."]
theorem MeasureTheory.IsFundamentalDomain.isMulLeftInvariant_map [Subgroup.Normal Γ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] :
    (Measure.map (QuotientGroup.mk' Γ) (μ.restrict 𝓕)).IsMulLeftInvariant where
  map_mul_left_eq_self x := by
    apply Measure.ext
    intro A hA
    obtain ⟨x₁, h⟩ := @Quotient.exists_rep _ (QuotientGroup.leftRel Γ) x
    haveI := h𝓕.smulInvariantMeasure_map
    convert measure_preimage_smul x₁ ((Measure.map QuotientGroup.mk) (μ.restrict 𝓕)) A using 1
    rw [← h, Measure.map_apply]
    · rfl
    · exact measurable_const_mul _
    · exact hA
#align measure_theory.is_fundamental_domain.is_mul_left_invariant_map MeasureTheory.IsFundamentalDomain.isMulLeftInvariant_map
#align measure_theory.is_add_fundamental_domain.is_add_left_invariant_map MeasureTheory.IsAddFundamentalDomain.isAddLeftInvariant_map

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on `G ⧸ Γ`. -/
@[to_additive "Given a normal subgroup `Γ` of an additive topological group `G` with Haar measure
  `μ`, which is also right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward
  to the quotient group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on
  `G ⧸ Γ`."]
theorem MeasureTheory.IsFundamentalDomain.map_restrict_quotient  [T2Space (G ⧸ Γ)]
    [SecondCountableTopology (G ⧸ Γ)] (K : PositiveCompacts (G ⧸ Γ)) [Subgroup.Normal Γ]
    [MeasureTheory.Measure.IsHaarMeasure μ] [μ.IsMulRightInvariant] (h𝓕_finite : μ 𝓕 < ⊤) :
    Measure.map (QuotientGroup.mk' Γ) (μ.restrict 𝓕) =
      μ (𝓕 ∩ QuotientGroup.mk' Γ ⁻¹' K) • MeasureTheory.Measure.haarMeasure K := by
  let π : G →* G ⧸ Γ := QuotientGroup.mk' Γ
  have meas_π : Measurable π := continuous_quotient_mk'.measurable
  have 𝓕meas : NullMeasurableSet 𝓕 μ := h𝓕.nullMeasurableSet
  haveI := Fact.mk h𝓕_finite
  -- the measure is left-invariant, so by the uniqueness of Haar measure it's enough to show that
  -- it has the stated size on the reference compact set `K`.
  haveI : (Measure.map (QuotientGroup.mk' Γ) (μ.restrict 𝓕)).IsMulLeftInvariant :=
    h𝓕.isMulLeftInvariant_map
  rw [Measure.haarMeasure_unique (Measure.map (QuotientGroup.mk' Γ) (μ.restrict 𝓕)) K,
    Measure.map_apply meas_π, Measure.restrict_apply₀' 𝓕meas, inter_comm]
  exact K.isCompact.measurableSet
#align measure_theory.is_fundamental_domain.map_restrict_quotient MeasureTheory.IsFundamentalDomain.map_restrict_quotient
#align measure_theory.is_add_fundamental_domain.map_restrict_quotient MeasureTheory.IsAddFundamentalDomain.map_restrict_quotient

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ` is
  measure-preserving between appropriate multiples of Haar measure on `G` and `G ⧸ Γ`. -/
@[to_additive MeasurePreservingQuotientAddGroup.mk' "Given a normal subgroup `Γ` of an additive
  topological group `G` with Haar measure `μ`, which is also right-invariant, and a finite volume
  fundamental domain `𝓕`, the quotient map to `G ⧸ Γ` is measure-preserving between appropriate
  multiples of Haar measure on `G` and `G ⧸ Γ`."]
theorem MeasurePreservingQuotientGroup.mk' [T2Space (G ⧸ Γ)] [SecondCountableTopology (G ⧸ Γ)]
    (K : PositiveCompacts (G ⧸ Γ)) [Subgroup.Normal Γ] [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (h𝓕_finite : μ 𝓕 < ⊤) (c : ℝ≥0)
    (h : μ (𝓕 ∩ QuotientGroup.mk' Γ ⁻¹' K) = c) :
    MeasurePreserving (QuotientGroup.mk' Γ) (μ.restrict 𝓕)
      (c • MeasureTheory.Measure.haarMeasure K) where
  measurable := continuous_quotient_mk'.measurable
  map_eq := by rw [h𝓕.map_restrict_quotient K h𝓕_finite, h]; rfl
#align measure_preserving_quotient_group.mk' MeasurePreservingQuotientGroup.mk'
#align measure_preserving_quotient_add_group.mk' MeasurePreservingQuotientAddGroup.mk'

section

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
  apply h𝓕.measure_zero_of_invariant _ _ hs
  · intro γ
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
  additive  group `G`, the integral of a function `f` on `G` with respect to a right-invariant
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
  · rw [← h𝓕.lintegral_eq_tsum'' (fun x ↦ ‖f x‖₊)]
    exact ne_of_lt hf₁.2

/-- This is the **Unfolding Trick**: Given a subgroup `Γ` of a group `G`, the integral of a
  function `f` on `G` times the lift to `G` of a function `g` on the quotient `G ⧸ Γ` with respect
  to a right-invariant measure `μ` on `G`, is equal to the integral over the quotient of the
  automorphization of `f` times `g`. -/
lemma QuotientGroup.integral_mul_eq_integral_automorphize_mul {K : Type*} [NormedField K]
    [NormedSpace ℝ K] [μ.IsMulRightInvariant] {f : G → K}
    (f_ℒ_1 : Integrable f μ) {g : G ⧸ Γ → K} (hg : AEStronglyMeasurable g μ_𝓕)
    (g_ℒ_infinity : essSup (fun x ↦ ↑‖g x‖₊) μ_𝓕 ≠ ∞)
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
  have H₁ : Integrable ((g ∘ π) * f) μ
  · have : AEStronglyMeasurable (fun (x : G) ↦ g (x : (G ⧸ Γ))) μ
    · refine (AEStronglyMeasurable.mono' hg ?_).comp_measurable meas_π
      exact h𝓕.absolutelyContinuous_map
    refine Integrable.essSup_smul f_ℒ_1 this ?_
    have hg' : AEStronglyMeasurable (fun x ↦ (‖g x‖₊ : ℝ≥0∞)) μ_𝓕 :=
      (ENNReal.continuous_coe.comp continuous_nnnorm).comp_aestronglyMeasurable hg
    rw [← essSup_comp_quotientGroup_mk h𝓕 hg'.aemeasurable]
    exact g_ℒ_infinity
  have H₂ : AEStronglyMeasurable (QuotientGroup.automorphize ((g ∘ π) * f)) μ_𝓕
  · simp_rw [H₀]
    exact hg.mul F_ae_measurable
  apply QuotientGroup.integral_eq_integral_automorphize h𝓕 H₁ H₂

end

section

variable {G' : Type*} [AddGroup G'] [MeasurableSpace G'] [TopologicalSpace G']
  [TopologicalAddGroup G'] [BorelSpace G']
  {μ' : Measure G'}
  {Γ' : AddSubgroup G'}
  [Countable Γ'] [MeasurableSpace (G' ⧸ Γ')] [BorelSpace (G' ⧸ Γ')]
  {𝓕' : Set G'}

local notation "μ_𝓕" => Measure.map (@QuotientAddGroup.mk G' _ Γ') (μ'.restrict 𝓕')

/-- This is the **Unfolding Trick**: Given an additive subgroup `Γ'` of an additive group `G'`, the
  integral of a function `f` on `G'` times the lift to `G'` of a function `g` on the quotient
  `G' ⧸ Γ'` with respect to a right-invariant measure `μ` on `G'`, is equal to the integral over
  the quotient of the automorphization of `f` times `g`. -/
lemma QuotientAddGroup.integral_mul_eq_integral_automorphize_mul {K : Type*} [NormedField K]
    [NormedSpace ℝ K] [μ'.IsAddRightInvariant] {f : G' → K}
    (f_ℒ_1 : Integrable f μ') {g : G' ⧸ Γ' → K} (hg : AEStronglyMeasurable g μ_𝓕)
    (g_ℒ_infinity : essSup (fun x ↦ (‖g x‖₊ : ℝ≥0∞)) μ_𝓕 ≠ ∞)
    (F_ae_measurable : AEStronglyMeasurable (QuotientAddGroup.automorphize f) μ_𝓕)
    (h𝓕 : IsAddFundamentalDomain Γ'.op 𝓕' μ') :
    ∫ x : G', g (x : G' ⧸ Γ') * (f x) ∂μ'
      = ∫ x : G' ⧸ Γ', g x * (QuotientAddGroup.automorphize f x) ∂μ_𝓕 := by
  let π : G' → G' ⧸ Γ' := QuotientAddGroup.mk
  have meas_π : Measurable π := continuous_quotient_mk'.measurable
  have H₀ : QuotientAddGroup.automorphize ((g ∘ π) * f) = g * (QuotientAddGroup.automorphize f) :=
    by exact QuotientAddGroup.automorphize_smul_left f g
  calc ∫ (x : G'), g (π x) * f x ∂μ' =
    ∫ (x : G' ⧸ Γ'), QuotientAddGroup.automorphize ((g ∘ π) * f) x ∂μ_𝓕 := ?_
    _ = ∫ (x : G' ⧸ Γ'), g x * (QuotientAddGroup.automorphize f x) ∂μ_𝓕 := by simp [H₀]
  have H₁ : Integrable ((g ∘ π) * f) μ'
  · have : AEStronglyMeasurable (fun (x : G') ↦ g (x : (G' ⧸ Γ'))) μ'
    · refine (AEStronglyMeasurable.mono' hg ?_).comp_measurable meas_π
      exact h𝓕.absolutelyContinuous_map
    refine Integrable.essSup_smul f_ℒ_1 this ?_
    have hg' : AEStronglyMeasurable (fun x ↦ (‖g x‖₊ : ℝ≥0∞)) μ_𝓕 :=
      (ENNReal.continuous_coe.comp continuous_nnnorm).comp_aestronglyMeasurable hg
    rw [← essSup_comp_quotientAddGroup_mk h𝓕 hg'.aemeasurable]
    exact g_ℒ_infinity
  have H₂ : AEStronglyMeasurable (QuotientAddGroup.automorphize ((g ∘ π) * f)) μ_𝓕
  · simp_rw [H₀]
    exact hg.mul F_ae_measurable
  apply QuotientAddGroup.integral_eq_integral_automorphize h𝓕 H₁ H₂

end

attribute [to_additive existing QuotientGroup.integral_mul_eq_integral_automorphize_mul]
  QuotientAddGroup.integral_mul_eq_integral_automorphize_mul
