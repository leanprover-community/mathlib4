import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Propose
import Mathlib.Tactic.GCongr

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction Topology

-- This file contains steps needed to prove the portmanteau implication
-- `le_liminf_open_implies_convergence`. Some intermediate steps need to be generalized
-- and cleaned up, and are to be placed in appropriate files. The main part should go
-- to the file `Mathlib.MeasureTheory.Measure.Portmanteau`.



section liminf_lemma

variable {ι R S : Type _} {F : Filter ι} [NeBot F]
  [ConditionallyCompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R]
  [ConditionallyCompleteLinearOrder S] [TopologicalSpace S] [OrderTopology S]

#check Monotone.map_sSup_of_continuousAt'

-- NOTE: The result `Monotone.map_sSup_of_continuousAt'` in the library has a natural version
-- generalized to *conditionally* complete linear orders. One just needs a hypothesis `BddAbove s`.
/-- A monotone function continuous at the supremum of a nonempty set sends this supremum to
the supremum of the image of this set. -/
theorem Monotone.map_sSup_of_continuousAt'' {f : R → S} {A : Set R} (Cf : ContinuousAt f (sSup A))
    (Mf : Monotone f) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A) :
    f (sSup A) = sSup (f '' A) := by
  --This is a particular case of the more general `IsLUB.isLUB_of_tendsto`
  refine ((@IsLUB.isLUB_of_tendsto R S _ _ _ _ _ _ f A (sSup A) (f (sSup A)) (Mf.monotoneOn _) ?_ A_nonemp ?_).csSup_eq (Set.nonempty_image_iff.mpr A_nonemp)).symm
  · exact isLUB_csSup A_nonemp A_bdd
  · exact tendsto_nhdsWithin_of_tendsto_nhds Cf

theorem Monotone.map_sInf_of_continuousAt'' {f : R → S} {A : Set R} (Cf : ContinuousAt f (sInf A))
    (Mf : Monotone f) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A) :
    f (sInf A) = sInf (f '' A) :=
  @Monotone.map_sSup_of_continuousAt'' Rᵒᵈ Sᵒᵈ _ _ _ _ _ _ f A Cf Mf.dual A_nonemp A_bdd

theorem Antitone.map_sInf_of_continuousAt'' {f : R → S} {A : Set R} (Cf : ContinuousAt f (sInf A))
    (Af : Antitone f) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A) :
    f (sInf A) = sSup (f '' A) :=
  @Monotone.map_sInf_of_continuousAt'' R Sᵒᵈ _ _ _ _ _ _ f A Cf Af.dual_right A_nonemp A_bdd

theorem Antitone.map_sSup_of_continuousAt'' {f : R → S} {A : Set R} (Cf : ContinuousAt f (sSup A))
    (Af : Antitone f) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A) :
    f (sSup A) = sInf (f '' A) :=
  @Monotone.map_sSup_of_continuousAt'' R Sᵒᵈ _ _ _ _ _ _ f A Cf Af.dual_right A_nonemp A_bdd

#check Filter.IsBounded.isCobounded_flip

-- NOTE: Missing from Mathlib? Probably not, but what is the name...?
lemma Monotone.isCoboundedUnder_ge [Preorder X] [Preorder Y] {f : X → Y} (hf : Monotone f) {u : ι → X}
    (F : Filter ι) [NeBot F] (bdd : F.IsBoundedUnder (· ≤ ·) u) :
    F.IsCoboundedUnder (· ≥ ·) (f ∘ u) := by
  --refine Filter.IsBounded.isCobounded_flip ?_
  obtain ⟨b, hb⟩ := bdd
  refine ⟨f b, fun y hy ↦ ?_⟩
  have obs : ∀ᶠ _ in map u F, y ≤ f b := by
    filter_upwards [hb, Filter.map_compose.symm ▸ hy] with x h₁ h₂ using h₂.trans (hf h₁)
  exact eventually_const.mp obs

-- NOTE: Missing from Mathlib? Probably not, but what is the name...?
lemma Monotone.isCoboundedUnder_le [Preorder X] [Preorder Y] {f : X → Y} (hf : Monotone f) {u : ι → X}
    (F : Filter ι) [NeBot F] (bdd : F.IsBoundedUnder (· ≥ ·) u) :
    F.IsCoboundedUnder (· ≤ ·) (f ∘ u) :=
  @Monotone.isCoboundedUnder_ge ι Xᵒᵈ Yᵒᵈ _ _ f hf.dual u F _ bdd

-- NOTE: Missing from Mathlib? Probably not, but what is the name...?
lemma Antitone.isCoboundedUnder_le [Preorder X] [Preorder Y] {f : X → Y} (hf : Antitone f) {u : ι → X}
    (F : Filter ι) [NeBot F] (bdd : F.IsBoundedUnder (· ≤ ·) u) :
    F.IsCoboundedUnder (· ≤ ·) (f ∘ u) :=
  @Monotone.isCoboundedUnder_ge ι X Yᵒᵈ _ _ f hf u F _ bdd

-- NOTE: Missing from Mathlib? Probably not, but what is the name...?
lemma Antitone.isCoboundedUnder_ge [Preorder X] [Preorder Y] {f : X → Y} (hf : Antitone f) {u : ι → X}
    (F : Filter ι) [NeBot F] (bdd : F.IsBoundedUnder (· ≥ ·) u) :
    F.IsCoboundedUnder (· ≥ ·) (f ∘ u) :=
  @Monotone.isCoboundedUnder_le ι X Yᵒᵈ _ _ f hf u F _ bdd

-- NOTE: Missing from Mathlib?
-- What would be a good generality? (Mixes order and metric, so typeclasses don't readily exist.)
lemma Filter.isBounded_le_map_of_bounded_range (F : Filter ι) {f : ι → ℝ}
    (h : Metric.Bounded (Set.range f)) :
    (F.map f).IsBounded (· ≤ ·) := by
  sorry
  --rw [← Metric.bounded_iff_isBounded, Real.bounded_iff_bddBelow_bddAbove] at h
  --obtain ⟨c, hc⟩ := h.2
  --apply isBoundedUnder_of
  --use c
  --simpa [mem_upperBounds] using hc

lemma Filter.isBounded_ge_map_of_bounded_range (F : Filter ι) {f : ι → ℝ}
    (h : Metric.Bounded (Set.range f)) :
    (F.map f).IsBounded (· ≥ ·) := by sorry

-- NOTE: Missing from Mathlib?
-- What would be a good generality? (Mixes order and metric, so typeclasses don't readily exist.)
lemma Filter.isBounded_le_map_of_isBounded_range (F : Filter ι) {f : ι → ℝ}
    (h : Bornology.IsBounded (Set.range f)) :
    (F.map f).IsBounded (· ≤ ·) := by
  rw [← Metric.bounded_iff_isBounded, Real.bounded_iff_bddBelow_bddAbove] at h
  obtain ⟨c, hc⟩ := h.2
  apply isBoundedUnder_of
  use c
  simpa [mem_upperBounds] using hc

-- NOTE: Missing from Mathlib? What would be a good generality?
lemma Filter.isBounded_ge_map_of_isBounded_range (F : Filter ι) {f : ι → ℝ}
    (h : Bornology.IsBounded (Set.range f)) :
    (F.map f).IsBounded (· ≥ ·) := by
  rw [← Metric.bounded_iff_isBounded, Real.bounded_iff_bddBelow_bddAbove] at h
  obtain ⟨c, hc⟩ := h.1
  apply isBoundedUnder_of
  use c
  simpa [mem_lowerBounds] using hc

#check Antitone.map_limsSup_of_continuousAt

-- NOTE: This was the key lemma to generalize.
/-- An antitone function between conditionally complete linear ordered spaces sends
a `Filter.limsSup` to the `Filter.liminf` of the image if it is continuous at the `limsSup`. -/
theorem Antitone.map_limsSup_of_continuousAt' {F : Filter R} [NeBot F] {f : R → S}
    (bdd_above : F.IsBounded (· ≤ ·)) (bdd_below : F.IsBounded (· ≥ ·))
    (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsSup) : f F.limsSup = F.liminf f := by
  have cobdd : F.IsCobounded (· ≤ ·) := bdd_below.isCobounded_flip
  apply le_antisymm
  · rw [limsSup, f_decr.map_sInf_of_continuousAt'' f_cont bdd_above cobdd]
    apply le_of_forall_lt
    intro c hc
    simp only [liminf, limsInf, eventually_map] at hc ⊢
    obtain ⟨d, hd, h'd⟩ := exists_lt_of_lt_csSup ((@Set.nonempty_image_iff R S f _).mpr bdd_above) hc
    apply lt_csSup_of_lt ?_ ?_ h'd
    · exact f_decr.isCoboundedUnder_ge F bdd_below
    · rcases hd with ⟨e, ⟨he, fe_eq_d⟩⟩
      filter_upwards [he] with x hx using (fe_eq_d.symm ▸ f_decr hx)
  · by_cases h' : ∃ c, c < F.limsSup ∧ Set.Ioo c F.limsSup = ∅
    · rcases h' with ⟨c, c_lt, hc⟩
      have B : ∃ᶠ n in F, F.limsSup ≤ n := by
        apply (frequently_lt_of_lt_limsSup cobdd c_lt).mono
        intro x hx
        by_contra'
        have : (Set.Ioo c F.limsSup).Nonempty := ⟨x, ⟨hx, this⟩⟩
        simp only [hc, Set.not_nonempty_empty] at this
      apply @liminf_le_of_frequently_le R S _ F f (f (limsSup F)) (B.mono fun x hx ↦ f_decr hx) ?_
      obtain ⟨b, hb⟩ := bdd_above
      use f b
      simp only [ge_iff_le, eventually_map]
      filter_upwards [hb] with t ht using f_decr ht
    simp only [gt_iff_lt, not_lt, ge_iff_le, not_exists, not_and] at h'
    by_contra' H
    obtain ⟨l, l_lt, h'l⟩ : ∃ l < F.limsSup, Set.Ioc l F.limsSup ⊆ { x : R | f x < F.liminf f }
    · apply exists_Ioc_subset_of_mem_nhds ((tendsto_order.1 f_cont.tendsto).2 _ H)
      by_contra con
      simp only [not_exists, not_lt] at con
      simpa only [lt_self_iff_false] using lt_of_le_of_lt
        (@liminf_le_of_frequently_le R S _ F f (f (limsSup F))
          (frequently_of_forall (fun r ↦ f_decr (con r))) (bdd_above.isBoundedUnder f_decr)) H
    obtain ⟨m, l_m, m_lt⟩ : (Set.Ioo l F.limsSup).Nonempty := by
      contrapose! h'
      refine' ⟨l, l_lt, by rwa [Set.not_nonempty_iff_eq_empty] at h'⟩
    have B : F.liminf f ≤ f m := by
      apply @liminf_le_of_frequently_le R S _ F f (f m)
      · apply (frequently_lt_of_lt_limsSup cobdd m_lt).mono
        exact fun x hx ↦ f_decr hx.le
      · exact IsBounded.isBoundedUnder f_decr bdd_above
    have I : f m < F.liminf f := h'l ⟨l_m, m_lt.le⟩
    exact lt_irrefl _ (B.trans_lt I)

theorem Antitone.map_limsInf_of_continuousAt' {F : Filter R} [NeBot F] {f : R → S}
    (bdd_above : F.IsBoundedUnder (· ≤ ·) id) (bdd_below : F.IsBoundedUnder (· ≥ ·) id)
    (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsInf) : f F.limsInf = F.limsup f :=
  @Antitone.map_limsSup_of_continuousAt' Rᵒᵈ Sᵒᵈ _ _ _ _ _ _ F _ f
    bdd_below bdd_above f_decr.dual f_cont

theorem Monotone.map_limsSup_of_continuousAt' {F : Filter R} [NeBot F] {f : R → S}
    (bdd_above : F.IsBoundedUnder (· ≤ ·) id) (bdd_below : F.IsBoundedUnder (· ≥ ·) id)
    (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsSup) : f F.limsSup = F.limsup f :=
  @Antitone.map_limsSup_of_continuousAt' R Sᵒᵈ _ _ _ _ _ _ F _ f
    bdd_above bdd_below f_incr f_cont

theorem Monotone.map_limsInf_of_continuousAt' {F : Filter R} [NeBot F] {f : R → S}
    (bdd_above : F.IsBoundedUnder (· ≤ ·) id) (bdd_below : F.IsBoundedUnder (· ≥ ·) id)
    (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsInf) : f F.limsInf = F.liminf f :=
  @Antitone.map_limsSup_of_continuousAt' Rᵒᵈ S _ _ _ _ _ _ F _ f
    bdd_below bdd_above f_incr.dual f_cont

lemma limsup_add_const (F : Filter ι) [NeBot F] (f : ι → ℝ) (c : ℝ)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.limsup (fun i ↦ f i + c) F = Filter.limsup f F + c := by
  have key := @Monotone.map_limsSup_of_continuousAt' ℝ ℝ _ _ _ _ _ _ (F.map f) _ (fun x ↦ x + c) bdd_above bdd_below ?_ ?_
  simp only at key
  convert key.symm
  · intro x y hxy
    simp only [add_le_add_iff_right, hxy]
  · exact (continuous_add_right c).continuousAt

lemma liminf_add_const (F : Filter ι) [NeBot F] (f : ι → ℝ) (c : ℝ)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ f i + c) F = Filter.liminf f F + c := by
  have key := @Monotone.map_limsInf_of_continuousAt' ℝ ℝ _ _ _ _ _ _ (F.map f) _ (fun x ↦ x + c) bdd_above bdd_below ?_ ?_
  simp only at key
  convert key.symm
  · intro x y hxy
    simp only [add_le_add_iff_right, hxy]
  · exact (continuous_add_right c).continuousAt

lemma limsup_const_sub (F : Filter ι) [NeBot F] (f : ι → ℝ) (c : ℝ)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.limsup (fun i ↦ c - f i ) F = c - Filter.liminf f F := by
  have key := @Antitone.map_limsInf_of_continuousAt' ℝ ℝ _ _ _ _ _ _ (F.map f) _ (fun x ↦ c - x) bdd_above bdd_below ?_ ?_
  simp only at key
  convert key.symm
  · intro x y hxy
    simp only [sub_le_sub_iff_left, hxy]
  · exact (continuous_sub_left c).continuousAt

lemma liminf_const_sub (F : Filter ι) [NeBot F] (f : ι → ℝ) (c : ℝ)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ c - f i ) F = c - Filter.limsup f F := by
  have key := @Antitone.map_limsSup_of_continuousAt' ℝ ℝ _ _ _ _ _ _ (F.map f) _ (fun x ↦ c - x) bdd_above bdd_below ?_ ?_
  simp only at key
  convert key.symm
  · intro x y hxy
    simp only [sub_le_sub_iff_left, hxy]
  · exact (continuous_sub_left c).continuousAt

end liminf_lemma



section boundedness_by_norm_bounds

-- TODO: Should use `Metric.Bounded`
#check Metric.Bounded
#check Metric.bounded_closedBall
#check Metric.bounded_ball

-- NOTE: Should this be in Mathlib?
lemma Metric.bounded_range_of_forall_norm_le [NormedAddGroup E]
    (f : ι → E) (c : ℝ) (h : ∀ i, ‖f i‖ ≤ c) :
    Metric.Bounded (Set.range f) := by
  apply Metric.Bounded.mono _ (@Metric.bounded_closedBall _ _ 0 c)
  intro x ⟨i, hi⟩
  simpa only [← hi, Metric.closedBall, dist_zero_right, Set.mem_setOf_eq, ge_iff_le] using h i

/-
-- NOTE: Can this really be missing from Mathlib?
lemma Metric.isBounded_closedBall [PseudoMetricSpace X] (z : X) (r : ℝ) :
    Bornology.IsBounded (Metric.closedBall z r) := by
  rw [Metric.isBounded_iff]
  use 2 * r
  intro x hx y hy
  simp only [closedBall, Set.mem_setOf_eq] at hx hy
  calc  dist x y
    _ ≤ dist x z + dist z y     := dist_triangle x z y
    _ = dist x z + dist y z     := by rw [dist_comm z y]
    _ ≤ r + r                   := by gcongr
    _ = 2 * r                   := by ring

-- NOTE: Can this really be missing from Mathlib?
lemma Metric.isBounded_ball [PseudoMetricSpace X] (z : X) (r : ℝ) :
    Bornology.IsBounded (Metric.ball z r) :=
  (Metric.isBounded_closedBall z r).subset ball_subset_closedBall

-- NOTE: Should this be in Mathlib?
lemma isBounded_range_of_forall_norm_le [NormedAddGroup E] (f : ι → E) (c : ℝ) (h : ∀ i, ‖f i‖ ≤ c) :
    Bornology.IsBounded (Set.range f) := by
  apply (Metric.isBounded_closedBall 0 c).subset
  intro x ⟨i, hi⟩
  simpa only [← hi, Metric.closedBall, dist_zero_right, Set.mem_setOf_eq, gt_iff_lt] using h i
 -/

end boundedness_by_norm_bounds



section layercake_for_integral

-- TODO: Generalize from ℝ to the usual type classes.
-- NOTE: This is currently a mess, because of mixing Measurable and AEStronglyMeasurable.
lemma Integrable.measure_pos_le_norm_lt_top [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {f : α → ℝ} --(f_nn : 0 ≤ f)
    (f_intble : Integrable f μ)
    {t : ℝ} (t_pos : 0 < t) :
    μ {a : α | t ≤ ‖f a‖} < ∞ := by
  have f_aemble := f_intble.1.aemeasurable
  have norm_f_aemble : AEMeasurable (fun a ↦ ENNReal.ofReal ‖f a‖) μ := by
    --have := ENNReal.measurable_ofReal.comp (@measurable_norm ℝ _ _ _)
    exact (ENNReal.measurable_ofReal.comp measurable_norm).comp_aemeasurable f_aemble
  obtain ⟨g, ⟨g_mble, ⟨g_nn, aeeq_g⟩⟩⟩ := @AEMeasurable.exists_measurable_nonneg α _ μ ℝ≥0∞ _ _ _ _
    norm_f_aemble (eventually_of_forall (fun x ↦ zero_le _))
  have foo : MeasurableSet {a : α | ENNReal.ofReal t < g a} := by
    sorry
  -- TODO: Generalize `lintegral_indicator_const` to null-measurable sets so there is no need
  -- to use g instead of f. (Have already `lintegral_indicator₀` so easy!)
  have aux := @lintegral_indicator_const _ _ μ _ foo (ENNReal.ofReal t)
  have markov := @mul_meas_ge_le_lintegral₀ α _ μ
                  (fun a ↦ ENNReal.ofReal ‖f a‖) norm_f_aemble (ENNReal.ofReal t)
  have same : ∀ a, ENNReal.ofReal t ≤ ENNReal.ofReal ‖f a‖ ↔ t ≤ ‖f a‖ := by sorry
  have also : ∫⁻ (a : α), ENNReal.ofReal ‖f a‖ ∂μ = ∫⁻ (a : α), ‖f a‖₊ ∂μ := by
    apply lintegral_congr
    intro x
    sorry
  simp_rw [same, also] at markov
  have almost := lt_of_le_of_lt markov f_intble.2
  have t_inv_ne_top : (ENNReal.ofReal t)⁻¹ ≠ ∞ := by
    exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr t_pos).ne.symm
  convert ENNReal.mul_lt_top t_inv_ne_top almost.ne
  simp [← mul_assoc,
        ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr t_pos).ne.symm ENNReal.ofReal_ne_top]

lemma Integrable.measure_pos_lt_norm_lt_top [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {f : α → ℝ} (f_intble : Integrable f μ) {t : ℝ} (t_pos : 0 < t) :
    μ {a : α | t < ‖f a‖} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ h ↦ (Set.mem_setOf_eq ▸ h).le))
    (Integrable.measure_pos_le_norm_lt_top f_intble t_pos)

lemma Integrable.measure_pos_le_lt_top [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {f : α → ℝ} (f_intble : Integrable f μ) {t : ℝ} (t_pos : 0 < t) :
    μ {a : α | t ≤ f a} < ∞ := by
  -- Need to do separately positive and negative parts?
  sorry

lemma Integrable.measure_pos_lt_lt_top [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {f : α → ℝ} (f_intble : Integrable f μ) {t : ℝ} (t_pos : 0 < t) :
    μ {a : α | t < f a} < ∞ := by
  apply lt_of_le_of_lt (measure_mono ?_) (Integrable.measure_pos_le_lt_top f_intble t_pos)
  exact fun x hx ↦ (Set.mem_setOf_eq ▸ hx).le

-- NOTE: This is a version of the basic "Layercake formula" for real-valued nonnegative integrands
-- and Bochner integral ∫ instead of ∫⁻. I don't know if the other (more general) versions of
-- layercake should be similarly generalized. The proofs are basically similar, but the statements
-- themselves become a bit unpleasant due to integrability requirements for something slightly
-- complicated.
-- TODO: Should remove `Measurable` assumption and just embrace the `AEStronglyMeasurable`
-- which comes from `Integrable`. This is not pleasant in the proof, but pays off for the user...
theorem integral_eq_integral_meas_lt [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    {f : α → ℝ} (f_nn : 0 ≤ f) (f_mble : Measurable f) (f_intble : Integrable f μ) :
    (∫ ω, f ω ∂μ) = ∫ t in Set.Ioi 0, ENNReal.toReal (μ {a : α | t < f a}) := by
  have key := lintegral_eq_lintegral_meas_lt μ f_nn f_mble -- should use `Integrable`
  have lhs_finite : ∫⁻ (ω : α), ENNReal.ofReal (f ω) ∂μ < ∞ := Integrable.lintegral_lt_top f_intble
  have rhs_finite : ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a} < ∞ := by simp only [← key, lhs_finite]
  have rhs_integrand_decr : Antitone (fun t ↦ (μ {a : α | t < f a})) :=
    fun _ _ hst ↦ measure_mono (fun _ h ↦ lt_of_le_of_lt hst h)
  have rhs_integrand_finite : ∀ (t : ℝ), t > 0 → μ {a | t < f a} < ∞ := by
    exact fun t ht ↦ Integrable.measure_pos_lt_lt_top f_intble ht
  convert (ENNReal.toReal_eq_toReal lhs_finite.ne rhs_finite.ne).mpr key
  · refine integral_eq_lintegral_of_nonneg_ae ?_ ?_
    · -- TODO: Maybe should relax the assumption to ae nonnegativity.
      exact eventually_of_forall f_nn
    · --exact f_mble.aestronglyMeasurable
      exact f_intble.aestronglyMeasurable
  · have aux := @integral_eq_lintegral_of_nonneg_ae _ _ ((volume : Measure ℝ).restrict (Set.Ioi 0))
      (fun t ↦ ENNReal.toReal (μ {a : α | t < f a})) ?_ ?_
    · rw [aux]
      apply congrArg ENNReal.toReal
      apply set_lintegral_congr_fun measurableSet_Ioi
      apply eventually_of_forall
      exact fun t t_pos ↦ ENNReal.ofReal_toReal (rhs_integrand_finite t t_pos).ne
    · exact eventually_of_forall (fun x ↦ by simp only [Pi.zero_apply, ENNReal.toReal_nonneg])
    · apply Measurable.aestronglyMeasurable
      refine Measurable.ennreal_toReal ?_
      apply Antitone.measurable
      exact rhs_integrand_decr

end layercake_for_integral



section le_liminf_open_implies_convergence

variable {Ω : Type} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
/-
-- TODO: Is it possible to add a @[gcongr] attribute to `lintegral_mono`?

attribute [gcongr] lintegral_mono -- @[gcongr] attribute only applies to lemmas proving x₁ ~₁ x₁' → ... xₙ ~ₙ xₙ' → f x₁ ... xₙ ∼ f x₁' ... xₙ', got ∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} ⦃f g : α → ℝ≥0∞⦄, f ≤ g → ∫⁻ (a : α), f a ∂μ ≤ ∫⁻ (a : α), g a ∂μ

lemma foo (μ : Measure Ω) {f g : Ω → ℝ≥0∞} (hfg : f ≤ g) :
    ∫⁻ ω, f ω ∂μ ≤ ∫⁻ ω, g ω ∂μ := by
  gcongr -- gcongr did not make progress
  sorry

-- This would solve it!

lemma MeasureTheory.lintegral_mono'' {α : Type} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f g : α → ℝ≥0∞}
  (hfg : f ≤ g) : lintegral μ f ≤ lintegral μ g := by sorry

#check lintegral_mono''

attribute [gcongr] lintegral_mono'' -- @[gcongr] attribute only applies to lemmas proving x₁ ~₁ x₁' → ... xₙ ~ₙ xₙ' → f x₁ ... xₙ ∼ f x₁' ... xₙ', got ∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} ⦃f g : α → ℝ≥0∞⦄, f ≤ g → ∫⁻ (a : α), f a ∂μ ≤ ∫⁻ (a : α), g a ∂μ
 -/

-- NOTE: I think I will work with real-valued integrals, after all...
lemma fatou_argument_lintegral
    {μ : Measure Ω} [SigmaFinite μ] {μs : ℕ → Measure Ω} [∀ i, SigmaFinite (μs i)]
    {f : Ω → ℝ} (f_cont : Continuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂ (μs i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ f_nn f_cont.measurable]
  calc  ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, atTop.liminf (fun i ↦ (μs i) {a | t < f a})
            := (lintegral_mono (fun t ↦ h_opens _ (continuous_def.mp f_cont _ isOpen_Ioi))).trans ?_
    _ ≤ atTop.liminf (fun i ↦ ∫⁻ (t : ℝ) in Set.Ioi 0, (μs i) {a | t < f a})
            := lintegral_liminf_le (fun n ↦ Antitone.measurable
                (fun s t hst ↦ measure_mono (fun ω hω ↦ lt_of_le_of_lt hst hω)))
  rfl

-- NOTE: I think this is the version I prefer to use, after all...
lemma fatou_argument_integral_nonneg
    {μ : Measure Ω} [IsFiniteMeasure μ] {μs : ℕ → Measure Ω} [∀ i, IsFiniteMeasure (μs i)]
    {f : Ω →ᵇ ℝ} (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
      ∫ x, (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)) := by
  sorry

-- NOTE: Maybe there should be a file for lemmas about integrals of `BoundedContinuousFunction`s?
lemma BoundedContinuousFunction.integrable (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω →ᵇ ℝ) :
    Integrable f μ := by
  refine ⟨f.continuous.measurable.aestronglyMeasurable, ?_⟩
  simp [HasFiniteIntegral]
  calc  ∫⁻ x, ‖f x‖₊ ∂μ
    _ ≤ ∫⁻ _, ‖f‖₊ ∂μ                       := ?_
    _ = ‖f‖₊ * (μ Set.univ)                 := by rw [lintegral_const]
    _ < ∞                                   := ENNReal.mul_lt_top
                                                ENNReal.coe_ne_top (measure_ne_top μ Set.univ)
  · apply lintegral_mono
    exact fun x ↦ ENNReal.coe_le_coe.mpr (nnnorm_coe_le_nnnorm f x)

-- NOTE: Maybe there should be a file for lemmas about integrals of `BoundedContinuousFunction`s?
lemma BoundedContinuousFunction.norm_integral_le_mul_norm_of_isFiniteMeasure
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω →ᵇ ℝ) :
    ‖∫ x, (f x) ∂μ‖ ≤ ENNReal.toReal (μ Set.univ) * ‖f‖ := by
  calc  ‖∫ x, (f x) ∂μ‖
    _ ≤ ∫ x, ‖f x‖ ∂μ                       := by exact norm_integral_le_integral_norm _
    _ ≤ ∫ _, ‖f‖ ∂μ                         := ?_
    _ = ENNReal.toReal (μ Set.univ) • ‖f‖   := by rw [integral_const]
  · apply integral_mono _ (integrable_const ‖f‖) (fun x ↦ f.norm_coe_le_norm x)
    exact (integrable_norm_iff f.continuous.measurable.aestronglyMeasurable).mpr (f.integrable μ)

-- NOTE: Maybe there should be a file for lemmas about integrals of `BoundedContinuousFunction`s?
lemma BoundedContinuousFunction.norm_integral_le_norm_of_isProbabilityMeasure
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω →ᵇ ℝ) :
    ‖∫ x, (f x) ∂μ‖ ≤ ‖f‖ := by
  convert f.norm_integral_le_mul_norm_of_isFiniteMeasure μ
  simp only [measure_univ, ENNReal.one_toReal, one_mul]

-- NOTE: Maybe there should be a file for lemmas about integrals of `BoundedContinuousFunction`s?
-- TODO: Should this be generalized to functions with values in Banach spaces?
lemma bounded_range_integral_boundedContinuousFunction_of_isProbabilityMeasure
    (μs : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μs i)] (f : Ω →ᵇ ℝ) :
    Metric.Bounded (Set.range (fun i ↦ ∫ x, (f x) ∂ (μs i))) := by
  apply Metric.bounded_range_of_forall_norm_le _ ‖f‖
  exact fun i ↦ f.norm_integral_le_norm_of_isProbabilityMeasure (μs i)

/-
-- NOTE: Maybe there should be a file for lemmas about integrals of `BoundedContinuousFunction`s?
-- TODO: Should this be generalized to functions with values in Banach spaces?
lemma isBounded_range_integral_boundedContinuousFunction_of_isProbabilityMeasure'
    (μs : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μs i)] (f : Ω →ᵇ ℝ) :
    Bornology.IsBounded (Set.range (fun i ↦ ∫ x, (f x) ∂ (μs i))) := by
  --apply isBounded_range_of_forall_norm_le _ ‖f‖
  --exact fun i ↦ f.norm_integral_le_norm_of_isProbabilityMeasure (μs i)
  sorry
 -/

lemma main_thing'
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μs : ℕ → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    {f : Ω → ℝ} (f_cont : Continuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂ (μs i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ f_nn f_cont.measurable]
  have obs : ∀ t, IsOpen {a : Ω | t < f a} := fun t ↦ (continuous_def.mp f_cont) _ isOpen_Ioi
  apply (lintegral_mono (fun t ↦ h_opens _ (obs t))).trans
  refine lintegral_liminf_le ?_
  refine fun i ↦ Antitone.measurable (fun s t hst ↦ measure_mono ?_)
  intro ω hω
  simp only [Set.mem_setOf_eq] at *
  linarith

lemma main_thing
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μs : ℕ → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    {f : Ω → ℝ} (f_cont : Continuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
      ∫ x, (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)) := by
  sorry

-- NOTE: Maybe there should be a file for lemmas about integrals of `BoundedContinuousFunction`s?
lemma BoundedContinuousFunction.neg_norm_le [TopologicalSpace X] (f : X →ᵇ ℝ) (x : X) :
    -‖f‖ ≤ f x := by
  exact (abs_le.mp (norm_coe_le_norm f x)).1

-- NOTE: Maybe there should be a file for lemmas about integrals of `BoundedContinuousFunction`s?
lemma BoundedContinuousFunction.le_norm [TopologicalSpace X] (f : X →ᵇ ℝ) (x : X):
    f x ≤ ‖f‖ := by
  exact (abs_le.mp (norm_coe_le_norm f x)).2

-- NOTE: Where should such things be placed? In the `Portmanteau`-file only?
lemma BoundedContinuousFunction.add_norm_nonneg [TopologicalSpace X] (f : X →ᵇ ℝ) :
    0 ≤ f + BoundedContinuousFunction.const _ ‖f‖ := by
  intro x
  dsimp
  linarith [(abs_le.mp (norm_coe_le_norm f x)).1]

-- NOTE: Where should such things be placed? In the `Portmanteau`-file only?
lemma BoundedContinuousFunction.norm_sub_nonneg [TopologicalSpace X] (f : X →ᵇ ℝ) :
    0 ≤ BoundedContinuousFunction.const _ ‖f‖ - f := by
  intro x
  dsimp
  linarith [(abs_le.mp (norm_coe_le_norm f x)).2]

-- NOTE: Maybe there should be a file for lemmas about integrals of `BoundedContinuousFunction`s?
lemma BoundedContinuousFunction.integral_add_const {μ : Measure Ω} [IsFiniteMeasure μ]
    (f : Ω →ᵇ ℝ) (c : ℝ) :
    ∫ x, (f + BoundedContinuousFunction.const Ω c) x ∂μ =
      ∫ x, f x ∂μ + ENNReal.toReal (μ (Set.univ)) • c := by
  simp only [coe_add, const_toFun, Pi.add_apply, smul_eq_mul]
  simp_rw [integral_add (FiniteMeasure.integrable_of_boundedContinuous_to_real _ f)
                        (integrable_const c)]
  simp only [integral_const, smul_eq_mul]

-- NOTE: Maybe there should be a file for lemmas about integrals of `BoundedContinuousFunction`s?
lemma BoundedContinuousFunction.integral_const_sub {μ : Measure Ω} [IsFiniteMeasure μ]
    (f : Ω →ᵇ ℝ) (c : ℝ) :
    ∫ x, (BoundedContinuousFunction.const Ω c - f) x ∂μ =
      ENNReal.toReal (μ (Set.univ)) • c - ∫ x, f x ∂μ := by
  simp only [coe_sub, const_toFun, Pi.sub_apply, smul_eq_mul]
  simp_rw [integral_sub (integrable_const c)
           (FiniteMeasure.integrable_of_boundedContinuous_to_real _ f)]
  simp only [integral_const, smul_eq_mul]

lemma reduction_to_liminf {ι : Type} {L : Filter ι} [NeBot L]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μs : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    (h : ∀ f : Ω →ᵇ ℝ, 0 ≤ f → ∫ x, (f x) ∂μ ≤ L.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)))
    (f : Ω →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ x, (f x) ∂ (μs i)) L (𝓝 (∫ x, (f x) ∂μ)) := by
  have obs := bounded_range_integral_boundedContinuousFunction_of_isProbabilityMeasure μs f
  have bdd_above : IsBoundedUnder (· ≤ ·) L (fun i ↦ ∫ (x : Ω), f x ∂μs i) := by
    apply isBounded_le_map_of_bounded_range
    apply bounded_range_integral_boundedContinuousFunction_of_isProbabilityMeasure
  have bdd_below : IsBoundedUnder (· ≥ ·) L (fun i ↦ ∫ (x : Ω), f x ∂μs i) := by
    apply isBounded_ge_map_of_bounded_range
    apply bounded_range_integral_boundedContinuousFunction_of_isProbabilityMeasure
  apply @tendsto_of_le_liminf_of_limsup_le ℝ ι _ _ _ L (fun i ↦ ∫ x, (f x) ∂ (μs i)) (∫ x, (f x) ∂μ)
  · have key := h _ (f.add_norm_nonneg)
    simp_rw [f.integral_add_const ‖f‖] at key
    simp only [measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul] at key
    -- TODO: Should the case of ⊥ filter be treated separately and not included as an assumption?
    have := liminf_add_const L (fun i ↦ ∫ x, (f x) ∂ (μs i)) ‖f‖ bdd_above bdd_below
    rwa [this, add_le_add_iff_right] at key
  · have key := h _ (f.norm_sub_nonneg)
    simp_rw [f.integral_const_sub ‖f‖] at key
    simp only [measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul] at key
    have := liminf_const_sub L (fun i ↦ ∫ x, (f x) ∂ (μs i)) ‖f‖ bdd_above bdd_below
    rwa [this, sub_le_sub_iff_left] at key
  · exact L.isBounded_le_map_of_bounded_range obs
  · exact L.isBounded_ge_map_of_bounded_range obs

/-- A characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function converge to the integral of the function
against the limit measure. -/
lemma ProbabilityMeasure.tendsto_iff_forall_nonneg_integral_tendsto {γ : Type _} {F : Filter γ}
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ, 0 ≤ f →
        Tendsto (fun i ↦ ∫ ω, (f ω) ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, (f ω) ∂(μ : Measure Ω))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  refine ⟨fun h f _ ↦ h f, fun h f ↦ ?_⟩
  set g := f + BoundedContinuousFunction.const _ ‖f‖ with g_def
  have fx_eq : ∀ x, f x = g x - ‖f‖ := by
    intro x
    simp only [BoundedContinuousFunction.coe_add, BoundedContinuousFunction.const_toFun, Pi.add_apply,
               add_sub_cancel]
  have key := h g (f.add_norm_nonneg)
  simp [g_def] at key
  simp_rw [integral_add (FiniteMeasure.integrable_of_boundedContinuous_to_real _ f)
                        (integrable_const ‖f‖)] at key
  simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul] at key
  simp_rw [fx_eq]
  convert tendsto_add.comp (Tendsto.prod_mk_nhds key (@tendsto_const_nhds _ _ _ (-‖f‖) F)) <;> simp

theorem le_liminf_open_implies_convergence
  {μ : ProbabilityMeasure Ω} {μs : ℕ → ProbabilityMeasure Ω}
  (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    atTop.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  refine ProbabilityMeasure.tendsto_iff_forall_nonneg_integral_tendsto.mpr ?_
  intro g g_nn
  apply reduction_to_liminf
  intro f f_nn
  have f_nn' : 0 ≤ (f : Ω → ℝ) := fun x ↦ by simpa using f_nn x
  apply main_thing f.continuous f_nn'
  -- Annoying coercions to reduce to `h_opens`...
  sorry

end le_liminf_open_implies_convergence
