import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Tactic

/-!
# Outline of portmanteau implication: liminf condition for open sets implies weak convergence

This file contains steps needed to prove the portmanteau implication
`le_liminf_open_implies_convergence`. Some intermediate steps need to be generalized
and cleaned up, and are to be placed in appropriate files. The main part should go
to the file `Mathlib.MeasureTheory.Measure.Portmanteau`.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction Topology


section yet_another_map_liminf_lemma

variable {ι R S : Type*} {F : Filter ι} [NeBot F]
  [ConditionallyCompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R]
  [ConditionallyCompleteLinearOrder S] [TopologicalSpace S] [OrderTopology S]

--#check Antitone.map_sInf_of_continuousAt'

/-- A function that is continuous at the supremum of a nonempty set and monotone on the set
sends this supremum to the supremum of the image of this set. -/
theorem MonotoneOn.map_sSup_of_continuousAt' {α β : Type*}
  [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]
  {f : α → β} {A A' : Set α} (hA : A ⊆ A') (Cf : ContinuousAt f (sSup A))
  (Mf : MonotoneOn f A') (A_nonemp : A.Nonempty) (A_bdd : BddAbove A := by bddDefault) :
    f (sSup A) = sSup (f '' A) :=
  --This is a particular case of the more general `IsLUB.isLUB_of_tendsto`
  .symm <| ((isLUB_csSup A_nonemp A_bdd).isLUB_of_tendsto (Mf.mono hA) A_nonemp <|
    Cf.mono_left inf_le_left).csSup_eq (A_nonemp.image f)

/-- A function that is continuous at the supremum of a nonempty set and monotone on the set
sends this supremum to the supremum of the image of this set. -/
theorem AntitoneOn.map_sInf_of_continuousAt' {α β : Type*}
  [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]
  {f : α → β} {A A' : Set α} (hA : A ⊆ A') (Cf : ContinuousAt f (sInf A))
  (Af : AntitoneOn f A') (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sSup (f '' A) := by
  sorry

theorem AntitoneOn.map_limsSup_of_continuousAt₀ {F : Filter R} [NeBot F] {f : R → S}
    {R' : Set R} (f_decr : AntitoneOn f R') (f_cont : ContinuousAt f F.limsSup)
    (hF : F ≤ Filter.principal R')
    (bdd_above : F.IsBounded (· ≤ ·) := by isBoundedDefault)
    (bdd_below : F.IsBounded (· ≥ ·) := by isBoundedDefault) :
    f F.limsSup = F.liminf f := by
  --simp only [le_principal_iff] at hF
  sorry

/-- An antitone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsSup` to the `Filter.liminf` of the image if the function is continuous at the `limsSup`
(and the filter is bounded from above and below). -/
theorem AntitoneOn.map_limsSup_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    {R' : Set R} (f_decr : AntitoneOn f R') (f_cont : ContinuousAt f F.limsSup)
    (hF : F ≤ Filter.principal R')
    (bdd_above : F.IsBounded (· ≤ ·) := by isBoundedDefault)
    (bdd_below : F.IsBounded (· ≥ ·) := by isBoundedDefault) :
    f F.limsSup = F.liminf f := by
  have cobdd : F.IsCobounded (· ≤ ·) := bdd_below.isCobounded_flip
  apply le_antisymm
  · rw [limsSup]
    have := @AntitoneOn.map_sInf_of_continuousAt' R S _ _ _ _ _ _ _ f
            {a | ∀ᶠ (n : R) in F, n ≤ a} R' _ f_cont f_decr bdd_above cobdd
    rw [this]
    --rw [limsSup, f_decr.map_sInf_of_continuousAt' f_cont bdd_above cobdd]
    apply le_of_forall_lt
    intro c hc
    simp only [liminf, limsInf, eventually_map] at hc ⊢
    obtain ⟨d, hd, h'd⟩ :=
      exists_lt_of_lt_csSup (bdd_above.recOn fun x hx ↦ ⟨f x, Set.mem_image_of_mem f hx⟩) hc
    apply lt_csSup_of_lt ?_ ?_ h'd
    · --exact (Antitone.isBoundedUnder_le_comp f_decr bdd_below).isCoboundedUnder_flip
      sorry
    · rcases hd with ⟨e, ⟨he, fe_eq_d⟩⟩
      filter_upwards [he] with x hx --using (fe_eq_d.symm ▸ f_decr hx)
      sorry
  · by_cases h' : ∃ c, c < F.limsSup ∧ Set.Ioo c F.limsSup = ∅
    · rcases h' with ⟨c, c_lt, hc⟩
      have B : ∃ᶠ n in F, F.limsSup ≤ n := by
        apply (frequently_lt_of_lt_limsSup cobdd c_lt).mono
        intro x hx
        by_contra'
        have : (Set.Ioo c F.limsSup).Nonempty := ⟨x, ⟨hx, this⟩⟩
        simp only [hc, Set.not_nonempty_empty] at this
      --apply liminf_le_of_frequently_le _ (bdd_above.isBoundedUnder f_decr)
      --exact (B.mono fun x hx ↦ f_decr hx)
      sorry
    push_neg at h'
    by_contra' H
    have not_bot : ¬ IsBot F.limsSup := fun maybe_bot ↦
      --lt_irrefl (F.liminf f) <| lt_of_le_of_lt
      --  (liminf_le_of_frequently_le (frequently_of_forall (fun r ↦ f_decr (maybe_bot r)))
      --    (bdd_above.isBoundedUnder f_decr)) H
      sorry
    obtain ⟨l, l_lt, h'l⟩ : ∃ l < F.limsSup, Set.Ioc l F.limsSup ⊆ { x : R | f x < F.liminf f }
    · apply exists_Ioc_subset_of_mem_nhds ((tendsto_order.1 f_cont.tendsto).2 _ H)
      simpa [IsBot] using not_bot
    obtain ⟨m, l_m, m_lt⟩ : (Set.Ioo l F.limsSup).Nonempty := by
      contrapose! h'
      refine' ⟨l, l_lt, by rwa [Set.not_nonempty_iff_eq_empty] at h'⟩
    have B : F.liminf f ≤ f m := by
      apply liminf_le_of_frequently_le _ _
      · apply (frequently_lt_of_lt_limsSup cobdd m_lt).mono
        --exact fun x hx ↦ f_decr hx.le
        sorry
      · --exact IsBounded.isBoundedUnder f_decr bdd_above
        sorry
    have I : f m < F.liminf f := h'l ⟨l_m, m_lt.le⟩
    exact lt_irrefl _ (B.trans_lt I)

/-
  have cobdd : F.IsCobounded (· ≤ ·) := bdd_below.isCobounded_flip
  apply le_antisymm
  · rw [limsSup, f_decr.map_sInf_of_continuousAt' f_cont bdd_above cobdd]
    apply le_of_forall_lt
    intro c hc
    simp only [liminf, limsInf, eventually_map] at hc ⊢
    obtain ⟨d, hd, h'd⟩ :=
      exists_lt_of_lt_csSup (bdd_above.recOn fun x hx ↦ ⟨f x, Set.mem_image_of_mem f hx⟩) hc
    apply lt_csSup_of_lt ?_ ?_ h'd
    · exact (Antitone.isBoundedUnder_le_comp f_decr bdd_below).isCoboundedUnder_flip
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
      apply liminf_le_of_frequently_le _ (bdd_above.isBoundedUnder f_decr)
      exact (B.mono fun x hx ↦ f_decr hx)
    push_neg at h'
    by_contra' H
    have not_bot : ¬ IsBot F.limsSup := fun maybe_bot ↦
      lt_irrefl (F.liminf f) <| lt_of_le_of_lt
        (liminf_le_of_frequently_le (frequently_of_forall (fun r ↦ f_decr (maybe_bot r)))
          (bdd_above.isBoundedUnder f_decr)) H
    obtain ⟨l, l_lt, h'l⟩ : ∃ l < F.limsSup, Set.Ioc l F.limsSup ⊆ { x : R | f x < F.liminf f }
    · apply exists_Ioc_subset_of_mem_nhds ((tendsto_order.1 f_cont.tendsto).2 _ H)
      simpa [IsBot] using not_bot
    obtain ⟨m, l_m, m_lt⟩ : (Set.Ioo l F.limsSup).Nonempty := by
      contrapose! h'
      refine' ⟨l, l_lt, by rwa [Set.not_nonempty_iff_eq_empty] at h'⟩
    have B : F.liminf f ≤ f m := by
      apply liminf_le_of_frequently_le _ _
      · apply (frequently_lt_of_lt_limsSup cobdd m_lt).mono
        exact fun x hx ↦ f_decr hx.le
      · exact IsBounded.isBoundedUnder f_decr bdd_above
    have I : f m < F.liminf f := h'l ⟨l_m, m_lt.le⟩
    exact lt_irrefl _ (B.trans_lt I)
 -/

theorem MonotoneOn.map_limsInf_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    {R' : Set R} (f_incr : MonotoneOn f R') (f_cont : ContinuousAt f F.limsInf)
    (hF : F ≤ Filter.principal R')
    (bdd_above : F.IsBounded (· ≤ ·) := by isBoundedDefault)
    (bdd_below : F.IsBounded (· ≥ ·) := by isBoundedDefault) :
    f F.limsInf = F.liminf f := by
  exact @AntitoneOn.map_limsSup_of_continuousAt Rᵒᵈ S _ _ _ _ F _ f R'
          (antitone_on_dual_iff.mp f_incr) f_cont hF bdd_below bdd_above

theorem MonotoneOn.map_liminf_of_continuousAt {F : Filter ι} [NeBot F]
    {f : R → S} {R' : Set R} (f_incr : MonotoneOn f R')
    (a : ι → R) (f_cont : ContinuousAt f (F.liminf a)) (hF : F.map a ≤ Filter.principal R')
    (bdd_above : F.IsBoundedUnder (· ≤ ·) a := by isBoundedDefault)
    (bdd_below : F.IsBoundedUnder (· ≥ ·) a := by isBoundedDefault) :
    f (F.liminf a) = F.liminf (f ∘ a) := by
  apply @MonotoneOn.map_limsInf_of_continuousAt  R S _ _ _ _ (F.map a) _ f R' f_incr f_cont hF
          bdd_above bdd_below

end yet_another_map_liminf_lemma



-- NOTE: Missing from Mathlib?
-- What would be a good generality?
-- (Mixes order-boundedness and metric-boundedness, so typeclasses don't readily exist.)
lemma Filter.isBounded_le_map_of_bounded_range {ι : Type*} (F : Filter ι) {f : ι → ℝ}
    (h : Bornology.IsBounded (Set.range f)) :
    (F.map f).IsBounded (· ≤ ·) := by
  rw [Real.isBounded_iff_bddBelow_bddAbove] at h
  obtain ⟨c, hc⟩ := h.2
  refine isBoundedUnder_of ⟨c, by simpa [mem_upperBounds] using hc⟩

lemma Filter.isBounded_ge_map_of_bounded_range {ι : Type*} (F : Filter ι) {f : ι → ℝ}
    (h : Bornology.IsBounded (Set.range f)) :
    (F.map f).IsBounded (· ≥ ·) := by
  rw [Real.isBounded_iff_bddBelow_bddAbove] at h
  obtain ⟨c, hc⟩ := h.1
  apply isBoundedUnder_of ⟨c, by simpa [mem_lowerBounds] using hc⟩



section le_liminf_open_implies_convergence

variable {Ω : Type} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

-- NOTE: I think I will work with real-valued integrals, after all...
lemma fatou_argument_lintegral
    {μ : Measure Ω} [SigmaFinite μ] {μs : ℕ → Measure Ω} [∀ i, SigmaFinite (μs i)]
    {f : Ω → ℝ} (f_cont : Continuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂ (μs i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (eventually_of_forall f_nn) f_cont.aemeasurable]
  calc  ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, atTop.liminf (fun i ↦ (μs i) {a | t < f a})
            := (lintegral_mono (fun t ↦ h_opens _ (continuous_def.mp f_cont _ isOpen_Ioi))).trans ?_
    _ ≤ atTop.liminf (fun i ↦ ∫⁻ (t : ℝ) in Set.Ioi 0, (μs i) {a | t < f a})
            := lintegral_liminf_le (fun n ↦ Antitone.measurable
                (fun s t hst ↦ measure_mono (fun ω hω ↦ lt_of_le_of_lt hst hω)))
  rfl

theorem BoundedContinuousFunction.lintegral_le_edist_mul
  {μ : Measure Ω} [IsFiniteMeasure μ] (f : Ω →ᵇ ℝ≥0) :
    (∫⁻ x, f x ∂μ) ≤ edist 0 f * (μ Set.univ) := by
  have bound : ∀ x, f x ≤ nndist 0 f := by
    intro x
    convert nndist_coe_le_nndist x
    simp only [coe_zero, Pi.zero_apply, NNReal.nndist_zero_eq_val]
  apply le_trans (lintegral_mono (fun x ↦ ENNReal.coe_le_coe.mpr (bound x)))
  simp

lemma ENNReal.monotoneOn_toReal : MonotoneOn ENNReal.toReal {∞}ᶜ :=
  fun _ _ _ hy x_le_y ↦ toReal_mono hy x_le_y

-- Argh. :|
lemma Real.lipschitzWith_toNNReal : LipschitzWith 1 Real.toNNReal := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  simp only [NNReal.coe_one, one_mul, NNReal.dist_eq, coe_toNNReal', ge_iff_le, Real.dist_eq]
  simpa only [ge_iff_le, NNReal.coe_one, dist_prod_same_right, one_mul, Real.dist_eq] using
    lipschitzWith_iff_dist_le_mul.mp lipschitzWith_max (x, 0) (y, 0)

-- NOTE: I think this is the version I prefer to use, after all...
lemma fatou_argument_integral_nonneg
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μs : ℕ → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    {f : Ω →ᵇ ℝ} (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
      ∫ x, (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)) := by
  have earlier := fatou_argument_lintegral f.continuous f_nn h_opens
  rw [@integral_eq_lintegral_of_nonneg_ae Ω _ μ f (eventually_of_forall f_nn)
        f.continuous.measurable.aestronglyMeasurable]
  convert (ENNReal.toReal_le_toReal ?_ ?_).mpr earlier
  · simp only [fun i ↦ @integral_eq_lintegral_of_nonneg_ae Ω _ (μs i) f (eventually_of_forall f_nn)
                        f.continuous.measurable.aestronglyMeasurable]
    let g := BoundedContinuousFunction.comp _ Real.lipschitzWith_toNNReal f
    have bound : ∀ i, ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i) ≤ nndist 0 g := fun i ↦ by
      simpa only [coe_nnreal_ennreal_nndist, measure_univ, mul_one, ge_iff_le] using
            BoundedContinuousFunction.lintegral_le_edist_mul (μ := μs i) g
    apply (@MonotoneOn.map_liminf_of_continuousAt ℕ ℝ≥0∞ ℝ _ _ _ _ atTop _ ENNReal.toReal {∞}ᶜ
            ENNReal.monotoneOn_toReal
            (fun i ↦ ∫⁻ (x : Ω), ENNReal.ofReal (f x) ∂(μs i)) ?_ ?_ ?_ ?_).symm
    · apply (NNReal.continuous_coe.comp_continuousOn ENNReal.continuousOn_toNNReal).continuousAt
      have obs : {x : ℝ≥0∞ | x ≠ ∞} = Set.Iio ∞ := by
        ext x
        simp only [ne_eq, Set.mem_setOf_eq, Set.mem_Iio, ne_iff_lt_iff_le, le_top]
      rw [obs]
      apply Iio_mem_nhds
      apply lt_of_le_of_lt (liminf_le_of_frequently_le (frequently_of_forall bound))
      exact ENNReal.coe_lt_top
    · simp only [le_principal_iff, mem_map, Set.preimage_compl, mem_atTop_sets, ge_iff_le,
                 Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨0, fun i _ ↦ (lt_of_le_of_lt (bound i) ENNReal.coe_lt_top).ne⟩
    · exact ⟨∞, eventually_of_forall (fun x ↦ by simp only [le_top])⟩
    · exact ⟨0, eventually_of_forall (fun x ↦ by simp only [ge_iff_le, zero_le])⟩
  · exact (f.lintegral_of_real_lt_top μ).ne
  · apply ne_of_lt
    have obs := fun (i : ℕ) ↦ @BoundedContinuousFunction.lintegral_nnnorm_le Ω _ _ (μs i) ℝ _ f
    simp at obs
    apply lt_of_le_of_lt _ (show (‖f‖₊ : ℝ≥0∞) < ∞ from ENNReal.coe_lt_top)
    apply liminf_le_of_le
    · refine ⟨0, eventually_of_forall (by simp only [ge_iff_le, zero_le, forall_const])⟩
    · intro x hx
      obtain ⟨i, hi⟩ := hx.exists
      apply le_trans hi
      convert obs i with x
      have aux := ENNReal.ofReal_eq_coe_nnreal (f_nn x)
      simp only [ContinuousMap.toFun_eq_coe, BoundedContinuousFunction.coe_to_continuous_fun] at aux
      rw [aux]
      congr
      exact (Real.norm_of_nonneg (f_nn x)).symm

lemma reduction_to_liminf {ι : Type*} {L : Filter ι} [NeBot L]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μs : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    (h : ∀ f : Ω →ᵇ ℝ, 0 ≤ f → ∫ x, (f x) ∂μ ≤ L.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)))
    (f : Ω →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ x, (f x) ∂ (μs i)) L (𝓝 (∫ x, (f x) ∂μ)) := by
  have obs := BoundedContinuousFunction.isBounded_range_integral μs f
  have bdd_above : IsBoundedUnder (· ≤ ·) L (fun i ↦ ∫ (x : Ω), f x ∂μs i) :=
    isBounded_le_map_of_bounded_range _ obs
  have bdd_below : IsBoundedUnder (· ≥ ·) L (fun i ↦ ∫ (x : Ω), f x ∂μs i) :=
    isBounded_ge_map_of_bounded_range _ obs
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
  · exact bdd_above
  · exact bdd_below

-- Not needed?
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
  simp_rw [integral_add (f.integrable _) (integrable_const ‖f‖)] at key
  simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul] at key
  simp_rw [fx_eq]
  convert tendsto_add.comp (Tendsto.prod_mk_nhds key (@tendsto_const_nhds _ _ _ (-‖f‖) F)) <;> simp

theorem le_liminf_open_implies_convergence {μ : ProbabilityMeasure Ω}
  {μs : ℕ → ProbabilityMeasure Ω} (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    atTop.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
  apply reduction_to_liminf
  intro f f_nn
  apply fatou_argument_integral_nonneg (f := f) f_nn
  intro G G_open
  specialize h_opens G G_open
  simp only at h_opens
  simp only [liminf, limsInf, eventually_map, eventually_atTop, ge_iff_le, le_sSup_iff] at *
  intro b b_ub
  by_cases b_eq_top : b = ∞
  · simp only [b_eq_top, le_top]
  · have foo := (@le_csSup_iff ℝ≥0 _ {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → a ≤ ENNReal.toNNReal (μs b G)}
              (ENNReal.toNNReal (μ G)) ?_ ?_).mp h_opens (ENNReal.toNNReal b) ?_
    · simp only [ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at foo
      convert ENNReal.coe_le_coe.mpr foo
      · simp only [ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      · simp only [ne_eq, b_eq_top, not_false_eq_true, ENNReal.coe_toNNReal]
    · use 1
      simp [mem_upperBounds]
      intro x n hn
      exact (hn n (le_refl n)).trans (ProbabilityMeasure.apply_le_one _ _)
    · refine ⟨0, by simp⟩
    · simp only [mem_upperBounds, Set.mem_setOf_eq, forall_exists_index, ne_eq,
                 ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at b_ub ⊢
      intro x n hn
      specialize b_ub x n ?_
      · intro m hm
        convert ENNReal.coe_le_coe.mpr (hn m hm)
        simp only [ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      · rw [(ENNReal.coe_toNNReal b_eq_top).symm] at b_ub
        exact ENNReal.coe_le_coe.mp b_ub

end le_liminf_open_implies_convergence
