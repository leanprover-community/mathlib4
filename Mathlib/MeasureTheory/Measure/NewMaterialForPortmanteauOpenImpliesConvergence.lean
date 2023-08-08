import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Layercake
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



-- NOTE: Missing from Mathlib?
-- What would be a good generality?
-- (Mixes order-boundedness and metric-boundedness, so typeclasses don't readily exist.)
lemma Filter.isBounded_le_map_of_bounded_range (F : Filter ι) {f : ι → ℝ}
    (h : Metric.Bounded (Set.range f)) :
    (F.map f).IsBounded (· ≤ ·) := by
  rw [Real.bounded_iff_bddBelow_bddAbove] at h
  obtain ⟨c, hc⟩ := h.2
  apply isBoundedUnder_of
  use c
  simpa [mem_upperBounds] using hc

lemma Filter.isBounded_ge_map_of_bounded_range (F : Filter ι) {f : ι → ℝ}
    (h : Metric.Bounded (Set.range f)) :
    (F.map f).IsBounded (· ≥ ·) := by
  rw [Real.bounded_iff_bddBelow_bddAbove] at h
  obtain ⟨c, hc⟩ := h.1
  apply isBoundedUnder_of
  use c
  simpa [mem_lowerBounds] using hc

section limsup_liminf_add_sub

example : ContinuousAdd ℝ := by exact LipschitzAdd.continuousAdd -- ok.
example : ContinuousAdd ℝ≥0 := by exact LipschitzAdd.continuousAdd -- ok.
example : ContinuousAdd ℝ≥0∞ := by infer_instance -- ok.

variable {R : Type _} [ConditionallyCompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R]

#check add_le_add_iff_right

lemma limsup_add_const (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [CovariantClass R R (Function.swap fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
    [ContravariantClass R R (Function.swap fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
    (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.limsup (fun i ↦ f i + c) F = Filter.limsup f F + c := by
  convert (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x + c) ?_
            (continuous_add_right c).continuousAt bdd_above bdd_below).symm
  intro x y hxy
  simp only
  simp only [add_le_add_iff_right, hxy]

lemma liminf_add_const (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [CovariantClass R R (Function.swap fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
    [ContravariantClass R R (Function.swap fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
    (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ f i + c) F = Filter.liminf f F + c := by
  convert (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x + c) ?_
            (continuous_add_right c).continuousAt bdd_above bdd_below).symm
  intro x y hxy
  simp only [add_le_add_iff_right, hxy]

#check AddLECancellable
#check AddLECancellable.add_le_add_iff_right
#check AddLECancellable.add_le_add_iff_left

example : AddLECancellable (15 : ℝ≥0) := by exact Contravariant.AddLECancellable
example : AddLECancellable (15 : ℝ) := by exact Contravariant.AddLECancellable
--example : AddLECancellable (1 : ℝ≥0∞) := by exact?

lemma ENNReal.addLECancellable_of_ne_top {c : ℝ≥0∞} (c_ne_top : c ≠ ∞) :
    AddLECancellable c := fun _ _ h ↦ (ENNReal.add_le_add_iff_left c_ne_top).mp h

--#check StrictMono.add_monotone
#check add_le_add

lemma liminf_const_add_improved (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [CovariantClass R R (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ c + f i) F = c + Filter.liminf f F := by
  convert (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ c + x) ?_
            (continuous_add_left c).continuousAt bdd_above bdd_below).symm
  exact fun _ _ h ↦ add_le_add_left h c

lemma liminf_add_const_improved (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [CovariantClass R R (Function.swap fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ f i + c) F = Filter.liminf f F + c := by
  convert (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x + c) ?_
            (continuous_add_right c).continuousAt bdd_above bdd_below).symm
  exact fun _ _ h ↦ add_le_add_right h c

lemma liminf_add_const_real (F : Filter ι) [NeBot F] (f : ι → ℝ) (c : ℝ)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ f i + c) F = Filter.liminf f F + c := by
  exact liminf_add_const_improved F (fun i ↦ f i) c bdd_above bdd_below

lemma liminf_add_const_nnReal (F : Filter ι) [NeBot F] (f : ι → ℝ≥0) (c : ℝ≥0)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ f i + c) F = Filter.liminf f F + c := by
  exact liminf_add_const_improved F (fun i ↦ f i) c bdd_above bdd_below

lemma liminf_add_const_ennReal (F : Filter ι) [NeBot F] (f : ι → ℝ≥0∞) (c : ℝ≥0∞)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ f i + c) F = Filter.liminf f F + c := by
  exact liminf_add_const_improved F (fun i ↦ f i) c bdd_above bdd_below

/-
lemma limsup_add_const (F : Filter ι) [NeBot F] (f : ι → ℝ) (c : ℝ)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.limsup (fun i ↦ f i + c) F = Filter.limsup f F + c := by
  convert (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : ℝ) ↦ x + c) ?_
            (continuous_add_right c).continuousAt bdd_above bdd_below).symm
  intro x y hxy
  simp only [add_le_add_iff_right, hxy]

lemma liminf_add_const (F : Filter ι) [NeBot F] (f : ι → ℝ) (c : ℝ)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ f i + c) F = Filter.liminf f F + c := by
  convert (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : ℝ) ↦ x + c) ?_
            (continuous_add_right c).continuousAt bdd_above bdd_below).symm
  intro x y hxy
  simp only [add_le_add_iff_right, hxy]

lemma limsup_const_sub (F : Filter ι) [NeBot F] (f : ι → ℝ) (c : ℝ)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.limsup (fun i ↦ c - f i ) F = c - Filter.liminf f F := by
  convert (Antitone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : ℝ) ↦ c - x) ?_
            (continuous_sub_left c).continuousAt bdd_above bdd_below).symm
  intro x y hxy
  simp only [sub_le_sub_iff_left, hxy]

lemma liminf_const_sub (F : Filter ι) [NeBot F] (f : ι → ℝ) (c : ℝ)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ c - f i ) F = c - Filter.limsup f F := by
  convert (Antitone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : ℝ) ↦ c - x) ?_
            (continuous_sub_left c).continuousAt bdd_above bdd_below).symm
  intro x y hxy
  simp only [sub_le_sub_iff_left, hxy]
 -/
end limsup_liminf_add_sub -- section




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
