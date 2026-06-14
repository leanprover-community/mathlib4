/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Semivariation

/-!
# Product of vector measures
-/

public section

open Filter Function MeasureTheory RCLike Set TopologicalSpace Topology
open scoped ENNReal NNReal Finset

variable {ι X Y E F G H I J : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup I] [NormedSpace ℝ I]
  [NormedAddCommGroup J] [NormedSpace ℝ J]
  {μ : VectorMeasure X E} {ν : VectorMeasure Y F}
  {B : E →L[ℝ] F →L[ℝ] G} {f g : X → E} {s t : Set X}

namespace MeasureTheory.VectorMeasure

open scoped Classical in
/-- The product of two vector measures `μ` and `ν` with respect to a continuous bilinear map `B`,
giving mass `B (μ s) (ν s)` to a measurable set `s`.
If such a measure does not exist, we use the junk value `0`. -/
noncomputable def prod (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E →L[ℝ] F →L[ℝ] G) :
    VectorMeasure (X × Y) G :=
  if h : ∃ ρ : VectorMeasure (X × Y) G, ∀ (s : Set X) (t : Set Y),
    MeasurableSet s → MeasurableSet t → ρ (s ×ˢ t) = B (μ s) (ν t) then h.choose
  else 0

/-- Two vector measures `μ` and `ν` have a product with respect to `B` if there exists a
measure giving mass `B (μ s) (ν t)` to any measurable product `s × t`.
This is satisfied whenever `μ` or `ν` has finite variation. -/
class HasProd (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E →L[ℝ] F →L[ℝ] G) : Prop where
  exists_prod : ∃ ρ : VectorMeasure (X × Y) G, ∀ (s : Set X) (t : Set Y),
    MeasurableSet s → MeasurableSet t → ρ (s ×ˢ t) = B (μ s) (ν t)

lemma prod_eq_zero_of_not_hasProd (h : ¬HasProd μ ν B) :
    μ.prod ν B = 0 := by
  grind [HasProd, prod]

@[simp] lemma prod_apply [h : HasProd μ ν B] {s : Set X} {t : Set Y} :
    μ.prod ν B (s ×ˢ t) = B (μ s) (ν t) := by
  rcases eq_or_ne s ∅ with rfl | hs
  · simp
  rcases eq_or_ne t ∅ with rfl | ht
  · simp
  by_cases h's : MeasurableSet s; swap
  · simp only [h's, not_false_eq_true, not_measurable, _root_.map_zero,
      ContinuousLinearMap.zero_apply]
    rw [not_measurable]
    simp [measurableSet_prod, hs, ht, h's]
  by_cases h't : MeasurableSet t; swap
  · simp only [h't, not_false_eq_true, not_measurable, _root_.map_zero]
    rw [not_measurable]
    simp [measurableSet_prod, hs, ht, h't]
  simpa [prod, h.exists_prod] using h.exists_prod.choose_spec s t h's h't

lemma HasProd.flip [HasProd μ ν B] : HasProd ν μ B.flip where
  exists_prod := by
    refine ⟨(μ.prod ν B).map Prod.swap, fun s t hs ht ↦ ?_⟩
    rw [map_apply _ (by fun_prop) (hs.prod ht)]
    simp

omit [NormedSpace ℝ F] in
/-- If `ν` is a vector measure, and `s ⊆ X × Y` is measurable, then `x ↦ ν { y | (x, y) ∈ s }` is
a strongly measurable function. -/
theorem stronglyMeasurable_vectorMeasure_prodMk_left {s : Set (X × Y)}
    (hs : MeasurableSet s) : StronglyMeasurable fun x ↦ ν (Prod.mk x ⁻¹' s) := by
  induction s, hs
    using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp [stronglyMeasurable_const]
  | basic s hs =>
    obtain ⟨s, hs, t, -, rfl⟩ := hs
    classical
    simpa [mk_preimage_prod_right_eq_if, of_if] using stronglyMeasurable_const.indicator hs
  | compl s hs ihs =>
    simp_rw [preimage_compl, VectorMeasure.of_compl (measurable_prodMk_left hs)]
    exact stronglyMeasurable_const.sub ihs
  | iUnion f hfd hfm ihf =>
    have (a : X) : HasSum (fun i ↦ ν (Prod.mk a ⁻¹' f i)) (ν (Prod.mk a ⁻¹' ⋃ i, f i)) := by
      rw [preimage_iUnion]
      apply hasSum_of_disjoint_iUnion
      exacts [fun i ↦ measurable_prodMk_left (hfm i), hfd.mono fun _ _ ↦ .preimage _]
    exact StronglyMeasurable.hasSum ihf this

omit [NormedSpace ℝ E] in
theorem integrable_vectorMeasure_prodMk_left [IsFiniteMeasure μ.variation]
    {s : Set (X × Y)} (hs : MeasurableSet s) :
    μ.Integrable fun x ↦ ν (Prod.mk x ⁻¹' s) := by
  refine Integrable.of_bound (μ := μ.variation) ?_ ν.bound ?_
  · exact (stronglyMeasurable_vectorMeasure_prodMk_left hs).aestronglyMeasurable
  · exact Eventually.of_forall (fun x ↦ norm_apply_le_bound)

open scoped Classical in
/-- The product of two vector measures when the first one has finite variation, obtained by
integrating the measure of the fibers, as in the definition of the product of positive measures.
*Do not use*: This is only used to instantiate the typeclass `HasProd`. Instead, use `μ.prod ν B`,
which uses the typeclass instance. -/
noncomputable def prodOfIsFiniteMeasureLeft
    (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E →L[ℝ] F →L[ℝ] G)
    [IsFiniteMeasure μ.variation] :
    VectorMeasure (X × Y) G where
  measureOf' s := if MeasurableSet s then ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B.flip; μ] else 0
  empty' := by simp
  not_measurable' := by simp +contextual
  m_iUnion' f f_meas f_disj := by
    simp only [f_meas, ↓reduceIte, implies_true, MeasurableSet.iUnion, preimage_iUnion,
      HasSum, SummationFilter.unconditional_filter]
    have A (a : Finset ℕ) : ∑ y ∈ a, ∫ᵛ x, ν (Prod.mk x ⁻¹' f y) ∂[B.flip; μ]
        = ∫ᵛ x, ∑ y ∈ a, ν (Prod.mk x ⁻¹' f y) ∂[B.flip; μ] := by
      rw [integral_finsetSum _ (fun i hi ↦ integrable_vectorMeasure_prodMk_left (f_meas i))]
    simp_rw [A]
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun x ↦ ν.bound)
    · apply Eventually.of_forall (fun a ↦ ?_)
      apply StronglyMeasurable.aestronglyMeasurable
      apply Finset.stronglyMeasurable_fun_sum _ (fun i hi ↦ ?_)
      apply stronglyMeasurable_vectorMeasure_prodMk_left (f_meas i)
    · filter_upwards with a
      filter_upwards with x
      rw [← VectorMeasure.of_biUnion_finset]
      · apply norm_apply_le_bound
      · exact fun i hi j hj hij ↦ (f_disj hij).preimage _
      · exact fun i hi ↦ measurable_prodMk_left (f_meas i)
    · apply integrable_const
    · filter_upwards with x
      apply hasSum_of_disjoint_iUnion
      · exact fun i ↦ measurable_prodMk_left (f_meas i)
      · exact fun i j hij ↦ (f_disj hij).preimage _

instance [CompleteSpace G] [IsFiniteMeasure μ.variation] : HasProd μ ν B where
  exists_prod := by
    classical
    refine ⟨prodOfIsFiniteMeasureLeft μ ν B, fun s t hs ht ↦ ?_⟩
    simp only [prodOfIsFiniteMeasureLeft, hs.prod ht, ↓reduceIte, mk_preimage_prod_right_eq_if,
      of_if, integral_indicator hs, setIntegral_const, ContinuousLinearMap.flip_apply]

instance [CompleteSpace G] [h : IsFiniteMeasure ν.variation] : HasProd μ ν B := by
  rw [← B.flip_flip]
  apply HasProd.flip

lemma prod_eq_of_forall_apply_prod {ρ : VectorMeasure (X × Y) G} (hρ : ∀ (s : Set X) (t : Set Y),
    MeasurableSet s → MeasurableSet t → ρ (s ×ˢ t) = B (μ s) (ν t)) :
    μ.prod ν B = ρ := by
  have : HasProd μ ν B := ⟨ρ, hρ⟩
  apply ext_of_generateFrom _ _ generateFrom_prod.symm isPiSystem_prod
  · rw [← univ_prod_univ, hρ _ _ MeasurableSet.univ MeasurableSet.univ, prod_apply]
  · rintro - ⟨s, hs, t, ht, rfl⟩
    rw [prod_apply, hρ _ _ hs ht]

lemma prod_apply_eq_integral [CompleteSpace G] [IsFiniteMeasure μ.variation]
    {s : Set (X × Y)} (hs : MeasurableSet s) :
    μ.prod ν B s = ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B.flip; μ] := by
  have : μ.prod ν B = prodOfIsFiniteMeasureLeft μ ν B := by
    classical
    apply prod_eq_of_forall_apply_prod (fun s t hs ht ↦ ?_)
    simp only [prodOfIsFiniteMeasureLeft, hs.prod ht, ↓reduceIte, mk_preimage_prod_right_eq_if,
      of_if, integral_indicator hs, setIntegral_const, ContinuousLinearMap.flip_apply]
  rw [this]
  simp [prodOfIsFiniteMeasureLeft, hs]

lemma prod_flip_apply_eq_integral [CompleteSpace G] [IsFiniteMeasure μ.variation]
    {B : F →L[ℝ] E →L[ℝ] G} {s : Set (X × Y)} (hs : MeasurableSet s) :
    μ.prod ν B.flip s = ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B; μ] := by
  simp [prod_apply_eq_integral hs]

lemma variation_prod_le [CompleteSpace G] [IsFiniteMeasure μ.variation] [SFinite ν.variation] :
    (μ.prod ν B).variation ≤ ‖B‖ₑ • μ.variation.prod ν.variation := by
  apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
  rw [prod_apply_eq_integral hs]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.prod_apply hs]
  grw [enorm_integral_le_lintegral_enorm, ContinuousLinearMap.opENorm_flip,
    enorm_measure_le_variation]

instance [CompleteSpace G] [IsFiniteMeasure μ.variation] [IsFiniteMeasure ν.variation] :
    IsFiniteMeasure (μ.prod ν B).variation := by
  have : IsFiniteMeasure (‖B‖ₑ • μ.variation.prod ν.variation) := by
    simp only [enorm_eq_nnnorm, Measure.coe_nnreal_smul]
    infer_instance
  exact isFiniteMeasure_of_le _ variation_prod_le

omit [NormedSpace ℝ H] in
lemma _root_.MeasureTheory.Integrable.prod_vectorMeasure
    [CompleteSpace G] [IsFiniteMeasure μ.variation] [IsFiniteMeasure ν.variation]
    {f : X × Y → H} (hf : Integrable f (μ.variation.prod ν.variation)) :
    (μ.prod ν B).Integrable f :=
  Integrable.of_measure_le_smul (by simp) variation_prod_le hf

/-- The vector measure integral is measurable. This shows that the integrand of (the right-hand-side
of) Fubini's theorem is measurable. This version has `f` in curried form. -/
theorem _root_.MeasureTheory.StronglyMeasurable.integral_vectorMeasure_prod_right
    {B : G →L[ℝ] F →L[ℝ] H} [SFinite ν.variation] ⦃f : X → Y → G⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun x ↦ ∫ᵛ y, f x y ∂[B; ν] := by
  simp only [integral_eq_setToFun]
  apply StronglyMeasurable.setToFun_prod_right _ (fun s hs ↦ ?_) hf
  exact stronglyMeasurable_vectorMeasure_prodMk_left hs

/-- The vector measure integral is measurable. This shows that the integrand of (the right-hand-side
of) Fubini's theorem is measurable. -/
theorem _root_.MeasureTheory.StronglyMeasurable.integral_vectorMeasure_prod_right'
    {B : G →L[ℝ] F →L[ℝ] H} [SFinite ν.variation] ⦃f : X × Y → G⦄
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x ↦  ∫ᵛ y, f (x, y) ∂[B; ν] := by
  rw [← uncurry_curry f] at hf; exact hf.integral_vectorMeasure_prod_right

/-- The vector measure integral is measurable. This shows that the integrand of (the right-hand-side
of) the symmetric version of Fubini's theorem is measurable.
This version has `f` in curried form. -/
theorem _root_.MeasureTheory.StronglyMeasurable.integral_vectorMeasure_prod_left
    {B : G →L[ℝ] E →L[ℝ] H} [SFinite μ.variation] ⦃f : X → Y → G⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun y ↦ ∫ᵛ x, f x y ∂[B; μ] :=
  (hf.comp_measurable measurable_swap).integral_vectorMeasure_prod_right'

/-- The vector measure integral is measurable. This shows that the integrand of (the right-hand-side
of) the symmetric version of Fubini's theorem is measurable. -/
theorem _root_.MeasureTheory.StronglyMeasurable.integral_vectorMeasure_prod_left'
    {B : G →L[ℝ] E →L[ℝ] H} [SFinite μ.variation] ⦃f : X × Y → G⦄
    (hf : StronglyMeasurable f) : StronglyMeasurable fun y ↦ ∫ᵛ x, f (x, y) ∂[B; μ] :=
  (hf.comp_measurable measurable_swap).integral_vectorMeasure_prod_right'

/-- The vector measure integral is a.e.-measurable.
This shows that the integrand of (the right-hand-side of) Fubini's theorem is a.e.-measurable. -/
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_vectorMeasure_prod_right'
    {B : G →L[ℝ] F →L[ℝ] H} [SFinite ν.variation] {μ : Measure X}
    ⦃f : X × Y → G⦄ (hf : AEStronglyMeasurable f (μ.prod ν.variation)) :
    AEStronglyMeasurable (fun x ↦ ∫ᵛ y, f (x, y) ∂[B; ν]) μ :=
  ⟨fun x ↦ ∫ᵛ y, hf.mk f (x, y) ∂[B; ν],
    hf.stronglyMeasurable_mk.integral_vectorMeasure_prod_right',
    by filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩

theorem _root_.MeasureTheory.Integrable.integral_vectorMeasure_prod_left {B : G →L[ℝ] F →L[ℝ] H}
    [SFinite ν.variation]
    {μ : Measure X} ⦃f : X × Y → G⦄ (hf : Integrable f (μ.prod ν.variation)) :
    Integrable (fun x ↦ ∫ᵛ y, f (x, y) ∂[B; ν]) μ := by
  apply Integrable.mono (hf.integral_norm_prod_left.const_mul ‖B‖)
    (hf.aestronglyMeasurable.integral_vectorMeasure_prod_right')
  filter_upwards with x
  grw [norm_integral_le_integral_norm]
  exact le_abs_self _

/-- Vector measure integrals commute with subtraction inside a lower Lebesgue integral. -/
theorem lintegral_fn_integral_sub ⦃f g : X × Y → G⦄ {μ : Measure X}
    {B : G →L[ℝ] F →L[ℝ] H} [SFinite μ] [SFinite ν.variation]
    (φ : H → ℝ≥0∞) (hf : Integrable f (μ.prod ν.variation))
    (hg : Integrable g (μ.prod ν.variation)) :
    (∫⁻ x, φ (∫ᵛ y, f (x, y) - g (x, y) ∂[B; ν]) ∂μ) =
      ∫⁻ x, φ ((∫ᵛ y, f (x, y) ∂[B; ν]) - ∫ᵛ y, g (x, y) ∂[B; ν]) ∂μ := by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with x h2f h2g
  simp [integral_fun_sub h2f h2g]

/-- The map that sends an L¹-function `f : X × Y → G` to `∫∫f` is continuous. -/
theorem continuous_integral_integral {B : G →L[ℝ] F →L[ℝ] H} {C : H →L[ℝ] E →L[ℝ] I}
    [SFinite ν.variation] [SFinite μ.variation] :
    Continuous fun f : X × Y →₁[μ.variation.prod ν.variation] G ↦
      ∫ᵛ x, (∫ᵛ y, f (x, y) ∂[B; ν]) ∂[C; μ] := by
  rw [continuous_iff_continuousAt]; intro g
  apply tendsto_integral_of_L1
  · exact (Integrable.integral_vectorMeasure_prod_left (L1.integrable_coeFn g)).aestronglyMeasurable
  · filter_upwards with h
    exact Integrable.integral_vectorMeasure_prod_left (L1.integrable_coeFn h)
  simp_rw [← lintegral_fn_integral_sub _ (L1.integrable_coeFn _) (L1.integrable_coeFn g)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun i ↦ zero_le) _
    (h := fun i ↦ ∫⁻ x, ‖B‖ₑ * ∫⁻ y,
      ‖i (x, y) - g (x, y)‖ₑ ∂ν.variation ∂μ.variation); swap
  · exact fun i ↦ lintegral_mono fun x ↦ enorm_integral_le_lintegral_enorm
  have this (i : X × Y →₁[μ.variation.prod ν.variation] G) : Measurable fun z ↦ ‖i z - g z‖ₑ :=
    ((Lp.stronglyMeasurable i).sub (Lp.stronglyMeasurable g)).enorm
  simp_rw [lintegral_const_mul' ‖B‖ₑ _ (by simp)]
  simp_rw [← lintegral_prod _ (this _).aemeasurable, ← L1.ofReal_norm_sub_eq_lintegral,
    ofReal_norm]
  suffices Tendsto (fun i ↦ ‖B‖ₑ * ‖i - g‖ₑ) (𝓝 g) (𝓝 (‖B‖ₑ * 0)) by simpa
  apply ENNReal.Tendsto.const_mul _ (by simp)
  rw [← tendsto_iff_enorm_sub_tendsto_zero]
  exact tendsto_id

/-- **Fubini's Theorem**: For integrable functions on `X × Y`,
the vector measure integral of `f` for the product vector measure is equal to the iterated vector
measure integral. We express this with respect to general pairing functions, with a compatibility
condition saying that the compositions coincide up to reordering. -/
theorem integral_prod {B : G →L[ℝ] F →L[ℝ] J} {C : J →L[ℝ] E →L[ℝ] I}
    {A : E →L[ℝ] F →L[ℝ] H} {D : G →L[ℝ] H →L[ℝ] I}
    [CompleteSpace H] [CompleteSpace J]
    [IsFiniteMeasure ν.variation] [IsFiniteMeasure μ.variation]
    {f : X × Y → G} (hf : Integrable f (μ.variation.prod ν.variation))
    (h : ∀ x y z, D x (A y z) = C (B x z) y) :
    ∫ᵛ z, f z ∂[D; μ.prod ν A] = ∫ᵛ x, (∫ᵛ y, f (x, y) ∂[B; ν]) ∂[C; μ] := by
  by_cases hI : CompleteSpace I; swap
  · simp only [integral_of_not_completeSpace hI]
  revert f
  apply Integrable.induction
  · intro c s hs h2s
    simp_rw [integral_indicator hs, ← indicator_comp_right, Function.comp_def,
      integral_indicator (measurable_prodMk_left hs), setIntegral_const]
    rw [integral_continuousLinearMap_comp (integrable_vectorMeasure_prodMk_left hs),
      ← prod_flip_apply_eq_integral hs]
    suffices (μ.prod ν A).mapRange (D c) (D c).continuous = μ.prod ν (C ∘SL B c).flip by
      simp [← this]
    apply (prod_eq_of_forall_apply_prod _).symm
    intro s t hs ht
    simp [h]
  · intro f g hfg fint gint hf hg
    rw [integral_add fint.prod_vectorMeasure gint.prod_vectorMeasure, hf, hg,
      ← integral_add fint.integral_vectorMeasure_prod_left gint.integral_vectorMeasure_prod_left]
    apply integral_congr_ae
    filter_upwards [fint.prod_right_ae, gint.prod_right_ae] with x hx h'x
    simp only [Pi.add_apply]
    rw [integral_fun_add hx h'x]
  · apply isClosed_eq ?_  continuous_integral_integral
    let P : Lp G 1 (μ.variation.prod ν.variation) →L[ℝ] Lp G 1 (μ.prod ν A).variation :=
      Lp.LpToLpOfMeasureLeSMul (by simp) variation_prod_le
    have M (f : Lp G 1 (μ.variation.prod ν.variation)) :
        ∫ᵛ z, f z ∂[D; μ.prod ν A] = ∫ᵛ z, (P f) z ∂[D; μ.prod ν A] := by
      apply integral_congr_ae
      grw [Lp.coeFn_LpToLpOfMeasureLeSMul]
    simp_rw [M]
    exact Continuous.comp continuous_integral P.continuous
  · intro f g hfg hf h'f
    have ac : (μ.prod ν A).variation ≪ μ.variation.prod ν.variation :=
      Measure.absolutelyContinuous_of_le_smul variation_prod_le
    rw [← integral_congr_ae (ac.ae_eq hfg), h'f]
    apply integral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hfg] with x hx
    exact integral_congr_ae hx

/-- **Fubini's Theorem**: For integrable functions on `X × Y`,
the vector measure integral of `f` for the product vector measure is equal to the iterated vector
measure integral. Version where `f` is scalar. -/
theorem integral_prod_smul [CompleteSpace H] [CompleteSpace F] {B : E →L[ℝ] F →L[ℝ] H}
    [IsFiniteMeasure ν.variation] [IsFiniteMeasure μ.variation]
    {f : X × Y → ℝ} (hf : Integrable f (μ.variation.prod ν.variation)) :
    ∫ᵛ z, f z ∂•(μ.prod ν B) = ∫ᵛ x, (∫ᵛ y, f (x, y) ∂•ν) ∂[B.flip; μ] :=
  integral_prod hf (fun x y z ↦ by simp)

end MeasureTheory.VectorMeasure
