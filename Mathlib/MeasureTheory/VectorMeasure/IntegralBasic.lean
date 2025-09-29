import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.SetToL1
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.VectorMeasure.Integral

/-!

## Main statements

1. Basic properties of the Bochner integral on functions of type `α → E`, where `α` is a measure
   space and `E` is a real normed space.

  * `integral_zero`                  : `∫ 0 ∂Bμ = 0`

2. (In the file `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`)
  `tendsto_integral_of_dominated_convergence` : the Lebesgue dominated convergence theorem

3. (In `Mathlib/MeasureTheory/Integral/Bochner/Set.lean`) integration commutes with continuous
  linear maps.

  * `ContinuousLinearMap.integral_comp_comm`
  * `LinearIsometry.integral_comp_comm`

-/
noncomputable section

open ENNReal Filter Set TopologicalSpace Topology MeasureTheory VectorMeasure ContinuousLinearMap

namespace VectorMeasure

/-!
## The vector-valued integral against a vector measure on functions

Define the vector-valued integral on functions generally to be the `L1` vector-valued integral,
for integrable functions, and 0 otherwise; prove its basic properties.
-/

variable {α E F G 𝕜 : Type*}
  [MeasurableSpace α] [NormedDivisionRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

open Classical in
/-- The vector-valued integral against a vector measure. -/
irreducible_def integral (f : α → E) (Bμ : VectorMeasureWithPairing α E F G) : G :=
  if _ : CompleteSpace G then
    if hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure
    then Bμ.integral (hf.toL1 f) else 0
  else 0

@[inherit_doc VectorMeasure.integral]
notation3 "∫ "(...)", "r:60:(scoped f => f)" ∂"Bμ:70 => integral r Bμ

@[inherit_doc VectorMeasure.integral]
notation3 "∫ "(...)" in "s", "r:60:(scoped f => f)" ∂"Bμ:70 =>
  integral r (VectorMeasureWithPairing.restrict Bμ s)

section Properties

variable {f : α → E} {Bμ : VectorMeasureWithPairing α E F G}

theorem integral_eq [hG : CompleteSpace G]
    (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, f a ∂Bμ = Bμ.integral (hf.toL1 f) := by
  simp [integral, hG, hf]

theorem integral_eq_setToFun [hG : CompleteSpace G] :
    ∫ a, f a ∂Bμ = setToFun Bμ.vectorMeasure.variation.ennrealToMeasure
    (weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
    (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) f := by
  simp only [integral, hG]; rfl

theorem L1.integral_eq_integral [hG : CompleteSpace G]
    (f : α →₁[Bμ.vectorMeasure.variation.ennrealToMeasure] E) :
    Bμ.integral f = ∫ a, f a ∂Bμ := by
  simp only [integral_eq_setToFun]
  exact (L1.setToFun_eq_setToL1 (dominatedFinMeasAdditive_weightedVectorSMul
    Bμ.pairing Bμ.vectorMeasure) f).symm

theorem integral_undef (h : ¬Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, f a ∂Bμ = 0 := by
  by_cases hG : CompleteSpace G
  · simp [integral, hG, h]
  · simp [integral, hG]

theorem Integrable.of_integral_ne_zero (h : ∫ a, f a ∂Bμ ≠ 0) :
    Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure :=
  Not.imp_symm integral_undef h

theorem integral_non_aestronglyMeasurable
    (h : ¬AEStronglyMeasurable f Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, f a ∂Bμ = 0 :=
  integral_undef <| not_and_of_not_left _ h

@[simp]
theorem integral_zero : ∫ _ : α, 0 ∂Bμ = 0 := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_zero (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
  · simp [integral, hG]

@[simp]
theorem integral_zero' : integral 0 Bμ = 0 :=
  integral_zero

lemma integral_indicator₂ {β : Type*} (f : β → α → E) (s : Set β) (b : β) :
    ∫ y, s.indicator (f · y) b ∂Bμ = s.indicator (fun x ↦ ∫ y, f x y ∂Bμ) b := by
  by_cases hb : b ∈ s <;> simp [hb]

theorem integrable_of_integral_eq_one {f : α → ℝ} {Bμ : VectorMeasureWithPairing α ℝ ℝ ℝ}
    (h : ∫ a, f a ∂Bμ = 1) : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure :=
  Integrable.of_integral_ne_zero <| h ▸ one_ne_zero

theorem integral_add {g : α → E} (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure)
    (hg : Integrable g Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, f a + g a ∂Bμ = ∫ a, f a ∂Bμ + ∫ a, g a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_add
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) hf hg
  · simp [integral, hG]

theorem integral_add' {g : α → E} (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure)
    (hg : Integrable g Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, (f + g) a ∂Bμ = ∫ a, f a ∂Bμ + ∫ a, g a ∂Bμ :=
  integral_add hf hg

theorem integral_finset_sum {ι} (s : Finset ι) {f : ι → α → E}
    (hf : ∀ i ∈ s, Integrable (f i) Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, ∑ i ∈ s, f i a ∂Bμ = ∑ i ∈ s, ∫ a, f i a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_finset_sum
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) s hf
  · simp [integral, hG]

@[integral_simps]
theorem integral_neg (f : α → E) : ∫ a, -f a ∂Bμ = -∫ a, f a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_neg (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) f
  · simp [integral, hG]

theorem integral_neg' (f : α → E) : ∫ a, (-f) a ∂Bμ = -∫ a, f a ∂Bμ :=
  integral_neg f

theorem integral_sub {g : α → E} (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure)
    (hg : Integrable g Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, f a - g a ∂Bμ = ∫ a, f a ∂Bμ - ∫ a, g a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_sub
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) hf hg
  · simp [integral, hG]

theorem integral_sub' {g : α → E} (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure)
    (hg : Integrable g Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, (f - g) a ∂Bμ = ∫ a, f a ∂Bμ - ∫ a, g a ∂Bμ :=
  integral_sub hf hg

theorem integral_congr_ae {g : α → E} (h : f =ᵐ[Bμ.vectorMeasure.variation.ennrealToMeasure] g) :
    ∫ a, f a ∂Bμ = ∫ a, g a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_congr_ae
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) h
  · simp [integral, hG]

lemma integral_congr_ae₂ {β H J : Type*} {_ : MeasurableSpace β}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup J] [NormedSpace ℝ J]
    {Bν : VectorMeasureWithPairing β H J E}
    {f g : α → β → H} (h : ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure,
      f a =ᵐ[Bν.vectorMeasure.variation.ennrealToMeasure] g a) :
    ∫ a, ∫ b, f a b ∂Bν ∂Bμ = ∫ a, ∫ b, g a b ∂Bν ∂Bμ := by
  apply integral_congr_ae
  filter_upwards [h] with _ ha
  apply integral_congr_ae
  filter_upwards [ha] with _ hb using hb

@[simp]
theorem L1.integral_of_fun_eq_integral'
    (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, (AEEqFun.mk f hf.aestronglyMeasurable) a ∂Bμ = ∫ a, f a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_toL1 (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) hf
  · simp [integral, hG]

theorem L1.integral_of_fun_eq_integral
    (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, (hf.toL1 f) a ∂Bμ = ∫ a, f a ∂Bμ := by
  simp [hf]

@[continuity]
theorem continuous_integral : Continuous fun f : α →₁[Bμ.vectorMeasure.variation.ennrealToMeasure] E
    => ∫ a, f a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact continuous_setToFun
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
  · simp [integral, hG, continuous_const]

theorem integral_eq_zero_of_ae
    (hf : f =ᵐ[Bμ.vectorMeasure.variation.ennrealToMeasure] 0) : ∫ a, f a ∂Bμ = 0 := by
  simp [integral_congr_ae hf]

/-- If `F i → f` in `L1`, then `∫ x, F i x ∂Bμ → ∫ x, f x ∂Bμ`. -/
theorem tendsto_integral_of_L1 {ι} (f : α → E)
    (hfi : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure) {F : ι → α → E} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) Bμ.vectorMeasure.variation.ennrealToMeasure)
    (hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂Bμ.vectorMeasure.variation.ennrealToMeasure)
    l (𝓝 0)) :
    Tendsto (fun i => ∫ x, F i x ∂Bμ) l (𝓝 <| ∫ x, f x ∂Bμ) := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact tendsto_setToFun_of_L1
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) f hfi hFi hF
  · simp [integral, hG, tendsto_const_nhds]

/-- If `F i → f` in `L1`, then `∫ x, F i x ∂Bμ → ∫ x, f x ∂Bμ`. -/
lemma tendsto_integral_of_L1' {ι} (f : α → E)
    (hfi : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure) {F : ι → α → E} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) Bμ.vectorMeasure.variation.ennrealToMeasure)
    (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 Bμ.vectorMeasure.variation.ennrealToMeasure)
    l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, F i x ∂Bμ) l (𝓝 (∫ x, f x ∂Bμ)) := by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

theorem continuousWithinAt_of_dominated {F : X → α → E} {x₀ : X} {bound : α → ℝ} {s : Set X}
    (hF_meas : ∀ᶠ x in 𝓝[s] x₀,
    AEStronglyMeasurable (F x) Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_bound : ∀ᶠ x in 𝓝[s] x₀,
    ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_cont : ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure,
    ContinuousWithinAt (fun x => F x a) s x₀) :
    ContinuousWithinAt (fun x => ∫ a, F x a ∂Bμ) s x₀ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact continuousWithinAt_setToFun_of_dominated
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuousWithinAt_const]

theorem continuousAt_of_dominated {F : X → α → E} {x₀ : X} {bound : α → ℝ}
    (hF_meas : ∀ᶠ x in 𝓝 x₀,
    AEStronglyMeasurable (F x) Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_bound : ∀ᶠ x in 𝓝 x₀,
    ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_cont : ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure,
    ContinuousAt (fun x => F x a) x₀) :
    ContinuousAt (fun x => ∫ a, F x a ∂Bμ) x₀ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact continuousAt_setToFun_of_dominated
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuousAt_const]

theorem continuousOn_of_dominated {F : X → α → E} {bound : α → ℝ} {s : Set X}
    (hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_bound : ∀ x ∈ s, ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_cont : ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure, ContinuousOn (fun x => F x a) s) :
    ContinuousOn (fun x => ∫ a, F x a ∂Bμ) s := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact continuousOn_setToFun_of_dominated
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuousOn_const]

theorem continuous_of_dominated {F : X → α → E} {bound : α → ℝ}
    (hF_meas : ∀ x, AEStronglyMeasurable (F x) Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_bound : ∀ x, ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_cont : ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure, Continuous fun x => F x a) :
    Continuous fun x => ∫ a, F x a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact continuous_setToFun_of_dominated
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuous_const]

@[simp]
theorem integral_const (c : E) [hG : CompleteSpace G]
    [IsFiniteMeasure Bμ.vectorMeasure.variation.ennrealToMeasure] :
    ∫ _ : α, c ∂Bμ = Bμ.pairing c (Bμ.vectorMeasure univ) := by
  simp only [integral, hG]
  exact setToFun_const (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) _

variable {μ ν : VectorMeasure α F}

theorem integral_add_measure (B : E →L[ℝ] F →L[ℝ] G)
    (hμ : Integrable f μ.variation.ennrealToMeasure)
    (hν : Integrable f ν.variation.ennrealToMeasure) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B (μ + ν)) =
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) + ∫ x, f x ∂(VectorMeasureWithPairing.mk B ν) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have hfi := hμ.add_measure hν
  simp_rw [integral_eq_setToFun]
  have hμν : (μ + ν).variation.ennrealToMeasure ≤
    μ.variation.ennrealToMeasure + ν.variation.ennrealToMeasure :=
    triangle_inequality_ennrealToMeasure μ ν
  have hμν_dfma1 : DominatedFinMeasAdditive
    (μ + ν).variation.ennrealToMeasure
    (weightedVectorSMul B (μ + ν) : Set α → E →L[ℝ] G) ‖B‖ :=
    dominatedFinMeasAdditive_weightedVectorSMul B (μ + ν)
  have hμν_dfma2 : DominatedFinMeasAdditive
    (μ.variation.ennrealToMeasure + ν.variation.ennrealToMeasure)
    (weightedVectorSMul B (μ + ν) : Set α → E →L[ℝ] G) ‖B‖ :=
    by simpa using (DominatedFinMeasAdditive.of_measure_le_smul one_ne_top
      (by simpa using hμν) hμν_dfma1 (norm_nonneg B))
  trans setToFun (μ.variation.ennrealToMeasure + ν.variation.ennrealToMeasure)
    (weightedVectorSMul B (μ + ν)) hμν_dfma2 f
  · refine (setToFun_congr_measure_of_integrable 1 one_ne_top (by simpa using hμν)
      hμν_dfma2 hμν_dfma1 f hfi).symm
  · have hμ_dfma : DominatedFinMeasAdditive
      (μ.variation.ennrealToMeasure + ν.variation.ennrealToMeasure)
      (weightedVectorSMul B μ : Set α → E →L[ℝ] G) ‖B‖ :=
        DominatedFinMeasAdditive.add_measure_right
        μ.variation.ennrealToMeasure ν.variation.ennrealToMeasure
        (dominatedFinMeasAdditive_weightedVectorSMul B μ) (norm_nonneg B)
    have hν_dfma : DominatedFinMeasAdditive
      (μ.variation.ennrealToMeasure + ν.variation.ennrealToMeasure)
      (weightedVectorSMul B ν : Set α → E →L[ℝ] G) ‖B‖ :=
        DominatedFinMeasAdditive.add_measure_left
        μ.variation.ennrealToMeasure ν.variation.ennrealToMeasure
        (dominatedFinMeasAdditive_weightedVectorSMul B ν) (norm_nonneg B)
    rw [← setToFun_congr_measure_of_add_right hμ_dfma
      (dominatedFinMeasAdditive_weightedVectorSMul B μ) f hfi,
      ← setToFun_congr_measure_of_add_left hν_dfma
      (dominatedFinMeasAdditive_weightedVectorSMul B ν) f hfi]
    refine setToFun_add_left' hμ_dfma hν_dfma _ (fun s _ hμνs =>
      (congr_fun (weightedVectorSMul_add_measure B μ ν) s)) f

theorem integral_neg_measure (B : E →L[ℝ] F →L[ℝ] G) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B (-μ))
    = - ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have hBμ := dominatedFinMeasAdditive_weightedVectorSMul_neg B μ
  have lem1 : setToFun (-μ).variation.ennrealToMeasure (weightedVectorSMul B (-μ))
    (dominatedFinMeasAdditive_weightedVectorSMul B (-μ)) f = setToFun μ.variation.ennrealToMeasure
    (weightedVectorSMul B (-μ)) hBμ f := by
    congr 2; exact variation_neg μ
  rw [weightedVectorSMul_neg_measure] at hBμ
  have lem2 : setToFun μ.variation.ennrealToMeasure (weightedVectorSMul B (-μ))
    (dominatedFinMeasAdditive_weightedVectorSMul_neg B μ) f = setToFun μ.variation.ennrealToMeasure
    (-weightedVectorSMul B μ) hBμ f := by
    congr 2; exact (weightedVectorSMul_neg_measure B μ)
  simp [integral_eq_setToFun, lem1, lem2]; rw [← neg_one_smul (R := ℝ) (M := G)]
  refine setToFun_smul_left' (dominatedFinMeasAdditive_weightedVectorSMul B μ) hBμ (-1) ?_ f
  intro; simp

theorem integral_sub_measure (B : E →L[ℝ] F →L[ℝ] G)
    (hμ : Integrable f μ.variation.ennrealToMeasure)
    (hν : Integrable f ν.variation.ennrealToMeasure) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B (μ - ν)) =
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) - ∫ x, f x ∂(VectorMeasureWithPairing.mk B ν) := by
  have hνn : Integrable f (- ν).variation.ennrealToMeasure := by
    simp [variation_neg]; exact hν
  simp [sub_eq_add_neg, integral_add_measure B hμ hνn, integral_neg_measure]

theorem integral_add_pairing (B C : E →L[ℝ] F →L[ℝ] G) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk (B + C) μ) =
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) + ∫ x, f x ∂(VectorMeasureWithPairing.mk C μ) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  simp [integral_eq_setToFun, weightedVectorSMul_add_pairing, ← setToFun_add_left]
  apply setToFun_congr_left; simp

theorem integral_neg_pairing (B : E →L[ℝ] F →L[ℝ] G) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk (-B) μ)
    = - ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  simp [integral_eq_setToFun, weightedVectorSMul_neg_pairing]
  rw [← neg_one_smul (R := ℝ) (M := G)]
  have hBμ1 := (dominatedFinMeasAdditive_weightedVectorSMul B μ)
  have hBμ2 := (dominatedFinMeasAdditive_weightedVectorSMul_neg B μ)
  rw [weightedVectorSMul_neg_measure] at hBμ2
  refine setToFun_smul_left' hBμ1 hBμ2 (-1) ?_ f
  intro; simp

theorem integral_sub_pairing (B C : E →L[ℝ] F →L[ℝ] G) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk (B - C) μ) =
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) - ∫ x, f x ∂(VectorMeasureWithPairing.mk C μ) := by
  simp [sub_eq_add_neg, integral_add_pairing B, integral_neg_pairing]

@[simp]
theorem integral_zero_measure (B : E →L[ℝ] F →L[ℝ] G) (f : α → E) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B (0 : VectorMeasure α F)) = 0 := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    refine setToFun_measure_zero (dominatedFinMeasAdditive_weightedVectorSMul B 0) ?_
    simp [variation_zero]
  · simp [integral, hG]

@[simp]
theorem integral_zero_pairing (μ : VectorMeasure α F) (f : α → E) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk (0 : E →L[ℝ] F →L[ℝ] G) μ) = 0 := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    by_cases hfi : Integrable f μ.variation.ennrealToMeasure
    · simp only [↓reduceDIte, hfi]
      apply L1.setToL1_zero_left' (dominatedFinMeasAdditive_weightedVectorSMul 0 μ); simp
    · simp [hfi]
  · simp [integral, hG]

@[simp]
theorem setIntegral_measure_zero {s : Set α}
    (hs : Bμ.vectorMeasure.variation.ennrealToMeasure s = 0) (f : α → E) :
    ∫ x in s, f x ∂Bμ = 0 := by
  have : Bμ.vectorMeasure.variation s = 0 := by
    by_cases hm : MeasurableSet s
    · rw [← ennrealToMeasure_apply hm]; exact hs
    · exact Bμ.vectorMeasure.variation.not_measurable' hm
  have : (Bμ.vectorMeasure.restrict s).variation = 0 := by sorry
  have : Bμ.vectorMeasure.restrict s = 0 :=
    eq_zero_of_zero_variation (Bμ.vectorMeasure.restrict s) this
  have : Bμ.restrict s = VectorMeasureWithPairing.mk Bμ.pairing 0 := by
    simp [VectorMeasureWithPairing.restrict]
    exact this
  exact this ▸ integral_zero_measure Bμ.pairing f

lemma integral_of_isEmpty [IsEmpty α] : ∫ x, f x ∂Bμ = 0 := by
  have lem := Bμ.vectorMeasure.eq_zero_of_isEmpty ▸ integral_zero_measure Bμ.pairing f
  rw [lem]

theorem integral_finset_sum_measure {ι} {f : α → E}
    {μ : ι → VectorMeasure α F} {s : Finset ι} (B : E →L[ℝ] F →L[ℝ] G)
    (hf : ∀ i ∈ s, Integrable f (μ i).variation.ennrealToMeasure) :
    ∫ a, f a ∂(VectorMeasureWithPairing.mk B (∑ i ∈ s, (μ i))) =
    ∑ i ∈ s, ∫ a, f a ∂(VectorMeasureWithPairing.mk B (μ i)) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ t h ih =>
    rw [Finset.forall_mem_cons] at hf
    rw [Finset.sum_cons, Finset.sum_cons, ← ih hf.2]
    refine integral_add_measure B hf.1 ?_
    apply Integrable.mono_measure
    · exact (integrable_finset_sum_measure.2 hf.2)
    · apply Finset.le_sum_of_subadditive (fun (μ : VectorMeasure α F) => μ.variation.ennrealToMeasure)

theorem nndist_integral_add_measure_le_lintegral
    {f : α → G} (h₁ : Integrable f μ) (h₂ : Integrable f ν) :
    (nndist (∫ x, f x ∂μ) (∫ x, f x ∂(μ + ν)) : ℝ≥0∞) ≤ ∫⁻ x, ‖f x‖ₑ ∂ν := by
  rw [integral_add_measure h₁ h₂, nndist_comm, nndist_eq_nnnorm, add_sub_cancel_left]
  exact enorm_integral_le_lintegral_enorm _

@[simp]
theorem integral_smul_measure (B : E →L[ℝ] F →L[ℝ] G) (c : ℝ) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk (c • B) μ)
    = c • ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  simp_rw [integral_eq_setToFun, ← setToFun_smul_left]
  have hdfma : DominatedFinMeasAdditive μ (weightedSMul (c • μ) : Set α → G →L[ℝ] G) c.toReal :=
    mul_one c.toReal ▸ (dominatedFinMeasAdditive_weightedSMul (c • μ)).of_smul_measure hc
  have hdfma_smul := dominatedFinMeasAdditive_weightedSMul (F := G) (c • μ)
  rw [← setToFun_congr_smul_measure c hc hdfma hdfma_smul f]
  exact setToFun_congr_left' _ _ (fun s _ _ => weightedSMul_smul_measure μ c) f

theorem integral_map_of_stronglyMeasurable {β} [MeasurableSpace β] {φ : α → β} (hφ : Measurable φ)
    {f : β → E} (hfm : StronglyMeasurable f) : ∫ y, f y ∂(VectorMeasureWithPairing.mk Bμ.pairing
    (VectorMeasure.map Bμ.vectorMeasure φ)) = ∫ x, f (φ x) ∂Bμ := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  by_cases hfi : Integrable f (Measure.map φ μ); swap
  · rw [integral_undef hfi, integral_undef]
    exact fun hfφ => hfi ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).2 hfφ)
  borelize G
  have : SeparableSpace (range f ∪ {0} : Set G) := hfm.separableSpace_range_union_singleton
  refine tendsto_nhds_unique
    (tendsto_integral_approxOn_of_measurable_of_range_subset hfm.measurable hfi _ Subset.rfl) ?_
  convert tendsto_integral_approxOn_of_measurable_of_range_subset (hfm.measurable.comp hφ)
    ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).1 hfi) (range f ∪ {0})
    (union_subset_union_left {0} (range_comp_subset_range φ f)) using 1
  ext1 i
  simp only [SimpleFunc.integral_eq, hφ, SimpleFunc.measurableSet_preimage, map_measureReal_apply,
    ← preimage_comp]
  refine (Finset.sum_subset (SimpleFunc.range_comp_subset_range _ hφ) fun y _ hy => ?_).symm
  rw [SimpleFunc.mem_range, ← Set.preimage_singleton_eq_empty, SimpleFunc.coe_comp] at hy
  rw [hy]
  simp

theorem integral_map {β} [MeasurableSpace β] {φ : α → β}
    (hφ : AEMeasurable φ μ) {f : β → E}
    (hfm : AEStronglyMeasurable f (Measure.map φ μ)) :
    ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ :=
  let g := hfm.mk f
  calc
    ∫ y, f y ∂Measure.map φ μ = ∫ y, g y ∂Measure.map φ μ := integral_congr_ae hfm.ae_eq_mk
    _ = ∫ y, g y ∂Measure.map (hφ.mk φ) μ := by congr 1; exact Measure.map_congr hφ.ae_eq_mk
    _ = ∫ x, g (hφ.mk φ x) ∂μ :=
      (integral_map_of_stronglyMeasurable hφ.measurable_mk hfm.stronglyMeasurable_mk)
    _ = ∫ x, g (φ x) ∂μ := integral_congr_ae (hφ.ae_eq_mk.symm.fun_comp _)
    _ = ∫ x, f (φ x) ∂μ := integral_congr_ae <| ae_eq_comp hφ hfm.ae_eq_mk.symm

theorem _root_.MeasurableEmbedding.integral_map {β} {_ : MeasurableSpace β} {f : α → β}
    (hf : MeasurableEmbedding f) (g : β → E) : ∫ y, g y ∂(VectorMeasureWithPairing.mk Bμ.pairing
    (VectorMeasure.map Bμ.vectorMeasure f)) = ∫ x, g (f x) ∂Bμ := by
  by_cases hgm : AEStronglyMeasurable g (Measure.map f Bμ.vectorMeasure.variation.ennrealToMeasure)
  · exact integral_map hf.measurable.aemeasurable hgm
  · rw [integral_non_aestronglyMeasurable hgm, integral_non_aestronglyMeasurable]
    exact fun hgf => hgm (hf.aestronglyMeasurable_map_iff.2 hgf)

theorem _root_.Topology.IsClosedEmbedding.integral_map {β} [TopologicalSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] {φ : α → β} (hφ : IsClosedEmbedding φ)
    (f : β → E) : ∫ y, f y ∂(VectorMeasureWithPairing.mk Bμ.pairing
    (VectorMeasure.map Bμ.vectorMeasure φ)) = ∫ x, f (φ x) ∂Bμ :=
  hφ.measurableEmbedding.integral_map _

theorem integral_map_equiv {β} [MeasurableSpace β] (e : α ≃ᵐ β) (f : β → E) :
    ∫ y, f y ∂(VectorMeasureWithPairing.mk Bμ.pairing
    (VectorMeasure.map Bμ.vectorMeasure e)) = ∫ x, f (e x) ∂Bμ :=
  e.measurableEmbedding.integral_map f

lemma integral_domSMul {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [MeasurableSpace A] [MeasurableConstSMul G A] {μ : Measure A} (g : Gᵈᵐᵃ) (f : A → E) :
    ∫ x, f x ∂g • μ = ∫ x, f ((DomMulAct.mk.symm g)⁻¹ • x) ∂μ :=
  integral_map_equiv (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) f

theorem integral_subtype_comap {α} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (f : α → G) :
    ∫ x : s, f (x : α) ∂(Measure.comap Subtype.val μ) = ∫ x in s, f x ∂μ := by
  rw [← map_comap_subtype_coe hs]
  exact ((MeasurableEmbedding.subtype_coe hs).integral_map _).symm

attribute [local instance] Measure.Subtype.measureSpace in
theorem integral_subtype {α} [MeasureSpace α] {s : Set α} (hs : MeasurableSet s) (f : α → G) :
    ∫ x : s, f x = ∫ x in s, f x := integral_subtype_comap hs f

theorem integral_countable' [Countable α] [MeasurableSingletonClass α]
    (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, f a ∂Bμ = ∑' a, Bμ.pairing (f a) (Bμ.vectorMeasure {a}) := by
  rw [← Measure.sum_smul_dirac μ] at hf
  rw [← Measure.sum_smul_dirac μ, integral_sum_measure hf]
  congr 1 with a : 1
  rw [integral_smul_measure, integral_dirac, Measure.sum_smul_dirac, measureReal_def]

theorem integral_singleton' (hf : StronglyMeasurable f) (a : α) :
    ∫ a in {a}, f a ∂Bμ = Bμ.pairing (f a) (Bμ.vectorMeasure {a}) := by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac' f a hf,
    measureReal_def]

theorem integral_singleton [MeasurableSingletonClass α] (f : α → E) (a : α) :
    ∫ a in {a}, f a ∂Bμ = Bμ.pairing (f a) (Bμ.vectorMeasure {a}) := by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac, measureReal_def]

theorem integral_countable [MeasurableSingletonClass α] {s : Set α} (hs : s.Countable)
    (hf : IntegrableOn f s Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a in s, f a ∂Bμ = ∑' a : s, Bμ.pairing (f a) (Bμ.vectorMeasure {(a : α)}) := by
  have hi : Countable { x // x ∈ s } := Iff.mpr countable_coe_iff hs
  have hf' : Integrable (fun (x : s) => f x) (Measure.comap Subtype.val μ) := by
    rw [IntegrableOn, ← map_comap_subtype_coe, integrable_map_measure] at hf
    · apply hf
    · exact Integrable.aestronglyMeasurable hf
    · exact Measurable.aemeasurable measurable_subtype_coe
    · exact Countable.measurableSet hs
  rw [← integral_subtype_comap hs.measurableSet, integral_countable' hf']
  congr 1 with a : 1
  rw [measureReal_def, Measure.comap_apply Subtype.val Subtype.coe_injective
    (fun s' hs' => MeasurableSet.subtype_image (Countable.measurableSet hs) hs') _
    (MeasurableSet.singleton a)]
  simp [measureReal_def]

theorem integral_finset [MeasurableSingletonClass α] (s : Finset α)
    (hf : IntegrableOn f s Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ x in s, f x ∂Bμ = ∑ x ∈ s, Bμ.pairing (f x) (Bμ.vectorMeasure {x})  := by
  rw [integral_countable s.countable_toSet hf, ← Finset.tsum_subtype']

theorem integral_fintype [MeasurableSingletonClass α] [Fintype α]
    (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ x, f x ∂Bμ = ∑ x, Bμ.pairing (f x) (Bμ.vectorMeasure {x}) := by
  rw [← integral_finset .univ, Finset.coe_univ, VectorMeasureWithPairing.restrict_univ]
  simp [Finset.coe_univ, hf]

theorem integral_unique [Unique α] [hG : CompleteSpace G]
    [IsFiniteMeasure Bμ.vectorMeasure.variation.ennrealToMeasure] :
    ∫ x, f x ∂Bμ = Bμ.pairing (f default) (Bμ.vectorMeasure univ) :=
  calc
    ∫ x, f x ∂Bμ = ∫ _, f default ∂Bμ := by congr with x; congr; exact Unique.uniq _ x
    _ = Bμ.pairing (f default) (Bμ.vectorMeasure univ) := by rw [integral_const]

end Properties

end VectorMeasure
