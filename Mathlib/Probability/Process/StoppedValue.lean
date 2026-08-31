/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Process.LimitProcess
public import Mathlib.Probability.Process.StronglyMeasurablePath
public import Mathlib.Probability.Process.Stopping

/-!

# Stopped value of a stochastic process

In mathlib, given a stochastic process `X : ι → Ω → E` and `τ : Ω → WithTop ι` a stopping time,
we define `stoppedValue X τ ω` as `X (τ ω)` if `τ ω ≠ ⊤`, and an arbitrary value otherwise.
This is not well suited in a number of context where `X` converges almost surely at infinity,
and we would expect the stopped value to be equal to the limit random variable when `τ ω = ⊤`
(this is for example true if `X` is a uniformly integrable martingale).

This limit process is always defined in mathlib as `𝓕.limitProcess X P`, with a default value
when it does not make sense. In this file we define `𝓕.stoppedValue X τ P ω` to be equal
to `X (τ ω)` if `τ ω ≠ ⊤`, and `𝓕.limitProcess X P ω` otherwise.

-/

public section

open MeasureTheory TopologicalSpace Filter WithTop
open scoped ENNReal

namespace MeasureTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ι → Ω → E} {τ σ : Ω → WithTop ι} {ω : Ω} {t : ι}

namespace Filtration

section Def

/-! ### Definition of the stopped value -/

variable [TopologicalSpace E] [Zero E] [Preorder ι] {𝓕 : Filtration ι mΩ}

open scoped Classical in
/-- Given a stochastic process `X` and a stopping time `τ` `𝓕.stoppedValue X τ P` is the process
given by `X (τ ω)`, where `X ⊤` is given by `𝓕.limitProcess X P`. -/
noncomputable def stoppedValue (X : ι → Ω → E) (τ : Ω → WithTop ι)
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) (ω : Ω) : E :=
  if h : τ ω = ⊤
    then 𝓕.limitProcess X P ω
    else
      X ((τ ω).untop h) ω

@[simp]
lemma stoppedValue_of_eq_top (hτ : τ ω = ⊤) :
    𝓕.stoppedValue X τ P ω = 𝓕.limitProcess X P ω := by
  rw [stoppedValue, dite_eq_left hτ]

lemma stoppedValue_of_ne_top (hτ : τ ω ≠ ⊤) :
    𝓕.stoppedValue X τ P ω = X ((τ ω).untop hτ) ω := by
  rw [stoppedValue, dite_eq_right hτ]

@[simp]
lemma stoppedValue_of_eq_coe (hτ : τ ω = t) :
    𝓕.stoppedValue X τ P ω = X t ω := by
  rw! [stoppedValue_of_ne_top, hτ]
  · simp
  · simp [hτ]

@[gcongr]
lemma stoppedValue_congr [IsDirectedOrder ι] [Nonempty ι] [T2Space E] (h : X ≡ᵐ[P] Y) :
    𝓕.stoppedValue X τ P =ᵐ[P] 𝓕.stoppedValue Y τ P := by
  filter_upwards [h, 𝓕.limitProcess_congr h] with ω h1 h2
  obtain _ | _ := eq_or_ne (τ ω) ⊤ <;> simp_all [stoppedValue_of_ne_top]

lemma stoppedValue_congr' (h : τ ω = σ ω) :
    𝓕.stoppedValue X τ P ω = 𝓕.stoppedValue X σ P ω := by
  simp_rw [stoppedValue]
  split_ifs <;> grind

end Def

-- section Measurability

-- /-! ### Strong measurability of the stopped value with respect to the stopped sigma-algebra -/

-- variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
--   {𝓕 : Filtration ι mΩ} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]

-- private lemma IsStoppingTime.stronglyMeasurable_limitProcess_indicator_eq_top
--     [Zero E] (hτ : IsStoppingTime 𝓕 τ) :
--     StronglyMeasurable[hτ.measurableSpace] ({ω | τ ω = ⊤}.indicator (𝓕.limitProcess X P)) := by
--   borelize E
--   rw [stronglyMeasurable_iff_measurable_separable]
--   refine ⟨fun s hs ↦ (hτ.measurableSet _).2 ⟨?_, fun t ↦ ?_⟩,
--     (𝓕.stronglyMeasurable_limit_process'.indicator hτ.measurableSet_eq_top).isSeparable_range⟩
--   · exact hs.preimage (𝓕.stronglyMeasurable_limitProcess.measurable.indicator
--       hτ.measurableSet_eq_top')
--   have : MeasurableSet[𝓕 t] ({ω | 0 ∈ s} ∩ {ω | τ ω ≤ t}) := by
--     by_cases h : 0 ∈ s
--     · simpa [h] using hτ t
--     · simp [h]
--   convert this using 1
--   ext ω
--   simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, and_congr_left_iff]
--   intro h
--   have : τ ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
--   simp [Set.indicator, this]

-- variable [MeasurableSpace ι] [BorelSpace ι]

-- lemma stronglyMeasurable_stoppedValue [Nonempty ι]
--     (h : IsStronglyProgressive 𝓕 X)
--     (hRC : ∀ ω, _root_.IsRightContinuous (X · ω)) (hτ : IsStoppingTime 𝓕 τ) :
--     StronglyMeasurable[hτ.measurableSpace] (stoppedValue X τ) := by
--   borelize E
--   refine stronglyMeasurable_iff_measurable_separable.2 ⟨measurable_stoppedValue h hτ, ?_⟩
--   refine (isSeparable_iUnion_range_of_stronglyMeasurable_of_isRightContinuous ?_ hRC).mono ?_
--   · intro t
--     exact h.stronglyAdapted t |>.mono (𝓕.le t)
--   rintro - ⟨ω, rfl⟩
--   simp [stoppedValue]

-- lemma Filtration.stronglyMeasurable_stoppedValue [Zero E] [OrderBot ι]
--     (hX : IsStronglyProgressive 𝓕 X) (hRC : ∀ ω, _root_.IsRightContinuous (X · ω))
--     (hτ : IsStoppingTime 𝓕 τ) :
--     StronglyMeasurable[hτ.measurableSpace] (𝓕.stoppedValue X τ P) := by
--   have : 𝓕.stoppedValue X τ P = {ω | τ ω = ⊤}.piecewise
--       ({ω | τ ω = ⊤}.indicator (𝓕.limitProcess X P)) (stoppedValue X τ) := by
--     ext ω
--     obtain h | h := eq_or_ne (τ ω) ⊤
--     · simp [h]
--     · simp [h, stoppedValue_eq_stoppedValue]
--   rw [this]
--   refine hτ.stronglyMeasurable_limitProcess_indicator_eq_top.piecewise ?_
--     (stronglyMeasurable_stoppedValue hX hRC hτ)
--   refine (hτ.measurableSet _).2 ⟨hτ.measurableSet_eq_top', fun t ↦ ?_⟩
--   convert MeasurableSet.empty
--   ext
--   simp +contextual

-- end Measurability

variable [TopologicalSpace E] {F G : Type*} [Zero F] [Zero G] [TopologicalSpace F]
  [TopologicalSpace G] [Preorder ι] {𝓕 : Filtration ι mΩ}
  {X Y : ι → Ω → E} {Z : ι → Ω → F} {ω : Ω}

@[simp]
theorem stoppedValue_const [Zero E] (u : ι → Ω → E) (i : ι) :
    (𝓕.stoppedValue u (fun _ => i) P) = u i := by rfl

@[simp]
lemma stoppedValue_comp_of_ne_top [Zero E] {γ : Type*} [Zero γ] [TopologicalSpace γ]
    (X : ι → Ω → E) (f : E → γ) (hτ : τ ω ≠ ⊤) :
    𝓕.stoppedValue (fun t ω ↦ f (X t ω)) τ P ω = f (𝓕.stoppedValue X τ P ω) := by
  simp [stoppedValue_of_ne_top hτ]

@[simp]
lemma stoppedValue_comp₂_of_ne_top [Zero E] (X : ι → Ω → E) (Z : ι → Ω → F) (f : E → F → G)
    (hτ : τ ω ≠ ⊤) :
    𝓕.stoppedValue (fun t ω ↦ f (X t ω) (Z t ω)) τ P ω =
      f (𝓕.stoppedValue X τ P ω) (𝓕.stoppedValue Z τ P ω) := by
  simp [stoppedValue_of_ne_top hτ]

@[to_fun stoppedValue_fun_comp]
lemma HasLimitProcess.stoppedValue_comp [Zero E] [IsDirectedOrder ι] [Nonempty ι] [T2Space F]
    {f : E → F} (hX : HasLimitProcess X 𝓕 P) (hf : Continuous f) :
    𝓕.stoppedValue (fun t ω ↦ f (X t ω)) τ P =ᵐ[P] f ∘ (𝓕.stoppedValue X τ P) := by
  filter_upwards [hX.limitProcess_comp hf] with ω hω
  obtain _ | _ := eq_or_ne (τ ω) ⊤ <;> simp_all

lemma HasLimitProcess.stoppedValue_comp₂ [Zero E] [IsDirectedOrder ι] [Nonempty ι] [T2Space G]
    {f : E → F → G} (hX : HasLimitProcess X 𝓕 P) (hZ : HasLimitProcess Z 𝓕 P)
    (hf : Continuous f.uncurry) :
    𝓕.stoppedValue (fun t ω ↦ f (X t ω) (Z t ω)) τ P =ᵐ[P]
      fun ω ↦ f (𝓕.stoppedValue X τ P ω) (𝓕.stoppedValue Z τ P ω) := by
  filter_upwards [hX.limitProcess_comp₂ hf hZ] with ω hω
  obtain _ | _ := eq_or_ne (τ ω) ⊤ <;> simp_all

@[deprecated (since := "2026-08-28")] alias stoppedValue_norm := stoppedValue_comp_of_ne_top

@[to_fun (attr := to_additive, simp) stoppedValue_fun_inv_of_ne_top]
lemma stoppedValue_inv_of_ne_top [Zero E] [Inv E] (hτ : τ ω ≠ ⊤) :
    𝓕.stoppedValue (X⁻¹) τ P ω = (𝓕.stoppedValue X τ P ω)⁻¹ :=
  stoppedValue_comp_of_ne_top X _ hτ

@[to_fun stoppedValue_fun_neg]
lemma stoppedValue_neg [IsDirectedOrder ι] [Nonempty ι] [AddGroup E] [ContinuousNeg E]
    [T2Space E] :
    𝓕.stoppedValue (-X) τ P =ᵐ[P] -(𝓕.stoppedValue X τ P) := by
  filter_upwards [𝓕.limitProcess_neg X] with ω hω
  obtain _ | _ := eq_or_ne (τ ω) ⊤ <;> simp_all [stoppedValue_of_ne_top]

@[to_fun (attr := to_additive, simp) stoppedValue_fun_mul_of_ne_top]
lemma stoppedValue_mul_of_ne_top [Zero E] [Mul E] (hτ : τ ω ≠ ⊤) :
    𝓕.stoppedValue (X * Y) τ P ω = 𝓕.stoppedValue X τ P ω * 𝓕.stoppedValue Y τ P ω :=
  stoppedValue_comp₂_of_ne_top X Y _ hτ

@[to_fun (attr := to_additive) stoppedValue_fun_mul]
lemma HasLimitProcess.stoppedValue_mul [IsDirectedOrder ι] [Nonempty ι] [Zero E] [Mul E]
    [ContinuousMul E] [T2Space E] (hX : HasLimitProcess X 𝓕 P) (hY : HasLimitProcess Y 𝓕 P) :
    𝓕.stoppedValue (X * Y) τ P =ᵐ[P] 𝓕.stoppedValue X τ P * 𝓕.stoppedValue Y τ P :=
  hX.stoppedValue_comp₂ hY continuous_mul

@[to_fun (attr := to_additive, simp) stoppedValue_fun_div_of_ne_top]
lemma stoppedValue_div_of_ne_top [Zero E] [Div E] (hτ : τ ω ≠ ⊤) :
    𝓕.stoppedValue (X / Y) τ P ω = 𝓕.stoppedValue X τ P ω / 𝓕.stoppedValue Y τ P ω :=
  stoppedValue_comp₂_of_ne_top X Y _ hτ

@[to_fun (attr := to_additive, simp) stoppedValue_const_fun_smul_of_ne_top]
lemma stoppedValue_const_smul_of_ne_top [Zero E] {𝕜 : Type*} [SMul 𝕜 E] (c : 𝕜) (hτ : τ ω ≠ ⊤) :
    𝓕.stoppedValue (c • X) τ P ω = c • 𝓕.stoppedValue X τ P ω :=
  stoppedValue_comp_of_ne_top X _ hτ

@[to_fun stoppedValue_const_fun_smul]
lemma stoppedValue_const_smul [Zero E] [IsDirectedOrder ι] [Nonempty ι] [T2Space E] {𝕜 : Type*}
    [GroupWithZero 𝕜] [MulActionWithZero 𝕜 E] [ContinuousConstSMul 𝕜 E] (c : 𝕜) :
    𝓕.stoppedValue (c • X) τ P =ᵐ[P] c • 𝓕.stoppedValue X τ P := by
  filter_upwards [𝓕.limitProcess_smul X c] with ω hω
  obtain _ | _ := eq_or_ne (τ ω) ⊤ <;> simp_all [stoppedValue_of_ne_top]

@[simp] lemma stoppedValue_const_bot [Zero E] [Bot ι] :
    𝓕.stoppedValue X (fun _ ↦ ⊥) P = X ⊥ :=
  stoppedValue_const X ⊥

section stoppedProcess

variable {ι : Type*} [LinearOrder ι] [Nonempty ι] {𝓕 : Filtration ι mΩ}
  {X : ι → Ω → E} {τ σ : Ω → WithTop ι} [Zero E]

theorem stoppedProcess_eq_stoppedValue :
    stoppedProcess X τ = fun (t : ι) ↦ 𝓕.stoppedValue X (fun ω => min t (τ ω)) P := by
  ext t ω
  simp [stoppedProcess, stoppedValue_of_ne_top, WithTop.untopA_eq_untop]

theorem stoppedProcess_eq_stoppedValue_apply (i : ι) (ω : Ω) :
    stoppedProcess X τ i ω = 𝓕.stoppedValue X (fun ω ↦ min i (τ ω)) P ω :=
  congrFun₂ stoppedProcess_eq_stoppedValue _ _

variable [T2Space E]



section Measurability

variable [MeasurableSpace ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [BorelSpace ι]

theorem stronglyMeasurable_stoppedValue_of_le (h : IsStronglyProgressive 𝓕 X)
    (hτ : IsStoppingTime 𝓕 τ) {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) :
    StronglyMeasurable[𝓕 n] (𝓕.stoppedValue X τ P) := by
  have h1 ω : τ ω ≠ ⊤ := by
    grw [← lt_top_iff_ne_top, hτ_le, WithTop.coe_lt_top]
  have h2 ω : (τ ω).untop (h1 ω) ≤ n := by simpa using hτ_le ω
  have : 𝓕.stoppedValue X τ P =
      (fun p : Set.Iic n × Ω => X (↑p.fst) p.snd) ∘ fun ω => (⟨(τ ω).untop (h1 ω), h2 ω⟩, ω) := by
    ext ω; simp [stoppedValue_of_ne_top, h1]
  rw [this]
  refine StronglyMeasurable.comp_measurable (h n) ?_
  refine (Measurable.subtype_mk ?_).prodMk measurable_id
  exact (hτ.measurable_of_le hτ_le).untop h1

lemma measurableSet_preimage_stoppedValue_inter [PseudoMetrizableSpace E] [MeasurableSpace E]
    [BorelSpace E]
    (hf_prog : IsStronglyProgressive 𝓕 X) (hτ : IsStoppingTime 𝓕 τ)
    {t : Set E} (ht : MeasurableSet t) (i : ι) :
    MeasurableSet[𝓕 i] (𝓕.stoppedValue X τ P ⁻¹' t ∩ {ω | τ ω ≤ i}) := by
  have h_str_meas : ∀ i, StronglyMeasurable[𝓕 i] (𝓕.stoppedValue X (fun ω => min (τ ω) i) P) :=
    fun i =>
      stronglyMeasurable_stoppedValue_of_le hf_prog (hτ.min_const i) fun _ => min_le_right _ _
  suffices 𝓕.stoppedValue X τ P ⁻¹' t ∩ {ω : Ω | τ ω ≤ i} =
      (𝓕.stoppedValue X (fun ω => min (τ ω) i) P) ⁻¹' t ∩ {ω : Ω | τ ω ≤ i} by
    rw [this]; exact ((h_str_meas i).measurable ht).inter (hτ.measurableSet_le i)
  ext1 ω
  simp only [stoppedValue, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
    and_congr_left_iff]
  intro h
  rw! [min_eq_left h]
  rfl

theorem measurable_stoppedValue [PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
    (hf_prog : IsStronglyProgressive 𝓕 X) (hτ : IsStoppingTime 𝓕 τ) :
    Measurable[hτ.measurableSpace] (𝓕.stoppedValue X τ P) := by
  have h_str_meas : ∀ i, StronglyMeasurable[𝓕 i] (𝓕.stoppedValue X (fun ω => min (τ ω) i) P) :=
    fun i =>
      stronglyMeasurable_stoppedValue_of_le hf_prog (hτ.min_const i) fun _ => min_le_right _ _
  intro t ht
  refine ⟨?_, fun i ↦ measurableSet_preimage_stoppedValue_inter hf_prog hτ ht i⟩
  obtain ⟨seq : ℕ → ι, h_seq_tendsto⟩ := (atTop : Filter ι).exists_seq_tendsto
  have : 𝓕.stoppedValue X τ P ⁻¹' t
      = (⋃ n, 𝓕.stoppedValue X τ P ⁻¹' t ∩ {ω | τ ω ≤ seq n})
        ∪ (𝓕.stoppedValue X τ P ⁻¹' t ∩ {ω | τ ω = ⊤}) := by
    ext1 ω
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq, exists_and_left]
    rw [← and_or_left, iff_self_and]
    intro _
    by_cases h : τ ω = ⊤
    · exact .inr h
    · lift τ ω to ι using h with t
      simp only [coe_le_coe, coe_ne_top, or_false]
      rw [tendsto_atTop] at h_seq_tendsto
      exact (h_seq_tendsto t).exists
  rw [this]
  refine MeasurableSet.union ?_ ?_
  · exact MeasurableSet.iUnion fun i ↦ le_iSup 𝓕 (seq i) _
      (measurableSet_preimage_stoppedValue_inter hf_prog hτ ht (seq i))
  · have : 𝓕.stoppedValue X τ P ⁻¹' t ∩ {ω | τ ω = ⊤}
       = 𝓕.limitProcess X P ⁻¹' t ∩ {ω | τ ω = ⊤} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, stoppedValue, untopA,
        Set.mem_ofPred_eq, and_congr_left_iff]
      intro h
      simp [h]
    rw [this]
    refine MeasurableSet.inter (ht.preimage ?_) hτ.measurableSet_eq_top'
    exact stronglyMeasurable_limitProcess.measurable

/-! ### Strong measurability of the stopped value with respect to the stopped sigma-algebra -/

variable [TopologicalSpace.PseudoMetrizableSpace E]

private lemma IsStoppingTime.stronglyMeasurable_limitProcess_indicator_eq_top
    [Zero E] (hτ : IsStoppingTime 𝓕 τ) :
    StronglyMeasurable[hτ.measurableSpace] ({ω | τ ω = ⊤}.indicator (𝓕.limitProcess X P)) := by
  borelize E
  rw [stronglyMeasurable_iff_measurable_separable]
  refine ⟨fun s hs ↦ (hτ.measurableSet _).2 ⟨?_, fun t ↦ ?_⟩,
    (𝓕.stronglyMeasurable_limit_process'.indicator hτ.measurableSet_eq_top).isSeparable_range⟩
  · exact hs.preimage (𝓕.stronglyMeasurable_limitProcess.measurable.indicator
      hτ.measurableSet_eq_top')
  have : MeasurableSet[𝓕 t] ({ω | 0 ∈ s} ∩ {ω | τ ω ≤ t}) := by
    by_cases h : 0 ∈ s
    · simpa [h] using hτ t
    · simp [h]
  convert this using 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, and_congr_left_iff]
  intro h
  have : τ ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
  simp [Set.indicator, this]

lemma stronglyMeasurable_stoppedValue
    (h : IsStronglyProgressive 𝓕 X)
    (hRC : ∀ ω, _root_.IsRightContinuous (X · ω)) (hτ : IsStoppingTime 𝓕 τ) :
    StronglyMeasurable[hτ.measurableSpace] (𝓕.stoppedValue X τ P) := by
  borelize E
  refine stronglyMeasurable_iff_measurable_separable.2 ⟨measurable_stoppedValue h hτ, ?_⟩
  refine ((isSeparable_iUnion_range_of_stronglyMeasurable_of_isRightContinuous ?_ hRC).union
      (stronglyMeasurable_limitProcess (𝓕 := 𝓕) (P := P) (X := X)).isSeparable_range).mono ?_
  · intro t
    exact h.stronglyAdapted t |>.mono (𝓕.le t)
  rintro - ⟨ω, rfl⟩
  cases h : τ ω
  · simp [h]
  · simp [h]

end Measurability

variable [TopologicalSpace ι] [MeasurableSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [BorelSpace ι] [PseudoMetrizableSpace E]

theorem HasLimitProcess.limitProcess_stoppedValue (hX : HasLimitProcess X 𝓕 P)
    (h1 : IsStronglyProgressive 𝓕 X) (h2 : ∀ ω, _root_.IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) :
    𝓕.limitProcess (stoppedProcess X τ) P =ᵐ[P] 𝓕.stoppedValue X τ P := by
  apply limitProcess_ae_eq
  · exact stronglyMeasurable_stoppedValue h1 h2 hτ |>.mono hτ.measurableSpace_le'
  filter_upwards [hX.ae_tendsto_limitProcess] with ω hω
  cases hτ : τ ω with
  | top => simp [stoppedProcess, hτ, hω]
  | coe t =>
    refine tendsto_const_nhds.congr' ?_
    refine eventually_atTop.2 ⟨t, fun s hs ↦ ?_⟩
    simp_all [stoppedProcess]

theorem HasLimitProcess.stoppedValue_stoppedProcess (hX : HasLimitProcess X 𝓕 P)
    (h1 : IsStronglyProgressive 𝓕 X) (h2 : ∀ ω, _root_.IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) :
    𝓕.stoppedValue (stoppedProcess X τ) σ P =ᵐ[P] 𝓕.stoppedValue X (fun ω ↦ min (σ ω) (τ ω)) P := by
  filter_upwards [hX.limitProcess_stoppedValue h1 h2 hτ] with ω hω
  cases h : σ ω with
  | top =>
    rw [stoppedValue_of_eq_top h, hω, stoppedValue_congr']
    simp [h]
  | coe t =>
    rw! [stoppedValue_of_eq_coe h, stoppedValue_of_ne_top, stoppedProcess, untopA_eq_untop, h]
    · rfl
    · simp [h]

theorem stoppedValue_stoppedProcess_apply {ω : Ω} (hω : σ ω ≠ ⊤) :
    𝓕.stoppedValue (stoppedProcess X τ) σ P ω = 𝓕.stoppedValue X (fun ω ↦ min (σ ω) (τ ω)) P ω := by
  rw [stoppedValue_of_ne_top hω, stoppedProcess, stoppedValue_of_ne_top,
    ← untopA_eq_untop (a := min _ _)]
  · simp
  · grind

theorem stoppedValue_stoppedProcess_ae_eq {P : Measure Ω}
    (hσ : ∀ᵐ ω ∂P, σ ω ≠ ⊤) :
    𝓕.stoppedValue (stoppedProcess X τ) σ P =ᵐ[P] 𝓕.stoppedValue X (fun ω ↦ min (σ ω) (τ ω)) P := by
  filter_upwards [hσ] with ω hσ using by simp [stoppedValue_stoppedProcess_apply, hσ]

end stoppedProcess

theorem stoppedValue_eq_of_mem_finset [AddCommMonoid E] {s : Finset ι}
   (hbdd : ∀ ω, τ ω ∈ (WithTop.some '' s)) :
    𝓕.stoppedValue X τ P = ∑ i ∈ s, Set.indicator {ω | τ ω = i} (X i) := by
  ext y
  classical
  have hτ ω : τ ω ≠ ⊤ := by
    obtain ⟨t, ht1, ht2⟩ := hbdd ω
    simp [← ht2]
  rw [stoppedValue_of_ne_top (hτ y), Finset.sum_apply, Finset.sum_indicator_eq_sum_filter]
  suffices {i ∈ s | y ∈ {ω : Ω | τ ω = (i : ι)}} = ({(τ y).untop (hτ y)} : Finset ι) by
    rw [this, Finset.sum_singleton]
  ext1 ω
  simp only [Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_singleton]
  constructor <;> intro h
  · simp [h.2]
  · simp only [h]
    specialize hbdd y
    have : τ y ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
    lift τ y to ι using this with i hi
    simpa using hbdd

theorem stoppedValue_eq' [LocallyFiniteOrderBot ι] [AddCommMonoid E] {N : ι}
    (hbdd : ∀ ω, τ ω ≤ N) :
    𝓕.stoppedValue X τ P = ∑ i ∈ Finset.Iic N, Set.indicator {ω | τ ω = i} (X i) := by
  refine stoppedValue_eq_of_mem_finset fun ω ↦ ?_
  simp only [Finset.coe_Iic, Set.mem_image]
  specialize hbdd ω
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩

section StoppedValue

variable {ι E : Type*} [PartialOrder ι] {𝓕 : Filtration ι mΩ}
  {X : ι → Ω → E} {τ σ : Ω → WithTop ι} [NormedAddCommGroup E] {p : ℝ≥0∞}

theorem memLp_stoppedValue_of_mem_finset (hτ : IsStoppingTime 𝓕 τ) (hu : ∀ n, MemLp (X n) p P)
    {s : Finset ι} (hbdd : ∀ ω, τ ω ∈ WithTop.some '' s) :
    MemLp (𝓕.stoppedValue X τ P) p P := by
  rw [stoppedValue_eq_of_mem_finset hbdd]
  refine memLp_finsetSum' _ fun i _ => MemLp.indicator ?_ (hu i)
  refine 𝓕.le i {a : Ω | τ a = i} (hτ.measurableSet_eq_of_countable_range ?_ i)
  have : Set.range τ ⊆ WithTop.some '' s := by
    rintro x ⟨y, rfl⟩
    exact hbdd y
  exact ((Finset.finite_toSet s).image _).subset this |>.countable

theorem memLp_stoppedValue [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime 𝓕 τ)
    (hu : ∀ n, MemLp (X n) p P) {N : ι} (hbdd : ∀ ω, τ ω ≤ N) :
    MemLp (𝓕.stoppedValue X τ P) p P := by
  refine memLp_stoppedValue_of_mem_finset hτ hu (s := Finset.Iic N) fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  specialize hbdd ω
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩

theorem integrable_stoppedValue_of_mem_finset (hτ : IsStoppingTime 𝓕 τ)
    (hu : ∀ n, Integrable (X n) P) {s : Finset ι} (hbdd : ∀ ω, τ ω ∈ WithTop.some '' s) :
    Integrable (𝓕.stoppedValue X τ P) P := by
  simp_rw [← memLp_one_iff_integrable] at hu ⊢
  exact memLp_stoppedValue_of_mem_finset hτ hu hbdd

variable (ι)

@[fun_prop]
theorem integrable_stoppedValue [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime 𝓕 τ)
    (hu : ∀ n, Integrable (X n) P) {N : ι} (hbdd : ∀ ω, τ ω ≤ N) :
    Integrable (𝓕.stoppedValue X τ P) P := by
  refine integrable_stoppedValue_of_mem_finset hτ hu (s := Finset.Iic N) fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  specialize hbdd ω
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩

end StoppedValue

/-! ### Filtrations indexed by `ℕ` -/

variable {u : ℕ → Ω → E} {τ π : Ω → WithTop ℕ}

theorem stoppedValue_sub_eq_sum [AddCommGroup E] (hle : τ ≤ π) (hπ : ∀ ω, π ω ≠ ⊤) :
    stoppedValue u π - 𝓕.stoppedValue X τ P = fun ω =>
      (∑ i ∈ Finset.Ico (τ ω).untopA (π ω).untopA, (u (i + 1) - u i)) ω := by
  ext ω
  have h_le' : (τ ω).untopA ≤ (π ω).untopA := untopA_mono (mod_cast hπ ω) (hle ω)
  rw [Finset.sum_Ico_eq_sub _ h_le', Finset.sum_range_sub, Finset.sum_range_sub]
  simp [stoppedValue]

theorem stoppedValue_sub_eq_sum' [AddCommGroup E] (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    stoppedValue u π - 𝓕.stoppedValue X τ P = fun ω =>
      (∑ i ∈ Finset.range (N + 1), Set.indicator {ω | τ ω ≤ i ∧ i < π ω} (u (i + 1) - u i)) ω := by
  have hπ_top ω : π ω ≠ ⊤ := fun h ↦ by specialize hbdd ω; simp [h] at hbdd
  have hτ_top ω : τ ω ≠ ⊤ := ne_top_of_le_ne_top (hπ_top ω) (hle ω)
  rw [stoppedValue_sub_eq_sum hle hπ_top]
  ext ω
  simp only [Finset.sum_apply, Finset.sum_indicator_eq_sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Set.mem_ofPred_eq, Finset.mem_Ico]
  specialize hbdd ω
  lift τ ω to ℕ using hτ_top ω with t ht
  lift π ω to ℕ using hπ_top ω with b hb
  simp at hbdd
  simp [← ENat.some_eq_natCast]
  grind

theorem stoppedValue_eq {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) : 𝓕.stoppedValue X τ P = fun x =>
    (∑ i ∈ Finset.range (N + 1), Set.indicator {ω | τ ω = i} (u i)) x := by
  refine stoppedValue_eq_of_mem_finset fun ω ↦ ?_
  specialize hbdd ω
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
  lift τ ω to ℕ using h_top with t ht
  simp only [Nat.cast_withTop, WithTop.coe_le_coe] at hbdd
  exact ⟨t, by simpa [Nat.lt_succ_iff], rfl⟩

theorem stoppedValue_piecewise_const {ι' α : Type*} [Nonempty ι'] {i j : ι'} {f : ι' → Ω → α} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) = s.piecewise (f i) (f j) := by
  ext ω; rw [stoppedValue]; by_cases hx : ω ∈ s <;> simp [hx]

theorem stoppedValue_piecewise_const' {ι' α : Type*} [AddCommGroup α]
    [Nonempty ι'] {i j : ι'} {f : ι' → Ω → α} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) =
    s.indicator (f i) + sᶜ.indicator (f j) := by
  ext ω; rw [stoppedValue]; by_cases hx : ω ∈ s <;> simp [hx]

end MeasureTheory.Filtration
