/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.IndicatorFunction

/-!
# Indicator of a set as an element of `Lp`

For a set `s` with `(hs : MeasurableSet s)` and `(hμs : μ s < ∞)`, we build
`indicatorConstLp p hs hμs c`, the element of `Lp` corresponding to `s.indicator (fun _ ↦ c)`.

## Main definitions

* `MeasureTheory.indicatorConstLp`: Indicator of a set as an element of `Lp`.
* `MeasureTheory.Lp.const`: Constant function as an element of `Lp` for a finite measure.
-/

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology symmDiff

variable {α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α} [NormedAddCommGroup E]

namespace MeasureTheory

/-- The `eLpNorm` of the indicator of a set is uniformly small if the set itself has small measure,
for any `p < ∞`. Given here as an existential `∀ ε > 0, ∃ η > 0, ...` to avoid later
management of `ℝ≥0∞`-arithmetic. -/
theorem exists_eLpNorm_indicator_le (hp : p ≠ ∞) (c : E) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η → eLpNorm (s.indicator fun _ ↦ c) p μ ≤ ε := by
  rcases eq_or_ne p 0 with (rfl | h'p)
  · exact ⟨1, zero_lt_one, fun s _ ↦ by simp⟩
  have hp₀ : 0 < p := bot_lt_iff_ne_bot.2 h'p
  have hp₀' : 0 ≤ 1 / p.toReal := div_nonneg zero_le_one ENNReal.toReal_nonneg
  have hp₀'' : 0 < p.toReal := ENNReal.toReal_pos hp₀.ne' hp
  obtain ⟨η, hη_pos, hη_le⟩ : ∃ η : ℝ≥0, 0 < η ∧ ‖c‖ₑ * (η : ℝ≥0∞) ^ (1 / p.toReal) ≤ ε := by
    have :
      Filter.Tendsto (fun x : ℝ≥0 ↦ ((‖c‖₊ * x ^ (1 / p.toReal) : ℝ≥0) : ℝ≥0∞)) (𝓝 0)
        (𝓝 (0 : ℝ≥0)) := by
      rw [ENNReal.tendsto_coe]
      convert (NNReal.continuousAt_rpow_const (Or.inr hp₀')).tendsto.const_mul _
      simp [hp₀''.ne']
    have hε' : 0 < ε := hε.bot_lt
    obtain ⟨δ, hδ, hδε'⟩ := NNReal.nhds_zero_basis.eventually_iff.mp (this.eventually_le_const hε')
    obtain ⟨η, hη, hηδ⟩ := exists_between hδ
    refine ⟨η, hη, ?_⟩
    simpa only [← ENNReal.coe_rpow_of_nonneg _ hp₀', enorm, ← ENNReal.coe_mul] using hδε' hηδ
  refine ⟨η, hη_pos, fun s hs ↦ ?_⟩
  refine (eLpNorm_indicator_const_le _ _).trans (le_trans ?_ hη_le)
  exact mul_le_mul_left' (ENNReal.rpow_le_rpow hs hp₀') _

section Topology
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

/-- A bounded measurable function with compact support is in L^p. -/
theorem _root_.HasCompactSupport.memLp_of_bound {f : X → E} (hf : HasCompactSupport f)
    (h2f : AEStronglyMeasurable f μ) (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : MemLp f p μ := by
  have := memLp_top_of_bound h2f C hfC
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x ↦ image_eq_zero_of_notMem_tsupport) (hf.measure_lt_top.ne) le_top

@[deprecated (since := "2025-02-21")]
alias _root_.HasCompactSupport.memℒp_of_bound := _root_.HasCompactSupport.memLp_of_bound

/-- A continuous function with compact support is in L^p. -/
theorem _root_.Continuous.memLp_of_hasCompactSupport [OpensMeasurableSpace X]
    {f : X → E} (hf : Continuous f) (h'f : HasCompactSupport f) : MemLp f p μ := by
  have := hf.memLp_top_of_hasCompactSupport h'f μ
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x ↦ image_eq_zero_of_notMem_tsupport) (h'f.measure_lt_top.ne) le_top

@[deprecated (since := "2025-02-21")]
alias _root_.Continuous.memℒp_of_hasCompactSupport := _root_.Continuous.memLp_of_hasCompactSupport

end Topology

section IndicatorConstLp

open Set Function

variable {s : Set α} {hs : MeasurableSet s} {hμs : μ s ≠ ∞} {c : E}

/-- Indicator of a set as an element of `Lp`. -/
def indicatorConstLp (p : ℝ≥0∞) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) : Lp E p μ :=
  MemLp.toLp (s.indicator fun _ ↦ c) (memLp_indicator_const p hs c (Or.inr hμs))

/-- A version of `Set.indicator_add` for `MeasureTheory.indicatorConstLp` -/
theorem indicatorConstLp_add {c' : E} :
    indicatorConstLp p hs hμs c + indicatorConstLp p hs hμs c' =
    indicatorConstLp p hs hμs (c + c') := by
  simp_rw [indicatorConstLp, ← MemLp.toLp_add, indicator_add]
  rfl

/-- A version of `Set.indicator_sub` for `MeasureTheory.indicatorConstLp` -/
theorem indicatorConstLp_sub {c' : E} :
    indicatorConstLp p hs hμs c - indicatorConstLp p hs hμs c' =
    indicatorConstLp p hs hμs (c - c') := by
  simp_rw [indicatorConstLp, ← MemLp.toLp_sub, indicator_sub]
  rfl

theorem indicatorConstLp_coeFn : ⇑(indicatorConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ ↦ c :=
  MemLp.coeFn_toLp (memLp_indicator_const p hs c (Or.inr hμs))

theorem indicatorConstLp_coeFn_mem : ∀ᵐ x : α ∂μ, x ∈ s → indicatorConstLp p hs hμs c x = c :=
  indicatorConstLp_coeFn.mono fun _x hx hxs ↦ hx.trans (Set.indicator_of_mem hxs _)

theorem indicatorConstLp_coeFn_notMem : ∀ᵐ x : α ∂μ, x ∉ s → indicatorConstLp p hs hμs c x = 0 :=
  indicatorConstLp_coeFn.mono fun _x hx hxs ↦ hx.trans (Set.indicator_of_notMem hxs _)

@[deprecated (since := "2025-05-24")]
alias indicatorConstLp_coeFn_nmem := indicatorConstLp_coeFn_notMem

theorem norm_indicatorConstLp (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * μ.real s ^ (1 / p.toReal) := by
  rw [Lp.norm_def, eLpNorm_congr_ae indicatorConstLp_coeFn,
    eLpNorm_indicator_const hs hp_ne_zero hp_ne_top, ENNReal.toReal_mul, measureReal_def,
    ENNReal.toReal_rpow, toReal_enorm]

theorem norm_indicatorConstLp_top (hμs_ne_zero : μ s ≠ 0) :
    ‖indicatorConstLp ∞ hs hμs c‖ = ‖c‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae indicatorConstLp_coeFn,
    eLpNorm_indicator_const' hs hμs_ne_zero ENNReal.top_ne_zero, ENNReal.toReal_top,
    _root_.div_zero, ENNReal.rpow_zero, mul_one, toReal_enorm]

theorem norm_indicatorConstLp' (hp_pos : p ≠ 0) (hμs_pos : μ s ≠ 0) :
    ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * μ.real s ^ (1 / p.toReal) := by
  by_cases hp_top : p = ∞
  · rw [hp_top, ENNReal.toReal_top, _root_.div_zero, Real.rpow_zero, mul_one]
    exact norm_indicatorConstLp_top hμs_pos
  · exact norm_indicatorConstLp hp_pos hp_top

theorem norm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖ ≤ ‖c‖ * μ.real s ^ (1 / p.toReal) := by
  rw [indicatorConstLp, Lp.norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (eLpNorm_indicator_const_le _ _).trans_eq ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, measureReal_def,
    ENNReal.toReal_rpow, ENNReal.ofReal_toReal]
  finiteness

theorem nnnorm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖₊ ≤ ‖c‖₊ * (μ s).toNNReal ^ (1 / p.toReal) :=
  norm_indicatorConstLp_le

theorem enorm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖ₑ ≤ ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
  simpa [ENNReal.coe_rpow_of_nonneg, ENNReal.coe_toNNReal hμs, Lp.enorm_def, ← enorm_eq_nnnorm]
    using ENNReal.coe_le_coe.2 <| nnnorm_indicatorConstLp_le (c := c) (hμs := hμs)

theorem edist_indicatorConstLp_eq_enorm {t : Set α} {ht : MeasurableSet t} {hμt : μ t ≠ ∞} :
    edist (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt c) =
      ‖indicatorConstLp p (hs.symmDiff ht) (measure_symmDiff_ne_top hμs hμt) c‖ₑ := by
  unfold indicatorConstLp
  rw [Lp.edist_toLp_toLp, eLpNorm_indicator_sub_indicator, Lp.enorm_toLp]

theorem dist_indicatorConstLp_eq_norm {t : Set α} {ht : MeasurableSet t} {hμt : μ t ≠ ∞} :
    dist (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt c) =
      ‖indicatorConstLp p (hs.symmDiff ht) (measure_symmDiff_ne_top hμs hμt) c‖ := by
  -- Squeezed for performance reasons
  simp only [Lp.dist_edist, edist_indicatorConstLp_eq_enorm, enorm, ENNReal.coe_toReal,
    Lp.coe_nnnorm]

/-- A family of `indicatorConstLp` functions tends to an `indicatorConstLp`,
if the underlying sets tend to the set in the sense of the measure of the symmetric difference. -/
theorem tendsto_indicatorConstLp_set [hp₁ : Fact (1 ≤ p)] {β : Type*} {l : Filter β} {t : β → Set α}
    {ht : ∀ b, MeasurableSet (t b)} {hμt : ∀ b, μ (t b) ≠ ∞} (hp : p ≠ ∞)
    (h : Tendsto (fun b ↦ μ (t b ∆ s)) l (𝓝 0)) :
    Tendsto (fun b ↦ indicatorConstLp p (ht b) (hμt b) c) l (𝓝 (indicatorConstLp p hs hμs c)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hp₀ : p ≠ 0 := (one_pos.trans_le hp₁.out).ne'
  simp only [dist_indicatorConstLp_eq_norm, norm_indicatorConstLp hp₀ hp]
  convert tendsto_const_nhds.mul
    (((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).rpow_const _)
  · simp [ENNReal.toReal_eq_zero_iff, hp, hp₀]
  · simp

/-- A family of `indicatorConstLp` functions is continuous in the parameter,
if `μ (s y ∆ s x)` tends to zero as `y` tends to `x` for all `x`. -/
theorem continuous_indicatorConstLp_set [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X]
    {s : X → Set α} {hs : ∀ x, MeasurableSet (s x)} {hμs : ∀ x, μ (s x) ≠ ∞} (hp : p ≠ ∞)
    (h : ∀ x, Tendsto (fun y ↦ μ (s y ∆ s x)) (𝓝 x) (𝓝 0)) :
    Continuous fun x ↦ indicatorConstLp p (hs x) (hμs x) c :=
  continuous_iff_continuousAt.2 fun x ↦ tendsto_indicatorConstLp_set hp (h x)

@[simp]
theorem indicatorConstLp_empty :
    indicatorConstLp p MeasurableSet.empty (by simp : μ ∅ ≠ ∞) c = 0 := by
  simp only [indicatorConstLp, Set.indicator_empty', MemLp.toLp_zero]

theorem indicatorConstLp_inj {s t : Set α} (hs : MeasurableSet s) (hsμ : μ s ≠ ∞)
    (ht : MeasurableSet t) (htμ : μ t ≠ ∞) {c : E} (hc : c ≠ 0) :
    indicatorConstLp p hs hsμ c = indicatorConstLp p ht htμ c ↔ s =ᵐ[μ] t := by
  simp_rw [← indicator_const_eventuallyEq hc, indicatorConstLp, MemLp.toLp_eq_toLp_iff]

theorem memLp_add_of_disjoint {f g : α → E} (h : Disjoint (support f) (support g))
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    MemLp (f + g) p μ ↔ MemLp f p μ ∧ MemLp g p μ := by
  borelize E
  refine ⟨fun hfg ↦ ⟨?_, ?_⟩, fun h ↦ h.1.add h.2⟩
  · rw [← Set.indicator_add_eq_left h]; exact hfg.indicator (measurableSet_support hf.measurable)
  · rw [← Set.indicator_add_eq_right h]; exact hfg.indicator (measurableSet_support hg.measurable)

@[deprecated (since := "2025-02-21")]
alias memℒp_add_of_disjoint := memLp_add_of_disjoint

/-- The indicator of a disjoint union of two sets is the sum of the indicators of the sets. -/
theorem indicatorConstLp_disjoint_union {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : Disjoint s t) (c : E) :
    indicatorConstLp p (hs.union ht) (measure_union_ne_top hμs hμt) c =
      indicatorConstLp p hs hμs c + indicatorConstLp p ht hμt c := by
  ext1
  grw [Lp.coeFn_add, indicatorConstLp_coeFn]
  refine
    EventuallyEq.trans ?_
      (EventuallyEq.fun_add indicatorConstLp_coeFn.symm indicatorConstLp_coeFn.symm)
  rw [Set.indicator_union_of_disjoint hst]

end IndicatorConstLp

section const

variable (μ p)
variable [IsFiniteMeasure μ] (c : E)

/-- Constant function as an element of `MeasureTheory.Lp` for a finite measure. -/
protected def Lp.const : E →+ Lp E p μ where
  toFun c := ⟨AEEqFun.const α c, const_mem_Lp α μ c⟩
  map_zero' := rfl
  map_add' _ _ := rfl

lemma Lp.coeFn_const : Lp.const p μ c =ᵐ[μ] Function.const α c :=
  AEEqFun.coeFn_const α c

@[simp] lemma Lp.const_val : (Lp.const p μ c).1 = AEEqFun.const α c := rfl

@[simp]
lemma MemLp.toLp_const : MemLp.toLp _ (memLp_const c) = Lp.const p μ c := rfl

@[deprecated (since := "2025-02-21")]
alias Memℒp.toLp_const := MemLp.toLp_const

@[simp]
lemma indicatorConstLp_univ :
    indicatorConstLp p .univ (measure_ne_top μ _) c = Lp.const p μ c := by
  rw [← MemLp.toLp_const, indicatorConstLp]
  simp only [Set.indicator_univ]

theorem Lp.norm_const [NeZero μ] (hp_zero : p ≠ 0) :
    ‖Lp.const p μ c‖ = ‖c‖ * μ.real Set.univ ^ (1 / p.toReal) := by
  have := NeZero.ne μ
  rw [← MemLp.toLp_const, Lp.norm_toLp, eLpNorm_const] <;> try assumption
  rw [measureReal_def, ENNReal.toReal_mul, toReal_enorm, ← ENNReal.toReal_rpow]

theorem Lp.norm_const' (hp_zero : p ≠ 0) (hp_top : p ≠ ∞) :
    ‖Lp.const p μ c‖ = ‖c‖ * μ.real Set.univ ^ (1 / p.toReal) := by
  rw [← MemLp.toLp_const, Lp.norm_toLp, eLpNorm_const'] <;> try assumption
  rw [measureReal_def, ENNReal.toReal_mul, toReal_enorm, ← ENNReal.toReal_rpow]

theorem Lp.norm_const_le : ‖Lp.const p μ c‖ ≤ ‖c‖ * μ.real Set.univ ^ (1 / p.toReal) := by
  rw [← indicatorConstLp_univ]
  exact norm_indicatorConstLp_le

/-- `MeasureTheory.Lp.const` as a `LinearMap`. -/
@[simps] protected def Lp.constₗ (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    E →ₗ[𝕜] Lp E p μ where
  toFun := Lp.const p μ
  map_add' := map_add _
  map_smul' _ _ := rfl

/-- `MeasureTheory.Lp.const` as a `ContinuousLinearMap`. -/
@[simps! apply]
protected def Lp.constL (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)] :
    E →L[𝕜] Lp E p μ :=
  (Lp.constₗ p μ 𝕜).mkContinuous (μ.real Set.univ ^ (1 / p.toReal)) fun _ ↦
    (Lp.norm_const_le _ _ _).trans_eq (mul_comm _ _)

theorem Lp.norm_constL_le (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [Fact (1 ≤ p)] :
    ‖(Lp.constL p μ 𝕜 : E →L[𝕜] Lp E p μ)‖ ≤ μ.real Set.univ ^ (1 / p.toReal) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end const

namespace Lp

variable {β : Type*} [MeasurableSpace β] {μb : MeasureTheory.Measure β} {f : α → β}

theorem indicatorConstLp_compMeasurePreserving {s : Set β} (hs : MeasurableSet s)
    (hμs : μb s ≠ ∞) (c : E) (hf : MeasurePreserving f μ μb) :
    Lp.compMeasurePreserving f hf (indicatorConstLp p hs hμs c) =
      indicatorConstLp p (hs.preimage hf.measurable)
        (by rwa [hf.measure_preimage hs.nullMeasurableSet]) c :=
  rfl

end Lp

theorem indicatorConstLp_eq_toSpanSingleton_compLp {s : Set α} [NormedSpace ℝ E]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) :
    indicatorConstLp 2 hs hμs x =
      (ContinuousLinearMap.toSpanSingleton ℝ x).compLp (indicatorConstLp 2 hs hμs (1 : ℝ)) := by
  ext1
  refine indicatorConstLp_coeFn.trans ?_
  have h_compLp :=
    (ContinuousLinearMap.toSpanSingleton ℝ x).coeFn_compLp (indicatorConstLp 2 hs hμs (1 : ℝ))
  rw [← EventuallyEq] at h_compLp
  refine EventuallyEq.trans ?_ h_compLp.symm
  refine (@indicatorConstLp_coeFn _ _ _ 2 μ _ s hs hμs (1 : ℝ)).mono fun y hy ↦ ?_
  dsimp only
  rw [hy]
  simp_rw [ContinuousLinearMap.toSpanSingleton_apply]
  by_cases hy_mem : y ∈ s <;> simp [hy_mem]

end MeasureTheory
