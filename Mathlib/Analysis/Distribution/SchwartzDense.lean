/-
Copyright (c) 2025 Jack Valmadre. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Valmadre
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.CompactDense
import Mathlib.MeasureTheory.Function.LpIntersection

/-!
# Density results for the Schwartz space

## Main definitions

* `MeasureTheory.Lp.LpSchwartzMap`: The subtype of `Lp F p μ` comprising functions that have a
Schwartz function representative.

## Main statements

* `SchwartzMap.toLp_denseRange`: The map from `𝓢(E, F)` to `Lp F p μ` is dense.
* `MeasureTheory.Lp.LpSchwartzMap.dense`: The set of functions in `L^p` with a Schwartz
representative is dense.

## Implementation details

The density of the Schwartz functions in `L^p` is proved using the density of infinitely
differentiable, compactly supported functions in `L^p`, and the fact that these are a subset of the
Schwartz functions.
-/

open MeasureTheory Filter
open scoped SchwartzMap ENNReal ContDiff

variable {𝕜 D E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section DenseSchwartz

/-- Make a Schwartz function from an infinitely differentiable, compactly supported function. -/
def SchwartzMap.of_smooth_of_hasCompactSupport (f : E → F) (hf_smooth : ContDiff ℝ ∞ f)
    (hf_supp : HasCompactSupport f) : 𝓢(E, F) where
  toFun x := f x
  smooth' := hf_smooth
  decay' := by
    have (m : ℕ × ℕ) : ∃ C, ∀ x, ‖x‖ ^ m.1 * ‖iteratedFDeriv ℝ m.2 f x‖ ≤ C := by
      suffices ∃ C, ∀ x, ‖‖x‖ ^ m.1 * ‖iteratedFDeriv ℝ m.2 f x‖‖ ≤ C by simpa using this
      refine HasCompactSupport.exists_bound_of_continuous ?_ ?_
      · exact (hf_supp.iteratedFDeriv m.2).norm.mul_left
      · refine .mul (continuous_norm.pow m.1) (.norm ?_)
        exact hf_smooth.continuous_iteratedFDeriv <| by simp [← WithTop.coe_natCast]
    choose C hC using this
    intro k n
    use (Finset.Iic (k, n)).sup' Finset.nonempty_Iic C
    exact fun x ↦ Finset.le_sup'_of_le _ (by simp) (hC (k, n) x)

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [HasContDiffBump E]
  [CompleteSpace F] {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

variable (F) in
/-- Schwartz functions are dense in `L^p`. -/
theorem SchwartzMap.toLp_denseRange (hp_top : p ≠ ⊤)
    (μ : Measure E := by volume_tac) [μ.HasTemperateGrowth]
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] [μ.IsNegInvariant] [μ.IsAddLeftInvariant] :
    DenseRange (fun f : 𝓢(E, F) ↦ toLp f p μ) := by
  refine Dense.mono ?_ (ContDiff.toLp_denseRange hp_top μ)
  exact Set.range_comp_subset_range
    (fun f : { f // ContDiff ℝ ∞ f ∧ HasCompactSupport f } ↦
      of_smooth_of_hasCompactSupport f.1 f.2.1 f.2.2)
    (fun f ↦ f.toLp p μ)

end DenseSchwartz

section Dense

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [HasContDiffBump E]
  [CompleteSpace F] {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

/-- For any function `f` that satisfies `Memℒp` with `p ≠ ⊤`, there exists a Schwartz function
`g` which is arbitrarily close to `f` in the `L^p` distance. -/
theorem MeasureTheory.Memℒp.exists_schwartzMap_eLpNorm_sub_le (hp_top : p ≠ ⊤) {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] [μ.IsNegInvariant] [μ.IsAddLeftInvariant]
    {f : E → F} (hf : Memℒp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : 𝓢(E, F), eLpNorm (f - (g : E → F)) p μ ≤ ε := by
  obtain ⟨g, hg_smooth, hg_supp, hg_dist⟩ :=
    exists_contDiff_hasCompactSupport_eLpNorm_sub_le hp_top hf hε
  exact ⟨SchwartzMap.of_smooth_of_hasCompactSupport g hg_smooth hg_supp, hg_dist⟩

variable (F) in
/-- The set of `L^p` functions with a Schwartz representative is dense in `L^p`. -/
theorem SchwartzMap.denseRange_toLp (hp_top : p ≠ ⊤)
-- theorem MeasureTheory.Lp.LpSchwartzMap.dense (hp_top : p ≠ ⊤)
    (μ : Measure E := by volume_tac) [μ.HasTemperateGrowth]
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] [μ.IsNegInvariant] [μ.IsAddLeftInvariant] :
    DenseRange (fun f : 𝓢(E, F) ↦ toLp f p μ) := by
  intro f
  refine (mem_closure_iff_nhds_basis EMetric.nhds_basis_closed_eball).2 fun ε hε ↦ ?_
  obtain ⟨g, hg⟩ := (Lp.memℒp f).exists_schwartzMap_eLpNorm_sub_le hp_top hε.ne'
  refine ⟨g.toLp p μ, Set.mem_range_self g, ?_⟩
  rw [EMetric.mem_closedBall, edist_comm, Lp.edist_def]
  refine le_of_eq_of_le (eLpNorm_congr_ae ?_) hg
  filter_upwards [g.coeFn_toLp p μ] with x h₁
  simp [h₁]

end Dense


namespace SchwartzMap

variable {𝕜 D E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-! ## Schwartz function to `L^p ∩ L^q` -/

section LpInf

variable [OpensMeasurableSpace E] [SecondCountableTopologyEither E F]

/-- Map from Schwartz map to `L^p ∩ L^q` as a linear map. Serves to define a `Submodule`. -/
def toLpInf (p₁ p₂ : ℝ≥0∞) (μ : Measure E) [μ.HasTemperateGrowth] :
    𝓢(E, F) →+ ↑(Lp F p₁ μ ⊓ Lp F p₂ μ) where
  -- toFun f := ⟨AEEqFun.mk f _, ⟨(f.toLp p₁ μ).2, (f.toLp p₂ μ).2⟩⟩
  toFun f := ⟨AEEqFun.mk f _, Lp.mk_mem_inf_of_eLpNorm_lt_top f f.continuous.aestronglyMeasurable
    (f.eLpNorm_lt_top p₁ μ) (f.eLpNorm_lt_top p₂ μ)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

-- TODO: Provide CLM?
variable (𝕜 F) in
/-- Map from Schwartz map to `L^p ∩ L^q` as a linear map. Serves to define a `Submodule`. -/
def toLpInfLM (p₁ p₂ : ℝ≥0∞) (μ : Measure E) [μ.HasTemperateGrowth] :
    𝓢(E, F) →ₗ[𝕜] ↑(Lp F p₁ μ ⊓ Lp F p₂ μ) :=
  { toLpInf p₁ p₂ μ with map_smul' _ _ := rfl }

theorem mem_range_toLpInfLM_iff
    {p₁ p₂ : ℝ≥0∞} {μ : Measure E} [hμ : μ.HasTemperateGrowth] {f : ↑(Lp F p₁ μ ⊓ Lp F p₂ μ)} :
    f ∈ LinearMap.range (toLpInfLM 𝕜 F p₁ p₂ μ) ↔ ∃ g : 𝓢(E, F), g =ᵐ[μ] f := by
  refine exists_congr fun g ↦ ?_
  rw [Subtype.ext_iff_val, AEEqFun.ext_iff]
  exact (coeFn_toAEEqFun 𝕜 μ g).congr_left

end LpInf

section Dense

variable [BorelSpace E] [FiniteDimensional ℝ E] [HasContDiffBump E] [CompleteSpace F]

variable (F) in
/-- Schwartz functions are dense in `L^p`. -/
theorem toLpInf_denseRange {p₁ p₂ : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)]
    (hp₁_top : p₁ ≠ ⊤) (hp₂_top : p₂ ≠ ⊤) (μ : Measure E := by volume_tac) [μ.HasTemperateGrowth]
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] [μ.IsNegInvariant] [μ.IsAddLeftInvariant] :
    DenseRange (toLpInf p₁ p₂ μ : 𝓢(E, F) → _) := by
  refine Metric.denseRange_iff.mpr ?_
  intro f r hr
  obtain ⟨g₁, hg₁⟩ := (toLp_denseRange F hp₁_top μ).exists_dist_lt (AddSubgroup.inf_fst f) hr
  obtain ⟨g₂, hg₂⟩ := (toLp_denseRange F hp₂_top μ).exists_dist_lt (AddSubgroup.inf_snd f) hr
  simp only [Lp.dist_inf_def]
  simp only [sup_lt_iff]
  simp only [Lp.dist_def, AddSubgroup.inf_fst_val, AddSubgroup.inf_snd_val]
  -- No control over `p₁`-distance of `g₂` or `p₂`-distance of `g₁`!
  -- Need to consider mutiple `p` at earlier point.
  sorry

end Dense

end SchwartzMap
