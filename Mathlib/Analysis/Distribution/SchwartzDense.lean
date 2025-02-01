/-
Copyright (c) 2025 Jack Valmadre. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Valmadre
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.CompactDense

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

open MeasureTheory
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
    (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] [μ.IsNegInvariant] [μ.IsAddLeftInvariant] :
    DenseRange (fun f : 𝓢(E, F) ↦ f.toLp p μ) := by
  refine Dense.mono ?_ (ContDiff.toLp_denseRange hp_top μ)
  exact Set.range_comp_subset_range
    (fun f : { f // ContDiff ℝ ∞ f ∧ HasCompactSupport f } ↦
      of_smooth_of_hasCompactSupport f.1 f.2.1 f.2.2)
    (fun f ↦ f.toLp p μ)

end DenseSchwartz

section LpSchwartzMap

variable [NormedField 𝕜] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] [SecondCountableTopologyEither E F]

-- TODO: Maybe this should go under `SchwartzMap.LpSchwartzMap` instead?
namespace MeasureTheory

-- TODO: Should we just define this with `volume`??
variable (F) in
/-- The Schwartz functions (or rather, the equivalence class of functions with a Schwartz
representative) as an additive subgroup of `L^p`, equipped with the `L^p` norm.

This will be used to show that the Fourier transform is uniform continuous under the `L^2` norm. -/
noncomputable def Lp.LpSchwartzMap (p : ℝ≥0∞) (μ : Measure E := by volume_tac) :
    AddSubgroup (Lp F p μ) :=
  AddSubgroup.addSubgroupOf
    (AddMonoidHom.range <| (ContinuousMap.toAEEqFunAddHom μ).comp <|
      (BoundedContinuousFunction.toContinuousMapAddHom E F).comp <|
      SchwartzMap.toBoundedContinuousFunctionAddHom E F)
    (Lp F p μ)

theorem Lp.LpSchwartzMap.mem_iff {p : ℝ≥0∞} {μ : Measure E} {f : Lp F p μ} :
    f ∈ LpSchwartzMap F p μ ↔
      ∃ g : 𝓢(E, F), g.toBoundedContinuousFunction.toContinuousMap.toAEEqFun μ = f :=
  AddSubgroup.mem_addSubgroupOf

theorem Lp.LpSchwartzMap.mem_iff_ae {p : ℝ≥0∞} {μ : Measure E} {f : Lp F p μ} :
    f ∈ LpSchwartzMap F p μ ↔ ∃ g : 𝓢(E, F), f =ᵐ[μ] g := by
  rw [mem_iff]
  refine exists_congr fun g ↦ ?_
  -- TODO: Easier way to show this?
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]
    filter_upwards [g.toBoundedContinuousFunction.toContinuousMap.coeFn_toAEEqFun μ] with x h₁
    simp [h₁]
  · ext
    filter_upwards [g.toBoundedContinuousFunction.toContinuousMap.coeFn_toAEEqFun μ, h] with x h₁ h₂
    simp [h₁, h₂]

-- TODO: Does this change anything?
instance Lp.LpSchwartzMap.instCoe {p : ℝ≥0∞} {μ : Measure E} :
    Coe (LpSchwartzMap F p μ) (Lp F p μ) where
  coe f := f

noncomputable instance Lp.LpSchwartzMap.instCoeFun {p : ℝ≥0∞} {μ : Measure E} :
    CoeFun (LpSchwartzMap F p μ) (fun _ ↦ E → F) where
  coe f := f

variable (𝕜 F) in
/-- `LpSchwartzMap` as a `Submodule`; used to obtain `Module`, `NormedSpace`. -/
noncomputable def Lp.LpSchwartzMapSubmodule (p : ℝ≥0∞) (μ : Measure E) : Submodule 𝕜 (Lp F p μ) :=
  { LpSchwartzMap F p μ with
    smul_mem' c f := by
      simp only [AddSubgroup.mem_carrier, @LpSchwartzMap.mem_iff_ae _]
      refine Exists.imp' (c • ·) fun g hg ↦ ?_
      filter_upwards [hg, coeFn_smul c f] with x h₁ h₂
      simp [h₁, h₂] }

/-- `LpSchwartzMap F p μ` is a `Module`. -/
noncomputable instance Lp.LpSchwartzMap.instModule {p : ℝ≥0∞} {μ : Measure E} :
    Module 𝕜 (LpSchwartzMap F p μ) :=
  (LpSchwartzMapSubmodule 𝕜 F p μ).module

/-- `LpSchwartzMap F p μ` is a `NormedSpace`. -/
noncomputable instance Lp.LpSchwartzMap.instNormedSpace {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure E} :
    NormedSpace 𝕜 (LpSchwartzMap F p μ) :=
  (LpSchwartzMapSubmodule 𝕜 F p μ).normedSpace

@[simp]
theorem Lp.LpSchwartzMap.coe_smul {p : ℝ≥0∞} {μ : Measure E} (c : 𝕜) (f : LpSchwartzMap F p μ) :
    ↑(c • f) = c • (f : Lp F p μ) :=
  (LpSchwartzMapSubmodule 𝕜 F p μ).coe_smul c f

theorem _root_.SchwartzMap.toLp_mem_LpSchwartzMap
    (p : ℝ≥0∞) (μ : Measure E := by volume_tac) [μ.HasTemperateGrowth] (f : 𝓢(E, F)) :
    f.toLp p μ ∈ Lp.LpSchwartzMap F p μ := ⟨f, rfl⟩

/-- Obtain the Schwartz representative using `Exists.choose`. -/
noncomputable def Lp.LpSchwartzMap.choose {p : ℝ≥0∞} {μ : Measure E}
    (f : LpSchwartzMap F p μ) : 𝓢(E, F) := (mem_iff.mp f.2).choose

/-- Prove `p ⇑f` with `f : LpSchwartzMap F q μ` by showing that
(1) ae-equality `f =ᵐ[μ] f'` is sufficient to prove `p f' → p f` and
(2) `p ⇑g` holds for all Schwartz functions `g : 𝓢(E, F)`. -/
theorem Lp.LpSchwartzMap.induction_on {p : ℝ≥0∞} {μ : Measure E}
    (f : LpSchwartzMap F p μ) (P : (E → F) → Prop)
    (h_congr : ∀ ⦃f' : E → F⦄, f =ᵐ[μ] f' → P f' → P f) (h : ∀ g : 𝓢(E, F), P g) : P f := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := mem_iff_ae.mp hf
  exact h_congr hg (h g)

theorem Lp.LpSchwartzMap.induction_on₂ {p : ℝ≥0∞} {μ : Measure E}
    (f g : LpSchwartzMap F p μ) (P : (E → F) → (E → F) → Prop)
    (h_congr : ∀ ⦃f' g' : E → F⦄, f =ᵐ[μ] f' → g =ᵐ[μ] g' → P f' g' → P f g)
    (h : ∀ f₀ g₀ : 𝓢(E, F), P f₀ g₀) : P f g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  obtain ⟨f₀, hf₀⟩ := mem_iff_ae.mp hf
  obtain ⟨g₀, hg₀⟩ := mem_iff_ae.mp hg
  exact h_congr hf₀ hg₀ (h f₀ g₀)

variable (𝕜 F) in
/-- The map from the subtype `LpSchwartzMap` to `Lp` as a continuous linear map. -/
def Lp.LpSchwartzMap.subtypeL (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure E) :
    LpSchwartzMap F p μ →L[𝕜] Lp F p μ where
  toFun f := f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_subtype_val

@[simp]
theorem Lp.LpSchwartzMap.coeFn_subtypeL (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure E) :
    ⇑(subtypeL 𝕜 F p μ) = Subtype.val := rfl

end MeasureTheory

end LpSchwartzMap

section Dense

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [HasContDiffBump E]
  [CompleteSpace F] {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

/-- For any function `f` that satisfies `Memℒp` with `p ≠ ⊤`, there exists a Schwartz function
`g` which is arbitrarily close to `f` in the `L^p` distance. -/
theorem MeasureTheory.Memℒp.exists_LpSchwartzMap_eLpNorm_sub_le (hp_top : p ≠ ⊤) {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] [μ.IsNegInvariant] [μ.IsAddLeftInvariant]
    {f : E → F} (hf : Memℒp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : 𝓢(E, F), eLpNorm (f - (g : E → F)) p μ ≤ ε := by
  obtain ⟨g, hg_smooth, hg_supp, hg_dist⟩ :=
    exists_contDiff_hasCompactSupport_eLpNorm_sub_le hp_top hf hε
  exact ⟨SchwartzMap.of_smooth_of_hasCompactSupport g hg_smooth hg_supp, hg_dist⟩

variable (F) in
/-- The set of `L^p` functions with a Schwartz representative is dense in `L^p`. -/
theorem MeasureTheory.Lp.LpSchwartzMap.dense (hp_top : p ≠ ⊤)
    (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] [μ.IsNegInvariant] [μ.IsAddLeftInvariant] :
    Dense (LpSchwartzMap F p μ : Set (Lp F p μ)) := by
  intro f
  refine (mem_closure_iff_nhds_basis EMetric.nhds_basis_closed_eball).2 fun ε hε ↦ ?_
  obtain ⟨g, hg⟩ := (Lp.memℒp f).exists_LpSchwartzMap_eLpNorm_sub_le hp_top hε.ne'
  use g.toLp p μ, g.toLp_mem_LpSchwartzMap p μ
  rw [EMetric.mem_closedBall, edist_comm, edist_def]
  refine le_of_eq_of_le (eLpNorm_congr_ae ?_) hg
  filter_upwards [g.coeFn_toLp p μ] with x h₁
  simp [h₁]

end Dense
