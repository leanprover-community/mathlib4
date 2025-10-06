/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.CompactOpen
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Continuity of the preimage of a set under a measure-preserving continuous function

In this file we prove that the preimage of a null measurable set `s : Set Y`
under a measure-preserving continuous function `f : C(X, Y)` is continuous in `f`
in the sense that `μ ((f a ⁻¹' s) ∆ (g ⁻¹' s))` tends to zero as `f a` tends to `g`.

As a corollary, we show that
for a continuous family of continuous maps `f z : C(X, Y)`,
a null measurable set `s`, and a null measurable set `t` of finite measure,
the set of parameters `z` such that `f z ⁻¹' t` is a.e. equal to `s` is a closed set.
-/

open Filter Set
open scoped ENNReal symmDiff Topology

namespace MeasureTheory

variable {α X Y Z : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [R1Space Y]
  [TopologicalSpace Z]
  {μ : Measure X} {ν : Measure Y} [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]

/-- Let `X` and `Y` be R₁ topological spaces
with Borel σ-algebras and measures `μ` and `ν`, respectively.
Suppose that `μ` is inner regular for finite measure sets with respect to compact sets
and `ν` is a locally finite measure.
Let `f : α → C(X, Y)` be a family of continuous maps
that converges to a continuous map `g : C(X, Y)` in the compact-open topology along a filter `l`.
Suppose that `g` is a measure-preserving map
and `f a` is a measure-preserving map eventually along `l`.
Then for any finite measure measurable set `s`,
the preimages `f a ⁻¹' s` tend to the preimage `g ⁻¹' s` in measure.
More precisely, the measure of the symmetric difference of these two sets tends to zero. -/
theorem tendsto_measure_symmDiff_preimage_nhds_zero
    {l : Filter α} {f : α → C(X, Y)} {g : C(X, Y)} {s : Set Y} (hfg : Tendsto f l (𝓝 g))
    (hf : ∀ᶠ a in l, MeasurePreserving (f a) μ ν) (hg : MeasurePreserving g μ ν)
    (hs : NullMeasurableSet s ν) (hνs : ν s ≠ ∞) :
    Tendsto (fun a ↦ μ ((f a ⁻¹' s) ∆ (g ⁻¹' s))) l (𝓝 0) := by
  have : ν.InnerRegularCompactLTTop := by
    rw [← hg.map_eq]
    exact .map_of_continuous (map_continuous _)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  -- Without loss of generality, `s` is an open set.
  wlog hso : IsOpen s generalizing s ε
  · have H : 0 < ε / 3 := ENNReal.div_pos hε.ne' ENNReal.coe_ne_top
    -- Indeed, we can choose an open set `U` such that `ν (U ∆ s) < ε / 3`,
    -- apply the lemma to `U`, then use the triangle inequality for `μ (_ ∆ _)`.
    rcases hs.exists_isOpen_symmDiff_lt hνs H.ne' with ⟨U, hUo, hU, hUs⟩
    have hmU : NullMeasurableSet U ν := hUo.measurableSet.nullMeasurableSet
    replace hUs := hUs.le
    filter_upwards [hf, this hmU hU.ne _ H hUo] with a hfa ha
    calc
      μ ((f a ⁻¹' s) ∆ (g ⁻¹' s))
        ≤ μ ((f a ⁻¹' s) ∆ (f a ⁻¹' U)) + μ ((f a ⁻¹' U) ∆ (g ⁻¹' U))
          + μ ((g ⁻¹' U) ∆ (g ⁻¹' s)) := by
        refine (measure_symmDiff_le _ (g ⁻¹' U) _).trans ?_
        gcongr
        apply measure_symmDiff_le
      _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · rwa [← preimage_symmDiff, hfa.measure_preimage (hs.symmDiff hmU), symmDiff_comm]
        · rwa [← preimage_symmDiff, hg.measure_preimage (hmU.symmDiff hs)]
      _ = ε := by simp
  -- Take a compact closed subset `K ⊆ g ⁻¹' s` of almost full measure,
  -- `μ (g ⁻¹' s \ K) < ε / 2`.
  have hνs' : μ (g ⁻¹' s) ≠ ∞ := by rwa [hg.measure_preimage hs]
  obtain ⟨K, hKg, hKco, hKcl, hKμ⟩ :
      ∃ K, MapsTo g K s ∧ IsCompact K ∧ IsClosed K ∧ μ (g ⁻¹' s \ K) < ε / 2 :=
    (hg.measurable hso.measurableSet).exists_isCompact_isClosed_diff_lt hνs' <| by simp [hε.ne']
  have hKm : NullMeasurableSet K μ := hKcl.nullMeasurableSet
  -- Take `a` such that `f a` is measure preserving and maps `K` to `s`.
  -- This is possible, because `K` is a compact set and `s` is an open set.
  filter_upwards [hf, ContinuousMap.tendsto_nhds_compactOpen.mp hfg K hKco s hso hKg] with a hfa ha
  -- Then each of the sets `g ⁻¹' s ∆ K = g ⁻¹' s \ K` and `f a ⁻¹' s ∆ K = f a ⁻¹' s \ K`
  -- have measure at most `ε / 2`, thus `f a ⁻¹' s ∆ g ⁻¹' s` has measure at most `ε`.
  rw [← ENNReal.add_halves ε]
  refine (measure_symmDiff_le _ K _).trans ?_
  rw [symmDiff_of_ge ha.subset_preimage, symmDiff_of_le hKg.subset_preimage]
  gcongr
  have hK' : μ K ≠ ∞ := ne_top_of_le_ne_top hνs' <| measure_mono hKg.subset_preimage
  rw [measure_diff_le_iff_le_add hKm ha.subset_preimage hK', hfa.measure_preimage hs,
    ← hg.measure_preimage hs, ← measure_diff_le_iff_le_add hKm hKg.subset_preimage hK']
  exact hKμ.le

/-- Let `f : Z → C(X, Y)` be a continuous (in the compact open topology) family
of continuous measure-preserving maps.
Let `t : Set Y` be a null measurable set of finite measure.
Then for any `s`, the set of parameters `z`
such that the preimage of `t` under `f_z` is a.e. equal to `s`
is a closed set.

In particular, if `X = Y` and `s = t`,
then we see that the a.e. stabilizer of a set is a closed set. -/
theorem isClosed_setOf_preimage_ae_eq {f : Z → C(X, Y)} (hf : Continuous f)
    (hfm : ∀ z, MeasurePreserving (f z) μ ν) (s : Set X)
    {t : Set Y} (htm : NullMeasurableSet t ν) (ht : ν t ≠ ∞) :
    IsClosed {z | f z ⁻¹' t =ᵐ[μ] s} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  replace hz : ∀ᶠ ε : ℝ≥0∞ in 𝓝 0, ε < μ ((f z ⁻¹' t) ∆ s) := by
    apply gt_mem_nhds
    rwa [pos_iff_ne_zero, ne_eq, measure_symmDiff_eq_zero_iff]
  filter_upwards [(tendsto_measure_symmDiff_preimage_nhds_zero (hf.tendsto z)
    (.of_forall hfm) (hfm z) htm ht).eventually hz] with w hw
  intro (hw' : f w ⁻¹' t =ᵐ[μ] s)
  rw [measure_congr (hw'.symmDiff (ae_eq_refl _)), symmDiff_comm] at hw
  exact hw.false

end MeasureTheory
