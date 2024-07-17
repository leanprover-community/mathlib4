/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Continuity of `MeasureTheory.Lp.compMeasurePreserving`

In this file we prove that the composition of an `L^p` function `g`
with a continuous measure-preservingg map `f` is continuous in both arguments.

First, we prove it for indicator functions,
in terms of convergence of `μ ((f a ⁻¹' s) ∆ (g ⁻¹' s))` to zero.

Then we prove the continuity of the function of two arguments
defined on `MeasureTheory.Lp E p ν × {f : C(X, Y) // MeasurePreserving f μ ν}`.

Finally, we provide dot notation convenience lemmas.
-/

open Filter Set MeasureTheory
open scoped ENNReal Topology symmDiff

variable {α X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [R1Space Y]
  {μ : Measure X} {ν : Measure Y} [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]

namespace MeasureTheory

/-- Let `X` and `Y` be R₁ topological spaces
with Borel σ-algebras and measures `μ` and `ν`, respectively.
Suppose that `μ` is inner regular for finite measure sets with respect to compact sets
and `ν` is a locally finite measure.
Let `f : α → C(X, Y)` be a family of continuous maps
that converges to a continuous map `g : C(X, Y)` in the compact-open topology along a filter `l`.
Suppose that `g` is a measure preserving map
and `f a` is a measure preserving map eventually along `l`.
Then for any finite measure measurable set `s`,
the preimages `f a ⁻¹' s` tend to the preimage `g ⁻¹' s` in measure.
More precisely, the measure of the symmetric difference of these two sets tends to zero. -/
theorem tendsto_measure_symmDiff_preimage_nhds_zero
    {l : Filter α} {f : α → C(X, Y)} {g : C(X, Y)} {s : Set Y} (hfg : Tendsto f l (𝓝 g))
    (hf : ∀ᶠ a in l, MeasurePreserving (f a) μ ν) (hg : MeasurePreserving g μ ν)
    (hs : MeasurableSet s) (hνs : ν s ≠ ∞) :
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
    have hmU : MeasurableSet U := hUo.measurableSet
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
    (hs.preimage hg.measurable).exists_isCompact_isClosed_diff_lt hνs' <| by simp [hε.ne']
  have hKm : MeasurableSet K := hKcl.measurableSet
  -- Take `a` such that `f a` is measure preserving and maps `K` to `s`.
  -- This is possible, because `K` is a compact set and `s` is an open set.
  filter_upwards [hf, ContinuousMap.tendsto_nhds_compactOpen.mp hfg K hKco s hso hKg] with a hfa ha
  -- Then each of the sets `g ⁻¹' s ∆ K = g ⁻¹' s \ K` and `f a ⁻¹' s ∆ K = f a ⁻¹' s \ K`
  -- have measure at most `ε / 2`, thus `f a ⁻¹' s ∆ g ⁻¹' s` has measure at  most `ε`.
  rw [← ENNReal.add_halves ε]
  refine (measure_symmDiff_le _ K _).trans ?_
  rw [symmDiff_of_ge ha.subset_preimage, symmDiff_of_le hKg.subset_preimage]
  gcongr
  have hK' : μ K ≠ ∞ := ne_top_of_le_ne_top hνs' <| measure_mono hKg.subset_preimage
  rw [measure_diff_le_iff_le_add hKm ha.subset_preimage hK', hfa.measure_preimage hs,
    ← hg.measure_preimage hs, ← measure_diff_le_iff_le_add hKm hKg.subset_preimage hK']
  exact hKμ.le

namespace Lp

variable (μ ν)
variable (E : Type*) [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Let `X` and `Y` be R₁ topological spaces
with Borel σ-algebras and measures `μ` and `ν`, respectively.
Suppose that `μ` is inner regular for finite measure sets with respect to compact sets
and `ν` is a locally finite measure.
Let `1 ≤ p < ∞` be an extended nonnegative real number.
Then the composition of a function `g : Lp E p ν`
and a measure preserving continuous function `f : C(X, Y)`
is continuous in both variables. -/
theorem compMeasurePreserving_continuous (hp : p ≠ ∞) :
    Continuous fun gf : Lp E p ν × {f : C(X, Y) // MeasurePreserving f μ ν} ↦
      compMeasurePreserving gf.2.1 gf.2.2 gf.1 := by
  have hp₀ : p ≠ 0 := (one_pos.trans_le Fact.out).ne'
  refine continuous_prod_of_dense_continuous_lipschitzWith _ 1
    (MeasureTheory.Lp.simpleFunc.dense hp) ?_ fun f ↦ (isometry_compMeasurePreserving f.2).lipschitz
  intro f hf
  lift f to Lp.simpleFunc E p ν using hf
  induction f using Lp.simpleFunc.induction hp₀ hp with
  | h_add hfp hgp _ ihf ihg => exact ihf.add ihg
  | @h_ind c s hs hνs =>
    dsimp only [Lp.simpleFunc.coe_indicatorConst, Lp.indicatorConstLp_compMeasurePreserving]
    refine continuous_indicatorConstLp_set hp fun f ↦ ?_
    apply tendsto_measure_symmDiff_preimage_nhds_zero continuousAt_subtype_val _ f.2 hs hνs.ne
    exact eventually_of_forall Subtype.property

end Lp

end MeasureTheory

section Lp

variable {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem Filter.Tendsto.compMeasurePreservingLp {α : Type*} {l : Filter α}
    {f : α → Lp E p ν} {f₀ : Lp E p ν} {g : α → C(X, Y)} {g₀ : C(X, Y)}
    (hf : Tendsto f l (𝓝 f₀)) (hg : Tendsto g l (𝓝 g₀))
    (hgm : ∀ a, MeasurePreserving (g a) μ ν) (hgm₀ : MeasurePreserving g₀ μ ν) (hp : p ≠ ∞) :
    Tendsto (fun a ↦ Lp.compMeasurePreserving (g a) (hgm a) (f a)) l
      (𝓝 (Lp.compMeasurePreserving g₀ hgm₀ f₀)) := by
  have := (Lp.compMeasurePreserving_continuous μ ν E hp).tendsto ⟨f₀, g₀, hgm₀⟩
  replace hg : Tendsto (fun a ↦ ⟨g a, hgm a⟩ : α → {g : C(X, Y) // MeasurePreserving g μ ν})
      l (𝓝 ⟨g₀, hgm₀⟩) :=
    tendsto_subtype_rng.2 hg
  convert this.comp (hf.prod_mk_nhds hg)

variable {Z : Type*} [TopologicalSpace Z] {f : Z → Lp E p ν} {g : Z → C(X, Y)} {s : Set Z} {z : Z}

theorem ContinuousWithinAt.compMeasurePreservingLp (hf : ContinuousWithinAt f s z)
    (hg : ContinuousWithinAt g s z) (hgm : ∀ z, MeasurePreserving (g z) μ ν) (hp : p ≠ ∞) :
    ContinuousWithinAt (fun z ↦ Lp.compMeasurePreserving (g z) (hgm z) (f z)) s z :=
  Tendsto.compMeasurePreservingLp hf hg _ _ hp

theorem ContinuousAt.compMeasurePreservingLp (hf : ContinuousAt f z)
    (hg : ContinuousAt g z) (hgm : ∀ z, MeasurePreserving (g z) μ ν) (hp : p ≠ ∞) :
    ContinuousAt (fun z ↦ Lp.compMeasurePreserving (g z) (hgm z) (f z)) z :=
  Tendsto.compMeasurePreservingLp hf hg _ _ hp

theorem ContinuousOn.compMeasurePreservingLp (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) (hgm : ∀ z, MeasurePreserving (g z) μ ν) (hp : p ≠ ∞) :
    ContinuousOn (fun z ↦ Lp.compMeasurePreserving (g z) (hgm z) (f z)) s := fun z hz ↦
  (hf z hz).compMeasurePreservingLp (hg z hz) hgm hp

theorem Continuous.compMeasurePreservingLp (hf : Continuous f) (hg : Continuous g)
    (hgm : ∀ z, MeasurePreserving (g z) μ ν) (hp : p ≠ ∞) :
    Continuous (fun z ↦ Lp.compMeasurePreserving (g z) (hgm z) (f z)) :=
  continuous_iff_continuousAt.mpr fun _ ↦
    hf.continuousAt.compMeasurePreservingLp hg.continuousAt hgm hp

end Lp

/-- Let `f : Z → C(X, Y)` be a continuous (in the compact open topology) family
of continuous measure preserving maps.
Let `t : Set Y` be a null measurable set of finite measure.
Then for any `s`, the set of parameters `z`
such that the preimage of `t` under `f_z` is a.e. equal to `s`
is a closed set.

In particular, if `X = Y` and `s = t`, then we see that the a.e. stabilizer of a set
is a closed set. -/
theorem MeasureTheory.isClosed_setOf_preimage_ae_eq {Z : Type*} [TopologicalSpace Z]
    {f : Z → C(X, Y)} (hf : Continuous f) (hfm : ∀ z, MeasurePreserving (f z) μ ν)
    (s : Set X) (t : Set Y) (htm : NullMeasurableSet t ν) (ht : ν t ≠ ∞) :
    IsClosed {z | f z ⁻¹' t =ᵐ[μ] s} := by
  obtain h | ⟨z₀, hz₀⟩ := eq_empty_or_nonempty {z | f z ⁻¹' t =ᵐ[μ] s}
  · simp [h]
  rcases htm with ⟨t', ht'm, htt'⟩
  rw [measure_congr htt'] at ht
  set φ : Lp ℝ 1 μ :=
    indicatorConstLp 1 ((hfm z₀).measurable ht'm) (by rwa [(hfm z₀).measure_preimage ht'm]) 1
  set ψ : Lp ℝ 1 ν := indicatorConstLp 1 ht'm ht 1 
  have : IsClosed {z | Lp.compMeasurePreserving (f z) (hfm z) ψ = φ} :=
    isClosed_eq (continuous_const.compMeasurePreservingLp hf _ ENNReal.one_ne_top) continuous_const
  convert this using 3 with z
  simp only [φ, ψ, Lp.indicatorConstLp_compMeasurePreserving,
    indicatorConstLp_inj (hc := one_ne_zero)]
  rw [((hfm z).quasiMeasurePreserving.preimage_ae_eq htt').congr_left,
    ← ((hfm z₀).quasiMeasurePreserving.preimage_ae_eq htt').congr_right,
    hz₀.out.congr_right]
