/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Measure.ContinuousPreimage

/-!
# Continuity of `MeasureTheory.Lp.compMeasurePreserving`

In this file we prove that the composition of an `L^p` function `g`
with a continuous measure-preserving map `f` is continuous in both arguments.

First, we prove it for indicator functions,
in terms of convergence of `μ ((f a ⁻¹' s) ∆ (g ⁻¹' s))` to zero.

Then we prove the continuity of the function of two arguments
defined on `MeasureTheory.Lp E p ν × {f : C(X, Y) // MeasurePreserving f μ ν}`.

Finally, we provide dot notation convenience lemmas.
-/

open Filter Set MeasureTheory
open scoped ENNReal Topology symmDiff

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [R1Space Y]
  {μ : Measure X} {ν : Measure Y} [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]

namespace MeasureTheory
namespace Lp

variable (μ ν)
variable (E : Type*) [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Let `X` and `Y` be R₁ topological spaces
with Borel σ-algebras and measures `μ` and `ν`, respectively.
Suppose that `μ` is inner regular for finite measure sets with respect to compact sets
and `ν` is a locally finite measure.
Let `1 ≤ p < ∞` be an extended nonnegative real number.
Then the composition of a function `g : Lp E p ν`
and a measure-preserving continuous function `f : C(X, Y)`
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
  | add hfp hgp _ ihf ihg => exact ihf.add ihg
  | @indicatorConst c s hs hνs =>
    dsimp only [Lp.simpleFunc.coe_indicatorConst, Lp.indicatorConstLp_compMeasurePreserving]
    refine continuous_indicatorConstLp_set hp fun f ↦ ?_
    apply tendsto_measure_symmDiff_preimage_nhds_zero continuousAt_subtype_val _ f.2
      hs.nullMeasurableSet hνs.ne
    exact .of_forall Subtype.property

end Lp

end MeasureTheory

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
  convert this.comp (hf.prodMk_nhds hg)

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
