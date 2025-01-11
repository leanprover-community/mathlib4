/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.IsManifold
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Measure zero subsets of a manifold

Defines the notion of "measure zero" subsets on a finite-dimensional topological manifold.

Let $M$ be a finite-dimensional manifold. While $M$ is a measurable space
(for instance, pull back the Lebesgue measure on each chart and use a partition of unity),
it has no canonical measure. However, there is a natural notion of *measure zero* subsets of $M$:
a subset $A\subset M$ has measure zero iff for each chart $(\phi, U)$ of $M$ the set
$\phi(U\cap A)\subset R^n$ has measure zero (w.r.t. to any additive Haar measure).
Measure zero sets are closed under subsets and countable unions, hence their complement defines
the **almost everywhere filter** on a manifold. Measure zero subsets have empty interior,
hence closed measure zero sets are nowhere dense.

to be continued!

-/

open MeasureTheory Measure Function TopologicalSpace Set
set_option autoImplicit false

variable
  -- Let `M` be a finite-dimensional topological manifold without boundary over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  --[I.Boundaryless]
  --[FiniteDimensional ℝ E]
  [MeasurableSpace E] --[BorelSpace E]

variable (I) in
/-- A measure zero subset of an n-dimensional manifold $M$ is a subset $S ⊆ M$ such that
for all charts $(φ, U)$ of $M$, $φ(U ∩ S) ⊆ ℝ^n$ has measure zero. -/
def MeasureZeroOld (s : Set M) : Prop :=
  ∀ (μ : Measure E) [IsAddHaarMeasure μ], ∀ e ∈ atlas H M, μ (I ∘ e '' (e.source ∩ s)) = 0

def foo {μ : Measure E} [IsAddHaarMeasure μ] (x : M) :=
    MeasureTheory.ae μ

def bar {μ : Measure E} [IsAddHaarMeasure μ] (x : M) : Filter M :=
    Filter.comap (extChartAt I x) (MeasureTheory.ae μ)

-- TODO: is this the right or the wrong direction?
-- should I restrict to "just the source"? well, for a.e. it probably doesn't matter...
variable (I) in
def ModelWithCorners.ae [ChartedSpace H M] (μ : Measure E) : Filter M :=
    iSup (fun (x : M) ↦ (Filter.comap (extChartAt I x) (MeasureTheory.ae μ)))

variable (I) in
def MeasureZero [ChartedSpace H M] (μ : Measure E) (s : Set M) : Prop :=
    sᶜ ∈ ModelWithCorners.ae I μ

namespace MeasureZero

variable (μ : Measure E)

lemma _root_.measureZero_iff {s : Set M} :
    MeasureZero I μ s ↔ sᶜ ∈ ModelWithCorners.ae I μ := by
  rfl

@[simp]
lemma empty : MeasureZero I μ (∅ : Set M) := by simp [measureZero_iff]

lemma mono {s t : Set M} (ht : MeasureZero I μ t) (hst : s ⊆ t) : MeasureZero I μ s :=
  Filter.mem_of_superset ht (by simpa only [compl_subset_compl])

lemma union {s t : Set M} (hs : MeasureZero I μ s) (ht : MeasureZero I μ t) :
    MeasureZero I μ (s ∪ t) := by simp_all [measureZero_iff]

-- countable union!

lemma inter {s t : Set M} (hs : MeasureZero I μ s) (ht : MeasureZero I μ t) :
    MeasureZero I μ (s ∩ t) := by
  simp_all [measureZero_iff]
  sorry -- argue what I.ae actually means... need some API for that :-)

#exit
/-- The “almost everywhere” filter of co-measure zero sets in a manifold. -/
def ModelWithCorners.ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [TopologicalSpace F] (I : ModelWithCorners ℝ E F)
    {M : Type*} [TopologicalSpace M] [ChartedSpace F M] [MeasurableSpace E] : Filter M where
  sets := { s | MeasureZero I sᶜ }
  univ_sets := by
    rw [mem_setOf, compl_univ]
    exact MeasureZero.empty
  inter_sets hx hy:= by
    simp only [mem_setOf_eq] at *
    rw [compl_inter]
    exact hx.union hy
  sets_of_superset hs hst := hs.mono (Iff.mpr compl_subset_compl hst)
