/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# Vitali families

On a topological space `X` with a measure `μ`, consider for each `x : X` a filter `filterAt x` on
sets shrinking to `x`. This family of filters is a Vitali family if it satisfies the following
property: consider a (possibly non-measurable) set `s`, and a predicate `P x a` such that for each
`x ∈ s`, `P x a` holds frequently along `filterAt x`. Then one can extract a countable disjoint
family of sets `a` satisfying `P x a` for some `x ∈ s`, covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.

This file gives the basic definition of Vitali families. More interesting developments of this
notion are deferred to other files:
* constructions of specific Vitali families are provided by the Besicovitch covering theorem, in
  `Besicovitch.vitaliFamily`, and by the Vitali covering theorem, in `Vitali.vitaliFamily`.
* The main theorem on differentiation of measures along a Vitali family is proved in
  `VitaliFamily.ae_tendsto_rnDeriv`.

## Main definitions

* `VitaliFamily μ` is a structure made, for each `x : X`, of a filter `filterAt x` on sets
  shrinking to `x`, such that one can extract an almost everywhere disjoint covering from any
  family of sets that is frequent along these filters.

Let `v` be such a Vitali family.
* `v.filterAt x` is a filter on sets of `X`, such that convergence with respect to this filter
  means convergence when sets in the Vitali family shrink towards `x`.
* `v.exists_covering` is the covering property of Vitali families: if for every `x ∈ s`,
  a predicate `P x a` holds for arbitrarily small sets `a` in the family at `x`,
  then one can extract a countable disjoint family of such sets covering almost all `s`.
* `v.mono ν hν` is the same family of filters, seen as a Vitali family for a measure `ν ≪ μ`.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.8][Federer1996]
  (Vitali families are called Vitali relations there)
-/

@[expose] public section


open MeasureTheory Metric Set Filter TopologicalSpace MeasureTheory.Measure
open scoped Topology ENNReal

variable {X : Type*} [TopologicalSpace X]

/-- On a topological space `X` with a measure `μ`, a Vitali family is given by a filter
`filterAt x` on sets around each point `x : X`, describing how sets shrink to `x`.
It is required to satisfy the following covering property: consider a (possibly non-measurable)
set `s`, and a predicate `P x a` on points and sets such that for every `x ∈ s`, `P x a` holds
frequently along `filterAt x`. Then one can extract a countable disjoint family of pairs `(x, a)`
with `x ∈ s` and `P x a`, such that the sets `a` cover almost all of `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.
-/
structure VitaliFamily {m : MeasurableSpace X} (μ : Measure X) where
  /-- The filter of sets shrinking to `x` along the Vitali family. -/
  filterAt : X → Filter (Set X)
  /-- The sets along `filterAt x` shrink to `x`. -/
  filterAt_le_smallSets_nhds (x : X) : filterAt x ≤ (𝓝 x).smallSets
  /-- Eventually along `filterAt x`, all sets are measurable. -/
  eventually_measurableSet (x : X) : ∀ᶠ a in filterAt x, MeasurableSet a
  /-- The filter `filterAt x` is nontrivial. -/
  filterAt_neBot (x : X) : (filterAt x).NeBot
  /-- **Covering property of Vitali families**. Let `s` be a (possibly non-measurable) set,
  and let `P x a` be a predicate on points and sets.
  If for every `x ∈ s`, `P x a` holds for arbitrarily small sets `a` in the Vitali family at `x`,
  then there exists a countable disjoint family of pairs `(x, a)` with `x ∈ s` and `P x a`
  such that the sets `a` cover almost all of `s`. -/
  exists_covering (s : Set X) (P : X → Set X → Prop)
    (frequently_filterAt : ∀ x ∈ s, ∃ᶠ a in filterAt x, P x a) :
    ∃ t : Set (X × Set X), t.Countable ∧ MapsTo Prod.fst t s ∧ t.PairwiseDisjoint Prod.snd ∧
      (∀ p ∈ t, P p.1 p.2) ∧ s ≤ᵐ[μ] ⋃ p ∈ t, p.2

namespace VitaliFamily

attribute [instance] filterAt_neBot

variable {m0 : MeasurableSpace X} {μ : Measure X}

/-- A Vitali family for a measure `μ` is also a Vitali family for any measure absolutely continuous
with respect to `μ`. -/
def mono (v : VitaliFamily μ) (ν : Measure X) (hν : ν ≪ μ) : VitaliFamily ν where
  __ := v
  exists_covering s P h :=
    let ⟨t, htc, ts, disj, hP, hμ⟩ := v.exists_covering s P h
    ⟨t, htc, ts, disj, hP, hν.ae_le hμ⟩

@[simp]
theorem mono_filterAt (v : VitaliFamily μ) (ν : Measure X) (hν : ν ≪ μ) :
    (v.mono ν hν).filterAt = v.filterAt :=
  rfl

variable (v : VitaliFamily μ)

theorem eventually_filterAt_subset_of_nhds {x : X} {o : Set X} (hx : o ∈ 𝓝 x) :
    ∀ᶠ t in v.filterAt x, t ⊆ o :=
  (eventually_smallSets_subset.2 hx).filter_mono (v.filterAt_le_smallSets_nhds x)

@[deprecated (since := "2026-11-18")]
alias eventually_filterAt_measurableSet := eventually_measurableSet

theorem eventually_filterAt_subset_closedBall {X : Type*} [PseudoMetricSpace X]
    {m0 : MeasurableSpace X} {μ : Measure X} (v : VitaliFamily μ) (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : Set X in v.filterAt x, t ⊆ closedBall x ε :=
  v.eventually_filterAt_subset_of_nhds (closedBall_mem_nhds x hε)

end VitaliFamily
