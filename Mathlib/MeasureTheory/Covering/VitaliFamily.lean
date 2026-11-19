/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# Vitali families

On a metric space `X` with a measure `μ`, consider for each `x : X` a family of measurable sets with
nonempty interiors, called `setsAt x`. This family is a Vitali family if it satisfies the following
property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `setsAt x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

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

* `VitaliFamily μ` is a structure made, for each `x : X`, of a family of sets around `x`, such that
  one can extract an almost everywhere disjoint covering from any subfamily containing sets of
  arbitrarily small diameters.

Let `v` be such a Vitali family.
* `v.filterAt x` is a filter on sets of `X`, such that convergence with respect to this filter
  means convergence when sets in the Vitali family shrink towards `x`.
* `v.exists_covering` is the covering property of Vitali families, stated in terms of
  `v.filterAt`: if for every `x ∈ s`, a predicate `P x a` holds for arbitrarily small sets `a` in
  the family at `x`, then one can extract a countable disjoint family of such sets
  covering almost all `s`.

Users of Vitali families should only rely on `v.filterAt` and `v.exists_covering`. The fields
`setsAt`, `measurableSet`, `nonempty_interior`, `nontrivial` and `covering` should only be used
to construct Vitali families.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.8][Federer1996]
  (Vitali families are called Vitali relations there)
-/

@[expose] public section


open MeasureTheory Metric Set Filter TopologicalSpace MeasureTheory.Measure
open scoped Topology ENNReal

variable {X : Type*} [PseudoMetricSpace X]

/-- On a metric space `X` with a measure `μ`, consider for each `x : X` a family of measurable sets
with nonempty interiors, called `setsAt x`. This family is a Vitali family if it satisfies the
following property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `setsAt x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.
-/
structure VitaliFamily {m : MeasurableSpace X} (μ : Measure X) where
  /-- Sets of the family "centered" at a given point. -/
  setsAt : X → Set (Set X)
  /-- All sets of the family are measurable. -/
  measurableSet : ∀ x : X, ∀ s ∈ setsAt x, MeasurableSet s
  /-- All sets of the family have nonempty interior. -/
  nonempty_interior : ∀ x : X, ∀ s ∈ setsAt x, (interior s).Nonempty
  /-- For any closed ball around `x`, there exists a set of the family contained in this ball. -/
  nontrivial : ∀ (x : X), ∀ ε > (0 : ℝ), ∃ s ∈ setsAt x, s ⊆ closedBall x ε
  /-- Consider a (possibly non-measurable) set `s`,
  and for any `x` in `s` a subfamily `f x` of `setsAt x`
  containing sets of arbitrarily small diameter.
  Then one can extract a disjoint subfamily covering almost all `s`. -/
  covering : ∀ (s : Set X) (f : X → Set (Set X)),
    (∀ x ∈ s, f x ⊆ setsAt x) → (∀ x ∈ s, ∀ ε > (0 : ℝ), ∃ t ∈ f x, t ⊆ closedBall x ε) →
    ∃ t : Set (X × Set X), (∀ p ∈ t, p.1 ∈ s) ∧ (t.PairwiseDisjoint fun p ↦ p.2) ∧
      (∀ p ∈ t, p.2 ∈ f p.1) ∧ μ (s \ ⋃ p ∈ t, p.2) = 0

namespace VitaliFamily

variable {m0 : MeasurableSpace X} {μ : Measure X}

/-- A Vitali family for a measure `μ` is also a Vitali family for any measure absolutely continuous
with respect to `μ`. -/
def mono (v : VitaliFamily μ) (ν : Measure X) (hν : ν ≪ μ) : VitaliFamily ν where
  __ := v
  covering s f h h' :=
    let ⟨t, ts, disj, mem_f, hμ⟩ := v.covering s f h h'
    ⟨t, ts, disj, mem_f, hν hμ⟩

/-- Given a Vitali family `v` for a measure `μ`, a family `f` is a fine subfamily on a set `s` if
every point `x` in `s` belongs to arbitrarily small sets in `v.setsAt x ∩ f x`. This is precisely
the subfamilies for which the Vitali family definition ensures that one can extract a disjoint
covering of almost all `s`. -/
@[deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
def FineSubfamilyOn (v : VitaliFamily μ) (f : X → Set (Set X)) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ ε > 0, ∃ t ∈ v.setsAt x ∩ f x, t ⊆ closedBall x ε

namespace FineSubfamilyOn

set_option linter.deprecated false

variable {v : VitaliFamily μ} {f : X → Set (Set X)} {s : Set X} (h : v.FineSubfamilyOn f s)
include h

@[deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
theorem exists_disjoint_covering_ae :
    ∃ t : Set (X × Set X),
      (∀ p : X × Set X, p ∈ t → p.1 ∈ s) ∧
      (t.PairwiseDisjoint fun p => p.2) ∧
      (∀ p : X × Set X, p ∈ t → p.2 ∈ v.setsAt p.1 ∩ f p.1) ∧
      μ (s \ ⋃ (p : X × Set X) (_ : p ∈ t), p.2) = 0 :=
  v.covering s (fun x => v.setsAt x ∩ f x) (fun _ _ => inter_subset_left) h

/-- Given `h : v.FineSubfamilyOn f s`, then `h.index` is a set parametrizing a disjoint
covering of almost every `s`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
@[deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
protected noncomputable def index : Set (X × Set X) :=
  h.exists_disjoint_covering_ae.choose

/-- Given `h : v.FineSubfamilyOn f s`, then `h.covering p` is a set in the family,
for `p ∈ h.index`, such that these sets form a disjoint covering of almost every `s`. -/
@[nolint unusedArguments,
  deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
protected def covering (_h : FineSubfamilyOn v f s) : X × Set X → Set X :=
  fun p => p.2

@[deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
theorem index_subset : ∀ p : X × Set X, p ∈ h.index → p.1 ∈ s :=
  h.exists_disjoint_covering_ae.choose_spec.1

@[deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
theorem covering_disjoint : h.index.PairwiseDisjoint h.covering :=
  h.exists_disjoint_covering_ae.choose_spec.2.1

open scoped Function in -- required for scoped `on` notation
@[deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
theorem covering_disjoint_subtype : Pairwise (Disjoint on fun x : h.index => h.covering x) :=
  (pairwise_subtype_iff_pairwise_set _ _).2 h.covering_disjoint

@[deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
theorem covering_mem {p : X × Set X} (hp : p ∈ h.index) : h.covering p ∈ f p.1 :=
  (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).2

@[deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
theorem covering_mem_family {p : X × Set X} (hp : p ∈ h.index) : h.covering p ∈ v.setsAt p.1 :=
  (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).1

@[deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
theorem measure_sdiff_biUnion : μ (s \ ⋃ p ∈ h.index, h.covering p) = 0 :=
  h.exists_disjoint_covering_ae.choose_spec.2.2.2

@[deprecated (since := "2026-06-03")] alias measure_diff_biUnion := measure_sdiff_biUnion

@[deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
theorem index_countable [SecondCountableTopology X] : h.index.Countable :=
  h.covering_disjoint.countable_of_nonempty_interior fun _ hx =>
    v.nonempty_interior _ _ (h.covering_mem_family hx)

@[deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
protected theorem measurableSet_u {p : X × Set X} (hp : p ∈ h.index) :
    MeasurableSet (h.covering p) :=
  v.measurableSet p.1 _ (h.covering_mem_family hp)

/-- Let `ρ` be an outer measure (or a measure) that vanishes on `μ`-null sets.
Then the `ρ`-measure of `s` is at most the sum of the `ρ`-measures of the sets of the covering. -/
@[deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
theorem outerMeasure_le_tsum_of_null_imp_null [SecondCountableTopology X] {F : Type*}
    [FunLike F (Set X) ℝ≥0∞] [OuterMeasureClass F X] {ρ : F}
    (hρ : ∀ ⦃t⦄, μ t = 0 → ρ t = 0) : ρ s ≤ ∑' p : h.index, ρ (h.covering p) :=
  calc
    ρ s ≤ ρ ((s \ ⋃ p ∈ h.index, h.covering p) ∪ ⋃ p ∈ h.index, h.covering p) :=
      measure_mono (by simp only [subset_union_left, sdiff_union_self])
    _ ≤ ρ (s \ ⋃ p ∈ h.index, h.covering p) + ρ (⋃ p ∈ h.index, h.covering p) :=
      (measure_union_le _ _)
    _ ≤ ∑' p : h.index, ρ (h.covering p) := by
      rw [hρ h.measure_sdiff_biUnion, zero_add]
      exact measure_biUnion_le _ h.index_countable _

@[deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
theorem measure_le_tsum_of_absolutelyContinuous [SecondCountableTopology X] {ρ : Measure X}
    (hρ : ρ ≪ μ) : ρ s ≤ ∑' p : h.index, ρ (h.covering p) :=
  h.outerMeasure_le_tsum_of_null_imp_null hρ

@[deprecated "Use `VitaliFamily.exists_covering` instead." (since := "2026-11-18")]
theorem measure_le_tsum [SecondCountableTopology X] : μ s ≤ ∑' x : h.index, μ (h.covering x) :=
  h.measure_le_tsum_of_absolutelyContinuous Measure.AbsolutelyContinuous.rfl

end FineSubfamilyOn

/-- One can enlarge a Vitali family by adding to the sets `f x` at `x` all sets which are not
contained in a `δ`-neighborhood on `x`. This does not change the local filter at a point, but it
can be convenient to get a nicer global behavior. -/
def enlarge (v : VitaliFamily μ) (δ : ℝ) (δpos : 0 < δ) : VitaliFamily μ where
  setsAt x := v.setsAt x ∪ {s | MeasurableSet s ∧ (interior s).Nonempty ∧ ¬s ⊆ closedBall x δ}
  measurableSet := by
    rintro x s (hs | hs)
    exacts [v.measurableSet _ _ hs, hs.1]
  nonempty_interior := by
    rintro x s (hs | hs)
    exacts [v.nonempty_interior _ _ hs, hs.2.1]
  nontrivial := by
    intro x ε εpos
    rcases v.nontrivial x ε εpos with ⟨s, hs, h's⟩
    exact ⟨s, mem_union_left _ hs, h's⟩
  covering := by
    intro s f fset ffine
    let g : X → Set (Set X) := fun x => f x ∩ v.setsAt x
    have : ∀ x ∈ s, ∀ ε : ℝ, ε > 0 → ∃ t ∈ g x, t ⊆ closedBall x ε := by
      intro x hx ε εpos
      obtain ⟨t, tf, ht⟩ : ∃ t ∈ f x, t ⊆ closedBall x (min ε δ) :=
        ffine x hx (min ε δ) (lt_min εpos δpos)
      rcases fset x hx tf with (h't | h't)
      · exact ⟨t, ⟨tf, h't⟩, ht.trans (closedBall_subset_closedBall (min_le_left _ _))⟩
      · refine False.elim (h't.2.2 ?_)
        exact ht.trans (closedBall_subset_closedBall (min_le_right _ _))
    rcases v.covering s g (fun x _ => inter_subset_right) this with ⟨t, ts, tdisj, tg, μt⟩
    exact ⟨t, ts, tdisj, fun p hp => (tg p hp).1, μt⟩

variable (v : VitaliFamily μ)

/-- Given a vitali family `v`, then `v.filterAt x` is the filter on `Set X` made of those families
that contain all sets of `v.setsAt x` of a sufficiently small diameter. This filter makes it
possible to express limiting behavior when sets in `v.setsAt x` shrink to `x`. -/
def filterAt (x : X) : Filter (Set X) := (𝓝 x).smallSets ⊓ 𝓟 (v.setsAt x)

theorem _root_.Filter.HasBasis.vitaliFamily {ι : Sort*} {p : ι → Prop} {s : ι → Set X} {x : X}
    (h : (𝓝 x).HasBasis p s) : (v.filterAt x).HasBasis p (fun i ↦ {t ∈ v.setsAt x | t ⊆ s i}) := by
  simpa only [← Set.ofPred_inter_eq_sep] using! h.smallSets.inf_principal _

theorem filterAt_basis_closedBall (x : X) :
    (v.filterAt x).HasBasis (0 < ·) ({t ∈ v.setsAt x | t ⊆ closedBall x ·}) :=
  nhds_basis_closedBall.vitaliFamily v

theorem mem_filterAt_iff {x : X} {s : Set (Set X)} :
    s ∈ v.filterAt x ↔ ∃ ε > (0 : ℝ), ∀ t ∈ v.setsAt x, t ⊆ closedBall x ε → t ∈ s := by
  simp only [(v.filterAt_basis_closedBall x).mem_iff, ← and_imp, subset_def, mem_ofPred]

instance filterAt_neBot (x : X) : (v.filterAt x).NeBot :=
  (v.filterAt_basis_closedBall x).neBot_iff.2 <| v.nontrivial _ _

theorem eventually_filterAt_iff {x : X} {P : Set X → Prop} :
    (∀ᶠ t in v.filterAt x, P t) ↔ ∃ ε > (0 : ℝ), ∀ t ∈ v.setsAt x, t ⊆ closedBall x ε → P t :=
  v.mem_filterAt_iff

theorem tendsto_filterAt_iff {ι : Type*} {l : Filter ι} {f : ι → Set X} {x : X} :
    Tendsto f l (v.filterAt x) ↔
      (∀ᶠ i in l, f i ∈ v.setsAt x) ∧ ∀ ε > (0 : ℝ), ∀ᶠ i in l, f i ⊆ closedBall x ε := by
  simp only [filterAt, tendsto_inf, nhds_basis_closedBall.smallSets.tendsto_right_iff,
    tendsto_principal, and_comm, mem_powerset_iff]

theorem eventually_filterAt_mem_setsAt (x : X) : ∀ᶠ t in v.filterAt x, t ∈ v.setsAt x :=
  (v.tendsto_filterAt_iff.mp tendsto_id).1

theorem eventually_filterAt_subset_closedBall (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : Set X in v.filterAt x, t ⊆ closedBall x ε :=
  (v.tendsto_filterAt_iff.mp tendsto_id).2 ε hε

theorem filterAt_le_smallSets_nhds (x : X) : v.filterAt x ≤ (𝓝 x).smallSets := inf_le_left

theorem eventually_measurableSet (x : X) : ∀ᶠ t in v.filterAt x, MeasurableSet t := by
  filter_upwards [v.eventually_filterAt_mem_setsAt x] with _ ha using v.measurableSet _ _ ha

@[deprecated (since := "2026-11-18")]
alias eventually_filterAt_measurableSet := eventually_measurableSet

theorem frequently_filterAt_iff {x : X} {P : Set X → Prop} :
    (∃ᶠ t in v.filterAt x, P t) ↔ ∀ ε > (0 : ℝ), ∃ t ∈ v.setsAt x, t ⊆ closedBall x ε ∧ P t := by
  simp only [(v.filterAt_basis_closedBall x).frequently_iff, ← and_assoc, subset_def, mem_ofPred]

theorem eventually_filterAt_subset_of_nhds {x : X} {o : Set X} (hx : o ∈ 𝓝 x) :
    ∀ᶠ t in v.filterAt x, t ⊆ o :=
  (eventually_smallSets_subset.2 hx).filter_mono inf_le_left

/-- **Covering property of Vitali families**. Let `s` be a (possibly non-measurable) set,
and let `P x a` be a predicate on points and sets.
If for every `x ∈ s`, `P x a` holds for arbitrarily small sets `a` in the Vitali family `v` at `x`,
then there exists a countable disjoint family of pairs `(x, a)` with `x ∈ s` and `P x a`
such that the sets `a` cover almost all of `s`. -/
theorem exists_covering [SecondCountableTopology X] (s : Set X) (P : X → Set X → Prop)
    (h : ∀ x ∈ s, ∃ᶠ a in v.filterAt x, P x a) :
    ∃ t : Set (X × Set X), t.Countable ∧ MapsTo Prod.fst t s ∧ t.PairwiseDisjoint Prod.snd ∧
      (∀ p ∈ t, P p.1 p.2) ∧ s ≤ᵐ[μ] ⋃ p ∈ t, p.2 := by
  obtain ⟨t, ts, disj, htP, hμ⟩ := v.covering s (fun x ↦ {a | a ∈ v.setsAt x ∧ P x a})
    (fun _ _ _ ha ↦ ha.1) fun x hx ε hε ↦ by
      obtain ⟨a, ha, haε, hPa⟩ := v.frequently_filterAt_iff.1 (h x hx) ε hε
      exact ⟨a, ⟨ha, hPa⟩, haε⟩
  exact ⟨t, disj.countable_of_nonempty_interior fun p hp ↦ v.nonempty_interior _ _ (htP p hp).1,
    ts, disj, fun p hp ↦ (htP p hp).2, ae_subset.2 hμ⟩

@[simp]
theorem filterAt_enlarge (v : VitaliFamily μ) {δ : ℝ} (δpos : 0 < δ) :
    (v.enlarge δ δpos).filterAt = v.filterAt := by
  ext1 x
  suffices {t | MeasurableSet t → (interior t).Nonempty → ¬t ⊆ closedBall x δ →
      t ∈ v.setsAt x} ∈ (𝓝 x).smallSets by
    simpa [VitaliFamily.filterAt, VitaliFamily.enlarge, ← sup_principal, inf_sup_left,
      mem_inf_principal]
  filter_upwards [eventually_smallSets_subset.mpr (closedBall_mem_nhds _ δpos)]
  simp +contextual

set_option linter.deprecated false in
@[deprecated exists_covering (since := "2026-11-18")]
theorem fineSubfamilyOn_iff_frequently (v : VitaliFamily μ) {f : X → Set (Set X)} {s : Set X} :
    v.FineSubfamilyOn f s ↔ ∀ x ∈ s, ∃ᶠ t in v.filterAt x, t ∈ f x := by
  refine forall₂_congr fun x hx ↦ ?_
  simp [frequently_filterAt_iff, ← and_assoc, and_right_comm]

set_option linter.deprecated false in
@[deprecated exists_covering (since := "2026-11-18")]
theorem fineSubfamilyOn_of_frequently (v : VitaliFamily μ) (f : X → Set (Set X)) (s : Set X)
    (h : ∀ x ∈ s, ∃ᶠ t in v.filterAt x, t ∈ f x) : v.FineSubfamilyOn f s := by
  rwa [fineSubfamilyOn_iff_frequently]

end VitaliFamily
