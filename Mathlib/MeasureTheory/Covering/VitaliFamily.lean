/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace

#align_import measure_theory.covering.vitali_family from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

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
* `v.FineSubfamilyOn` describes the subfamilies of `v` from which one can extract almost
everywhere disjoint coverings. This property, called
`v.FineSubfamilyOn.exists_disjoint_covering_ae`, is essentially a restatement of the definition
of a Vitali family. We also provide an API to use efficiently such a disjoint covering.
* `v.filterAt x` is a filter on sets of `X`, such that convergence with respect to this filter
means convergence when sets in the Vitali family shrink towards `x`.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.8][Federer1996] (Vitali families are called
Vitali relations there)
-/


open MeasureTheory Metric Set Filter TopologicalSpace MeasureTheory.Measure

open Filter MeasureTheory Topology

variable {α : Type*} [MetricSpace α]

/-- On a metric space `X` with a measure `μ`, consider for each `x : X` a family of measurable sets
with nonempty interiors, called `setsAt x`. This family is a Vitali family if it satisfies the
following property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `setsAt x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.
-/
-- Porting note(#5171): this linter isn't ported yet.
-- @[nolint has_nonempty_instance]
structure VitaliFamily {m : MeasurableSpace α} (μ : Measure α) where
  /-- Sets of the family "centered" at a given point. -/
  setsAt :  α → Set (Set α)
  /-- All sets of the family are measurable. -/
  measurableSet : ∀ x : α, ∀ s ∈ setsAt x, MeasurableSet s
  /-- All sets of the family have nonempty interior. -/
  nonempty_interior : ∀ x : α, ∀ s ∈ setsAt x, (interior s).Nonempty
  /-- For any closed ball around `x`, there exists a set of the family contained in this ball. -/
  nontrivial : ∀ (x : α), ∀ ε > (0 : ℝ), ∃ s ∈ setsAt x, s ⊆ closedBall x ε
  /-- Consider a (possibly non-measurable) set `s`,
  and for any `x` in `s` a subfamily `f x` of `setsAt x`
  containing sets of arbitrarily small diameter.
  Then one can extract a disjoint subfamily covering almost all `s`. -/
  covering : ∀ (s : Set α) (f : α → Set (Set α)),
    (∀ x ∈ s, f x ⊆ setsAt x) → (∀ x ∈ s, ∀ ε > (0 : ℝ), ∃ a ∈ f x, a ⊆ closedBall x ε) →
    ∃ t : Set (α × Set α), (∀ p ∈ t, p.1 ∈ s) ∧ (t.PairwiseDisjoint fun p ↦ p.2) ∧
      (∀ p ∈ t, p.2 ∈ f p.1) ∧ μ (s \ ⋃ p ∈ t, p.2) = 0
#align vitali_family VitaliFamily

namespace VitaliFamily

variable {m0 : MeasurableSpace α} {μ : Measure α}

/-- A Vitali family for a measure `μ` is also a Vitali family for any measure absolutely continuous
with respect to `μ`. -/
def mono (v : VitaliFamily μ) (ν : Measure α) (hν : ν ≪ μ) : VitaliFamily ν where
  __ := v
  covering s f h h' :=
    let ⟨t, ts, disj, mem_f, hμ⟩ := v.covering s f h h'
    ⟨t, ts, disj, mem_f, hν hμ⟩
#align vitali_family.mono VitaliFamily.mono

/-- Given a Vitali family `v` for a measure `μ`, a family `f` is a fine subfamily on a set `s` if
every point `x` in `s` belongs to arbitrarily small sets in `v.setsAt x ∩ f x`. This is precisely
the subfamilies for which the Vitali family definition ensures that one can extract a disjoint
covering of almost all `s`. -/
def FineSubfamilyOn (v : VitaliFamily μ) (f : α → Set (Set α)) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ ε > 0, ∃ a ∈ v.setsAt x ∩ f x, a ⊆ closedBall x ε
#align vitali_family.fine_subfamily_on VitaliFamily.FineSubfamilyOn

namespace FineSubfamilyOn

variable {v : VitaliFamily μ} {f : α → Set (Set α)} {s : Set α} (h : v.FineSubfamilyOn f s)

theorem exists_disjoint_covering_ae :
    ∃ t : Set (α × Set α),
      (∀ p : α × Set α, p ∈ t → p.1 ∈ s) ∧
      (t.PairwiseDisjoint fun p => p.2) ∧
      (∀ p : α × Set α, p ∈ t → p.2 ∈ v.setsAt p.1 ∩ f p.1) ∧
      μ (s \ ⋃ (p : α × Set α) (_ : p ∈ t), p.2) = 0 :=
  v.covering s (fun x => v.setsAt x ∩ f x) (fun _ _ => inter_subset_left _ _) h
#align vitali_family.fine_subfamily_on.exists_disjoint_covering_ae VitaliFamily.FineSubfamilyOn.exists_disjoint_covering_ae

/-- Given `h : v.FineSubfamilyOn f s`, then `h.index` is a set parametrizing a disjoint
covering of almost every `s`. -/
protected def index : Set (α × Set α) :=
  h.exists_disjoint_covering_ae.choose
#align vitali_family.fine_subfamily_on.index VitaliFamily.FineSubfamilyOn.index

-- Porting note: Needed to add `(_h : FineSubfamilyOn v f s)`
/-- Given `h : v.FineSubfamilyOn f s`, then `h.covering p` is a set in the family,
for `p ∈ h.index`, such that these sets form a disjoint covering of almost every `s`. -/
@[nolint unusedArguments]
protected def covering (_h : FineSubfamilyOn v f s) : α × Set α → Set α :=
  fun p => p.2
#align vitali_family.fine_subfamily_on.covering VitaliFamily.FineSubfamilyOn.covering

theorem index_subset : ∀ p : α × Set α, p ∈ h.index → p.1 ∈ s :=
  h.exists_disjoint_covering_ae.choose_spec.1
#align vitali_family.fine_subfamily_on.index_subset VitaliFamily.FineSubfamilyOn.index_subset

theorem covering_disjoint : h.index.PairwiseDisjoint h.covering :=
  h.exists_disjoint_covering_ae.choose_spec.2.1
#align vitali_family.fine_subfamily_on.covering_disjoint VitaliFamily.FineSubfamilyOn.covering_disjoint

theorem covering_disjoint_subtype : Pairwise (Disjoint on fun x : h.index => h.covering x) :=
  (pairwise_subtype_iff_pairwise_set _ _).2 h.covering_disjoint
#align vitali_family.fine_subfamily_on.covering_disjoint_subtype VitaliFamily.FineSubfamilyOn.covering_disjoint_subtype

theorem covering_mem {p : α × Set α} (hp : p ∈ h.index) : h.covering p ∈ f p.1 :=
  (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).2
#align vitali_family.fine_subfamily_on.covering_mem VitaliFamily.FineSubfamilyOn.covering_mem

theorem covering_mem_family {p : α × Set α} (hp : p ∈ h.index) : h.covering p ∈ v.setsAt p.1 :=
  (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).1
#align vitali_family.fine_subfamily_on.covering_mem_family VitaliFamily.FineSubfamilyOn.covering_mem_family

theorem measure_diff_biUnion : μ (s \ ⋃ p ∈ h.index, h.covering p) = 0 :=
  h.exists_disjoint_covering_ae.choose_spec.2.2.2
#align vitali_family.fine_subfamily_on.measure_diff_bUnion VitaliFamily.FineSubfamilyOn.measure_diff_biUnion

theorem index_countable [SecondCountableTopology α] : h.index.Countable :=
  h.covering_disjoint.countable_of_nonempty_interior fun _ hx =>
    v.nonempty_interior _ _ (h.covering_mem_family hx)
#align vitali_family.fine_subfamily_on.index_countable VitaliFamily.FineSubfamilyOn.index_countable

protected theorem measurableSet_u {p : α × Set α} (hp : p ∈ h.index) :
    MeasurableSet (h.covering p) :=
  v.measurableSet p.1 _ (h.covering_mem_family hp)
#align vitali_family.fine_subfamily_on.measurable_set_u VitaliFamily.FineSubfamilyOn.measurableSet_u

theorem measure_le_tsum_of_absolutelyContinuous [SecondCountableTopology α] {ρ : Measure α}
    (hρ : ρ ≪ μ) : ρ s ≤ ∑' p : h.index, ρ (h.covering p) :=
  calc
    ρ s ≤ ρ ((s \ ⋃ p ∈ h.index, h.covering p) ∪ ⋃ p ∈ h.index, h.covering p) :=
      measure_mono (by simp only [subset_union_left, diff_union_self])
    _ ≤ ρ (s \ ⋃ p ∈ h.index, h.covering p) + ρ (⋃ p ∈ h.index, h.covering p) :=
      (measure_union_le _ _)
    _ = ∑' p : h.index, ρ (h.covering p) := by
      rw [hρ h.measure_diff_biUnion, zero_add,
        measure_biUnion h.index_countable h.covering_disjoint fun x hx => h.measurableSet_u hx]
#align vitali_family.fine_subfamily_on.measure_le_tsum_of_absolutely_continuous VitaliFamily.FineSubfamilyOn.measure_le_tsum_of_absolutelyContinuous

theorem measure_le_tsum [SecondCountableTopology α] : μ s ≤ ∑' x : h.index, μ (h.covering x) :=
  h.measure_le_tsum_of_absolutelyContinuous Measure.AbsolutelyContinuous.rfl
#align vitali_family.fine_subfamily_on.measure_le_tsum VitaliFamily.FineSubfamilyOn.measure_le_tsum

end FineSubfamilyOn

/-- One can enlarge a Vitali family by adding to the sets `f x` at `x` all sets which are not
contained in a `δ`-neighborhood on `x`. This does not change the local filter at a point, but it
can be convenient to get a nicer global behavior. -/
def enlarge (v : VitaliFamily μ) (δ : ℝ) (δpos : 0 < δ) : VitaliFamily μ where
  setsAt x := v.setsAt x ∪ { a | MeasurableSet a ∧ (interior a).Nonempty ∧ ¬a ⊆ closedBall x δ }
  measurableSet x a ha := by
    cases' ha with ha ha
    exacts [v.measurableSet _ _ ha, ha.1]
  nonempty_interior x a ha := by
    cases' ha with ha ha
    exacts [v.nonempty_interior _ _ ha, ha.2.1]
  nontrivial := by
    intro x ε εpos
    rcases v.nontrivial x ε εpos with ⟨a, ha, h'a⟩
    exact ⟨a, mem_union_left _ ha, h'a⟩
  covering := by
    intro s f fset ffine
    let g : α → Set (Set α) := fun x => f x ∩ v.setsAt x
    have : ∀ x ∈ s, ∀ ε : ℝ, ε > 0 → ∃ (a : Set α), a ∈ g x ∧ a ⊆ closedBall x ε := by
      intro x hx ε εpos
      obtain ⟨a, af, ha⟩ : ∃ a ∈ f x, a ⊆ closedBall x (min ε δ) :=
        ffine x hx (min ε δ) (lt_min εpos δpos)
      rcases fset x hx af with (h'a | h'a)
      · exact ⟨a, ⟨af, h'a⟩, ha.trans (closedBall_subset_closedBall (min_le_left _ _))⟩
      · refine False.elim (h'a.2.2 ?_)
        exact ha.trans (closedBall_subset_closedBall (min_le_right _ _))
    rcases v.covering s g (fun x _ => inter_subset_right _ _) this with ⟨t, ts, tdisj, tg, μt⟩
    exact ⟨t, ts, tdisj, fun p hp => (tg p hp).1, μt⟩
#align vitali_family.enlarge VitaliFamily.enlarge

variable (v : VitaliFamily μ)

/-- Given a vitali family `v`, then `v.filterAt x` is the filter on `Set α` made of those families
that contain all sets of `v.setsAt x` of a sufficiently small diameter. This filter makes it
possible to express limiting behavior when sets in `v.setsAt x` shrink to `x`. -/
def filterAt (x : α) : Filter (Set α) := (𝓝 x).smallSets ⊓ 𝓟 (v.setsAt x)
#align vitali_family.filter_at VitaliFamily.filterAt

theorem _root_.Filter.HasBasis.vitaliFamily {ι : Sort*} {p : ι → Prop} {s : ι → Set α} {x : α}
    (h : (𝓝 x).HasBasis p s) : (v.filterAt x).HasBasis p (fun i ↦ {t ∈ v.setsAt x | t ⊆ s i}) := by
  simpa only [← Set.setOf_inter_eq_sep] using h.smallSets.inf_principal _

theorem filterAt_basis_closedBall (x : α) :
    (v.filterAt x).HasBasis (0 < ·) ({a ∈ v.setsAt x | a ⊆ closedBall x ·}) :=
  nhds_basis_closedBall.vitaliFamily v

theorem mem_filterAt_iff {x : α} {s : Set (Set α)} :
    s ∈ v.filterAt x ↔ ∃ ε > (0 : ℝ), ∀ a ∈ v.setsAt x, a ⊆ closedBall x ε → a ∈ s := by
  simp only [(v.filterAt_basis_closedBall x).mem_iff, ← and_imp, subset_def, mem_setOf]
#align vitali_family.mem_filter_at_iff VitaliFamily.mem_filterAt_iff

instance filterAt_neBot (x : α) : (v.filterAt x).NeBot :=
  (v.filterAt_basis_closedBall x).neBot_iff.2 <| v.nontrivial _ _
#align vitali_family.filter_at_ne_bot VitaliFamily.filterAt_neBot

theorem eventually_filterAt_iff {x : α} {P : Set α → Prop} :
    (∀ᶠ a in v.filterAt x, P a) ↔ ∃ ε > (0 : ℝ), ∀ a ∈ v.setsAt x, a ⊆ closedBall x ε → P a :=
  v.mem_filterAt_iff
#align vitali_family.eventually_filter_at_iff VitaliFamily.eventually_filterAt_iff

theorem tendsto_filterAt_iff {ι : Type*} {l : Filter ι} {f : ι → Set α} {x : α} :
    Tendsto f l (v.filterAt x) ↔
      (∀ᶠ i in l, f i ∈ v.setsAt x) ∧ ∀ ε > (0 : ℝ), ∀ᶠ i in l, f i ⊆ closedBall x ε := by
  simp only [filterAt, tendsto_inf, nhds_basis_closedBall.smallSets.tendsto_right_iff,
    tendsto_principal, and_comm, mem_powerset_iff]
#align vitali_family.tendsto_filter_at_iff VitaliFamily.tendsto_filterAt_iff

theorem eventually_filterAt_mem_setsAt (x : α) : ∀ᶠ a in v.filterAt x, a ∈ v.setsAt x :=
  (v.tendsto_filterAt_iff.mp tendsto_id).1
#align vitali_family.eventually_filter_at_mem_sets VitaliFamily.eventually_filterAt_mem_setsAt

theorem eventually_filterAt_subset_closedBall (x : α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : Set α in v.filterAt x, a ⊆ closedBall x ε :=
  (v.tendsto_filterAt_iff.mp tendsto_id).2 ε hε
#align vitali_family.eventually_filter_at_subset_closed_ball VitaliFamily.eventually_filterAt_subset_closedBall

theorem eventually_filterAt_measurableSet (x : α) : ∀ᶠ a in v.filterAt x, MeasurableSet a := by
  filter_upwards [v.eventually_filterAt_mem_setsAt x] with _ ha using v.measurableSet _ _ ha
#align vitali_family.eventually_filter_at_measurable_set VitaliFamily.eventually_filterAt_measurableSet

theorem frequently_filterAt_iff {x : α} {P : Set α → Prop} :
    (∃ᶠ a in v.filterAt x, P a) ↔ ∀ ε > (0 : ℝ), ∃ a ∈ v.setsAt x, a ⊆ closedBall x ε ∧ P a := by
  simp only [(v.filterAt_basis_closedBall x).frequently_iff, ← and_assoc, subset_def, mem_setOf]
#align vitali_family.frequently_filter_at_iff VitaliFamily.frequently_filterAt_iff

theorem eventually_filterAt_subset_of_nhds {x : α} {o : Set α} (hx : o ∈ 𝓝 x) :
    ∀ᶠ a in v.filterAt x, a ⊆ o :=
  (eventually_smallSets_subset.2 hx).filter_mono inf_le_left
#align vitali_family.eventually_filter_at_subset_of_nhds VitaliFamily.eventually_filterAt_subset_of_nhds

theorem fineSubfamilyOn_of_frequently (v : VitaliFamily μ) (f : α → Set (Set α)) (s : Set α)
    (h : ∀ x ∈ s, ∃ᶠ a in v.filterAt x, a ∈ f x) : v.FineSubfamilyOn f s := by
  intro x hx ε εpos
  obtain ⟨a, av, ha, af⟩ : ∃ (a : Set α) , a ∈ v.setsAt x ∧ a ⊆ closedBall x ε ∧ a ∈ f x :=
    v.frequently_filterAt_iff.1 (h x hx) ε εpos
  exact ⟨a, ⟨av, af⟩, ha⟩
#align vitali_family.fine_subfamily_on_of_frequently VitaliFamily.fineSubfamilyOn_of_frequently

end VitaliFamily
