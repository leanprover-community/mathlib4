/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace

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


open MeasureTheory Set Filter TopologicalSpace MeasureTheory.Measure

open scoped Topology

universe u

/-- On a metric space `X` with a measure `μ`, consider for each `x : X` a family of measurable sets
with nonempty interiors, called `setsAt x`. This family is a Vitali family if it satisfies the
following property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `setsAt x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.
-/
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/5171): this linter isn't ported yet.
-- @[nolint has_nonempty_instance]
structure VitaliFamily {X : Type u} [TopologicalSpace X] {m : MeasurableSpace X}
    (μ : Measure X) where
  /-- Sets of the family "centered" at a given point. -/
  setsAt :  X → Set (Set X)
  /-- All sets of the family are measurable. -/
  measurableSet : ∀ x : X, ∀ s ∈ setsAt x, MeasurableSet s
  /-- For any closed ball around `x`, there exists a set of the family contained in this ball. -/
  nontrivial : ∀ (x : X), ∃ᶠ s in (𝓝 x).smallSets, s ∈ setsAt x
  /-- Consider a (possibly non-measurable) set `s`,
  and for any `x` in `s` a subfamily `f x` of `setsAt x`
  containing sets of arbitrarily small diameter.
  Then one can extract a disjoint subfamily covering almost all `s`. -/
  covering : ∀ (s : Set X) (f : X → Set (Set X)),
    (∀ x, f x ⊆ setsAt x) → (∀ x, ∃ᶠ t in (𝓝 x).smallSets, t ∈ f x) →
    ∃ (ι : Type u) (c : ι → X) (t : ι → Set X), Countable ι ∧
      (∀ i, c i ∈ s) ∧ Pairwise (Disjoint on t) ∧ (∀ i, t i ∈ f (c i)) ∧ μ (s \ ⋃ i, t i) = 0

namespace VitaliFamily

section TopologicalSpace

variable {X : Type u} [TopologicalSpace X] {m0 : MeasurableSpace X} {μ : Measure X}

/-- A Vitali family for a measure `μ` is also a Vitali family for any measure absolutely continuous
with respect to `μ`. -/
def mono (v : VitaliFamily μ) (ν : Measure X) (hν : ν ≪ μ) : VitaliFamily ν where
  __ := v
  covering s f h h' :=
    let ⟨ι, c, t, hcount, hc, hd, ht, hμ⟩ := v.covering s f h h'
    ⟨ι, c, t, hcount, hc, hd, ht, hν hμ⟩

/-- Given a vitali family `v`, then `v.filterAt x` is the filter on `Set X` made of those families
that contain all sets of `v.setsAt x` of a sufficiently small diameter. This filter makes it
possible to express limiting behavior when sets in `v.setsAt x` shrink to `x`. -/
def filterAt (v : VitaliFamily μ) (x : X) : Filter (Set X) := (𝓝 x).smallSets ⊓ 𝓟 (v.setsAt x)

theorem _root_.Filter.HasBasis.vitaliFamily {ι : Sort*} {p : ι → Prop} {s : ι → Set X} {x : X}
    (h : (𝓝 x).HasBasis p s) (v : VitaliFamily μ) :
    (v.filterAt x).HasBasis p (fun i ↦ {t ∈ v.setsAt x | t ⊆ s i}) := by
  simpa only [← Set.setOf_inter_eq_sep] using h.smallSets.inf_principal _

instance filterAt_neBot (v : VitaliFamily μ) (x : X) : (v.filterAt x).NeBot :=
  frequently_mem_iff_neBot.1 <| v.nontrivial x

theorem eventually_subset_of_nhds (v : VitaliFamily μ) {x : X} {U : Set X} (hx : U ∈ 𝓝 x) :
    ∀ᶠ a in v.filterAt x, a ⊆ U :=
  (eventually_smallSets_subset.2 hx).filter_mono inf_le_left

theorem eventually_mem_setsAt (v : VitaliFamily μ) (x : X) :
    ∀ᶠ s in v.filterAt x, s ∈ v.setsAt x :=
  eventually_inf_principal.2 <| eventually_of_forall fun _ ↦ id

theorem eventually_measurableSet (v : VitaliFamily μ) (x : X) :
    ∀ᶠ a in v.filterAt x, MeasurableSet a :=
  (v.eventually_mem_setsAt x).mono <| v.measurableSet _

structure FineSubfamilyOn (v : VitaliFamily μ) (s : Set X) where
  toFun : X → Set (Set X)
  ae_frequently' : ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ t in v.filterAt x, t ∈ toFun x

namespace FineSubfamilyOn

variable {v : VitaliFamily μ} {s : Set X}

instance : FunLike (FineSubfamilyOn v s) X (Set (Set X)) where
  coe f := f.toFun
  coe_injective' | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem ae_frequently (f : FineSubfamilyOn v s) : ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ t in v.filterAt x, t ∈ f x :=
  f.ae_frequently'

theorem exists_aecovering (f : FineSubfamilyOn v s) :
    ∃ (ι : Type u) (c : ι → X) (t : ι → Set X), Countable ι ∧ μ (s \ ⋃ i, t i) = 0 ∧
      Pairwise (Disjoint on t) ∧ ∀ i, c i ∈ s ∧ t i ∈ v.setsAt (c i) ∧ t i ∈ f (c i) := by
  classical
  set s' := {x ∈ s | ∃ᶠ t in v.filterAt x, t ∈ f x}
  set f' := fun x ↦ v.setsAt x ∩ if x ∈ s' then f x else univ
  have H : ∀ x, ∃ᶠ t in smallSets (𝓝 x), t ∈ f' x := fun x ↦ by
    if hx : x ∈ s' then simpa only [if_pos hx] using hx.2.of_inf_principal
    else simpa only [if_neg hx, inter_univ] using v.nontrivial x
  obtain ⟨ι, c, t, hcount, hcs, hd, ht, hμ⟩ := v.covering s' f' (fun x ↦ inter_subset_left _ _) H
  refine ⟨ι, c, t, hcount, ?_, hd, fun i ↦ ⟨(hcs i).1, (ht i).1, ?_⟩⟩
  · rw [← ae_le_set] at hμ ⊢
    refine EventuallyLE.trans ?_ hμ
    filter_upwards [f.ae_frequently] with x hx hxs using ⟨hxs, hx hxs⟩
  · simpa only [if_pos (hcs i)] using (ht i).2

def Index (f : FineSubfamilyOn v s) : Type u := f.exists_aecovering.choose

noncomputable def center (f : FineSubfamilyOn v s) : f.Index → X :=
  f.exists_aecovering.choose_spec.choose

noncomputable def covering (f : FineSubfamilyOn v s) : f.Index → Set X :=
  f.exists_aecovering.choose_spec.choose_spec.choose

instance (f : FineSubfamilyOn v s) : Countable f.Index :=
  f.exists_aecovering.choose_spec.choose_spec.choose_spec.1

theorem measure_diff_iUnion (f : FineSubfamilyOn v s) : μ (s \ ⋃ i, f.covering i) = 0 :=
  f.exists_aecovering.choose_spec.choose_spec.choose_spec.2.1

theorem ae_le_iUnion (f : FineSubfamilyOn v s) : s ≤ᵐ[μ] ⋃ i, f.covering i :=
  ae_le_set.2 f.measure_diff_iUnion

theorem ae_eq_iUnion_inter (f : FineSubfamilyOn v s) : s =ᵐ[μ] ⋃ i, f.covering i ∩ s := by
  rw [← iUnion_inter, ae_eq_set]
  simp [f.measure_diff_iUnion, inter_diff_assoc]

theorem pairwise_disjoint (f : FineSubfamilyOn v s) : Pairwise (Disjoint on f.covering) :=
  f.exists_aecovering.choose_spec.choose_spec.choose_spec.2.2.1

theorem disjoint (f : FineSubfamilyOn v s) {i j : f.Index} (h : i ≠ j) :
    Disjoint (f.covering i) (f.covering j) :=
  f.pairwise_disjoint h

theorem center_mem (f : FineSubfamilyOn v s) (i : f.Index) : f.center i ∈ s :=
  (f.exists_aecovering.choose_spec.choose_spec.choose_spec.2.2.2 i).1

theorem covering_mem_setsAt (f : FineSubfamilyOn v s) (i : f.Index) :
    f.covering i ∈ v.setsAt (f.center i) :=
  (f.exists_aecovering.choose_spec.choose_spec.choose_spec.2.2.2 i).2.1

theorem covering_mem (f : FineSubfamilyOn v s) (i : f.Index) : f.covering i ∈ f (f.center i) :=
  (f.exists_aecovering.choose_spec.choose_spec.choose_spec.2.2.2 i).2.2

protected theorem measurableSet_covering (f : FineSubfamilyOn v s) (i : f.Index) :
    MeasurableSet (f.covering i) :=
  v.measurableSet _ _ (f.covering_mem_setsAt _)

theorem outerMeasure_le_tsum_of_absolutelyContinuous (f : FineSubfamilyOn v s)
    {ρ : OuterMeasure X} (hρ : ∀ ⦃t⦄, μ t = 0 → ρ t = 0) : ρ s ≤ ∑' i, ρ (f.covering i) :=
  -- TODO: introduce `OuterMeasure.ae` and golf
  calc
    ρ s ≤ ρ ((s \ ⋃ i, f.covering i) ∪ ⋃ i, f.covering i) := by
      rw [diff_union_self]; exact ρ.mono <| subset_union_left _ _
    _ ≤ ρ (s \ ⋃ i, f.covering i) + ρ (⋃ i, f.covering i) := ρ.union _ _
    _ ≤ ρ (s \ ⋃ i, f.covering i) + ∑' i, ρ (f.covering i) := by gcongr; apply ρ.iUnion
    _ = ∑' i, ρ (f.covering i) := by rw [hρ f.measure_diff_iUnion, zero_add]

theorem measure_le_tsum_of_absolutelyContinuous (f : FineSubfamilyOn v s) {ρ : Measure X}
    (hρ : ρ ≪ μ) : ρ s ≤ ∑' i, ρ (f.covering i) :=
  f.outerMeasure_le_tsum_of_absolutelyContinuous hρ

theorem measure_le_tsum (f : FineSubfamilyOn v s) : μ s ≤ ∑' i, μ (f.covering i) :=
  f.measure_le_tsum_of_absolutelyContinuous Measure.AbsolutelyContinuous.rfl

def restrOpen (f : FineSubfamilyOn v s) (o : Set X) (ho : IsOpen o) (hsub : s ⊆ o) :
    FineSubfamilyOn v s where
  toFun := fun i ↦ f i ∩ {t | t ⊆ o}
  ae_frequently' := f.ae_frequently.mono fun _x hx hxs ↦ (hx hxs).and_eventually <|
    v.eventually_subset_of_nhds <| ho.mem_nhds <| hsub hxs

theorem tsum_measure_covering_restrOpen_le (f : FineSubfamilyOn v s) {o : Set X} (ho : IsOpen o)
    (hsub : s ⊆ o) : ∑' i, μ ((f.restrOpen o ho hsub).covering i) ≤ μ o := by
  rw [← measure_iUnion (pairwise_disjoint _) (FineSubfamilyOn.measurableSet_covering _)]
  exact measure_mono <| iUnion_subset fun i ↦ (covering_mem _ i).2

end FineSubfamilyOn

/-- For almost every point `x`,
sufficiently small sets in a Vitali family around `x` have positive measure.

This is a nontrivial result, following from the covering property of Vitali families.
-/
theorem ae_eventually_measure_pos (v : VitaliFamily μ) :
    ∀ᵐ x ∂μ, ∀ᶠ t in v.filterAt x, 0 < μ t := by
  set s := {x : X | ∃ᶠ t in v.filterAt x, μ t = 0}
  suffices μ s ≤ 0 by simpa [ae_iff] using this
  set f : v.FineSubfamilyOn s := ⟨fun _ ↦ {t | μ t = 0}, ae_of_all _ fun _ ↦ id⟩
  have : ∀ i, μ (f.covering i) = 0 := f.covering_mem
  calc
    μ s ≤ ∑' i, μ (f.covering i) := f.measure_le_tsum
    _ = 0 := by simp [this]

-- theorem filterAt_basis_closedBall (x : α) :
--     (v.filterAt x).HasBasis (0 < ·) ({a ∈ v.setsAt x | a ⊆ closedBall x ·}) :=
--   nhds_basis_closedBall.vitaliFamily v

-- theorem mem_filterAt_iff {x : α} {s : Set (Set α)} :
--     s ∈ v.filterAt x ↔ ∃ ε > (0 : ℝ), ∀ a ∈ v.setsAt x, a ⊆ closedBall x ε → a ∈ s := by
--   simp only [(v.filterAt_basis_closedBall x).mem_iff, ← and_imp, subset_def, mem_setOf]

-- theorem eventually_filterAt_iff {x : α} {P : Set α → Prop} :
--     (∀ᶠ a in v.filterAt x, P a) ↔ ∃ ε > (0 : ℝ), ∀ a ∈ v.setsAt x, a ⊆ closedBall x ε → P a :=
--   v.mem_filterAt_iff

-- theorem tendsto_filterAt_iff {ι : Type*} {l : Filter ι} {f : ι → Set α} {x : α} :
--     Tendsto f l (v.filterAt x) ↔
--       (∀ᶠ i in l, f i ∈ v.setsAt x) ∧ ∀ ε > (0 : ℝ), ∀ᶠ i in l, f i ⊆ closedBall x ε := by
--   simp only [filterAt, tendsto_inf, nhds_basis_closedBall.smallSets.tendsto_right_iff,
--     tendsto_principal, and_comm, mem_powerset_iff]

-- theorem eventually_filterAt_subset_closedBall (x : α) {ε : ℝ} (hε : 0 < ε) :
--     ∀ᶠ a : Set α in v.filterAt x, a ⊆ closedBall x ε :=
--   (v.tendsto_filterAt_iff.mp tendsto_id).2 ε hε

-- theorem frequently_filterAt_iff {x : α} {P : Set α → Prop} :
--     (∃ᶠ a in v.filterAt x, P a) ↔ ∀ ε > (0 : ℝ), ∃ a ∈ v.setsAt x, a ⊆ closedBall x ε ∧ P a := by
--   simp only [(v.filterAt_basis_closedBall x).frequently_iff, ← and_assoc, subset_def, mem_setOf]


-- namespace FineSubfamilyOn

-- variable {v : VitaliFamily μ} {f : α → Set (Set α)} {s : Set α} (h : v.FineSubfamilyOn f s)

-- theorem exists_disjoint_covering_ae :
--     ∃ t : Set (α × Set α),
--       (∀ p : α × Set α, p ∈ t → p.1 ∈ s) ∧
--       (t.PairwiseDisjoint fun p => p.2) ∧
--       (∀ p : α × Set α, p ∈ t → p.2 ∈ v.setsAt p.1 ∩ f p.1) ∧
--       μ (s \ ⋃ (p : α × Set α) (_ : p ∈ t), p.2) = 0 :=
--   v.covering s (fun x => v.setsAt x ∩ f x) (fun _ _ => inter_subset_left _ _) h

-- /-- Given `h : v.FineSubfamilyOn f s`, then `h.index` is a set parametrizing a disjoint
-- covering of almost every `s`. -/
-- protected def Index : Type _ :=
--   h.exists_disjoint_covering_ae.choose

-- /-- Given `h : v.FineSubfamilyOn f s`, then `h.covering p` is a set in the family,
-- for `p ∈ h.index`, such that these sets form a disjoint covering of almost every `s`. -/
-- protected def covering (h : FineSubfamilyOn v f s) : h.Index → Set α :=
--   fun p => p.2

-- theorem index_subset : ∀ p : α × Set α, p ∈ h.index → p.1 ∈ s :=
--   h.exists_disjoint_covering_ae.choose_spec.1

-- theorem covering_disjoint : h.index.PairwiseDisjoint h.covering :=
--   h.exists_disjoint_covering_ae.choose_spec.2.1

-- theorem covering_disjoint_subtype : Pairwise (Disjoint on fun x : h.index => h.covering x) :=
--   (pairwise_subtype_iff_pairwise_set _ _).2 h.covering_disjoint

-- theorem covering_mem {p : α × Set α} (hp : p ∈ h.index) : h.covering p ∈ f p.1 :=
--   (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).2

-- theorem covering_mem_family {p : α × Set α} (hp : p ∈ h.index) : h.covering p ∈ v.setsAt p.1 :=
--   (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).1

-- theorem measure_diff_biUnion : μ (s \ ⋃ p ∈ h.index, h.covering p) = 0 :=
--   h.exists_disjoint_covering_ae.choose_spec.2.2.2

-- theorem index_countable [SecondCountableTopology α] : h.index.Countable :=
--   h.covering_disjoint.countable_of_nonempty_interior fun _ hx =>
--     v.nonempty_interior _ _ (h.covering_mem_family hx)

-- end FineSubfamilyOn

end TopologicalSpace

section MetricSpace

open Metric

variable {X : Type*} [MetricSpace X] {m : MeasurableSpace X} {μ : Measure X}

theorem eventually_subset_closedBall (v : VitaliFamily μ) (x : X) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in v.filterAt x, t ⊆ closedBall x δ :=
  v.eventually_subset_of_nhds <| closedBall_mem_nhds x hδ

/-- One can enlarge a Vitali family by adding to the sets `f x` at `x` all sets which are not
contained in a `δ`-neighborhood on `x`. This does not change the local filter at a point, but it
can be convenient to get a nicer global behavior. -/
def enlarge (v : VitaliFamily μ) (δ : ℝ) (δpos : 0 < δ) : VitaliFamily μ where
  setsAt x := v.setsAt x ∪ { a | MeasurableSet a ∧ ¬a ⊆ closedBall x δ }
  measurableSet
    | _, _, .inl h => v.measurableSet _ _ h
    | _, _, .inr h => h.1
  nontrivial x := (v.nontrivial x).mono fun _ ↦ .inl
  covering s f fset ffine := by
    have hf : ∀ x ∈ s, ∃ᶠ t in v.filterAt x, t ∈ f x := fun x _ ↦ by
      refine frequently_inf_principal.2 <| (ffine x).mp ?_
      filter_upwards [eventually_smallSets_subset.2 (closedBall_mem_nhds _ δpos)] with t htδ htf
      exact ⟨(fset x htf).resolve_right fun h ↦ h.2 htδ, htf⟩
    let g : v.FineSubfamilyOn s := ⟨f, ae_of_all _ hf⟩
    exact ⟨g.Index, g.center, g.covering, inferInstance, g.center_mem, g.pairwise_disjoint,
      g.covering_mem, g.measure_diff_iUnion⟩

@[simp]
theorem enlarge_filterAt (v : VitaliFamily μ) {δ : ℝ} (δpos : 0 < δ) :
    (v.enlarge δ δpos).filterAt = v.filterAt := by
  ext1 x
  refine set_eventuallyEq_iff_inf_principal.1 <| eventuallyEq_set.2 ?_
  filter_upwards [eventually_smallSets_subset.2 (closedBall_mem_nhds _ δpos)] with t ht
  simp [enlarge, ht]
