/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Measures positive on nonempty opens

In this file we define a typeclass for measures that are positive on nonempty opens, see
`MeasureTheory.Measure.IsOpenPosMeasure`. Examples include (additive) Haar measures, as well as
measures that have positive density with respect to a Haar measure. We also prove some basic facts
about these measures.

-/


open Topology ENNReal MeasureTheory

open Set Function Filter

namespace MeasureTheory

namespace Measure

section Basic

variable {X Y : Type*} [TopologicalSpace X] {m : MeasurableSpace X} [TopologicalSpace Y]
  [T2Space Y] (μ ν : Measure X)

/-- A measure is said to be `IsOpenPosMeasure` if it is positive on nonempty open sets. -/
class IsOpenPosMeasure : Prop where
  open_pos : ∀ U : Set X, IsOpen U → U.Nonempty → μ U ≠ 0

variable [IsOpenPosMeasure μ] {s U F : Set X} {x : X}

theorem _root_.IsOpen.measure_ne_zero (hU : IsOpen U) (hne : U.Nonempty) : μ U ≠ 0 :=
  IsOpenPosMeasure.open_pos U hU hne

theorem _root_.IsOpen.measure_pos (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U :=
  (hU.measure_ne_zero μ hne).bot_lt

instance (priority := 100) [Nonempty X] : NeZero μ :=
  ⟨measure_univ_pos.mp <| isOpen_univ.measure_pos μ univ_nonempty⟩

theorem _root_.IsOpen.measure_pos_iff (hU : IsOpen U) : 0 < μ U ↔ U.Nonempty :=
  ⟨fun h => nonempty_iff_ne_empty.2 fun he => h.ne' <| he.symm ▸ measure_empty, hU.measure_pos μ⟩

theorem _root_.IsOpen.measure_eq_zero_iff (hU : IsOpen U) : μ U = 0 ↔ U = ∅ := by
  simpa only [not_lt, nonpos_iff_eq_zero, not_nonempty_iff_eq_empty] using
    not_congr (hU.measure_pos_iff μ)

theorem measure_pos_of_nonempty_interior (h : (interior s).Nonempty) : 0 < μ s :=
  (isOpen_interior.measure_pos μ h).trans_le (measure_mono interior_subset)

theorem measure_pos_of_mem_nhds (h : s ∈ 𝓝 x) : 0 < μ s :=
  measure_pos_of_nonempty_interior _ ⟨x, mem_interior_iff_mem_nhds.2 h⟩

theorem isOpenPosMeasure_smul {c : ℝ≥0∞} (h : c ≠ 0) : IsOpenPosMeasure (c • μ) :=
  ⟨fun _U Uo Une => mul_ne_zero h (Uo.measure_ne_zero μ Une)⟩

variable {μ ν}

protected theorem AbsolutelyContinuous.isOpenPosMeasure (h : μ ≪ ν) : IsOpenPosMeasure ν :=
  ⟨fun _U ho hne h₀ => ho.measure_ne_zero μ hne (h h₀)⟩

theorem _root_.LE.le.isOpenPosMeasure (h : μ ≤ ν) : IsOpenPosMeasure ν :=
  h.absolutelyContinuous.isOpenPosMeasure

theorem _root_.IsOpen.measure_zero_iff_eq_empty (hU : IsOpen U) :
    μ U = 0 ↔ U = ∅ :=
  ⟨fun h ↦ (hU.measure_eq_zero_iff μ).mp h, fun h ↦ by simp [h]⟩

theorem _root_.IsOpen.ae_eq_empty_iff_eq (hU : IsOpen U) :
    U =ᵐ[μ] (∅ : Set X) ↔ U = ∅ := by
  rw [ae_eq_empty, hU.measure_zero_iff_eq_empty]

/-- An open null set w.r.t. an `IsOpenPosMeasure` is empty. -/
theorem _root_.IsOpen.eq_empty_of_measure_zero (hU : IsOpen U) (h₀ : μ U = 0) : U = ∅ :=
  (hU.measure_eq_zero_iff μ).mp h₀

theorem _root_.IsClosed.ae_eq_univ_iff_eq (hF : IsClosed F) :
    F =ᵐ[μ] univ ↔ F = univ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rwa [ae_eq_univ, hF.isOpen_compl.measure_eq_zero_iff μ, compl_empty_iff] at h

theorem _root_.IsClosed.measure_eq_univ_iff_eq [OpensMeasurableSpace X] [IsFiniteMeasure μ]
    (hF : IsClosed F) :
    μ F = μ univ ↔ F = univ := by
  rw [← ae_eq_univ_iff_measure_eq hF.measurableSet.nullMeasurableSet, hF.ae_eq_univ_iff_eq]

theorem _root_.IsClosed.measure_eq_one_iff_eq_univ [OpensMeasurableSpace X] [IsProbabilityMeasure μ]
    (hF : IsClosed F) :
    μ F = 1 ↔ F = univ := by
  rw [← measure_univ (μ := μ), hF.measure_eq_univ_iff_eq]

/-- A null set has empty interior. -/
theorem interior_eq_empty_of_null (hs : μ s = 0) : interior s = ∅ :=
  isOpen_interior.eq_empty_of_measure_zero <| measure_mono_null interior_subset hs

/-- A property satisfied almost everywhere is satisfied on a dense subset. -/
theorem dense_of_ae {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x) : Dense {x | p x} := by
  rw [dense_iff_closure_eq, closure_eq_compl_interior_compl, compl_univ_iff]
  exact μ.interior_eq_empty_of_null hp

/-- If two functions are a.e. equal on an open set and are continuous on this set, then they are
equal on this set. -/
theorem eqOn_open_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ.restrict U] g) (hU : IsOpen U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) : EqOn f g U := by
  replace h := ae_imp_of_ae_restrict h
  simp only [ae_iff, Classical.not_imp] at h
  have : IsOpen (U ∩ { a | f a ≠ g a }) := by
    refine isOpen_iff_mem_nhds.mpr fun a ha => inter_mem (hU.mem_nhds ha.1) ?_
    rcases ha with ⟨ha : a ∈ U, ha' : (f a, g a) ∈ (diagonal Y)ᶜ⟩
    exact
      (hf.continuousAt (hU.mem_nhds ha)).prodMk_nhds (hg.continuousAt (hU.mem_nhds ha))
        (isClosed_diagonal.isOpen_compl.mem_nhds ha')
  replace := (this.eq_empty_of_measure_zero h).le
  exact fun x hx => Classical.not_not.1 fun h => this ⟨hx, h⟩

/-- If two continuous functions are a.e. equal, then they are equal. -/
theorem eq_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ] g) (hf : Continuous f) (hg : Continuous g) : f = g :=
  suffices EqOn f g univ from funext fun _ => this trivial
  eqOn_open_of_ae_eq (ae_restrict_of_ae h) isOpen_univ hf.continuousOn hg.continuousOn

theorem eqOn_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ.restrict s] g) (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) (hU : s ⊆ closure (interior s)) : EqOn f g s :=
  have : interior s ⊆ s := interior_subset
  (eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset this h) isOpen_interior (hf.mono this)
        (hg.mono this)).of_subset_closure
    hf hg this hU

variable (μ) in
theorem _root_.Continuous.ae_eq_iff_eq {f g : X → Y} (hf : Continuous f) (hg : Continuous g) :
    f =ᵐ[μ] g ↔ f = g :=
  ⟨fun h => eq_of_ae_eq h hf hg, fun h => h ▸ EventuallyEq.rfl⟩

theorem _root_.Continuous.isOpenPosMeasure_map [OpensMeasurableSpace X]
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    {f : X → Z} (hf : Continuous f) (hf_surj : Function.Surjective f) :
    (Measure.map f μ).IsOpenPosMeasure := by
  refine ⟨fun U hUo hUne => ?_⟩
  rw [Measure.map_apply hf.measurable hUo.measurableSet]
  exact (hUo.preimage hf).measure_ne_zero μ (hf_surj.nonempty_preimage.mpr hUne)

protected theorem IsOpenPosMeasure.comap [BorelSpace X]
    {Z : Type*} [TopologicalSpace Z] {mZ : MeasurableSpace Z} [BorelSpace Z]
    (μ : Measure Z) [IsOpenPosMeasure μ] {f : X → Z} (hf : IsOpenEmbedding f) :
    (μ.comap f).IsOpenPosMeasure where
  open_pos U hU Une := by
    rw [hf.measurableEmbedding.comap_apply]
    exact IsOpenPosMeasure.open_pos _ (hf.isOpen_iff_image_isOpen.mp hU) (Une.image f)

end Basic

section LinearOrder

variable {X Y : Type*} [TopologicalSpace X] [LinearOrder X] [OrderTopology X]
  {m : MeasurableSpace X} [TopologicalSpace Y] [T2Space Y] (μ : Measure X) [IsOpenPosMeasure μ]

theorem measure_Ioi_pos [NoMaxOrder X] (a : X) : 0 < μ (Ioi a) :=
  isOpen_Ioi.measure_pos μ nonempty_Ioi

theorem measure_Iio_pos [NoMinOrder X] (a : X) : 0 < μ (Iio a) :=
  isOpen_Iio.measure_pos μ nonempty_Iio

theorem measure_Ioo_pos [DenselyOrdered X] {a b : X} : 0 < μ (Ioo a b) ↔ a < b :=
  (isOpen_Ioo.measure_pos_iff μ).trans nonempty_Ioo

theorem measure_Ioo_eq_zero [DenselyOrdered X] {a b : X} : μ (Ioo a b) = 0 ↔ b ≤ a :=
  (isOpen_Ioo.measure_eq_zero_iff μ).trans (Ioo_eq_empty_iff.trans not_lt)

theorem eqOn_Ioo_of_ae_eq {a b : X} {f g : X → Y} (hfg : f =ᵐ[μ.restrict (Ioo a b)] g)
    (hf : ContinuousOn f (Ioo a b)) (hg : ContinuousOn g (Ioo a b)) : EqOn f g (Ioo a b) :=
  eqOn_of_ae_eq hfg hf hg Ioo_subset_closure_interior

theorem eqOn_Ioc_of_ae_eq [DenselyOrdered X] {a b : X} {f g : X → Y}
    (hfg : f =ᵐ[μ.restrict (Ioc a b)] g) (hf : ContinuousOn f (Ioc a b))
    (hg : ContinuousOn g (Ioc a b)) : EqOn f g (Ioc a b) :=
  eqOn_of_ae_eq hfg hf hg (Ioc_subset_closure_interior _ _)

theorem eqOn_Ico_of_ae_eq [DenselyOrdered X] {a b : X} {f g : X → Y}
    (hfg : f =ᵐ[μ.restrict (Ico a b)] g) (hf : ContinuousOn f (Ico a b))
    (hg : ContinuousOn g (Ico a b)) : EqOn f g (Ico a b) :=
  eqOn_of_ae_eq hfg hf hg (Ico_subset_closure_interior _ _)

theorem eqOn_Icc_of_ae_eq [DenselyOrdered X] {a b : X} (hne : a ≠ b) {f g : X → Y}
    (hfg : f =ᵐ[μ.restrict (Icc a b)] g) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) : EqOn f g (Icc a b) :=
  eqOn_of_ae_eq hfg hf hg (closure_interior_Icc hne).symm.subset

end LinearOrder

end Measure

end MeasureTheory

open MeasureTheory MeasureTheory.Measure

namespace Metric

variable {X : Type*} [PseudoMetricSpace X] {m : MeasurableSpace X} (μ : Measure X)
  [IsOpenPosMeasure μ]

theorem measure_ball_pos (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ (ball x r) :=
  isOpen_ball.measure_pos μ (nonempty_ball.2 hr)

/-- See also `Metric.measure_closedBall_pos_iff`. -/
theorem measure_closedBall_pos (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ (closedBall x r) :=
  (measure_ball_pos μ x hr).trans_le (measure_mono ball_subset_closedBall)

@[simp] lemma measure_closedBall_pos_iff {X : Type*} [MetricSpace X] {m : MeasurableSpace X}
    (μ : Measure X) [IsOpenPosMeasure μ] [NoAtoms μ] {x : X} {r : ℝ} :
    0 < μ (closedBall x r) ↔ 0 < r := by
  refine ⟨fun h ↦ ?_, measure_closedBall_pos μ x⟩
  contrapose! h
  rw [(subsingleton_closedBall x h).measure_zero μ]

end Metric

namespace EMetric

variable {X : Type*} [PseudoEMetricSpace X] {m : MeasurableSpace X} (μ : Measure X)
  [IsOpenPosMeasure μ]

theorem measure_ball_pos (x : X) {r : ℝ≥0∞} (hr : r ≠ 0) : 0 < μ (ball x r) :=
  isOpen_ball.measure_pos μ ⟨x, mem_ball_self hr.bot_lt⟩

theorem measure_closedBall_pos (x : X) {r : ℝ≥0∞} (hr : r ≠ 0) : 0 < μ (closedBall x r) :=
  (measure_ball_pos μ x hr).trans_le (measure_mono ball_subset_closedBall)

end EMetric

section MeasureZero
/-! ## Meagre sets and measure zero
In general, neither of meagre and measure zero implies the other.
- The set of Liouville numbers is a Lebesgue measure zero subset of ℝ, but is not meagre.
(In fact, its complement is meagre. See `Real.disjoint_residual_ae`.)

- The complement of the set of Liouville numbers in $[0,1]$ is meagre and has measure 1.
For another counterexample, for all $α ∈ (0,1)$, there is a generalised Cantor set $C ⊆ [0,1]$
of measure `α`. Cantor sets are nowhere dense (hence meagre). Taking a countable union of
fat Cantor sets whose measure approaches 1 even yields a meagre set of measure 1.

However, with respect to a measure which is positive on non-empty open sets, *closed* measure
zero sets are nowhere dense and σ-compact measure zero sets in a Hausdorff space are meagre.
-/

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {s : Set X}
  {μ : Measure X} [IsOpenPosMeasure μ]

/-- A *closed* measure zero subset is nowhere dense. (Closedness is required: for instance, the
rational numbers are countable (thus have measure zero), but are dense (hence not nowhere dense). -/
lemma IsNowhereDense.of_isClosed_null (h₁s : IsClosed s) (h₂s : μ s = 0) :
    IsNowhereDense s := h₁s.isNowhereDense_iff.mpr (interior_eq_empty_of_null h₂s)

/-- A σ-compact measure zero subset is meagre.
(More generally, every Fσ set of measure zero is meagre.) -/
lemma IsMeagre.of_isSigmaCompact_null [T2Space X] (h₁s : IsSigmaCompact s) (h₂s : μ s = 0) :
    IsMeagre s := by
  rcases h₁s with ⟨K, hcompact, hcover⟩
  have h (n : ℕ) : IsNowhereDense (K n) := by
    have : μ (K n) = 0 := measure_mono_null (hcover ▸ subset_iUnion K n) h₂s
    exact .of_isClosed_null (hcompact n).isClosed this
  rw [isMeagre_iff_countable_union_isNowhereDense]
  exact ⟨range K, fun t ⟨n, hn⟩ ↦ hn ▸ h n, countable_range K, hcover.symm.subset⟩

end MeasureZero
