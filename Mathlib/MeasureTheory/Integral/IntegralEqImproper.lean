/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Bhavik Mehta
-/
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Links between an integral and its "improper" version

In its current state, mathlib only knows how to talk about definite ("proper") integrals,
in the sense that it treats integrals over `[x, +∞)` the same as it treats integrals over
`[y, z]`. For example, the integral over `[1, +∞)` is **not** defined to be the limit of
the integral over `[1, x]` as `x` tends to `+∞`, which is known as an **improper integral**.

Indeed, the "proper" definition is stronger than the "improper" one. The usual counterexample
is `x ↦ sin(x)/x`, which has an improper integral over `[1, +∞)` but no definite integral.

Although definite integrals have better properties, they are hardly usable when it comes to
computing integrals on unbounded sets, which is much easier using limits. Thus, in this file,
we prove various ways of studying the proper integral by studying the improper one.

## Definitions

The main definition of this file is `MeasureTheory.AECover`. It is a rather technical definition
whose sole purpose is generalizing and factoring proofs. Given an index type `ι`, a countably
generated filter `l` over `ι`, and an `ι`-indexed family `φ` of subsets of a measurable space `α`
equipped with a measure `μ`, one should think of a hypothesis `hφ : MeasureTheory.AECover μ l φ` as
a sufficient condition for being able to interpret `∫ x, f x ∂μ` (if it exists) as the limit of `∫ x
in φ i, f x ∂μ` as `i` tends to `l`.

When using this definition with a measure restricted to a set `s`, which happens fairly often, one
should not try too hard to use a `MeasureTheory.AECover` of subsets of `s`, as it often makes proofs
more complicated than necessary. See for example the proof of
`MeasureTheory.integrableOn_Iic_of_intervalIntegral_norm_tendsto` where we use `(fun x ↦ oi x)` as a
`MeasureTheory.AECover` w.r.t. `μ.restrict (Iic b)`, instead of using `(fun x ↦ Ioc x b)`.

## Main statements

- `MeasureTheory.AECover.lintegral_tendsto_of_countably_generated` : if `φ` is a
  `MeasureTheory.AECover μ l`, where `l` is a countably generated filter, and if `f` is a measurable
  `ENNReal`-valued function, then `∫⁻ x in φ n, f x ∂μ` tends to `∫⁻ x, f x ∂μ` as `n` tends to `l`

- `MeasureTheory.AECover.integrable_of_integral_norm_tendsto` : if `φ` is a
  `MeasureTheory.AECover μ l`, where `l` is a countably generated filter, if `f` is measurable and
  integrable on each `φ n`, and if `∫ x in φ n, ‖f x‖ ∂μ` tends to some `I : ℝ` as n tends to `l`,
  then `f` is integrable

- `MeasureTheory.AECover.integral_tendsto_of_countably_generated` : if `φ` is a
  `MeasureTheory.AECover μ l`, where `l` is a countably generated filter, and if `f` is measurable
  and integrable (globally), then `∫ x in φ n, f x ∂μ` tends to `∫ x, f x ∂μ` as `n` tends to `+∞`.

We then specialize these lemmas to various use cases involving intervals, which are frequent
in analysis. In particular,

- `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto` is a version of FTC-2 on the interval
  `(a, +∞)`, giving the formula `∫ x in (a, +∞), g' x = l - g a` if `g'` is integrable and
  `g` tends to `l` at `+∞`.
- `MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg` gives the same result assuming that
  `g'` is nonnegative instead of integrable. Its automatic integrability in this context is proved
  in `MeasureTheory.integrableOn_Ioi_deriv_of_nonneg`.
- `MeasureTheory.integral_comp_smul_deriv_Ioi` is a version of the change of variables formula
  on semi-infinite intervals.
- `MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi` shows that a function whose
  derivative is integrable on `(a, +∞)` has a limit at `+∞`.
- `MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi` shows that an integrable function
  whose derivative is integrable on `(a, +∞)` tends to `0` at `+∞`.

Versions of these results are also given on the intervals `(-∞, a]` and `(-∞, +∞)`, as well as
the corresponding versions of integration by parts.
-/

open MeasureTheory Filter Set TopologicalSpace Topology
open scoped ENNReal NNReal

namespace MeasureTheory

section AECover

variable {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (l : Filter ι)

/-- A sequence `φ` of subsets of `α` is a `MeasureTheory.AECover` w.r.t. a measure `μ` and a filter
`l` if almost every point (w.r.t. `μ`) of `α` eventually belongs to `φ n` (w.r.t. `l`), and if
each `φ n` is measurable.  This definition is a technical way to avoid duplicating a lot of
proofs.  It should be thought of as a sufficient condition for being able to interpret
`∫ x, f x ∂μ` (if it exists) as the limit of `∫ x in φ n, f x ∂μ` as `n` tends to `l`.
See for example `MeasureTheory.AECover.lintegral_tendsto_of_countably_generated`,
`MeasureTheory.AECover.integrable_of_integral_norm_tendsto` and
`MeasureTheory.AECover.integral_tendsto_of_countably_generated`. -/
structure AECover (φ : ι → Set α) : Prop where
  ae_eventually_mem : ∀ᵐ x ∂μ, ∀ᶠ i in l, x ∈ φ i
  protected measurableSet : ∀ i, MeasurableSet <| φ i

variable {μ} {l}

namespace AECover

/-!
## Operations on `AECover`s
-/

/-- Elementwise intersection of two `AECover`s is an `AECover`. -/
theorem inter {φ ψ : ι → Set α} (hφ : AECover μ l φ) (hψ : AECover μ l ψ) :
    AECover μ l (fun i ↦ φ i ∩ ψ i) where
  ae_eventually_mem := hψ.1.mp <| hφ.1.mono fun _ ↦ Eventually.and
  measurableSet _ := (hφ.2 _).inter (hψ.2 _)

theorem superset {φ ψ : ι → Set α} (hφ : AECover μ l φ) (hsub : ∀ i, φ i ⊆ ψ i)
    (hmeas : ∀ i, MeasurableSet (ψ i)) : AECover μ l ψ :=
  ⟨hφ.1.mono fun _x hx ↦ hx.mono fun i hi ↦ hsub i hi, hmeas⟩

theorem mono_ac {ν : Measure α} {φ : ι → Set α} (hφ : AECover μ l φ) (hle : ν ≪ μ) :
    AECover ν l φ := ⟨hle hφ.1, hφ.2⟩

theorem mono {ν : Measure α} {φ : ι → Set α} (hφ : AECover μ l φ) (hle : ν ≤ μ) :
    AECover ν l φ := hφ.mono_ac hle.absolutelyContinuous

end AECover

section MetricSpace

variable [PseudoMetricSpace α] [OpensMeasurableSpace α]

theorem aecover_ball {x : α} {r : ι → ℝ} (hr : Tendsto r l atTop) :
    AECover μ l (fun i ↦ Metric.ball x (r i)) where
  measurableSet _ := Metric.isOpen_ball.measurableSet
  ae_eventually_mem := by
    filter_upwards with y
    filter_upwards [hr (Ioi_mem_atTop (dist x y))] with a ha using by simpa [dist_comm] using ha

theorem aecover_closedBall {x : α} {r : ι → ℝ} (hr : Tendsto r l atTop) :
    AECover μ l (fun i ↦ Metric.closedBall x (r i)) where
  measurableSet _ := Metric.isClosed_closedBall.measurableSet
  ae_eventually_mem := by
    filter_upwards with y
    filter_upwards [hr (Ici_mem_atTop (dist x y))] with a ha using by simpa [dist_comm] using ha

end MetricSpace

section Preorderα

variable [Preorder α] [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
  {a b : ι → α}

theorem aecover_Ici (ha : Tendsto a l atBot) : AECover μ l fun i => Ici (a i) where
  ae_eventually_mem := ae_of_all μ ha.eventually_le_atBot
  measurableSet _ := measurableSet_Ici

theorem aecover_Iic (hb : Tendsto b l atTop) : AECover μ l fun i => Iic <| b i :=
  aecover_Ici (α := αᵒᵈ) hb

theorem aecover_Icc (ha : Tendsto a l atBot) (hb : Tendsto b l atTop) :
    AECover μ l fun i => Icc (a i) (b i) :=
  (aecover_Ici ha).inter (aecover_Iic hb)

end Preorderα

section LinearOrderα

variable [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
  {a b : ι → α} (ha : Tendsto a l atBot) (hb : Tendsto b l atTop)

include ha in
theorem aecover_Ioi [NoMinOrder α] : AECover μ l fun i => Ioi (a i) where
  ae_eventually_mem := ae_of_all μ ha.eventually_lt_atBot
  measurableSet _ := measurableSet_Ioi

include hb in
theorem aecover_Iio [NoMaxOrder α] : AECover μ l fun i => Iio (b i) := aecover_Ioi (α := αᵒᵈ) hb

include ha hb

theorem aecover_Ioo [NoMinOrder α] [NoMaxOrder α] : AECover μ l fun i => Ioo (a i) (b i) :=
  (aecover_Ioi ha).inter (aecover_Iio hb)

theorem aecover_Ioc [NoMinOrder α] : AECover μ l fun i => Ioc (a i) (b i) :=
  (aecover_Ioi ha).inter (aecover_Iic hb)

theorem aecover_Ico [NoMaxOrder α] : AECover μ l fun i => Ico (a i) (b i) :=
  (aecover_Ici ha).inter (aecover_Iio hb)

end LinearOrderα

section FiniteIntervals

variable [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
  {a b : ι → α} {A B : α} (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))

include ha in
theorem aecover_Ioi_of_Ioi : AECover (μ.restrict (Ioi A)) l fun i ↦ Ioi (a i) where
  ae_eventually_mem := (ae_restrict_mem measurableSet_Ioi).mono fun _x hx ↦ ha.eventually <|
    eventually_lt_nhds hx
  measurableSet _ := measurableSet_Ioi

include hb in
theorem aecover_Iio_of_Iio : AECover (μ.restrict (Iio B)) l fun i ↦ Iio (b i) :=
  aecover_Ioi_of_Ioi (α := αᵒᵈ) hb

include ha in
theorem aecover_Ioi_of_Ici : AECover (μ.restrict (Ioi A)) l fun i ↦ Ici (a i) :=
  (aecover_Ioi_of_Ioi ha).superset (fun _ ↦ Ioi_subset_Ici_self) fun _ ↦ measurableSet_Ici

include hb in
theorem aecover_Iio_of_Iic : AECover (μ.restrict (Iio B)) l fun i ↦ Iic (b i) :=
  aecover_Ioi_of_Ici (α := αᵒᵈ) hb

include ha hb in
theorem aecover_Ioo_of_Ioo : AECover (μ.restrict <| Ioo A B) l fun i => Ioo (a i) (b i) :=
  ((aecover_Ioi_of_Ioi ha).mono <| Measure.restrict_mono Ioo_subset_Ioi_self le_rfl).inter
    ((aecover_Iio_of_Iio hb).mono <| Measure.restrict_mono Ioo_subset_Iio_self le_rfl)

include ha hb in
theorem aecover_Ioo_of_Icc : AECover (μ.restrict <| Ioo A B) l fun i => Icc (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).superset (fun _ ↦ Ioo_subset_Icc_self) fun _ ↦ measurableSet_Icc

include ha hb in
theorem aecover_Ioo_of_Ico : AECover (μ.restrict <| Ioo A B) l fun i => Ico (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).superset (fun _ ↦ Ioo_subset_Ico_self) fun _ ↦ measurableSet_Ico

include ha hb in
theorem aecover_Ioo_of_Ioc : AECover (μ.restrict <| Ioo A B) l fun i => Ioc (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).superset (fun _ ↦ Ioo_subset_Ioc_self) fun _ ↦ measurableSet_Ioc

variable [NoAtoms μ]

theorem aecover_Ioc_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ioc A B) l fun i => Icc (a i) (b i) :=
  (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

theorem aecover_Ioc_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ioc A B) l fun i => Ico (a i) (b i) :=
  (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

theorem aecover_Ioc_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ioc A B) l fun i => Ioc (a i) (b i) :=
  (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

theorem aecover_Ioc_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ioc A B) l fun i => Ioo (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

theorem aecover_Ico_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ico A B) l fun i => Icc (a i) (b i) :=
  (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

theorem aecover_Ico_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ico A B) l fun i => Ico (a i) (b i) :=
  (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

theorem aecover_Ico_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ico A B) l fun i => Ioc (a i) (b i) :=
  (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

theorem aecover_Ico_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ico A B) l fun i => Ioo (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

theorem aecover_Icc_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Icc A B) l fun i => Icc (a i) (b i) :=
  (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

theorem aecover_Icc_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Icc A B) l fun i => Ico (a i) (b i) :=
  (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

theorem aecover_Icc_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Icc A B) l fun i => Ioc (a i) (b i) :=
  (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

theorem aecover_Icc_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Icc A B) l fun i => Ioo (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

end FiniteIntervals

protected theorem AECover.restrict {φ : ι → Set α} (hφ : AECover μ l φ) {s : Set α} :
    AECover (μ.restrict s) l φ :=
  hφ.mono Measure.restrict_le_self

theorem aecover_restrict_of_ae_imp {s : Set α} {φ : ι → Set α} (hs : MeasurableSet s)
    (ae_eventually_mem : ∀ᵐ x ∂μ, x ∈ s → ∀ᶠ n in l, x ∈ φ n)
    (measurable : ∀ n, MeasurableSet <| φ n) : AECover (μ.restrict s) l φ where
  ae_eventually_mem := by rwa [ae_restrict_iff' hs]
  measurableSet := measurable

theorem AECover.inter_restrict {φ : ι → Set α} (hφ : AECover μ l φ) {s : Set α}
    (hs : MeasurableSet s) : AECover (μ.restrict s) l fun i => φ i ∩ s :=
  aecover_restrict_of_ae_imp hs
    (hφ.ae_eventually_mem.mono fun _x hx hxs => hx.mono fun _i hi => ⟨hi, hxs⟩) fun i =>
    (hφ.measurableSet i).inter hs

theorem AECover.ae_tendsto_indicator {β : Type*} [Zero β] [TopologicalSpace β] (f : α → β)
    {φ : ι → Set α} (hφ : AECover μ l φ) :
    ∀ᵐ x ∂μ, Tendsto (fun i => (φ i).indicator f x) l (𝓝 <| f x) :=
  hφ.ae_eventually_mem.mono fun _x hx =>
    tendsto_const_nhds.congr' <| hx.mono fun _n hn => (indicator_of_mem hn _).symm

theorem AECover.aemeasurable {β : Type*} [MeasurableSpace β] [l.IsCountablyGenerated] [l.NeBot]
    {f : α → β} {φ : ι → Set α} (hφ : AECover μ l φ)
    (hfm : ∀ i, AEMeasurable f (μ.restrict <| φ i)) : AEMeasurable f μ := by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  have := aemeasurable_iUnion_iff.mpr fun n : ℕ => hfm (u n)
  rwa [Measure.restrict_eq_self_of_ae_mem] at this
  filter_upwards [hφ.ae_eventually_mem] with x hx using
    mem_iUnion.mpr (hu.eventually hx).exists

theorem AECover.aestronglyMeasurable {β : Type*} [TopologicalSpace β] [PseudoMetrizableSpace β]
    [l.IsCountablyGenerated] [l.NeBot] {f : α → β} {φ : ι → Set α} (hφ : AECover μ l φ)
    (hfm : ∀ i, AEStronglyMeasurable f (μ.restrict <| φ i)) : AEStronglyMeasurable f μ := by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  have := aestronglyMeasurable_iUnion_iff.mpr fun n : ℕ => hfm (u n)
  rwa [Measure.restrict_eq_self_of_ae_mem] at this
  filter_upwards [hφ.ae_eventually_mem] with x hx using mem_iUnion.mpr (hu.eventually hx).exists

end AECover

theorem AECover.comp_tendsto {α ι ι' : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    {l' : Filter ι'} {φ : ι → Set α} (hφ : AECover μ l φ) {u : ι' → ι} (hu : Tendsto u l' l) :
    AECover μ l' (φ ∘ u) where
  ae_eventually_mem := hφ.ae_eventually_mem.mono fun _x hx => hu.eventually hx
  measurableSet i := hφ.measurableSet (u i)

section AECoverUnionInterCountable

variable {α ι : Type*} [Countable ι] [MeasurableSpace α] {μ : Measure α}

theorem AECover.biUnion_Iic_aecover [Preorder ι] {φ : ι → Set α} (hφ : AECover μ atTop φ) :
    AECover μ atTop fun n : ι => ⋃ (k) (_h : k ∈ Iic n), φ k :=
  hφ.superset (fun _ ↦ subset_biUnion_of_mem right_mem_Iic) fun _ ↦ .biUnion (to_countable _)
    fun _ _ ↦ (hφ.2 _)

theorem AECover.biInter_Ici_aecover [Preorder ι] {φ : ι → Set α}
    (hφ : AECover μ atTop φ) : AECover μ atTop fun n : ι => ⋂ (k) (_h : k ∈ Ici n), φ k where
  ae_eventually_mem := hφ.ae_eventually_mem.mono fun x h ↦ by
    simpa only [mem_iInter, mem_Ici, eventually_forall_ge_atTop]
  measurableSet _ := .biInter (to_countable _) fun n _ => hφ.measurableSet n

end AECoverUnionInterCountable

section Lintegral

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}

private theorem lintegral_tendsto_of_monotone_of_nat {φ : ℕ → Set α} (hφ : AECover μ atTop φ)
    (hmono : Monotone φ) {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ) :
    Tendsto (fun i => ∫⁻ x in φ i, f x ∂μ) atTop (𝓝 <| ∫⁻ x, f x ∂μ) :=
  let F n := (φ n).indicator f
  have key₁ : ∀ n, AEMeasurable (F n) μ := fun n => hfm.indicator (hφ.measurableSet n)
  have key₂ : ∀ᵐ x : α ∂μ, Monotone fun n => F n x := ae_of_all _ fun x _i _j hij =>
    indicator_le_indicator_of_subset (hmono hij) (fun x => zero_le <| f x) x
  have key₃ : ∀ᵐ x : α ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := hφ.ae_tendsto_indicator f
  (lintegral_tendsto_of_tendsto_of_monotone key₁ key₂ key₃).congr fun n =>
    lintegral_indicator (hφ.measurableSet n) _

theorem AECover.lintegral_tendsto_of_nat {φ : ℕ → Set α} (hφ : AECover μ atTop φ) {f : α → ℝ≥0∞}
    (hfm : AEMeasurable f μ) : Tendsto (∫⁻ x in φ ·, f x ∂μ) atTop (𝓝 <| ∫⁻ x, f x ∂μ) := by
  have lim₁ := lintegral_tendsto_of_monotone_of_nat hφ.biInter_Ici_aecover
    (fun i j hij => biInter_subset_biInter_left (Ici_subset_Ici.mpr hij)) hfm
  have lim₂ := lintegral_tendsto_of_monotone_of_nat hφ.biUnion_Iic_aecover
    (fun i j hij => biUnion_subset_biUnion_left (Iic_subset_Iic.mpr hij)) hfm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le lim₁ lim₂ (fun n ↦ ?_) fun n ↦ ?_
  exacts [lintegral_mono_set (biInter_subset_of_mem left_mem_Ici),
    lintegral_mono_set (subset_biUnion_of_mem right_mem_Iic)]

theorem AECover.lintegral_tendsto_of_countably_generated [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AECover μ l φ) {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ) :
    Tendsto (fun i => ∫⁻ x in φ i, f x ∂μ) l (𝓝 <| ∫⁻ x, f x ∂μ) :=
  tendsto_of_seq_tendsto fun _u hu => (hφ.comp_tendsto hu).lintegral_tendsto_of_nat hfm

theorem AECover.lintegral_eq_of_tendsto [l.NeBot] [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AECover μ l φ) {f : α → ℝ≥0∞} (I : ℝ≥0∞) (hfm : AEMeasurable f μ)
    (htendsto : Tendsto (fun i => ∫⁻ x in φ i, f x ∂μ) l (𝓝 I)) : ∫⁻ x, f x ∂μ = I :=
  tendsto_nhds_unique (hφ.lintegral_tendsto_of_countably_generated hfm) htendsto

theorem AECover.iSup_lintegral_eq_of_countably_generated [Nonempty ι] [l.NeBot]
    [l.IsCountablyGenerated] {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → ℝ≥0∞}
    (hfm : AEMeasurable f μ) : ⨆ i : ι, ∫⁻ x in φ i, f x ∂μ = ∫⁻ x, f x ∂μ := by
  have := hφ.lintegral_tendsto_of_countably_generated hfm
  refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt
    (fun i => lintegral_mono' Measure.restrict_le_self le_rfl) fun w hw => ?_
  exact (this.eventually_const_lt hw).exists

end Lintegral

section Integrable

variable {α ι E : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [NormedAddCommGroup E]

theorem AECover.integrable_of_lintegral_enorm_bounded [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → E} (I : ℝ) (hfm : AEStronglyMeasurable f μ)
    (hbounded : ∀ᶠ i in l, ∫⁻ x in φ i, ‖f x‖ₑ ∂μ ≤ ENNReal.ofReal I) : Integrable f μ := by
  refine ⟨hfm, (le_of_tendsto ?_ hbounded).trans_lt ENNReal.ofReal_lt_top⟩
  exact hφ.lintegral_tendsto_of_countably_generated hfm.enorm

theorem AECover.integrable_of_lintegral_enorm_tendsto [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → E} (I : ℝ) (hfm : AEStronglyMeasurable f μ)
    (htendsto : Tendsto (fun i => ∫⁻ x in φ i, ‖f x‖ₑ ∂μ) l (𝓝 <| .ofReal I)) :
    Integrable f μ := by
  refine hφ.integrable_of_lintegral_enorm_bounded (max 1 (I + 1)) hfm ?_
  refine htendsto.eventually (ge_mem_nhds ?_)
  refine (ENNReal.ofReal_lt_ofReal_iff (lt_max_of_lt_left zero_lt_one)).2 ?_
  exact lt_max_of_lt_right (lt_add_one I)

theorem AECover.integrable_of_lintegral_enorm_bounded' [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → E} (I : ℝ≥0) (hfm : AEStronglyMeasurable f μ)
    (hbounded : ∀ᶠ i in l, ∫⁻ x in φ i, ‖f x‖ₑ ∂μ ≤ I) : Integrable f μ :=
  hφ.integrable_of_lintegral_enorm_bounded I hfm
    (by simpa only [ENNReal.ofReal_coe_nnreal] using hbounded)

theorem AECover.integrable_of_lintegral_enorm_tendsto' [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → E} (I : ℝ≥0) (hfm : AEStronglyMeasurable f μ)
    (htendsto : Tendsto (fun i => ∫⁻ x in φ i, ‖f x‖ₑ ∂μ) l (𝓝 I)) : Integrable f μ :=
  hφ.integrable_of_lintegral_enorm_tendsto I hfm
    (by simpa only [ENNReal.ofReal_coe_nnreal] using htendsto)

theorem AECover.integrable_of_integral_norm_bounded [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → E} (I : ℝ) (hfi : ∀ i, IntegrableOn f (φ i) μ)
    (hbounded : ∀ᶠ i in l, (∫ x in φ i, ‖f x‖ ∂μ) ≤ I) : Integrable f μ := by
  have hfm : AEStronglyMeasurable f μ :=
    hφ.aestronglyMeasurable fun i => (hfi i).aestronglyMeasurable
  refine hφ.integrable_of_lintegral_enorm_bounded I hfm ?_
  conv at hbounded in integral _ _ =>
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => @norm_nonneg E _ (f x))
        hfm.norm.restrict]
  conv at hbounded in ENNReal.ofReal _ =>
    rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
  refine hbounded.mono fun i hi => ?_
  rw [← ENNReal.ofReal_toReal <| ne_top_of_lt <| hasFiniteIntegral_iff_enorm.mp (hfi i).2]
  apply ENNReal.ofReal_le_ofReal hi

theorem AECover.integrable_of_integral_norm_tendsto [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → E} (I : ℝ) (hfi : ∀ i, IntegrableOn f (φ i) μ)
    (htendsto : Tendsto (fun i => ∫ x in φ i, ‖f x‖ ∂μ) l (𝓝 I)) : Integrable f μ :=
  let ⟨I', hI'⟩ := htendsto.isBoundedUnder_le
  hφ.integrable_of_integral_norm_bounded I' hfi hI'

theorem AECover.integrable_of_integral_bounded_of_nonneg_ae [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → ℝ} (I : ℝ) (hfi : ∀ i, IntegrableOn f (φ i) μ)
    (hnng : ∀ᵐ x ∂μ, 0 ≤ f x) (hbounded : ∀ᶠ i in l, (∫ x in φ i, f x ∂μ) ≤ I) : Integrable f μ :=
  hφ.integrable_of_integral_norm_bounded I hfi <| hbounded.mono fun _i hi =>
    (integral_congr_ae <| ae_restrict_of_ae <| hnng.mono fun _ => Real.norm_of_nonneg).le.trans hi

theorem AECover.integrable_of_integral_tendsto_of_nonneg_ae [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → ℝ} (I : ℝ) (hfi : ∀ i, IntegrableOn f (φ i) μ)
    (hnng : ∀ᵐ x ∂μ, 0 ≤ f x) (htendsto : Tendsto (fun i => ∫ x in φ i, f x ∂μ) l (𝓝 I)) :
    Integrable f μ :=
  let ⟨I', hI'⟩ := htendsto.isBoundedUnder_le
  hφ.integrable_of_integral_bounded_of_nonneg_ae I' hfi hnng hI'

end Integrable

section Integral

variable {α ι E : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

theorem AECover.integral_tendsto_of_countably_generated [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AECover μ l φ) {f : α → E} (hfi : Integrable f μ) :
    Tendsto (fun i => ∫ x in φ i, f x ∂μ) l (𝓝 <| ∫ x, f x ∂μ) :=
  suffices h : Tendsto (fun i => ∫ x : α, (φ i).indicator f x ∂μ) l (𝓝 (∫ x : α, f x ∂μ)) from by
    convert h using 2; rw [integral_indicator (hφ.measurableSet _)]
  tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
    (Eventually.of_forall fun i => hfi.aestronglyMeasurable.indicator <| hφ.measurableSet i)
    (Eventually.of_forall fun _ => ae_of_all _ fun _ => norm_indicator_le_norm_self _ _) hfi.norm
    (hφ.ae_tendsto_indicator f)

/-- Slight reformulation of `MeasureTheory.AECover.integral_tendsto_of_countably_generated`. -/
theorem AECover.integral_eq_of_tendsto [l.NeBot] [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AECover μ l φ) {f : α → E} (I : E) (hfi : Integrable f μ)
    (h : Tendsto (fun n => ∫ x in φ n, f x ∂μ) l (𝓝 I)) : ∫ x, f x ∂μ = I :=
  tendsto_nhds_unique (hφ.integral_tendsto_of_countably_generated hfi) h

theorem AECover.integral_eq_of_tendsto_of_nonneg_ae [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → ℝ} (I : ℝ) (hnng : 0 ≤ᵐ[μ] f)
    (hfi : ∀ n, IntegrableOn f (φ n) μ) (htendsto : Tendsto (fun n => ∫ x in φ n, f x ∂μ) l (𝓝 I)) :
    ∫ x, f x ∂μ = I :=
  have hfi' : Integrable f μ := hφ.integrable_of_integral_tendsto_of_nonneg_ae I hfi hnng htendsto
  hφ.integral_eq_of_tendsto I hfi' htendsto

end Integral

section IntegrableOfIntervalIntegral

variable {ι E : Type*} {μ : Measure ℝ} {l : Filter ι} [Filter.NeBot l] [IsCountablyGenerated l]
  [NormedAddCommGroup E] {a b : ι → ℝ} {f : ℝ → E}

theorem integrable_of_intervalIntegral_norm_bounded (I : ℝ)
    (hfi : ∀ i, IntegrableOn f (Ioc (a i) (b i)) μ) (ha : Tendsto a l atBot)
    (hb : Tendsto b l atTop) (h : ∀ᶠ i in l, (∫ x in a i..b i, ‖f x‖ ∂μ) ≤ I) : Integrable f μ := by
  have hφ : AECover μ l _ := aecover_Ioc ha hb
  refine hφ.integrable_of_integral_norm_bounded I hfi (h.mp ?_)
  filter_upwards [ha.eventually (eventually_le_atBot 0),
    hb.eventually (eventually_ge_atTop 0)] with i hai hbi ht
  rwa [← intervalIntegral.integral_of_le (hai.trans hbi)]

/-- If `f` is integrable on intervals `Ioc (a i) (b i)`,
where `a i` tends to -∞ and `b i` tends to ∞, and
`∫ x in a i .. b i, ‖f x‖ ∂μ` converges to `I : ℝ` along a filter `l`,
then `f` is integrable on the interval (-∞, ∞) -/
theorem integrable_of_intervalIntegral_norm_tendsto (I : ℝ)
    (hfi : ∀ i, IntegrableOn f (Ioc (a i) (b i)) μ) (ha : Tendsto a l atBot)
    (hb : Tendsto b l atTop) (h : Tendsto (fun i => ∫ x in a i..b i, ‖f x‖ ∂μ) l (𝓝 I)) :
    Integrable f μ :=
  let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrable_of_intervalIntegral_norm_bounded I' hfi ha hb hI'

theorem integrableOn_Iic_of_intervalIntegral_norm_bounded (I b : ℝ)
    (hfi : ∀ i, IntegrableOn f (Ioc (a i) b) μ) (ha : Tendsto a l atBot)
    (h : ∀ᶠ i in l, (∫ x in a i..b, ‖f x‖ ∂μ) ≤ I) : IntegrableOn f (Iic b) μ := by
  have hφ : AECover (μ.restrict <| Iic b) l _ := aecover_Ioi ha
  have hfi : ∀ i, IntegrableOn f (Ioi (a i)) (μ.restrict <| Iic b) := by
    intro i
    rw [IntegrableOn, Measure.restrict_restrict (hφ.measurableSet i)]
    exact hfi i
  refine hφ.integrable_of_integral_norm_bounded I hfi (h.mp ?_)
  filter_upwards [ha.eventually (eventually_le_atBot b)] with i hai
  rw [intervalIntegral.integral_of_le hai, Measure.restrict_restrict (hφ.measurableSet i)]
  exact id

/-- If `f` is integrable on intervals `Ioc (a i) b`,
where `a i` tends to -∞, and
`∫ x in a i .. b, ‖f x‖ ∂μ` converges to `I : ℝ` along a filter `l`,
then `f` is integrable on the interval (-∞, b) -/
theorem integrableOn_Iic_of_intervalIntegral_norm_tendsto (I b : ℝ)
    (hfi : ∀ i, IntegrableOn f (Ioc (a i) b) μ) (ha : Tendsto a l atBot)
    (h : Tendsto (fun i => ∫ x in a i..b, ‖f x‖ ∂μ) l (𝓝 I)) : IntegrableOn f (Iic b) μ :=
  let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrableOn_Iic_of_intervalIntegral_norm_bounded I' b hfi ha hI'

theorem integrableOn_Ioi_of_intervalIntegral_norm_bounded (I a : ℝ)
    (hfi : ∀ i, IntegrableOn f (Ioc a (b i)) μ) (hb : Tendsto b l atTop)
    (h : ∀ᶠ i in l, (∫ x in a..b i, ‖f x‖ ∂μ) ≤ I) : IntegrableOn f (Ioi a) μ := by
  have hφ : AECover (μ.restrict <| Ioi a) l _ := aecover_Iic hb
  have hfi : ∀ i, IntegrableOn f (Iic (b i)) (μ.restrict <| Ioi a) := by
    intro i
    rw [IntegrableOn, Measure.restrict_restrict (hφ.measurableSet i), inter_comm]
    exact hfi i
  refine hφ.integrable_of_integral_norm_bounded I hfi (h.mp ?_)
  filter_upwards [hb.eventually (eventually_ge_atTop a)] with i hbi
  rw [intervalIntegral.integral_of_le hbi, Measure.restrict_restrict (hφ.measurableSet i),
    inter_comm]
  exact id

/-- If `f` is integrable on intervals `Ioc a (b i)`,
where `b i` tends to ∞, and
`∫ x in a .. b i, ‖f x‖ ∂μ` converges to `I : ℝ` along a filter `l`,
then `f` is integrable on the interval (a, ∞) -/
theorem integrableOn_Ioi_of_intervalIntegral_norm_tendsto (I a : ℝ)
    (hfi : ∀ i, IntegrableOn f (Ioc a (b i)) μ) (hb : Tendsto b l atTop)
    (h : Tendsto (fun i => ∫ x in a..b i, ‖f x‖ ∂μ) l (𝓝 <| I)) : IntegrableOn f (Ioi a) μ :=
  let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrableOn_Ioi_of_intervalIntegral_norm_bounded I' a hfi hb hI'

theorem integrableOn_Ioc_of_intervalIntegral_norm_bounded {I a₀ b₀ : ℝ}
    (hfi : ∀ i, IntegrableOn f <| Ioc (a i) (b i)) (ha : Tendsto a l <| 𝓝 a₀)
    (hb : Tendsto b l <| 𝓝 b₀) (h : ∀ᶠ i in l, (∫ x in Ioc (a i) (b i), ‖f x‖) ≤ I) :
    IntegrableOn f (Ioc a₀ b₀) := by
  refine (aecover_Ioc_of_Ioc ha hb).integrable_of_integral_norm_bounded I
    (fun i => (hfi i).restrict) (h.mono fun i hi ↦ ?_)
  rw [Measure.restrict_restrict measurableSet_Ioc]
  grw [← hi]
  gcongr
  · apply ae_of_all
    simp
  · exact (hfi i).norm
  · exact inter_subset_left

theorem integrableOn_Ioc_of_intervalIntegral_norm_bounded_left {I a₀ b : ℝ}
    (hfi : ∀ i, IntegrableOn f <| Ioc (a i) b) (ha : Tendsto a l <| 𝓝 a₀)
    (h : ∀ᶠ i in l, (∫ x in Ioc (a i) b, ‖f x‖) ≤ I) : IntegrableOn f (Ioc a₀ b) :=
  integrableOn_Ioc_of_intervalIntegral_norm_bounded hfi ha tendsto_const_nhds h

theorem integrableOn_Ioc_of_intervalIntegral_norm_bounded_right {I a b₀ : ℝ}
    (hfi : ∀ i, IntegrableOn f <| Ioc a (b i)) (hb : Tendsto b l <| 𝓝 b₀)
    (h : ∀ᶠ i in l, (∫ x in Ioc a (b i), ‖f x‖) ≤ I) : IntegrableOn f (Ioc a b₀) :=
  integrableOn_Ioc_of_intervalIntegral_norm_bounded hfi tendsto_const_nhds hb h

end IntegrableOfIntervalIntegral

section IntegralOfIntervalIntegral

variable {ι E : Type*} {μ : Measure ℝ} {l : Filter ι} [IsCountablyGenerated l]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ι → ℝ} {f : ℝ → E}

theorem intervalIntegral_tendsto_integral (hfi : Integrable f μ) (ha : Tendsto a l atBot)
    (hb : Tendsto b l atTop) : Tendsto (fun i => ∫ x in a i..b i, f x ∂μ) l (𝓝 <| ∫ x, f x ∂μ) := by
  let φ i := Ioc (a i) (b i)
  have hφ : AECover μ l φ := aecover_Ioc ha hb
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [ha.eventually (eventually_le_atBot 0),
    hb.eventually (eventually_ge_atTop 0)] with i hai hbi
  exact (intervalIntegral.integral_of_le (hai.trans hbi)).symm

theorem intervalIntegral_tendsto_integral_Iic (b : ℝ) (hfi : IntegrableOn f (Iic b) μ)
    (ha : Tendsto a l atBot) :
    Tendsto (fun i => ∫ x in a i..b, f x ∂μ) l (𝓝 <| ∫ x in Iic b, f x ∂μ) := by
  let φ i := Ioi (a i)
  have hφ : AECover (μ.restrict <| Iic b) l φ := aecover_Ioi ha
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [ha.eventually (eventually_le_atBot <| b)] with i hai
  rw [intervalIntegral.integral_of_le hai, Measure.restrict_restrict (hφ.measurableSet i)]
  rfl

theorem intervalIntegral_tendsto_integral_Ioi (a : ℝ) (hfi : IntegrableOn f (Ioi a) μ)
    (hb : Tendsto b l atTop) :
    Tendsto (fun i => ∫ x in a..b i, f x ∂μ) l (𝓝 <| ∫ x in Ioi a, f x ∂μ) := by
  let φ i := Iic (b i)
  have hφ : AECover (μ.restrict <| Ioi a) l φ := aecover_Iic hb
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [hb.eventually (eventually_ge_atTop <| a)] with i hbi
  rw [intervalIntegral.integral_of_le hbi, Measure.restrict_restrict (hφ.measurableSet i),
    inter_comm]
  rfl

end IntegralOfIntervalIntegral

open Real

open scoped Interval

section IoiFTC

variable {E : Type*} {f f' : ℝ → E} {g g' : ℝ → ℝ} {a l : ℝ} {m : E} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- If the derivative of a function defined on the real line is integrable close to `+∞`, then
the function has a limit at `+∞`. -/
theorem tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi [CompleteSpace E]
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Ioi a)) :
    Tendsto f atTop (𝓝 (limUnder atTop f)) := by
  suffices ∃ a, Tendsto f atTop (𝓝 a) from tendsto_nhds_limUnder this
  suffices CauchySeq f from cauchySeq_tendsto_of_complete this
  apply Metric.cauchySeq_iff'.2 (fun ε εpos ↦ ?_)
  have A : ∀ᶠ (n : ℕ) in atTop, ∫ (x : ℝ) in Ici ↑n, ‖f' x‖ < ε := by
    have L : Tendsto (fun (n : ℕ) ↦ ∫ x in Ici (n : ℝ), ‖f' x‖) atTop
        (𝓝 (∫ x in ⋂ (n : ℕ), Ici (n : ℝ), ‖f' x‖)) := by
      apply tendsto_setIntegral_of_antitone (fun n ↦ measurableSet_Ici)
      · intro m n hmn
        exact Ici_subset_Ici.2 (Nat.cast_le.mpr hmn)
      · rcases exists_nat_gt a with ⟨n, hn⟩
        exact ⟨n, IntegrableOn.mono_set f'int.norm (Ici_subset_Ioi.2 hn)⟩
    have B : ⋂ (n : ℕ), Ici (n : ℝ) = ∅ := by
      apply eq_empty_of_forall_notMem (fun x ↦ ?_)
      simpa only [mem_iInter, mem_Ici, not_forall, not_le] using exists_nat_gt x
    simp only [B, Measure.restrict_empty, integral_zero_measure] at L
    exact (tendsto_order.1 L).2 _ εpos
  have B : ∀ᶠ (n : ℕ) in atTop, a < n := by
    rcases exists_nat_gt a with ⟨n, hn⟩
    filter_upwards [Ioi_mem_atTop n] with m (hm : n < m) using hn.trans (Nat.cast_lt.mpr hm)
  rcases (A.and B).exists with ⟨N, hN, h'N⟩
  refine ⟨N, fun x hx ↦ ?_⟩
  calc
  dist (f x) (f ↑N)
    = ‖f x - f N‖ := dist_eq_norm _ _
  _ = ‖∫ t in Ioc ↑N x, f' t‖ := by
      rw [← intervalIntegral.integral_of_le hx, intervalIntegral.integral_eq_sub_of_hasDerivAt]
      · intro y hy
        simp only [hx, uIcc_of_le, mem_Icc] at hy
        exact hderiv _ (h'N.trans_le hy.1)
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
        exact f'int.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi h'N.le))
  _ ≤ ∫ t in Ioc ↑N x, ‖f' t‖ := norm_integral_le_integral_norm fun a ↦ f' a
  _ ≤ ∫ t in Ici ↑N, ‖f' t‖ := by
      apply setIntegral_mono_set
      · apply IntegrableOn.mono_set f'int.norm (Ici_subset_Ioi.2 h'N)
      · filter_upwards with x using norm_nonneg _
      · have : Ioc (↑N) x ⊆ Ici ↑N := Ioc_subset_Ioi_self.trans Ioi_subset_Ici_self
        exact this.eventuallyLE
  _ < ε := hN

open UniformSpace in
/-- If a function and its derivative are integrable on `(a, +∞)`, then the function tends to zero
at `+∞`. -/
theorem tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (f'int : IntegrableOn f' (Ioi a)) (fint : IntegrableOn f (Ioi a)) :
    Tendsto f atTop (𝓝 0) := by
  let F : E →L[ℝ] Completion E := Completion.toComplL
  have Fderiv : ∀ x ∈ Ioi a, HasDerivAt (F ∘ f) (F (f' x)) x :=
    fun x hx ↦ F.hasFDerivAt.comp_hasDerivAt _ (hderiv x hx)
  have Fint : IntegrableOn (F ∘ f) (Ioi a) := by apply F.integrable_comp fint
  have F'int : IntegrableOn (F ∘ f') (Ioi a) := by apply F.integrable_comp f'int
  have A : Tendsto (F ∘ f) atTop (𝓝 (limUnder atTop (F ∘ f))) := by
    apply tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi Fderiv F'int
  have B : limUnder atTop (F ∘ f) = F 0 := by
    have : IntegrableAtFilter (F ∘ f) atTop := by exact ⟨Ioi a, Ioi_mem_atTop _, Fint⟩
    apply IntegrableAtFilter.eq_zero_of_tendsto this ?_ A
    intro s hs
    rcases mem_atTop_sets.1 hs with ⟨b, hb⟩
    rw [← top_le_iff, ← volume_Ici (a := b)]
    exact measure_mono hb
  rwa [B, ← IsEmbedding.tendsto_nhds_iff] at A
  exact (Completion.isUniformEmbedding_coe E).isEmbedding

variable [CompleteSpace E]

/-- **Fundamental theorem of calculus-2**, on semi-infinite intervals `(a, +∞)`.
When a function has a limit at infinity `m`, and its derivative is integrable, then the
integral of the derivative on `(a, +∞)` is `m - f a`. Version assuming differentiability
on `(a, +∞)` and continuity at `a⁺`.

Note that such a function always has a limit at infinity,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`. -/
theorem integral_Ioi_of_hasDerivAt_of_tendsto (hcont : ContinuousWithinAt f (Ici a) a)
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Ioi a))
    (hf : Tendsto f atTop (𝓝 m)) : ∫ x in Ioi a, f' x = m - f a := by
  have hcont : ContinuousOn f (Ici a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi a f'int tendsto_id) ?_
  apply Tendsto.congr' _ (hf.sub_const _)
  filter_upwards [Ioi_mem_atTop a] with x hx
  have h'x : a ≤ id x := le_of_lt hx
  symm
  apply
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h'x (hcont.mono Icc_subset_Ici_self)
      fun y hy => hderiv y hy.1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h'x]
  exact f'int.mono (fun y hy => hy.1) le_rfl

/-- **Fundamental theorem of calculus-2**, on semi-infinite intervals `(a, +∞)`.
When a function has a limit at infinity `m`, and its derivative is integrable, then the
integral of the derivative on `(a, +∞)` is `m - f a`. Version assuming differentiability
on `[a, +∞)`.

Note that such a function always has a limit at infinity,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`. -/
theorem integral_Ioi_of_hasDerivAt_of_tendsto' (hderiv : ∀ x ∈ Ici a, HasDerivAt f (f' x) x)
    (f'int : IntegrableOn f' (Ioi a)) (hf : Tendsto f atTop (𝓝 m)) :
    ∫ x in Ioi a, f' x = m - f a := by
  refine integral_Ioi_of_hasDerivAt_of_tendsto ?_ (fun x hx => hderiv x hx.out.le)
    f'int hf
  exact (hderiv a left_mem_Ici).continuousAt.continuousWithinAt

/-- A special case of `integral_Ioi_of_hasDerivAt_of_tendsto` where we assume that `f` is C^1 with
compact support. -/
theorem _root_.HasCompactSupport.integral_Ioi_deriv_eq (hf : ContDiff ℝ 1 f)
    (h2f : HasCompactSupport f) (b : ℝ) : ∫ x in Ioi b, deriv f x = - f b := by
  have := fun x (_ : x ∈ Ioi b) ↦ hf.differentiable le_rfl x |>.hasDerivAt
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hf.continuous.continuousWithinAt this, zero_sub]
  · refine hf.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport h2f.deriv |>.integrableOn
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at h2f
  exact h2f.filter_mono _root_.atTop_le_cocompact |>.tendsto

/-- When a function has a limit at infinity, and its derivative is nonnegative, then the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `(a, +∞)` and continuity at `a⁺`. -/
theorem integrableOn_Ioi_deriv_of_nonneg (hcont : ContinuousWithinAt g (Ici a) a)
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x) (g'pos : ∀ x ∈ Ioi a, 0 ≤ g' x)
    (hg : Tendsto g atTop (𝓝 l)) : IntegrableOn g' (Ioi a) := by
  have hcont : ContinuousOn g (Ici a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto (l - g a) a (fun x => ?_) tendsto_id ?_
  · exact intervalIntegral.integrableOn_deriv_of_nonneg (hcont.mono Icc_subset_Ici_self)
      (fun y hy => hderiv y hy.1) fun y hy => g'pos y hy.1
  apply Tendsto.congr' _ (hg.sub_const _)
  filter_upwards [Ioi_mem_atTop a] with x hx
  have h'x : a ≤ id x := le_of_lt hx
  calc
    g x - g a = ∫ y in a..id x, g' y := by
      symm
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h'x
        (hcont.mono Icc_subset_Ici_self) fun y hy => hderiv y hy.1
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h'x]
      exact intervalIntegral.integrableOn_deriv_of_nonneg (hcont.mono Icc_subset_Ici_self)
        (fun y hy => hderiv y hy.1) fun y hy => g'pos y hy.1
    _ = ∫ y in a..id x, ‖g' y‖ := by
      simp_rw [intervalIntegral.integral_of_le h'x]
      refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
      dsimp
      rw [abs_of_nonneg]
      exact g'pos _ hy.1

/-- When a function has a limit at infinity, and its derivative is nonnegative, then the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `[a, +∞)`. -/
theorem integrableOn_Ioi_deriv_of_nonneg' (hderiv : ∀ x ∈ Ici a, HasDerivAt g (g' x) x)
    (g'pos : ∀ x ∈ Ioi a, 0 ≤ g' x) (hg : Tendsto g atTop (𝓝 l)) : IntegrableOn g' (Ioi a) := by
  refine integrableOn_Ioi_deriv_of_nonneg ?_ (fun x hx => hderiv x hx.out.le) g'pos hg
  exact (hderiv a left_mem_Ici).continuousAt.continuousWithinAt

/-- When a function has a limit at infinity `l`, and its derivative is nonnegative, then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is integrable, see
`integrable_on_Ioi_deriv_of_nonneg`). Version assuming differentiability on `(a, +∞)` and
continuity at `a⁺`. -/
theorem integral_Ioi_of_hasDerivAt_of_nonneg (hcont : ContinuousWithinAt g (Ici a) a)
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x) (g'pos : ∀ x ∈ Ioi a, 0 ≤ g' x)
    (hg : Tendsto g atTop (𝓝 l)) : ∫ x in Ioi a, g' x = l - g a :=
  integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_Ioi_deriv_of_nonneg hcont hderiv g'pos hg) hg

/-- When a function has a limit at infinity `l`, and its derivative is nonnegative, then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is integrable, see
`integrable_on_Ioi_deriv_of_nonneg'`). Version assuming differentiability on `[a, +∞)`. -/
theorem integral_Ioi_of_hasDerivAt_of_nonneg' (hderiv : ∀ x ∈ Ici a, HasDerivAt g (g' x) x)
    (g'pos : ∀ x ∈ Ioi a, 0 ≤ g' x) (hg : Tendsto g atTop (𝓝 l)) : ∫ x in Ioi a, g' x = l - g a :=
  integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_Ioi_deriv_of_nonneg' hderiv g'pos hg)
    hg

/-- When a function has a limit at infinity, and its derivative is nonpositive, then the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `(a, +∞)` and continuity at `a⁺`. -/
theorem integrableOn_Ioi_deriv_of_nonpos (hcont : ContinuousWithinAt g (Ici a) a)
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x) (g'neg : ∀ x ∈ Ioi a, g' x ≤ 0)
    (hg : Tendsto g atTop (𝓝 l)) : IntegrableOn g' (Ioi a) := by
  apply integrable_neg_iff.1
  exact integrableOn_Ioi_deriv_of_nonneg hcont.neg (fun x hx => (hderiv x hx).neg)
    (fun x hx => neg_nonneg_of_nonpos (g'neg x hx)) hg.neg

/-- When a function has a limit at infinity, and its derivative is nonpositive, then the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `[a, +∞)`. -/
theorem integrableOn_Ioi_deriv_of_nonpos' (hderiv : ∀ x ∈ Ici a, HasDerivAt g (g' x) x)
    (g'neg : ∀ x ∈ Ioi a, g' x ≤ 0) (hg : Tendsto g atTop (𝓝 l)) : IntegrableOn g' (Ioi a) := by
  refine integrableOn_Ioi_deriv_of_nonpos ?_ (fun x hx ↦ hderiv x hx.out.le) g'neg hg
  exact (hderiv a left_mem_Ici).continuousAt.continuousWithinAt

/-- When a function has a limit at infinity `l`, and its derivative is nonpositive, then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is integrable, see
`integrable_on_Ioi_deriv_of_nonneg`). Version assuming differentiability on `(a, +∞)` and
continuity at `a⁺`. -/
theorem integral_Ioi_of_hasDerivAt_of_nonpos (hcont : ContinuousWithinAt g (Ici a) a)
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x) (g'neg : ∀ x ∈ Ioi a, g' x ≤ 0)
    (hg : Tendsto g atTop (𝓝 l)) : ∫ x in Ioi a, g' x = l - g a :=
  integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_Ioi_deriv_of_nonpos hcont hderiv g'neg hg) hg

/-- When a function has a limit at infinity `l`, and its derivative is nonpositive, then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is integrable, see
`integrable_on_Ioi_deriv_of_nonneg'`). Version assuming differentiability on `[a, +∞)`. -/
theorem integral_Ioi_of_hasDerivAt_of_nonpos' (hderiv : ∀ x ∈ Ici a, HasDerivAt g (g' x) x)
    (g'neg : ∀ x ∈ Ioi a, g' x ≤ 0) (hg : Tendsto g atTop (𝓝 l)) : ∫ x in Ioi a, g' x = l - g a :=
  integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_Ioi_deriv_of_nonpos' hderiv g'neg hg)
    hg

end IoiFTC

section IicFTC

variable {E : Type*} {f f' : ℝ → E} {a : ℝ} {m : E} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- If the derivative of a function defined on the real line is integrable close to `-∞`, then
the function has a limit at `-∞`. -/
theorem tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic [CompleteSpace E]
    (hderiv : ∀ x ∈ Iic a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a)) :
    Tendsto f atBot (𝓝 (limUnder atBot f)) := by
  suffices ∃ a, Tendsto f atBot (𝓝 a) from tendsto_nhds_limUnder this
  let g := f ∘ (fun x ↦ -x)
  have hdg : ∀ x ∈ Ioi (-a), HasDerivAt g (-f' (-x)) x := by
    intro x hx
    have : -x ∈ Iic a := by simp only [mem_Iic, mem_Ioi, neg_le] at *; exact hx.le
    simpa using HasDerivAt.scomp x (hderiv (-x) this) (hasDerivAt_neg' x)
  have L : Tendsto g atTop (𝓝 (limUnder atTop g)) := by
    apply tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi hdg
    exact ((MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _)
      (Homeomorph.neg ℝ).measurableEmbedding).2 f'int.neg).mono_set (by simp)
  refine ⟨limUnder atTop g, ?_⟩
  have : Tendsto (fun x ↦ g (-x)) atBot (𝓝 (limUnder atTop g)) := L.comp tendsto_neg_atBot_atTop
  simpa [g] using this

open UniformSpace in
/-- If a function and its derivative are integrable on `(-∞, a]`, then the function tends to zero
at `-∞`. -/
theorem tendsto_zero_of_hasDerivAt_of_integrableOn_Iic
    (hderiv : ∀ x ∈ Iic a, HasDerivAt f (f' x) x)
    (f'int : IntegrableOn f' (Iic a)) (fint : IntegrableOn f (Iic a)) :
    Tendsto f atBot (𝓝 0) := by
  let F : E →L[ℝ] Completion E := Completion.toComplL
  have Fderiv : ∀ x ∈ Iic a, HasDerivAt (F ∘ f) (F (f' x)) x :=
    fun x hx ↦ F.hasFDerivAt.comp_hasDerivAt _ (hderiv x hx)
  have Fint : IntegrableOn (F ∘ f) (Iic a) := by apply F.integrable_comp fint
  have F'int : IntegrableOn (F ∘ f') (Iic a) := by apply F.integrable_comp f'int
  have A : Tendsto (F ∘ f) atBot (𝓝 (limUnder atBot (F ∘ f))) := by
    apply tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic Fderiv F'int
  have B : limUnder atBot (F ∘ f) = F 0 := by
    have : IntegrableAtFilter (F ∘ f) atBot := by exact ⟨Iic a, Iic_mem_atBot _, Fint⟩
    apply IntegrableAtFilter.eq_zero_of_tendsto this ?_ A
    intro s hs
    rcases mem_atBot_sets.1 hs with ⟨b, hb⟩
    apply le_antisymm (le_top)
    rw [← volume_Iic (a := b)]
    exact measure_mono hb
  rwa [B, ← IsEmbedding.tendsto_nhds_iff] at A
  exact (Completion.isUniformEmbedding_coe E).isEmbedding

variable [CompleteSpace E]

/-- **Fundamental theorem of calculus-2**, on semi-infinite intervals `(-∞, a)`.
When a function has a limit `m` at `-∞`, and its derivative is integrable, then the
integral of the derivative on `(-∞, a)` is `f a - m`. Version assuming differentiability
on `(-∞, a)` and continuity at `a⁻`.

Note that such a function always has a limit at minus infinity,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic`. -/
theorem integral_Iic_of_hasDerivAt_of_tendsto (hcont : ContinuousWithinAt f (Iic a) a)
    (hderiv : ∀ x ∈ Iio a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a))
    (hf : Tendsto f atBot (𝓝 m)) : ∫ x in Iic a, f' x = f a - m := by
  have hcont : ContinuousOn f (Iic a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Iic a f'int tendsto_id) ?_
  apply Tendsto.congr' _ (hf.const_sub _)
  filter_upwards [Iic_mem_atBot a] with x hx
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
    (hcont.mono Icc_subset_Iic_self) fun y hy => hderiv y hy.2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  exact f'int.mono (fun y hy => hy.2) le_rfl

/-- **Fundamental theorem of calculus-2**, on semi-infinite intervals `(-∞, a)`.
When a function has a limit `m` at `-∞`, and its derivative is integrable, then the
integral of the derivative on `(-∞, a)` is `f a - m`. Version assuming differentiability
on `(-∞, a]`.

Note that such a function always has a limit at minus infinity,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic`. -/
theorem integral_Iic_of_hasDerivAt_of_tendsto'
    (hderiv : ∀ x ∈ Iic a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a))
    (hf : Tendsto f atBot (𝓝 m)) : ∫ x in Iic a, f' x = f a - m := by
  refine integral_Iic_of_hasDerivAt_of_tendsto ?_ (fun x hx => hderiv x hx.out.le)
    f'int hf
  exact (hderiv a right_mem_Iic).continuousAt.continuousWithinAt

/-- A special case of `integral_Iic_of_hasDerivAt_of_tendsto` where we assume that `f` is C^1 with
compact support. -/
theorem _root_.HasCompactSupport.integral_Iic_deriv_eq (hf : ContDiff ℝ 1 f)
    (h2f : HasCompactSupport f) (b : ℝ) : ∫ x in Iic b, deriv f x = f b := by
  have := fun x (_ : x ∈ Iio b) ↦ hf.differentiable le_rfl x |>.hasDerivAt
  rw [integral_Iic_of_hasDerivAt_of_tendsto hf.continuous.continuousWithinAt this, sub_zero]
  · refine hf.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport h2f.deriv |>.integrableOn
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at h2f
  exact h2f.filter_mono _root_.atBot_le_cocompact |>.tendsto

open UniformSpace in
lemma _root_.HasCompactSupport.enorm_le_lintegral_Ici_deriv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContDiff ℝ 1 f) (h'f : HasCompactSupport f) (x : ℝ) :
    ‖f x‖ₑ ≤ ∫⁻ y in Iic x, ‖deriv f y‖ₑ := by
  let I : F →L[ℝ] Completion F := Completion.toComplL
  let f' : ℝ → Completion F := I ∘ f
  have hf' : ContDiff ℝ 1 f' := hf.continuousLinearMap_comp I
  have h'f' : HasCompactSupport f' := h'f.comp_left rfl
  have : ‖f' x‖ₑ ≤ ∫⁻ y in Iic x, ‖deriv f' y‖ₑ := by
    rw [← HasCompactSupport.integral_Iic_deriv_eq hf' h'f' x]
    exact enorm_integral_le_lintegral_enorm _
  convert this with y
  · simp [f', I, Completion.enorm_coe]
  · rw [fderiv_comp_deriv _ I.differentiableAt (hf.differentiable le_rfl _)]
    simp only [ContinuousLinearMap.fderiv]
    simp [I]

end IicFTC

section UnivFTC

variable {E : Type*} {f f' : ℝ → E} {m n : E} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- **Fundamental theorem of calculus-2**, on the whole real line
When a function has a limit `m` at `-∞` and `n` at `+∞`, and its derivative is integrable, then the
integral of the derivative is `n - m`.

Note that such a function always has a limit at `-∞` and `+∞`,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic` and
`tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`. -/
theorem integral_of_hasDerivAt_of_tendsto [CompleteSpace E]
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hf' : Integrable f')
    (hbot : Tendsto f atBot (𝓝 m)) (htop : Tendsto f atTop (𝓝 n)) : ∫ x, f' x = n - m := by
  rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := 0),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hf'.integrableOn hf'.integrableOn,
    integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ ↦ hderiv x) hf'.integrableOn hbot,
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ ↦ hderiv x) hf'.integrableOn htop]
  abel

/-- If a function and its derivative are integrable on the real line, then the integral of the
derivative is zero. -/
theorem integral_eq_zero_of_hasDerivAt_of_integrable
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hf' : Integrable f') (hf : Integrable f) :
    ∫ x, f' x = 0 := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  have A : Tendsto f atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun x _hx ↦ hderiv x)
      hf'.integrableOn hf.integrableOn
  have B : Tendsto f atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun x _hx ↦ hderiv x)
      hf'.integrableOn hf.integrableOn
  simpa using integral_of_hasDerivAt_of_tendsto hderiv hf' A B

end UnivFTC

section IoiChangeVariables

open Real

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Change-of-variables formula for `Ioi` integrals of vector-valued functions, proved by taking
limits from the result for finite intervals. -/
theorem integral_comp_smul_deriv_Ioi {f f' : ℝ → ℝ} {g : ℝ → E} {a : ℝ}
    (hf : ContinuousOn f <| Ici a) (hft : Tendsto f atTop atTop)
    (hff' : ∀ x ∈ Ioi a, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hg_cont : ContinuousOn g <| f '' Ioi a) (hg1 : IntegrableOn g <| f '' Ici a)
    (hg2 : IntegrableOn (fun x => f' x • (g ∘ f) x) (Ici a)) :
    (∫ x in Ioi a, f' x • (g ∘ f) x) = ∫ u in Ioi (f a), g u := by
  have eq : ∀ b : ℝ, a < b → (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := fun b hb ↦ by
    have i1 : Ioo (min a b) (max a b) ⊆ Ioi a := by
      rw [min_eq_left hb.le]
      exact Ioo_subset_Ioi_self
    have i2 : [[a, b]] ⊆ Ici a := by rw [uIcc_of_le hb.le]; exact Icc_subset_Ici_self
    refine
      intervalIntegral.integral_comp_smul_deriv''' (hf.mono i2)
        (fun x hx => hff' x <| mem_of_mem_of_subset hx i1) (hg_cont.mono <| image_mono ?_)
        (hg1.mono_set <| image_mono ?_) (hg2.mono_set i2) <;> assumption
  rw [integrableOn_Ici_iff_integrableOn_Ioi] at hg2
  have t2 := intervalIntegral_tendsto_integral_Ioi _ hg2 tendsto_id
  have : Ioi (f a) ⊆ f '' Ici a :=
    Ioi_subset_Ici_self.trans <|
      IsPreconnected.intermediate_value_Ici isPreconnected_Ici left_mem_Ici
        (le_principal_iff.mpr <| Ici_mem_atTop _) hf hft
  have t1 := (intervalIntegral_tendsto_integral_Ioi _ (hg1.mono_set this) tendsto_id).comp hft
  exact tendsto_nhds_unique (Tendsto.congr' (eventuallyEq_of_mem (Ioi_mem_atTop a) eq) t2) t1

/-- Change-of-variables formula for `Ioi` integrals of scalar-valued functions -/
theorem integral_comp_mul_deriv_Ioi {f f' : ℝ → ℝ} {g : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousOn f <| Ici a) (hft : Tendsto f atTop atTop)
    (hff' : ∀ x ∈ Ioi a, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hg_cont : ContinuousOn g <| f '' Ioi a) (hg1 : IntegrableOn g <| f '' Ici a)
    (hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici a)) :
    (∫ x in Ioi a, (g ∘ f) x * f' x) = ∫ u in Ioi (f a), g u := by
  have hg2' : IntegrableOn (fun x => f' x • (g ∘ f) x) (Ici a) := by simpa [mul_comm] using hg2
  simpa [mul_comm] using integral_comp_smul_deriv_Ioi hf hft hff' hg_cont hg1 hg2'

/-- Substitution `y = x ^ p` in integrals over `Ioi 0` -/
theorem integral_comp_rpow_Ioi (g : ℝ → E) {p : ℝ} (hp : p ≠ 0) :
    (∫ x in Ioi 0, (|p| * x ^ (p - 1)) • g (x ^ p)) = ∫ y in Ioi 0, g y := by
  let S := Ioi (0 : ℝ)
  have a1 : ∀ x : ℝ, x ∈ S → HasDerivWithinAt (fun t : ℝ => t ^ p) (p * x ^ (p - 1)) S x :=
    fun x hx => (hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hx).ne')).hasDerivWithinAt
  have a2 : InjOn (fun x : ℝ => x ^ p) S := by
    rcases lt_or_gt_of_ne hp with (h | h)
    · apply StrictAntiOn.injOn
      intro x hx y hy hxy
      rw [← inv_lt_inv₀ (rpow_pos_of_pos hx p) (rpow_pos_of_pos hy p), ← rpow_neg (le_of_lt hx),
        ← rpow_neg (le_of_lt hy)]
      exact rpow_lt_rpow (le_of_lt hx) hxy (neg_pos.mpr h)
    exact StrictMonoOn.injOn fun x hx y _ hxy => rpow_lt_rpow (mem_Ioi.mp hx).le hxy h
  have a3 : (fun t : ℝ => t ^ p) '' S = S := by
    ext1 x; rw [mem_image]; constructor
    · rintro ⟨y, hy, rfl⟩; exact rpow_pos_of_pos hy p
    · intro hx; refine ⟨x ^ (1 / p), rpow_pos_of_pos hx _, ?_⟩
      rw [← rpow_mul (le_of_lt hx), one_div_mul_cancel hp, rpow_one]
  have := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi a1 a2 g
  rw [a3] at this; rw [this]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx; dsimp only
  rw [abs_mul, abs_of_nonneg (rpow_nonneg (le_of_lt hx) _)]

theorem integral_comp_rpow_Ioi_of_pos {g : ℝ → E} {p : ℝ} (hp : 0 < p) :
    (∫ x in Ioi 0, (p * x ^ (p - 1)) • g (x ^ p)) = ∫ y in Ioi 0, g y := by
  convert integral_comp_rpow_Ioi g hp.ne'
  rw [abs_of_nonneg hp.le]

theorem integral_comp_mul_left_Ioi (g : ℝ → E) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ x in Ioi a, g (b * x)) = b⁻¹ • ∫ x in Ioi (b * a), g x := by
  have : ∀ c : ℝ, MeasurableSet (Ioi c) := fun c => measurableSet_Ioi
  rw [← integral_indicator (this a), ← integral_indicator (this (b * a)),
    ← abs_of_pos (inv_pos.mpr hb), ← Measure.integral_comp_mul_left]
  congr
  ext1 x
  rw [← indicator_comp_right, preimage_const_mul_Ioi _ hb, mul_div_cancel_left₀ _ hb.ne',
    Function.comp_def]

theorem integral_comp_mul_right_Ioi (g : ℝ → E) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ x in Ioi a, g (x * b)) = b⁻¹ • ∫ x in Ioi (a * b), g x := by
  simpa only [mul_comm] using integral_comp_mul_left_Ioi g a hb

end IoiChangeVariables

section IoiIntegrability

open Real

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E]

/-- The substitution `y = x ^ p` in integrals over `Ioi 0` preserves integrability. -/
theorem integrableOn_Ioi_comp_rpow_iff [NormedSpace ℝ E] (f : ℝ → E) {p : ℝ} (hp : p ≠ 0) :
    IntegrableOn (fun x => (|p| * x ^ (p - 1)) • f (x ^ p)) (Ioi 0) ↔ IntegrableOn f (Ioi 0) := by
  let S := Ioi (0 : ℝ)
  have a1 : ∀ x : ℝ, x ∈ S → HasDerivWithinAt (fun t : ℝ => t ^ p) (p * x ^ (p - 1)) S x :=
    fun x hx => (hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hx).ne')).hasDerivWithinAt
  have a2 : InjOn (fun x : ℝ => x ^ p) S := by
    rcases lt_or_gt_of_ne hp with (h | h)
    · apply StrictAntiOn.injOn
      intro x hx y hy hxy
      rw [← inv_lt_inv₀ (rpow_pos_of_pos hx p) (rpow_pos_of_pos hy p), ← rpow_neg (le_of_lt hx), ←
        rpow_neg (le_of_lt hy)]
      exact rpow_lt_rpow (le_of_lt hx) hxy (neg_pos.mpr h)
    exact StrictMonoOn.injOn fun x hx y _hy hxy => rpow_lt_rpow (mem_Ioi.mp hx).le hxy h
  have a3 : (fun t : ℝ => t ^ p) '' S = S := by
    ext1 x; rw [mem_image]; constructor
    · rintro ⟨y, hy, rfl⟩; exact rpow_pos_of_pos hy p
    · intro hx; refine ⟨x ^ (1 / p), rpow_pos_of_pos hx _, ?_⟩
      rw [← rpow_mul (le_of_lt hx), one_div_mul_cancel hp, rpow_one]
  have := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi a1 a2 f
  rw [a3] at this
  rw [this]
  refine integrableOn_congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp_rw [abs_mul, abs_of_nonneg (rpow_nonneg (le_of_lt hx) _)]

/-- The substitution `y = x ^ p` in integrals over `Ioi 0` preserves integrability (version
without `|p|` factor) -/
theorem integrableOn_Ioi_comp_rpow_iff' [NormedSpace ℝ E] (f : ℝ → E) {p : ℝ} (hp : p ≠ 0) :
    IntegrableOn (fun x => x ^ (p - 1) • f (x ^ p)) (Ioi 0) ↔ IntegrableOn f (Ioi 0) := by
  simpa only [← integrableOn_Ioi_comp_rpow_iff f hp, mul_smul] using
    (integrable_smul_iff (abs_pos.mpr hp).ne' _).symm

theorem integrableOn_Ioi_comp_mul_left_iff (f : ℝ → E) (c : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x => f (a * x)) (Ioi c) ↔ IntegrableOn f (Ioi <| a * c) := by
  rw [← integrable_indicator_iff (measurableSet_Ioi : MeasurableSet <| Ioi c)]
  rw [← integrable_indicator_iff (measurableSet_Ioi : MeasurableSet <| Ioi <| a * c)]
  convert integrable_comp_mul_left_iff ((Ioi (a * c)).indicator f) ha.ne' using 2
  ext1 x
  rw [← indicator_comp_right, preimage_const_mul_Ioi _ ha, mul_comm a c,
    mul_div_cancel_right₀ _ ha.ne', Function.comp_def]

theorem integrableOn_Ioi_comp_mul_right_iff (f : ℝ → E) (c : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x => f (x * a)) (Ioi c) ↔ IntegrableOn f (Ioi <| c * a) := by
  simpa only [mul_comm, mul_zero] using integrableOn_Ioi_comp_mul_left_iff f c ha

end IoiIntegrability

/-!
## Integration by parts
-/

section IntegrationByPartsBilinear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {L : E →L[ℝ] F →L[ℝ] G} {u : ℝ → E} {v : ℝ → F} {u' : ℝ → E} {v' : ℝ → F}
  {m n : G}

theorem integral_bilinear_hasDerivAt_eq_sub [CompleteSpace G]
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (huv : Integrable (fun x ↦ L (u x) (v' x) + L (u' x) (v x)))
    (h_bot : Tendsto (fun x ↦ L (u x) (v x)) atBot (𝓝 m))
    (h_top : Tendsto (fun x ↦ L (u x) (v x)) atTop (𝓝 n)) :
    ∫ (x : ℝ), L (u x) (v' x) + L (u' x) (v x) = n - m :=
  integral_of_hasDerivAt_of_tendsto (fun x ↦ L.hasDerivAt_of_bilinear (hu x) (hv x))
    huv h_bot h_top

/-- **Integration by parts on (-∞, ∞).**
With respect to a general bilinear form. For the specific case of multiplication, see
`integral_mul_deriv_eq_deriv_mul`. -/
theorem integral_bilinear_hasDerivAt_right_eq_sub [CompleteSpace G]
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (huv' : Integrable (fun x ↦ L (u x) (v' x))) (hu'v : Integrable (fun x ↦ L (u' x) (v x)))
    (h_bot : Tendsto (fun x ↦ L (u x) (v x)) atBot (𝓝 m))
    (h_top : Tendsto (fun x ↦ L (u x) (v x)) atTop (𝓝 n)) :
    ∫ (x : ℝ), L (u x) (v' x) = n - m - ∫ (x : ℝ), L (u' x) (v x) := by
  rw [eq_sub_iff_add_eq, ← integral_add huv' hu'v]
  exact integral_bilinear_hasDerivAt_eq_sub hu hv (huv'.add hu'v) h_bot h_top

/-- **Integration by parts on (-∞, ∞).**
With respect to a general bilinear form, assuming moreover that the total function is integrable.
-/
theorem integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (huv' : Integrable (fun x ↦ L (u x) (v' x))) (hu'v : Integrable (fun x ↦ L (u' x) (v x)))
    (huv : Integrable (fun x ↦ L (u x) (v x))) :
    ∫ (x : ℝ), L (u x) (v' x) = - ∫ (x : ℝ), L (u' x) (v x) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have I : Tendsto (fun x ↦ L (u x) (v x)) atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
      (fun x _hx ↦ L.hasDerivAt_of_bilinear (hu x) (hv x))
      (huv'.add hu'v).integrableOn huv.integrableOn
  have J : Tendsto (fun x ↦ L (u x) (v x)) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
      (fun x _hx ↦ L.hasDerivAt_of_bilinear (hu x) (hv x))
      (huv'.add hu'v).integrableOn huv.integrableOn
  simp [integral_bilinear_hasDerivAt_right_eq_sub hu hv huv' hu'v I J]

end IntegrationByPartsBilinear

section IntegrationByPartsAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  {a : ℝ} {a' b' : A} {u : ℝ → A} {v : ℝ → A} {u' : ℝ → A} {v' : ℝ → A}

/-- For finite intervals, see: `intervalIntegral.integral_deriv_mul_eq_sub`. -/
theorem integral_deriv_mul_eq_sub [CompleteSpace A]
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (huv : Integrable (u' * v + u * v'))
    (h_bot : Tendsto (u * v) atBot (𝓝 a')) (h_top : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ (x : ℝ), u' x * v x + u x * v' x = b' - a' :=
  integral_of_hasDerivAt_of_tendsto (fun x ↦ (hu x).mul (hv x)) huv h_bot h_top

/-- **Integration by parts on (-∞, ∞).**
For finite intervals, see: `intervalIntegral.integral_mul_deriv_eq_deriv_mul`. -/
theorem integral_mul_deriv_eq_deriv_mul [CompleteSpace A]
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v))
    (h_bot : Tendsto (u * v) atBot (𝓝 a')) (h_top : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ (x : ℝ), u x * v' x = b' - a' - ∫ (x : ℝ), u' x * v x :=
  integral_bilinear_hasDerivAt_right_eq_sub (L := ContinuousLinearMap.mul ℝ A)
    hu hv huv' hu'v h_bot h_top

/-- **Integration by parts on (-∞, ∞).**
Version assuming that the total function is integrable -/
theorem integral_mul_deriv_eq_deriv_mul_of_integrable
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v)) (huv : Integrable (u * v)) :
    ∫ (x : ℝ), u x * v' x = - ∫ (x : ℝ), u' x * v x :=
  integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable (L := ContinuousLinearMap.mul ℝ A)
    hu hv huv' hu'v huv

variable [CompleteSpace A]

-- TODO: also apply `Tendsto _ (𝓝[>] a) (𝓝 a')` generalization to
-- `integral_Ioi_of_hasDerivAt_of_tendsto` and `integral_Iic_of_hasDerivAt_of_tendsto`
/-- For finite intervals, see: `intervalIntegral.integral_deriv_mul_eq_sub`. -/
theorem integral_Ioi_deriv_mul_eq_sub
    (hu : ∀ x ∈ Ioi a, HasDerivAt u (u' x) x) (hv : ∀ x ∈ Ioi a, HasDerivAt v (v' x) x)
    (huv : IntegrableOn (u' * v + u * v') (Ioi a))
    (h_zero : Tendsto (u * v) (𝓝[>] a) (𝓝 a')) (h_infty : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ (x : ℝ) in Ioi a, u' x * v x + u x * v' x = b' - a' := by
  rw [← Ici_diff_left] at h_zero
  let f := Function.update (u * v) a a'
  have hderiv : ∀ x ∈ Ioi a, HasDerivAt f (u' x * v x + u x * v' x) x := by
    intro x (hx : a < x)
    apply ((hu x hx).mul (hv x hx)).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx.ne.symm] with y hy
    exact Function.update_of_ne hy a' (u * v)
  have htendsto : Tendsto f atTop (𝓝 b') := by
    apply h_infty.congr'
    filter_upwards [eventually_ne_atTop a] with x hx
    exact (Function.update_of_ne hx a' (u * v)).symm
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto
    (continuousWithinAt_update_same.mpr h_zero) hderiv huv htendsto

/-- **Integration by parts on (a, ∞).**
For finite intervals, see: `intervalIntegral.integral_mul_deriv_eq_deriv_mul`. -/
theorem integral_Ioi_mul_deriv_eq_deriv_mul
    (hu : ∀ x ∈ Ioi a, HasDerivAt u (u' x) x) (hv : ∀ x ∈ Ioi a, HasDerivAt v (v' x) x)
    (huv' : IntegrableOn (u * v') (Ioi a)) (hu'v : IntegrableOn (u' * v) (Ioi a))
    (h_zero : Tendsto (u * v) (𝓝[>] a) (𝓝 a')) (h_infty : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ (x : ℝ) in Ioi a, u x * v' x = b' - a' - ∫ (x : ℝ) in Ioi a, u' x * v x := by
  rw [Pi.mul_def] at huv' hu'v
  rw [eq_sub_iff_add_eq, ← integral_add huv' hu'v]
  simpa only [add_comm] using integral_Ioi_deriv_mul_eq_sub hu hv (hu'v.add huv') h_zero h_infty

/-- For finite intervals, see: `intervalIntegral.integral_deriv_mul_eq_sub`. -/
theorem integral_Iic_deriv_mul_eq_sub
    (hu : ∀ x ∈ Iio a, HasDerivAt u (u' x) x) (hv : ∀ x ∈ Iio a, HasDerivAt v (v' x) x)
    (huv : IntegrableOn (u' * v + u * v') (Iic a))
    (h_zero : Tendsto (u * v) (𝓝[<] a) (𝓝 a')) (h_infty : Tendsto (u * v) atBot (𝓝 b')) :
    ∫ (x : ℝ) in Iic a, u' x * v x + u x * v' x = a' - b' := by
  rw [← Iic_diff_right] at h_zero
  let f := Function.update (u * v) a a'
  have hderiv : ∀ x ∈ Iio a, HasDerivAt f (u' x * v x + u x * v' x) x := by
    intro x hx
    apply ((hu x hx).mul (hv x hx)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with x (hx : x < a)
    exact Function.update_of_ne (ne_of_lt hx) a' (u * v)
  have htendsto : Tendsto f atBot (𝓝 b') := by
    apply h_infty.congr'
    filter_upwards [Iio_mem_atBot a] with x (hx : x < a)
    exact (Function.update_of_ne (ne_of_lt hx) a' (u * v)).symm
  simpa using integral_Iic_of_hasDerivAt_of_tendsto
    (continuousWithinAt_update_same.mpr h_zero) hderiv huv htendsto

/-- **Integration by parts on (∞, a].**
For finite intervals, see: `intervalIntegral.integral_mul_deriv_eq_deriv_mul`. -/
theorem integral_Iic_mul_deriv_eq_deriv_mul
    (hu : ∀ x ∈ Iio a, HasDerivAt u (u' x) x) (hv : ∀ x ∈ Iio a, HasDerivAt v (v' x) x)
    (huv' : IntegrableOn (u * v') (Iic a)) (hu'v : IntegrableOn (u' * v) (Iic a))
    (h_zero : Tendsto (u * v) (𝓝[<] a) (𝓝 a')) (h_infty : Tendsto (u * v) atBot (𝓝 b')) :
    ∫ (x : ℝ) in Iic a, u x * v' x = a' - b' - ∫ (x : ℝ) in Iic a, u' x * v x := by
  rw [Pi.mul_def] at huv' hu'v
  rw [eq_sub_iff_add_eq, ← integral_add huv' hu'v]
  simpa only [add_comm] using integral_Iic_deriv_mul_eq_sub hu hv (hu'v.add huv') h_zero h_infty

end IntegrationByPartsAlgebra

end MeasureTheory
