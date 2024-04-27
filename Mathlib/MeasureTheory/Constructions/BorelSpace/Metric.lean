/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

#align_import measure_theory.constructions.borel_space.basic from "leanprover-community/mathlib"@"9f55d0d4363ae59948c33864cbc52e0b12e0e8ce"

/-!
# Borel sigma algebras on (pseudo-)metric spaces

## Main definitions

## Main statements

-/

open Set Filter MeasureTheory MeasurableSpace TopologicalSpace

open scoped Classical BigOperators Topology NNReal ENNReal MeasureTheory

universe u v w x y

variable {α β γ δ : Type*} {ι : Sort y} {s t u : Set α}

section PseudoMetricSpace

variable [PseudoMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
variable [MeasurableSpace β] {x : α} {ε : ℝ}

open Metric

@[measurability]
theorem measurableSet_ball : MeasurableSet (Metric.ball x ε) :=
  Metric.isOpen_ball.measurableSet
#align measurable_set_ball measurableSet_ball

@[measurability]
theorem measurableSet_closedBall : MeasurableSet (Metric.closedBall x ε) :=
  Metric.isClosed_ball.measurableSet
#align measurable_set_closed_ball measurableSet_closedBall

@[measurability]
theorem measurable_infDist {s : Set α} : Measurable fun x => infDist x s :=
  (continuous_infDist_pt s).measurable
#align measurable_inf_dist measurable_infDist

@[measurability]
theorem Measurable.infDist {f : β → α} (hf : Measurable f) {s : Set α} :
    Measurable fun x => infDist (f x) s :=
  measurable_infDist.comp hf
#align measurable.inf_dist Measurable.infDist

@[measurability]
theorem measurable_infNndist {s : Set α} : Measurable fun x => infNndist x s :=
  (continuous_infNndist_pt s).measurable
#align measurable_inf_nndist measurable_infNndist

@[measurability]
theorem Measurable.infNndist {f : β → α} (hf : Measurable f) {s : Set α} :
    Measurable fun x => infNndist (f x) s :=
  measurable_infNndist.comp hf
#align measurable.inf_nndist Measurable.infNndist

section

variable [SecondCountableTopology α]

@[measurability]
theorem measurable_dist : Measurable fun p : α × α => dist p.1 p.2 :=
  continuous_dist.measurable
#align measurable_dist measurable_dist

@[measurability]
theorem Measurable.dist {f g : β → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => dist (f b) (g b) :=
  (@continuous_dist α _).measurable2 hf hg
#align measurable.dist Measurable.dist

@[measurability]
theorem measurable_nndist : Measurable fun p : α × α => nndist p.1 p.2 :=
  continuous_nndist.measurable
#align measurable_nndist measurable_nndist

@[measurability]
theorem Measurable.nndist {f g : β → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => nndist (f b) (g b) :=
  (@continuous_nndist α _).measurable2 hf hg
#align measurable.nndist Measurable.nndist

end

end PseudoMetricSpace

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
variable [MeasurableSpace β] {x : α} {ε : ℝ≥0∞}

open EMetric

@[measurability]
theorem measurableSet_eball : MeasurableSet (EMetric.ball x ε) :=
  EMetric.isOpen_ball.measurableSet
#align measurable_set_eball measurableSet_eball

@[measurability]
theorem measurable_edist_right : Measurable (edist x) :=
  (continuous_const.edist continuous_id).measurable
#align measurable_edist_right measurable_edist_right

@[measurability]
theorem measurable_edist_left : Measurable fun y => edist y x :=
  (continuous_id.edist continuous_const).measurable
#align measurable_edist_left measurable_edist_left

@[measurability]
theorem measurable_infEdist {s : Set α} : Measurable fun x => infEdist x s :=
  continuous_infEdist.measurable
#align measurable_inf_edist measurable_infEdist

@[measurability]
theorem Measurable.infEdist {f : β → α} (hf : Measurable f) {s : Set α} :
    Measurable fun x => infEdist (f x) s :=
  measurable_infEdist.comp hf
#align measurable.inf_edist Measurable.infEdist

open Metric EMetric

/-- If a set has a closed thickening with finite measure, then the measure of its `r`-closed
thickenings converges to the measure of its closure as `r` tends to `0`. -/
theorem tendsto_measure_cthickening {μ : Measure α} {s : Set α}
    (hs : ∃ R > 0, μ (cthickening R s) ≠ ∞) :
    Tendsto (fun r => μ (cthickening r s)) (𝓝 0) (𝓝 (μ (closure s))) := by
  have A : Tendsto (fun r => μ (cthickening r s)) (𝓝[Ioi 0] 0) (𝓝 (μ (closure s))) := by
    rw [closure_eq_iInter_cthickening]
    exact
      tendsto_measure_biInter_gt (fun r _ => isClosed_cthickening.measurableSet)
        (fun i j _ ij => cthickening_mono ij _) hs
  have B : Tendsto (fun r => μ (cthickening r s)) (𝓝[Iic 0] 0) (𝓝 (μ (closure s))) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin (α := ℝ)] with _ hr
    rw [cthickening_of_nonpos hr]
  convert B.sup A
  exact (nhds_left_sup_nhds_right' 0).symm
#align tendsto_measure_cthickening tendsto_measure_cthickening

/-- If a closed set has a closed thickening with finite measure, then the measure of its closed
`r`-thickenings converge to its measure as `r` tends to `0`. -/
theorem tendsto_measure_cthickening_of_isClosed {μ : Measure α} {s : Set α}
    (hs : ∃ R > 0, μ (cthickening R s) ≠ ∞) (h's : IsClosed s) :
    Tendsto (fun r => μ (cthickening r s)) (𝓝 0) (𝓝 (μ s)) := by
  convert tendsto_measure_cthickening hs
  exact h's.closure_eq.symm
#align tendsto_measure_cthickening_of_is_closed tendsto_measure_cthickening_of_isClosed

/-- If a set has a thickening with finite measure, then the measures of its `r`-thickenings
converge to the measure of its closure as `r > 0` tends to `0`. -/
theorem tendsto_measure_thickening {μ : Measure α} {s : Set α}
    (hs : ∃ R > 0, μ (thickening R s) ≠ ∞) :
    Tendsto (fun r => μ (thickening r s)) (𝓝[>] 0) (𝓝 (μ (closure s))) := by
  rw [closure_eq_iInter_thickening]
  exact tendsto_measure_biInter_gt (fun r _ => isOpen_thickening.measurableSet)
      (fun i j _ ij => thickening_mono ij _) hs

/-- If a closed set has a thickening with finite measure, then the measure of its
`r`-thickenings converge to its measure as `r > 0` tends to `0`. -/
theorem tendsto_measure_thickening_of_isClosed {μ : Measure α} {s : Set α}
    (hs : ∃ R > 0, μ (thickening R s) ≠ ∞) (h's : IsClosed s) :
    Tendsto (fun r => μ (thickening r s)) (𝓝[>] 0) (𝓝 (μ s)) := by
  convert tendsto_measure_thickening hs
  exact h's.closure_eq.symm

variable [SecondCountableTopology α]

@[measurability]
theorem measurable_edist : Measurable fun p : α × α => edist p.1 p.2 :=
  continuous_edist.measurable
#align measurable_edist measurable_edist

@[measurability]
theorem Measurable.edist {f g : β → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => edist (f b) (g b) :=
  (@continuous_edist α _).measurable2 hf hg
#align measurable.edist Measurable.edist

@[measurability]
theorem AEMeasurable.edist {f g : β → α} {μ : Measure β} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun a => edist (f a) (g a)) μ :=
  (@continuous_edist α _).aemeasurable2 hf hg
#align ae_measurable.edist AEMeasurable.edist

end PseudoEMetricSpace

/-- Given a compact set in a proper space, the measure of its `r`-closed thickenings converges to
its measure as `r` tends to `0`. -/
theorem tendsto_measure_cthickening_of_isCompact [MetricSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [ProperSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {s : Set α} (hs : IsCompact s) :
    Tendsto (fun r => μ (Metric.cthickening r s)) (𝓝 0) (𝓝 (μ s)) :=
  tendsto_measure_cthickening_of_isClosed
    ⟨1, zero_lt_one, hs.isBounded.cthickening.measure_lt_top.ne⟩ hs.isClosed
#align tendsto_measure_cthickening_of_is_compact tendsto_measure_cthickening_of_isCompact

/-- If a measurable space is countably generated and separates points, it arises as
the borel sets of some second countable t4 topology (i.e. a separable metrizable one). -/
theorem exists_borelSpace_of_countablyGenerated_of_separatesPoints (α : Type*)
    [m : MeasurableSpace α] [CountablyGenerated α] [SeparatesPoints α] :
    ∃ τ : TopologicalSpace α, SecondCountableTopology α ∧ T4Space α ∧ BorelSpace α := by
  rcases measurableEquiv_nat_bool_of_countablyGenerated α with ⟨s, ⟨f⟩⟩
  letI := induced f inferInstance
  let F := f.toEquiv.toHomeomorphOfInducing $ inducing_induced _
  exact ⟨inferInstance, F.secondCountableTopology, F.symm.t4Space,
    MeasurableEmbedding.borelSpace f.measurableEmbedding F.inducing⟩

/-- If a measurable space on `α` is countably generated and separates points, there is some
second countable t4 topology on `α` (i.e. a separable metrizable one) for which every
open set is measurable. -/
theorem exists_opensMeasurableSpace_of_hasCountableSeparatingOn (α : Type*)
    [m : MeasurableSpace α] [HasCountableSeparatingOn α MeasurableSet univ] :
    ∃ τ : TopologicalSpace α, SecondCountableTopology α ∧ T4Space α ∧ OpensMeasurableSpace α := by
  rcases exists_countablyGenerated_le_of_hasCountableSeparatingOn α with ⟨m', _, _, m'le⟩
  rcases exists_borelSpace_of_countablyGenerated_of_separatesPoints (m := m') with ⟨τ, _, _, τm'⟩
  exact ⟨τ, ‹_›, ‹_›, @OpensMeasurableSpace.mk _ _ m (τm'.measurable_eq.symm.le.trans m'le)⟩
