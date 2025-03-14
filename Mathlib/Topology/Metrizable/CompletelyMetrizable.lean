import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity

open Filter Function Topology

variable {X Y : Type*}

namespace TopologicalSpace

/-- A topological space is completely metrizable if there exists a metric space structure
compatible with the topology which makes the space complete.
To endow such a space with a compatible distance, use
`letI : MetricSpace X := TopologicalSpace.completelyMetrizableSpaceMetric X`. -/
class CompletelyMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_metric : ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
    @CompleteSpace X m.toUniformSpace

instance (priority := 100) _root_.MetricSpace.toCompletelyMetrizableSpace
    [m : MetricSpace X] [CompleteSpace X] : CompletelyMetrizableSpace X :=
  ⟨⟨m, rfl, ‹_›⟩⟩

/-- A convenience class, for a completely metrizable space endowed with a complete metric.
No instance of this class should be registered: It should be used as
`letI := upgradeCompletelyMetrizable X` to endow a completely metrizable
space with a complete metric. -/
class UpgradedCompletelyMetrizableSpace (X : Type*) extends MetricSpace X, CompleteSpace X

open scoped Uniformity in
instance (priority := 100) CompletelyMetrizableSpace.of_completeSpace_metrizable [UniformSpace X]
    [CompleteSpace X] [(𝓤 X).IsCountablyGenerated] [T0Space X] :
    CompletelyMetrizableSpace X where
  exists_metric := ⟨UniformSpace.metricSpace X, rfl, ‹_›⟩

/-- Construct on a completely metrizable space a metric (compatible with the topology)
which is complete. -/
noncomputable
def completelyMetrizableMetric (X : Type*) [TopologicalSpace X] [h : CompletelyMetrizableSpace X] :
    MetricSpace X :=
  h.exists_metric.choose.replaceTopology h.exists_metric.choose_spec.1.symm

theorem complete_completelyMetrizableMetric (X : Type*) [ht : TopologicalSpace X]
    [h : CompletelyMetrizableSpace X] :
    @CompleteSpace X (completelyMetrizableMetric X).toUniformSpace := by
  convert h.exists_metric.choose_spec.2
  exact MetricSpace.replaceTopology_eq _ _

/-- This definition endows a completely metrizable space with a complete metric. Use it as:
`letI := upgradeCompletelyMetrizable X`. -/
noncomputable
def upgradeCompletelyMetrizable (X : Type*) [TopologicalSpace X] [CompletelyMetrizableSpace X] :
    UpgradedCompletelyMetrizableSpace X :=
  letI := completelyMetrizableMetric X
  { complete_completelyMetrizableMetric X with }

namespace CompletelyMetrizableSpace

instance (priority := 100) instMetrizableSpace (X : Type*) [TopologicalSpace X]
    [CompletelyMetrizableSpace X] : MetrizableSpace X := by
  letI := upgradeCompletelyMetrizable X
  infer_instance

/-- A countable product of completely metrizable spaces is completely metrizable. -/
instance pi_countable {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, CompletelyMetrizableSpace (X i)] : CompletelyMetrizableSpace (Π i, X i) := by
  letI := fun i ↦ upgradeCompletelyMetrizable (X i)
  infer_instance

/-- A disjoint union of completely metrizable spaces is completely metrizable. -/
instance sigma {ι : Type*} {X : ι → Type*} [∀ n, TopologicalSpace (X n)]
    [∀ n, CompletelyMetrizableSpace (X n)] : CompletelyMetrizableSpace (Σn, X n) :=
  letI := fun n ↦ upgradeCompletelyMetrizable (X n)
  letI : MetricSpace (Σ n, X n) := Metric.Sigma.metricSpace
  haveI : CompleteSpace (Σn, X n) := Metric.Sigma.completeSpace
  inferInstance

/-- The product of two completely metrizable spaces is completely metrizable. -/
instance prod [TopologicalSpace X] [CompletelyMetrizableSpace X] [TopologicalSpace Y]
    [CompletelyMetrizableSpace Y] : CompletelyMetrizableSpace (X × Y) :=
  letI := upgradeCompletelyMetrizable X
  letI := upgradeCompletelyMetrizable Y
  inferInstance

/-- The disjoint union of two completely metrizable spaces is completely metrizable. -/
instance sum [TopologicalSpace X] [CompletelyMetrizableSpace X] [TopologicalSpace Y]
    [CompletelyMetrizableSpace Y] : CompletelyMetrizableSpace (X ⊕ Y) :=
  letI := upgradeCompletelyMetrizable X
  letI := upgradeCompletelyMetrizable Y
  inferInstance

/-- Given a closed embedding into a completely metrizable space,
the source space is also completely metrizable. -/
theorem _root_.Topology.IsClosedEmbedding.CompletelyMetrizableSpace [TopologicalSpace X]
    [TopologicalSpace Y] [CompletelyMetrizableSpace Y] {f : X → Y} (hf : IsClosedEmbedding f) :
    CompletelyMetrizableSpace X := by
  letI := upgradeCompletelyMetrizable Y
  letI : MetricSpace X := hf.isEmbedding.comapMetricSpace f
  have : CompleteSpace X := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

/-- Any discrete space is completely metrizable. -/
instance (priority := 50) discrete [TopologicalSpace X] [DiscreteTopology X] :
    CompletelyMetrizableSpace X := by
  classical
  let m : MetricSpace X :=
    { dist x y := if x = y then 0 else 1
      dist_self x := by simp
      dist_comm x y := by
        obtain h | h := eq_or_ne x y
        · simp [h]
        · simp [h, h.symm]
      dist_triangle x y z := by
        by_cases x = y <;> by_cases x = z <;> by_cases y = z <;> simp_all
      eq_of_dist_eq_zero := by
        contrapose!
        simp }
  refine ⟨m, ?_, ?_⟩
  · rw [DiscreteTopology.eq_bot (α := X)]
    apply eq_bot_of_singletons_open
    intro x
    convert @Metric.isOpen_ball _ _ x 1
    ext y
    simp only [Set.mem_singleton_iff, Metric.mem_ball]; constructor
    · intro h
      simp [h]
    · intro h
      by_contra
      change (if y = x then 0 else 1) < 1 at h
      simp_all
  · apply Metric.complete_of_cauchySeq_tendsto
    intro u hu
    rw [Metric.cauchySeq_iff'] at hu
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, u n = u N := by
      obtain ⟨N, hN⟩ := hu 1 (by norm_num)
      refine ⟨N, fun n hn ↦ ?_⟩
      specialize hN n hn
      by_contra
      change (if u n = u N then 0 else 1) < 1 at hN
      simp_all
    refine ⟨u N, ?_⟩
    exact @tendsto_atTop_of_eventually_const X (u N) UniformSpace.toTopologicalSpace _ _ _ _ hN

/-- Pulling back a completely metrizable topology under an equiv gives again a completely metrizable topology. -/
theorem _root_.Equiv.CompletelyMetrizableSpace_induced [t : TopologicalSpace Y] [CompletelyMetrizableSpace Y] (f : X ≃ Y) :
    @CompletelyMetrizableSpace X (t.induced f) :=
  letI : TopologicalSpace X := t.induced f
  (f.toHomeomorphOfIsInducing ⟨rfl⟩).isClosedEmbedding.CompletelyMetrizableSpace

/-- A closed subset of a completely metrizable space is also completely metrizable. -/
theorem _root_.IsClosed.CompletelyMetrizableSpace [TopologicalSpace X] [CompletelyMetrizableSpace X] {s : Set X}
    (hs : IsClosed s) : CompletelyMetrizableSpace s :=
  hs.isClosedEmbedding_subtypeVal.CompletelyMetrizableSpace

instance instCompletelyMetrizableSpaceUniv [TopologicalSpace X] [CompletelyMetrizableSpace X] :
    CompletelyMetrizableSpace (univ : Set X) :=
  isClosed_univ.CompletelyMetrizableSpace
