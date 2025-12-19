/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.UniformSpace.Pi

/-!
# Metrizable Spaces

In this file we define metrizable topological spaces, i.e., topological spaces for which there
exists a metric space structure that generates the same topology.
We define it without any reference to metric spaces in order to avoid importing the real numbers.
For the proof that metrizable spaces admit a compatible metric,
see `Mathlib/Topology/Metrizable/Uniformity.lean`.
-/

-- don't import the real numbers
assert_not_exists AddMonoidWithOne

@[expose] public section

open Filter Set Topology Uniformity

namespace TopologicalSpace

variable {ι X Y : Type*} {A : ι → Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
  [∀ i, TopologicalSpace (A i)]

/-- A topological space is *pseudometrizable* if there exists a pseudometric space structure
compatible with the topology. To minimize imports, we implement this class in terms of the
existence of a countably generated uniformity inducing the topology, which is mathematically
equivalent.
To endow such a space with a compatible uniformity, use
`letI : UniformSpace X := TopologicalSpace.pseudoMetrizableSpaceUniformity X`.
To endow such a space with a compatible distance, use
`letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X`. -/
class PseudoMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_countably_generated :
    ∃ u : UniformSpace X, u.toTopologicalSpace = t ∧ (uniformity X).IsCountablyGenerated

/-- A uniform space with countably generated `𝓤 X` is pseudometrizable. -/
instance (priority := 100) _root_.UniformSpace.pseudoMetrizableSpace {X : Type*}
    [u : UniformSpace X] [hu : IsCountablyGenerated (uniformity X)] : PseudoMetrizableSpace X :=
  ⟨⟨u, rfl, hu⟩⟩

/-- Construct on a pseudometrizable space a countably generated uniformity
compatible with the topology. Use `pseudoMetrizableSpaceUniformity_countably_generated` for a proof
that this uniformity is countably generated. -/
-- see note [reducible non-instances]
noncomputable abbrev pseudoMetrizableSpaceUniformity (X : Type*) [TopologicalSpace X]
    [h : PseudoMetrizableSpace X] : UniformSpace X :=
  h.exists_countably_generated.choose.replaceTopology
    h.exists_countably_generated.choose_spec.1.symm

example {X : Type*} [t : TopologicalSpace X] [PseudoMetrizableSpace X] :
    (pseudoMetrizableSpaceUniformity X).toTopologicalSpace = t := by
  with_reducible_and_instances rfl

/-- The uniformity coming from `pseudoMetrizableSpaceUniformity` is countably generated.. -/
theorem pseudoMetrizableSpaceUniformity_countably_generated
    (X : Type*) [TopologicalSpace X] [h : PseudoMetrizableSpace X] :
    𝓤[pseudoMetrizableSpaceUniformity X].IsCountablyGenerated :=
  h.exists_countably_generated.choose_spec.2

instance pseudoMetrizableSpace_prod [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y] :
    PseudoMetrizableSpace (X × Y) :=
  let : UniformSpace X := pseudoMetrizableSpaceUniformity X
  have : (uniformity X).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated X
  let : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
  have : (uniformity Y).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated Y
  inferInstance

/-- Given an inducing map of a topological space into a pseudometrizable space, the source space
is also pseudometrizable. -/
theorem _root_.Topology.IsInducing.pseudoMetrizableSpace [PseudoMetrizableSpace Y] {f : X → Y}
    (hf : IsInducing f) : PseudoMetrizableSpace X :=
  let u : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
  have : (uniformity Y).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated Y
  ⟨⟨u.comap f, u.toTopologicalSpace_comap.trans hf.eq_induced.symm,
    Filter.comap.isCountablyGenerated (uniformity Y) (Prod.map f f)⟩⟩

/-- Every pseudo-metrizable space is first countable. -/
instance (priority := 100) PseudoMetrizableSpace.firstCountableTopology
    [h : PseudoMetrizableSpace X] : FirstCountableTopology X :=
  let : UniformSpace X := pseudoMetrizableSpaceUniformity X
  have : (uniformity X).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated X
  inferInstance

instance PseudoMetrizableSpace.subtype [PseudoMetrizableSpace X] (s : Set X) :
    PseudoMetrizableSpace s :=
  IsInducing.subtypeVal.pseudoMetrizableSpace

instance pseudoMetrizableSpace_pi [∀ i, PseudoMetrizableSpace (A i)] :
    PseudoMetrizableSpace (∀ i, A i) :=
  let := fun i => pseudoMetrizableSpaceUniformity (A i)
  have := fun i => pseudoMetrizableSpaceUniformity_countably_generated (A i)
  inferInstance

instance PseudoMetrizableSpace.regularSpace [PseudoMetrizableSpace X] : RegularSpace X :=
  let := pseudoMetrizableSpaceUniformity X
  inferInstance

/-- A topological space is metrizable if there exists a metric space structure compatible with the
topology. To minimize imports, we implement this class in terms of the existence of a
countably generated uniformity inducing the topology, which is mathematically
equivalent.
To endow such a space with a compatible uniformity, use
`letI : UniformSpace X := TopologicalSpace.pseudoMetrizableSpaceUniformity X`.
To endow such a space with a compatible distance, use
`letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X`. -/
class MetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop extends
    PseudoMetrizableSpace X, T0Space X

-- See note [lower instance priority]
attribute [instance 100] MetrizableSpace.toT0Space
attribute [instance 100] MetrizableSpace.toPseudoMetrizableSpace

instance (priority := 100) PseudoMetrizableSpace.toMetrizableSpace
    [T0Space X] [h : PseudoMetrizableSpace X] : MetrizableSpace X where

instance (priority := 100) t2Space_of_metrizableSpace [MetrizableSpace X] : T2Space X :=
  letI : UniformSpace X := pseudoMetrizableSpaceUniformity X
  inferInstance

instance metrizableSpace_prod [MetrizableSpace X] [MetrizableSpace Y] :
    MetrizableSpace (X × Y) where

/-- Given an embedding of a topological space into a metrizable space, the source space is also
metrizable. -/
theorem _root_.Topology.IsEmbedding.metrizableSpace [MetrizableSpace Y] {f : X → Y}
    (hf : IsEmbedding f) : MetrizableSpace X where
  toPseudoMetrizableSpace := hf.toIsInducing.pseudoMetrizableSpace
  toT0Space := hf.t0Space

instance MetrizableSpace.subtype [MetrizableSpace X] (s : Set X) : MetrizableSpace s :=
  IsEmbedding.subtypeVal.metrizableSpace

instance metrizableSpace_pi [∀ i, MetrizableSpace (A i)] : MetrizableSpace (∀ i, A i) where

theorem IsSeparable.secondCountableTopology [PseudoMetrizableSpace X] {s : Set X}
    (hs : IsSeparable s) : SecondCountableTopology s :=
  let ⟨u, hu, hs⟩ := hs
  have := hu.to_subtype
  have : SeparableSpace (closure u) :=
    ⟨Set.range (u.inclusion subset_closure), Set.countable_range (u.inclusion subset_closure),
      Subtype.dense_iff.2 <| by rw [← Set.range_comp, Set.val_comp_inclusion, Subtype.range_coe]⟩
  let := pseudoMetrizableSpaceUniformity (closure u)
  have := pseudoMetrizableSpaceUniformity_countably_generated (closure u)
  have := UniformSpace.secondCountable_of_separable (closure u)
  (Topology.IsEmbedding.inclusion hs).secondCountableTopology

instance (X : Type*) [TopologicalSpace X] [LindelofSpace X] [PseudoMetrizableSpace X] :
    SecondCountableTopology X := by
  let := pseudoMetrizableSpaceUniformity X
  have := pseudoMetrizableSpaceUniformity_countably_generated X
  suffices _ : SeparableSpace X from UniformSpace.secondCountable_of_separable X
  obtain ⟨V, hVb, hVs⟩ := UniformSpace.has_seq_basis X
  choose U hUc hUu using fun n =>
    LindelofSpace.elim_nhds_subcover (fun x => UniformSpace.ball x (V n))
      (fun x => UniformSpace.ball_mem_nhds x (hVb.mem n))
  refine ⟨Set.iUnion U, Set.countable_iUnion hUc, fun x => ?_⟩
  rw [mem_closure_iff_frequently, nhds_eq_comap_uniformity, frequently_comap, hVb.frequently_iff]
  intro n _
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (Set.eq_univ_iff_forall.1 (hUu n) x)
  rw [UniformSpace.ball_eq_of_symmetry] at hx
  exact ⟨(x, i), hx, i, rfl, Set.mem_iUnion_of_mem n hi⟩

instance (priority := 100) DiscreteTopology.metrizableSpace [DiscreteTopology X] :
    MetrizableSpace X where
  exists_countably_generated :=
    ⟨⊥, DiscreteTopology.eq_bot.symm, Filter.isCountablyGenerated_principal SetRel.id⟩

end TopologicalSpace
