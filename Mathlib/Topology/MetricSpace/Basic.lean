/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Defs

/-!
# Basic properties of metric spaces, and instances.

-/

open Set Filter Bornology Topology
open scoped NNReal Uniformity

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}
variable [PseudoMetricSpace α]
variable {γ : Type w} [MetricSpace γ]

namespace Metric

variable {x : γ} {s : Set γ}

-- see Note [lower instance priority]
instance (priority := 100) _root_.MetricSpace.instT0Space : T0Space γ where
  t0 _ _ h := eq_of_dist_eq_zero <| Metric.inseparable_iff.1 h

/-- A map between metric spaces is a uniform embedding if and only if the distance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
theorem isUniformEmbedding_iff' [PseudoMetricSpace β] {f : γ → β} :
    IsUniformEmbedding f ↔
      (∀ ε > 0, ∃ δ > 0, ∀ {a b : γ}, dist a b < δ → dist (f a) (f b) < ε) ∧
        ∀ δ > 0, ∃ ε > 0, ∀ {a b : γ}, dist (f a) (f b) < ε → dist a b < δ := by
  rw [isUniformEmbedding_iff_isUniformInducing, isUniformInducing_iff, uniformContinuous_iff]

/-- If a `PseudoMetricSpace` is a T₀ space, then it is a `MetricSpace`. -/
abbrev _root_.MetricSpace.ofT0PseudoMetricSpace (α : Type*) [PseudoMetricSpace α] [T0Space α] :
    MetricSpace α where
  toPseudoMetricSpace := ‹_›
  eq_of_dist_eq_zero hdist := (Metric.inseparable_iff.2 hdist).eq

-- see Note [lower instance priority]
/-- A metric space induces an emetric space -/
instance (priority := 100) _root_.MetricSpace.toEMetricSpace : EMetricSpace γ :=
  .ofT0PseudoEMetricSpace γ

theorem isClosed_of_pairwise_le_dist {s : Set γ} {ε : ℝ} (hε : 0 < ε)
    (hs : s.Pairwise fun x y => ε ≤ dist x y) : IsClosed s :=
  isClosed_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hs

theorem isClosedEmbedding_of_pairwise_le_dist {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    {ε : ℝ} (hε : 0 < ε) {f : α → γ} (hf : Pairwise fun x y => ε ≤ dist (f x) (f y)) :
    IsClosedEmbedding f :=
  isClosedEmbedding_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hf

/-- If `f : β → α` sends any two distinct points to points at distance at least `ε > 0`, then
`f` is a uniform embedding with respect to the discrete uniformity on `β`. -/
theorem isUniformEmbedding_bot_of_pairwise_le_dist {β : Type*} {ε : ℝ} (hε : 0 < ε) {f : β → α}
    (hf : Pairwise fun x y => ε ≤ dist (f x) (f y)) :
    @IsUniformEmbedding _ _ ⊥ (by infer_instance) f :=
  isUniformEmbedding_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hf

end Metric

/-- One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the metric space and the emetric space. In this definition, the distance
is given separately, to be able to prescribe some expression which is not defeq to the push-forward
of the edistance to reals. -/
abbrev EMetricSpace.toMetricSpaceOfDist {α : Type u} [EMetricSpace α] (dist : α → α → ℝ)
    (edist_ne_top : ∀ x y : α, edist x y ≠ ⊤) (h : ∀ x y, dist x y = ENNReal.toReal (edist x y)) :
    MetricSpace α :=
  @MetricSpace.ofT0PseudoMetricSpace _
    (PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist edist_ne_top h) _

/-- One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the metric space and the emetric space. -/
def EMetricSpace.toMetricSpace {α : Type u} [EMetricSpace α] (h : ∀ x y : α, edist x y ≠ ⊤) :
    MetricSpace α :=
  EMetricSpace.toMetricSpaceOfDist (fun x y => ENNReal.toReal (edist x y)) h fun _ _ => rfl

/-- Metric space structure pulled back by an injective function. Injectivity is necessary to
ensure that `dist x y = 0` only if `x = y`. -/
abbrev MetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : MetricSpace β) :
    MetricSpace γ :=
  { PseudoMetricSpace.induced f m.toPseudoMetricSpace with
    eq_of_dist_eq_zero := fun h => hf (dist_eq_zero.1 h) }

/-- Pull back a metric space structure by a uniform embedding. This is a version of
`MetricSpace.induced` useful in case if the domain already has a `UniformSpace` structure. -/
abbrev IsUniformEmbedding.comapMetricSpace {α β} [UniformSpace α] [m : MetricSpace β] (f : α → β)
    (h : IsUniformEmbedding f) : MetricSpace α :=
  .replaceUniformity (.induced f h.injective m) h.comap_uniformity.symm

/-- Pull back a metric space structure by an embedding. This is a version of
`MetricSpace.induced` useful in case if the domain already has a `TopologicalSpace` structure. -/
abbrev Topology.IsEmbedding.comapMetricSpace {α β} [TopologicalSpace α] [m : MetricSpace β]
    (f : α → β) (h : IsEmbedding f) : MetricSpace α :=
  .replaceTopology (.induced f h.injective m) h.eq_induced

@[deprecated (since := "2024-10-26")]
alias Embedding.comapMetricSpace := IsEmbedding.comapMetricSpace

instance Subtype.metricSpace {α : Type*} {p : α → Prop} [MetricSpace α] :
    MetricSpace (Subtype p) :=
  .induced Subtype.val Subtype.coe_injective ‹_›

@[to_additive]
instance MulOpposite.instMetricSpace {α : Type*} [MetricSpace α] : MetricSpace αᵐᵒᵖ :=
  MetricSpace.induced MulOpposite.unop MulOpposite.unop_injective ‹_›

section Real

/-- Instantiate the reals as a metric space. -/
instance Real.metricSpace : MetricSpace ℝ := .ofT0PseudoMetricSpace ℝ

end Real

section NNReal

instance : MetricSpace ℝ≥0 :=
  Subtype.metricSpace

end NNReal

instance [MetricSpace β] : MetricSpace (ULift β) :=
  MetricSpace.induced ULift.down ULift.down_injective ‹_›

section Prod

instance Prod.metricSpaceMax [MetricSpace β] : MetricSpace (γ × β) :=
  .ofT0PseudoMetricSpace _

end Prod

section Pi

open Finset

variable {π : β → Type*} [Fintype β] [∀ b, MetricSpace (π b)]

/-- A finite product of metric spaces is a metric space, with the sup distance. -/
instance metricSpacePi : MetricSpace (∀ b, π b) := .ofT0PseudoMetricSpace _

end Pi

namespace Metric

section SecondCountable

open TopologicalSpace

-- TODO: use `Countable` instead of `Encodable`
/-- A metric space is second countable if one can reconstruct up to any `ε>0` any element of the
space from countably many data. -/
theorem secondCountable_of_countable_discretization {α : Type u} [PseudoMetricSpace α]
    (H : ∀ ε > (0 : ℝ), ∃ (β : Type*) (_ : Encodable β) (F : α → β),
      ∀ x y, F x = F y → dist x y ≤ ε) :
    SecondCountableTopology α := by
  refine secondCountable_of_almost_dense_set fun ε ε0 => ?_
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩
  let Finv := rangeSplitting F
  refine ⟨range Finv, ⟨countable_range _, fun x => ?_⟩⟩
  let x' := Finv ⟨F x, mem_range_self _⟩
  have : F x' = F x := apply_rangeSplitting F _
  exact ⟨x', mem_range_self _, hF _ _ this.symm⟩

end SecondCountable

end Metric

section EqRel

-- TODO: add `dist_congr` similar to `edist_congr`?
instance SeparationQuotient.instDist {α : Type u} [PseudoMetricSpace α] :
    Dist (SeparationQuotient α) where
  dist := lift₂ dist fun x y x' y' hx hy ↦ by rw [dist_edist, dist_edist, ← edist_mk x,
    ← edist_mk x', mk_eq_mk.2 hx, mk_eq_mk.2 hy]

theorem SeparationQuotient.dist_mk {α : Type u} [PseudoMetricSpace α] (p q : α) :
    dist (mk p) (mk q) = dist p q :=
  rfl

instance SeparationQuotient.instMetricSpace {α : Type u} [PseudoMetricSpace α] :
    MetricSpace (SeparationQuotient α) :=
  EMetricSpace.toMetricSpaceOfDist dist (surjective_mk.forall₂.2 edist_ne_top) <|
    surjective_mk.forall₂.2 dist_edist

end EqRel
