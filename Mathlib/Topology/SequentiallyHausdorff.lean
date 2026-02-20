/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Sequentially T₂ spaces.

This file defines the sequentially T₂ spaces,
i.e. topological spaces whhere converging sequences have unique limits.
This lies between T₂ and T₁.

## Main definitions

* `SeqT2Space`: A *sequentially T₂ space*, i.e. topological space
  where a converging sequence has a unique limit.

This property is also called US space or semi-hausdorff space in the literature.

## Main results

* `T2Space.SeqT2Space`: A T₂ space is sequentially T₂.
* `SeqT2Space.T1Space`: A sequentially T₂ space is T₁.
* `TopologicalSpace.instT2SpaceOfSeqT2SpaceOfFirstCountableTopology`:
  A first countable, sequentially T₂ space is T₂.

## References

* <https://topology.pi-base.org/properties/P000099>
* [Semi-Hausdorff Spaces](https://www.cambridge.org/core/journals/canadian-mathematical-bulletin/article/semihausdorff-spaces/044926FC9F64DFEDF4BBF379AD717518)

# TODO

* Prove disjoint unions of sequentially T₂ are sequentially T₂
* Prove (countably) compact subsets in sequentially T₂ spaces are closed.

-/

@[expose] public section

open Topology Filter Function

variable (X : Type*) {Y : Type*} [TopologicalSpace X]

section SequentiallyT2

/-- A topological space is said to be a *sequentially T₂*
if converging sequence has at most one limit. -/
@[mk_iff]
class SeqT2Space : Prop where
  tendsto_unique : ∀ f : ℕ → X, ∀ a b : X,
    Tendsto f atTop (𝓝 a) → Tendsto f atTop (𝓝 b) → a = b

variable {X}

/-- If the codomain of an injective continuous function is a sequentially T₂ space, then so is its
domain. -/
theorem SeqT2Space.of_injective_continuous [TopologicalSpace Y] [SeqT2Space Y] {f : X → Y}
    (hinj : Injective f) (hf : Continuous f) : SeqT2Space X := by
  constructor
  intro l a b ha hb
  have s1 : Tendsto (f ∘ l) atTop (𝓝 (f a)) :=
    Tendsto.comp (Continuous.continuousAt hf) ha
  have s2 : Tendsto (f ∘ l) atTop (𝓝 (f b)) :=
    Tendsto.comp (Continuous.continuousAt hf) hb
  exact hinj (tendsto_unique (f ∘ l) (f a) (f b) s1 s2)

/-- If the codomain of a topological embedding is a sequentially T₂ space, then so is its domain.
See also `SeqT2Space.of_injective_continuous`. -/
theorem Topology.IsEmbedding.seqT2Space [TopologicalSpace Y] [SeqT2Space Y] {f : X → Y}
    (hf : IsEmbedding f) : SeqT2Space X :=
  .of_injective_continuous hf.injective hf.continuous

protected theorem Homeomorph.seqT2Space [TopologicalSpace Y] [SeqT2Space X] (h : X ≃ₜ Y) :
    SeqT2Space Y := h.symm.isEmbedding.seqT2Space

variable (X)

instance {p : X → Prop} [SeqT2Space X] : SeqT2Space (Subtype p) :=
  .of_injective_continuous Subtype.val_injective continuous_subtype_val

instance ULift.instSeqT2Space [SeqT2Space X] : SeqT2Space (ULift X) :=
  IsEmbedding.uliftDown.seqT2Space

/-- Products of sequentially T₂ spaces are sequentially T₂. -/
instance Pi.seqT2Space {Y : X → Type v} [∀ a, TopologicalSpace (Y a)]
    [∀ a, SeqT2Space (Y a)] : SeqT2Space (∀ a, Y a) := by
  constructor
  intro f _ _ ha hb
  ext i
  apply SeqT2Space.tendsto_unique (f := (fun j ↦ (f j) i))
  · exact Tendsto.apply_nhds ha i
  · exact Tendsto.apply_nhds hb i

/-- A T₂ space is sequentially T₂. -/
instance T2Space.SeqT2Space [T2Space X] : SeqT2Space X where
  tendsto_unique _ _ _ h h' := tendsto_nhds_unique h h'

/-- A sequentially T₂ space is T₁. -/
instance SeqT2Space.T1Space [SeqT2Space X] : T1Space X := by
  rw [t1Space_iff_specializes_imp_eq]
  intro x y xy
  exact tendsto_unique (fun _ ↦ x) x y tendsto_const_nhds
    (tendsto_iff_forall_eventually_mem.mpr fun s a ↦ tendsto_const_nhds (xy a))

/-- A first countable, sequentially T₂ space is T₂. -/
instance TopologicalSpace.instT2SpaceOfSeqT2SpaceOfFirstCountableTopology
    [SeqT2Space X] [FirstCountableTopology X] : T2Space X := by
  have has_basis (z : X) : ∃ u : ℕ → Set X, (𝓝 z).HasAntitoneBasis u :=
    isCountablyGenerated_iff_exists_antitone_basis.mp
      (FirstCountableTopology.nhds_generated_countable z)
  rw [t2Space_iff_disjoint_nhds]
  intro x y xy
  obtain ⟨u, hu⟩ := has_basis x
  obtain ⟨v, hv⟩ := has_basis y
  contrapose! xy
  have nonempty (i : ℕ) : (u i ∩ v i).Nonempty := by
    rw [Filter.disjoint_iff] at xy
    push_neg at xy
    exact Set.not_disjoint_iff_nonempty_inter.mp
      <| xy (u i) (HasAntitoneBasis.mem hu i) (v i) (HasAntitoneBasis.mem hv i)
  apply SeqT2Space.tendsto_unique (fun i ↦ (nonempty i).choose)
  · exact HasAntitoneBasis.tendsto hu (fun i ↦ (Exists.choose_spec (nonempty i)).1)
  · exact HasAntitoneBasis.tendsto hv (fun i ↦ (Exists.choose_spec (nonempty i)).2)

end SequentiallyT2
