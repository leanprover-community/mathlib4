/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li, Alessandro D'Angelo
-/
module

public import Mathlib.Order.KrullDimension
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sober

/-!
# The Krull dimension of a topological space

The Krull dimension of a topological space is the order-theoretic Krull dimension applied to the
collection of all its subsets that are closed and irreducible. Unfolding this definition, it is
the length of longest series of closed irreducible subsets ordered by inclusion.

## Main results

- `topologicalKrullDim_subspace_le`: For any subspace Y ⊆ X, we have dim(Y) ≤ dim(X)

## Implementation notes

The proofs use order-preserving maps between posets of irreducible closed sets to establish
dimension inequalities.
-/

@[expose] public section

open Set Function Order TopologicalSpace Topology TopologicalSpace.IrreducibleCloseds

/--
The Krull dimension of a topological space is the supremum of lengths of chains of
closed irreducible sets.
-/
noncomputable def topologicalKrullDim (T : Type*) [TopologicalSpace T] : WithBot ℕ∞ :=
  krullDim (IrreducibleCloseds T)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-!
### Main dimension theorems -/

/-- If `f : Y → X` is inducing, then `dim(Y) ≤ dim(X)`. -/
theorem IsInducing.topologicalKrullDim_le {f : Y → X} (hf : IsInducing f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  krullDim_le_of_strictMono _ (map_strictMono_of_isInducing hf)

@[deprecated (since := "2025-10-19")]
alias IsClosedEmbedding.topologicalKrullDim_le := IsInducing.topologicalKrullDim_le

/-- The topological Krull dimension is invariant under homeomorphisms -/
theorem IsHomeomorph.topologicalKrullDim_eq (f : X → Y) (h : IsHomeomorph f) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  have fwd : topologicalKrullDim X ≤ topologicalKrullDim Y :=
    IsInducing.topologicalKrullDim_le h.isClosedEmbedding.toIsInducing
  have bwd : topologicalKrullDim Y ≤ topologicalKrullDim X :=
    IsInducing.topologicalKrullDim_le (h.homeomorph f).symm.isClosedEmbedding.toIsInducing
  le_antisymm fwd bwd

/-- The topological Krull dimension of any subspace is at most the dimension of the
ambient space. -/
theorem topologicalKrullDim_subspace_le (X : Type*) [TopologicalSpace X] (Y : Set X) :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  IsInducing.topologicalKrullDim_le IsInducing.subtypeVal

theorem topologicalKrullDim_zero_of_discreteTopology
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    topologicalKrullDim X ≤ 0 := by
  refine krullDim_nonpos_iff_forall_isMax.mpr fun Z Y h ↦ (h.antisymm' fun x hx ↦ ?_).le
  obtain ⟨z, hz⟩ := Z.2.nonempty
  rwa [DiscreteTopology.isDiscrete.subsingleton_of_isPreirreducible Y.2.isPreirreducible hx (h hz)]

variable {α : Type*} [TopologicalSpace α]

open TopologicalSpace Topology Order Set IrreducibleCloseds

lemma Topology.IsOpenEmbedding.coheight_map {U X : Type*} [TopologicalSpace U]
    [TopologicalSpace X] {f : U → X} (hf : IsOpenEmbedding f)
    (Z : TopologicalSpace.IrreducibleCloseds U) :
    Order.coheight (map f hf.continuous Z) = Order.coheight Z := by
  rw [← coheight_orderIso (mapOrderIso f hf) Z]
  let g : {V : IrreducibleCloseds X | (f ⁻¹' ↑V).Nonempty} ↪o
      IrreducibleCloseds X :=
    OrderEmbedding.subtype {V : IrreducibleCloseds X | (f ⁻¹' V).Nonempty}
  let a := (mapOrderIso f hf) Z
  have : ∀ p : LTSeries (IrreducibleCloseds X), p.head = g a →
         ∃ p' : LTSeries ({V : IrreducibleCloseds X | (f ⁻¹' ↑V).Nonempty}),
           p'.head = a ∧ p = p'.map g (OrderEmbedding.strictMono g) := fun p hp ↦ by
    let p' : LTSeries {V : IrreducibleCloseds X | (f ⁻¹' ↑V).Nonempty} := {
      length := p.length
      toFun i := {
        val := p i
        property := by
          suffices  ¬ f ⁻¹' a = ∅ by
            rw[← Ne, ← nonempty_iff_ne_empty] at this
            exact Nonempty.mono (fun _ b ↦ (hp ▸ LTSeries.head_le p i) b) this
          exact nonempty_iff_ne_empty.mp a.2
      }
      step := p.step
    }
    exact ⟨p', SetCoe.ext hp, rfl⟩
  exact (coheight_eq_of_strictMono g (fun _ _ a ↦ a)
     ((mapOrderIso f hf) Z) this).symm

attribute [local instance] specializationOrder

@[simp]
lemma coe_irreducibleEquivPoints_symm_apply [QuasiSober α] [T0Space α] (x : α) :
    (irreducibleSetEquivPoints.symm x : Set α) = closure {x} := rfl

lemma Topology.IsOpenEmbedding.coheight_eq {U X : Type*} [TopologicalSpace U] [TopologicalSpace X]
    [QuasiSober X] [T0Space X] [QuasiSober U] [T0Space U]
    {x : U} (f : U → X) (hf : IsOpenEmbedding f) :
    coheight (f x) = coheight x := by
  rw [← coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm (f x),
    ← coheight_orderIso (irreducibleSetEquivPoints (α := U)).symm x,
    ← Topology.IsOpenEmbedding.coheight_map hf]
  congr
  ext : 1
  simp [closure_image_closure hf.continuous]
