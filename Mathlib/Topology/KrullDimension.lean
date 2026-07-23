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
public import Mathlib.Topology.NoetherianSpace

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
theorem Topology.IsInducing.topologicalKrullDim_le {f : Y → X} (hf : IsInducing f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  krullDim_le_of_strictMono _ (map_strictMono_of_isInducing hf)

/-- The topological Krull dimension is invariant under homeomorphisms -/
theorem IsHomeomorph.topologicalKrullDim_eq (f : X → Y) (h : IsHomeomorph f) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  have fwd : topologicalKrullDim X ≤ topologicalKrullDim Y :=
    h.isInducing.topologicalKrullDim_le
  have bwd : topologicalKrullDim Y ≤ topologicalKrullDim X :=
    (h.homeomorph f).symm.isInducing.topologicalKrullDim_le
  le_antisymm fwd bwd

/-- The topological Krull dimension of any subspace is at most the dimension of the
ambient space. -/
theorem topologicalKrullDim_subspace_le (X : Type*) [TopologicalSpace X] (Y : Set X) :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  IsInducing.subtypeVal.topologicalKrullDim_le

theorem topologicalKrullDim_zero_of_discreteTopology
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    topologicalKrullDim X ≤ 0 := by
  refine krullDim_nonpos_iff_forall_isMax.mpr fun Z Y h ↦ (h.antisymm' fun x hx ↦ ?_).le
  obtain ⟨z, hz⟩ := Z.2.nonempty
  rwa [DiscreteTopology.isDiscrete.subsingleton_of_isPreirreducible Y.2.isPreirreducible hx (h hz)]

lemma Topology.IsOpenEmbedding.coheight_map {f : X → Y} (hf : IsOpenEmbedding f)
    (Z : TopologicalSpace.IrreducibleCloseds X) :
    Order.coheight (map f hf.continuous Z) = Order.coheight Z := by
  rw [← coheight_orderIso (orderIsoOfIsOpenEmbedding f hf) Z]
  refine .symm (coheight_eq_of_strictMono Subtype.val (Subtype.strictMono_coe _) ?_ _)
  intro a b hlt
  exact ⟨⟨b, a.2.mono (Set.preimage_mono hlt.le)⟩, hlt, rfl⟩

attribute [local instance] specializationOrder in
lemma Topology.IsOpenEmbedding.coheight_eq [QuasiSober Y] [T0Space Y] [QuasiSober X] [T0Space X]
    {x : X} (f : X → Y) (hf : IsOpenEmbedding f) : coheight (f x) = coheight x := by
  rw [← coheight_orderIso (irreducibleSetEquivPoints (α := Y)).symm (f x),
    ← coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm x,
    ← Topology.IsOpenEmbedding.coheight_map hf]
  congr
  ext : 1
  simp [closure_image_closure hf.continuous]

attribute [local instance 10000] specializationPreorder in
/--
In a quasi-sober, irreducible, T0 space `X`, a Noetherian quasi-sober subspace `p` whose closure
is not all of `X` contains only finitely many points of coheight `1` (in the specialization order
of `X`).
-/
lemma TopologicalSpace.NoetherianSpace.finite_coheight_one_of_closure_ne_univ
    [QuasiSober X] [IrreducibleSpace X] [T0Space X] {p : Set X}
    [NoetherianSpace p] [QuasiSober p] (hp : closure p ≠ univ) :
    {x | x ∈ p ∧ coheight x = 1}.Finite := by
  have h : {x : p | coheight x = 0}.Finite :=
    finite_coe_iff.mp <| (Equiv.finite_iff
      (coheightZeroSetOrderIsoIrreducibleComponents (α := p)).toEquiv).mpr
      NoetherianSpace.finite_irreducibleComponents
  exact (h.image Subtype.val).subset
    (QuasiSober.coheight_eq_zero_subset_of_coheight_eq_one hp)
