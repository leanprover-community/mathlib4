/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li, Alessandro D'Angelo
-/
import Mathlib.Order.KrullDimension
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Closeds

/-!
# The Krull dimension of a topological space

The Krull dimension of a topological space is the order-theoretic Krull dimension applied to the
collection of all its subsets that are closed and irreducible. Unfolding this definition, it is
the length of longest series of closed irreducible subsets ordered by inclusion.

## Main results

- `topKrullDim_subspace_le`: For any subspace Y ⊆ X, we have dim(Y) ≤ dim(X)
- Basic properties of maps between irreducible closed sets
- Partial order structure on irreducible closed sets

## Implementation notes

The proofs use order-preserving maps between posets of irreducible closed sets to establish
dimension inequalities.
-/

open Set Function Order TopologicalSpace Topology

/--
The Krull dimension of a topological space is the supremum of lengths of chains of
closed irreducible sets.
-/
noncomputable def topologicalKrullDim (T : Type*) [TopologicalSpace T] : WithBot ℕ∞ :=
  krullDim (IrreducibleCloseds T)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/--
Map induced on irreducible closed subsets by a closed continuous map `f`.
This is just a wrapper around the image of `f` together with proofs that it
preserves irreducibility (by continuity) and closedness (since `f` is closed).
-/
def IrreducibleCloseds.map {f : X → Y} (hf1 : Continuous f) (hf2 : IsClosedMap f)
    (c : IrreducibleCloseds X) :
    IrreducibleCloseds Y where
  carrier := f '' c
  isIrreducible' := c.isIrreducible.image f hf1.continuousOn
  isClosed' := hf2 c c.isClosed

/--
Taking images under a closed embedding is strictly monotone on the preorder of irreducible closeds.
-/
lemma IrreducibleCloseds.map_strictMono {f : X → Y} (hf : IsClosedEmbedding f) :
    StrictMono (IrreducibleCloseds.map hf.continuous hf.isClosedMap) :=
  fun ⦃_ _⦄ UltV ↦ hf.injective.image_strictMono UltV

/--
If `f : X → Y` is a closed embedding, then the Krull dimension of `X` is less than or equal
to the Krull dimension of `Y`.
-/
theorem IsClosedEmbedding.topologicalKrullDim_le (f : X → Y) (hf : IsClosedEmbedding f) :
    topologicalKrullDim X ≤ topologicalKrullDim Y :=
  krullDim_le_of_strictMono _ (IrreducibleCloseds.map_strictMono hf)

/-- The topological Krull dimension is invariant under homeomorphisms -/
theorem IsHomeomorph.topologicalKrullDim_eq (f : X → Y) (h : IsHomeomorph f) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  have fwd : topologicalKrullDim X ≤ topologicalKrullDim Y :=
    IsClosedEmbedding.topologicalKrullDim_le f h.isClosedEmbedding
  have bwd : topologicalKrullDim Y ≤ topologicalKrullDim X :=
    IsClosedEmbedding.topologicalKrullDim_le (h.homeomorph f).symm
    (h.homeomorph f).symm.isClosedEmbedding
  le_antisymm fwd bwd

/-! ### Maps between irreducible closed sets -/

/-- The canonical map from irreducible closed sets of a subspace `Y` to irreducible
closed sets of the ambient space `X`, defined by taking the closure of the image
under the inclusion map. This map is crucial for comparing Krull dimensions. -/
def mapIrreducibleClosed (Y : Set X) (c : IrreducibleCloseds Y) : IrreducibleCloseds X where
  carrier := closure (Subtype.val '' c.carrier)
  is_irreducible' := c.is_irreducible'.image Subtype.val
    (continuous_subtype_val.continuousOn) |>.closure
  is_closed' := isClosed_closure

/-- The map `mapIrreducibleClosed` is injective, meaning distinct irreducible
closed sets in a subspace map to distinct irreducible closed sets in the ambient space.
This ensures that the dimension-preserving properties hold. -/
lemma mapIrreducibleClosed_injective (Y : Set X) :
    Function.Injective (mapIrreducibleClosed Y) := by
  intro A B h_images_eq
  ext x
  have h_closures_eq : closure (Subtype.val '' A.carrier) =
      closure (Subtype.val '' B.carrier) :=
    congrArg IrreducibleCloseds.carrier h_images_eq
  constructor
  · -- Forward direction: x ∈ A → x ∈ B
    intro hx_in_A
    change x ∈ B.carrier
    rw [← B.is_closed'.closure_eq]
    -- Use the mathlib lemma for embeddings
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    rw [← h_closures_eq]
    simp_rw [mem_preimage]
    apply subset_closure
    exact mem_image_of_mem Subtype.val hx_in_A
  · -- Backward direction: x ∈ B → x ∈ A
    intro hx_in_B
    change x ∈ A.carrier
    rw [← A.is_closed'.closure_eq]
    -- Use the mathlib lemma for embeddings
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    rw [h_closures_eq]
    simp_rw [mem_preimage]
    apply subset_closure
    exact mem_image_of_mem Subtype.val hx_in_B


/-! ### Partial order structure on irreducible closed sets -/

instance : PartialOrder (IrreducibleCloseds X) where
  le s t := s.carrier ⊆ t.carrier
  le_refl s := Set.Subset.refl _
  le_trans s t u hst htu := Set.Subset.trans hst htu
  le_antisymm s t hst hts := by
    apply IrreducibleCloseds.ext
    exact Set.Subset.antisymm hst hts

/-- The partial order on `IrreducibleCloseds X` is given by subset inclusion
of the underlying sets. -/
lemma IrreducibleCloseds.le_iff_subset {s t : IrreducibleCloseds X} :
    s ≤ t ↔ s.carrier ⊆ t.carrier := by rfl

/-- The strict partial order on `IrreducibleCloseds X` corresponds to strict
subset inclusion of the underlying sets. -/
lemma IrreducibleCloseds.lt_iff_subset {s t : IrreducibleCloseds X} :
    s < t ↔ s.carrier ⊂ t.carrier := by
  constructor
  · intro h_lt
    have h_le := le_of_lt h_lt
    have h_ne := ne_of_lt h_lt
    rw [ssubset_iff_subset_ne]
    constructor
    · rw [← IrreducibleCloseds.le_iff_subset]
      exact h_le
    · apply mt IrreducibleCloseds.ext
      exact h_ne
  · intro h_ssubset
    rw [lt_iff_le_and_ne]
    rcases h_ssubset with ⟨h_subset, h_ne_carrier⟩
    constructor
    · rw [IrreducibleCloseds.le_iff_subset]
      exact h_subset
    · intro h_s_eq_t
      apply h_ne_carrier
      rw [h_s_eq_t]

/-- The canonical map `mapIrreducibleClosed` is strictly monotone, preserving
the order structure when comparing irreducible closed sets between subspaces
and ambient spaces. This is essential for the dimension inequality theorem. -/
lemma mapIrreducibleClosed_strictMono (Y : Set X) :
    StrictMono (mapIrreducibleClosed Y) := by
  intro A B h_less_AB
  constructor
  · -- Part 1: Prove map A ≤ map B
    apply closure_mono
    apply image_mono
    exact le_of_lt h_less_AB
  · -- Part 2: Prove ¬(map B ≤ map A)
    intro h_contra_le
    have h_forward_subset : (mapIrreducibleClosed Y A).carrier ⊆
        (mapIrreducibleClosed Y B).carrier := by
      apply closure_mono
      apply image_mono
      exact le_of_lt h_less_AB
    have h_carrier_eq : (mapIrreducibleClosed Y A).carrier = (mapIrreducibleClosed Y B).carrier :=
      Subset.antisymm h_forward_subset h_contra_le
    have h_A_eq_B : A = B := by
      apply mapIrreducibleClosed_injective Y
      apply IrreducibleCloseds.ext
      exact h_carrier_eq
    exact (ne_of_lt h_less_AB) h_A_eq_B

/-! ### Main dimension theorems -/

/-- **Subspace Dimension Inequality**: The topological Krull dimension of any subspace
is at most the dimension of the ambient space. This fundamental result shows that
subspaces cannot have larger dimension than their ambient space. -/
theorem topKrullDim_subspace_le (X : Type*) [TopologicalSpace X] (Y : Set X) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  unfold topologicalKrullDim
  apply krullDim_le_of_strictMono (mapIrreducibleClosed Y)
  exact mapIrreducibleClosed_strictMono Y
