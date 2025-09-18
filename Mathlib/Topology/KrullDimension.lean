/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/
import Mathlib.Order.KrullDimension
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Closeds

/-!
# The Krull dimension of a topological space

The Krull dimension of a topological space is the order-theoretic Krull dimension applied to the
collection of all its subsets that are closed and irreducible. Unfolding this definition, it is
the length of longest series of closed irreducible subsets ordered by inclusion.
-/

open Order TopologicalSpace Topology Set

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
  is_irreducible' := c.is_irreducible'.image f hf1.continuousOn
  is_closed' := hf2 c c.is_closed'

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


namespace IrreducibleCloseds

variable {U X : Type*} [TopologicalSpace X] [TopologicalSpace U] (f : U → X) (h : Continuous f)

/--
Alternate definition of `map` not requiring the map to be closed, instead taking the closure of the
image.
-/
def map' (T : IrreducibleCloseds U) : {V : IrreducibleCloseds X | f ⁻¹' V ≠ ∅} where
  val := {
    carrier := closure (f '' T.1)
    is_irreducible' := IsIrreducible.closure <|
      IsIrreducible.image T.is_irreducible' f (Continuous.continuousOn h)
    is_closed' := isClosed_closure
  }
  property := nonempty_iff_ne_empty.mp
    (Nonempty.mono (closure_subset_preimage_closure_image h (s := T))
    (closure_nonempty_iff.mpr T.2.nonempty))

/--
Map induced by the preimage under a continuous closed embedding on irreducible closed subsets.
-/
def comap (h2 : IsOpenEmbedding f) (V : {V : IrreducibleCloseds X | f ⁻¹' V ≠ ∅}) :
    IrreducibleCloseds U where
  carrier := f ⁻¹' V
  is_irreducible' := ⟨nonempty_iff_ne_empty.mpr V.2,
    IsPreirreducible.preimage (IsIrreducible.isPreirreducible V.1.2) h2⟩
  is_closed' := V.1.3.preimage h

/--
The map taking an irreducible closed set `T` to `closure (f '' T)` is monotone.
-/
lemma map'_mono {U X : Type*} [TopologicalSpace X] [TopologicalSpace U]
  (f : U → X) (h2 : Continuous f) :
  Monotone <| map' f h2 := fun _ _ s ↦ closure_mono (image_mono s)

/--
The map taking an irreducible closed set `T` to `closure (f '' T)` is injective when `f` is an
open embedding
-/
lemma map'_injective_of_openEmbedding (h2 : IsOpenEmbedding f) :
    Function.Injective <| map' f h := by
  intro V W hVW
  simp only [ne_eq, coe_setOf, map', mem_setOf_eq, Subtype.mk.injEq,
    IrreducibleCloseds.mk.injEq] at hVW
  have : f ⁻¹' closure (f '' V) = f ⁻¹' closure (f '' W) := congrArg (preimage f) hVW
  simp only [h2.isOpenMap.preimage_closure_eq_closure_preimage h,
        Function.Injective.preimage_image h2.1.injective _,
        V.isClosed.closure_eq, W.isClosed.closure_eq] at this
  exact IrreducibleCloseds.ext_iff.mpr this

/--
The map taking an irreducible closed set `T` to `closure (f '' T)` is surjective onto irreducible
closeds `V` satisfying `f ⁻¹' V ≠ ∅` when `f` is an open embedding.
-/
lemma map'_surjective_of_openEmbedding (h2 : IsOpenEmbedding f) :
    Function.Surjective <| map' f h := by
  intro V
  use comap f h h2 V
  simp only [ne_eq, coe_setOf, map', mem_setOf_eq]
  have : (V.1.1 ∩ range f).Nonempty := by
    have := V.2
    dsimp at this
    rw[← Set.preimage_inter_range] at this
    have : (f ⁻¹' (↑↑V ∩ range f)).Nonempty := nonempty_iff_ne_empty.mpr this
    exact Set.nonempty_of_nonempty_preimage this
  have lem := subset_closure_inter_of_isPreirreducible_of_isOpen (S := V.1.1) (U := range f)
    (IsIrreducible.isPreirreducible V.1.2) (h2.isOpen_range) this
  refine le_antisymm (((IsClosed.closure_subset_iff (IrreducibleCloseds.isClosed V.1)).mpr
    (image_preimage_subset f ↑↑V))) ?_
  suffices V.1.1 ⊆ closure (f '' (f ⁻¹' V.1.1)) from this
  convert lem
  exact image_preimage_eq_inter_range

/--
The map taking an irreducible closed set `T` to `closure (f '' T)` is bijective onto irreducible
closeds `V` satisfying `f ⁻¹' V ≠ ∅` when `f` is an open embedding.
-/
lemma map'_bijective_of_openEmbedding (h2 : IsOpenEmbedding f) :
  Function.Bijective <| map' f h :=
  ⟨map'_injective_of_openEmbedding f h h2, map'_surjective_of_openEmbedding f h h2⟩

/--
The map taking an irreducible closed set `T` to `closure (f '' T)` is strictly monotone when
`f` is an open embedding.
-/
lemma map'_strictMono_of_openEmbedding (h2 : IsOpenEmbedding f) :
  StrictMono <| map' f h := Monotone.strictMono_of_injective
   (map'_mono f h) (map'_injective_of_openEmbedding f h h2)

/--
Given `f : U → X` a continuous open embedding, the irreducble closeds of `U` are order isomorphic
to the irreducible closeds of `X` nontrivially intersecting the range of `f`.
-/
noncomputable
def map'OrderIso (h2 : IsOpenEmbedding f) :
  IrreducibleCloseds U ≃o {V : IrreducibleCloseds X | f ⁻¹' V ≠ ∅} := by
  refine ⟨Equiv.ofBijective (map' f h) (map'_bijective_of_openEmbedding f h h2), ?_⟩
  have := map'_mono f h
  refine fun a b ↦ ⟨fun h ↦ ?_, fun a_1 ↦ (map'_mono f h) a_1⟩
  · have eq : f ⁻¹' closure (f '' a.carrier) ≤ f ⁻¹' closure (f '' b.carrier) := fun _ b ↦ h b
    have (c : IrreducibleCloseds U) : c.carrier = f ⁻¹' (closure (f '' c.carrier)) := by
      suffices closure c.carrier = f ⁻¹' (closure (f '' c.carrier)) by
        nth_rewrite 1 [← IsClosed.closure_eq c.3]
        exact this
      exact Topology.IsEmbedding.closure_eq_preimage_closure_image h2.isEmbedding c
    rwa [← this a, ← this b] at eq

end IrreducibleCloseds
