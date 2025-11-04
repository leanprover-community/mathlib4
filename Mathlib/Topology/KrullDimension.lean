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

variable {U X : Type*} [TopologicalSpace X] [TopologicalSpace U] (f : U → X)


--{V : IrreducibleCloseds X | f ⁻¹' V ≠ ∅}
/--
Alternate definition of `map` not requiring the map to be closed, instead taking the closure of the
image.
-/
def closureImage (h : Continuous f) (T : IrreducibleCloseds U) : IrreducibleCloseds X where
  carrier := closure (f '' T.1)
  is_irreducible' := T.is_irreducible'.image f (Continuous.continuousOn h) |>.closure
  is_closed' := isClosed_closure
  /-property := nonempty_iff_ne_empty.mp
    (Nonempty.mono (closure_subset_preimage_closure_image h (s := T))
    (closure_nonempty_iff.mpr T.2.nonempty))-/

lemma closureImage_eq (h : Continuous f) (T : IrreducibleCloseds U) (h2 : IsClosedMap f) :
    closureImage f h T = map h h2 T := by
  simp [map, closureImage]
  /-
  I think this is going to be a real pain if we just replace map with closureImage
  -/

  --rw[IsClosedMap.closure_image_eq_of_continuous h2 h T]
  sorry
  --rw [T.3.closure_eq]



lemma closureImage_preimage_nonemtpy (h : Continuous f) (T : IrreducibleCloseds U) :
    (f ⁻¹' (closureImage f h T)).Nonempty :=
  (Nonempty.mono (closure_subset_preimage_closure_image h (s := T))
      (closure_nonempty_iff.mpr T.2.nonempty))


/--
Map induced by the preimage under a continuous closed embedding on irreducible closed subsets.
-/
def comap (h : IsOpenEmbedding f) (V : IrreducibleCloseds X) (hV : (f ⁻¹' V).Nonempty) :
    IrreducibleCloseds U where
  carrier := f ⁻¹' V
  is_irreducible' := ⟨hV,
    IsPreirreducible.preimage (IsIrreducible.isPreirreducible V.2) h⟩
  is_closed' := V.3.preimage h.continuous

/--
The map taking an irreducible closed set `T` to `closure (f '' T)` is monotone.
-/
lemma closureImage_mono (h : Continuous f) :
  Monotone <| closureImage f h := fun _ _ s ↦ closure_mono (image_mono s)


def closureImageSubtype (h : Continuous f) (T : IrreducibleCloseds U) :
    {V : IrreducibleCloseds X | (f ⁻¹' V).Nonempty} :=
  ⟨closureImage f h T, closureImage_preimage_nonemtpy f h T⟩

def comapSubtype (h : IsOpenEmbedding f) (V : {V : IrreducibleCloseds X | (f ⁻¹' V).Nonempty}) :=
  comap f h V.1 V.2
/--
The map taking an irreducible closed set `T` to `closure (f '' T)` is left inverse to the preimage
when `f` is an open embedding
-/
lemma closureImage_comap_leftInverse (h : IsOpenEmbedding f) :
    Function.LeftInverse (closureImageSubtype f h.continuous) (comapSubtype f h) := by
  intro V
  simp only [coe_setOf]
  have : (V.1.1 ∩ range f).Nonempty := by
    have := V.2
    dsimp at this
    rw[← Set.preimage_inter_range] at this
    have : (f ⁻¹' (↑↑V ∩ range f)).Nonempty := this
    exact Set.nonempty_of_nonempty_preimage this
  have lem := subset_closure_inter_of_isPreirreducible_of_isOpen (S := V.1.1) (U := range f)
    (IsIrreducible.isPreirreducible V.1.2) (h.isOpen_range) this
  refine le_antisymm (((IsClosed.closure_subset_iff (IrreducibleCloseds.isClosed V.1)).mpr
    (image_preimage_subset f ↑↑V))) ?_
  suffices V.1.1 ⊆ closure (f '' (f ⁻¹' V.1.1)) from this
  convert lem
  exact image_preimage_eq_inter_range


/--
The map taking an irreducible closed set `T` to `closure (f '' T)` is right inverse to the preimage
when `f` is an open embedding
-/
lemma closureImage_comap_rightInverse (h : IsOpenEmbedding f) :
    Function.RightInverse (closureImageSubtype f h.continuous) (comapSubtype f h) := by
  intro V
  simp only [comapSubtype, comap, mem_setOf_eq, closureImageSubtype, closureImage,
    IrreducibleCloseds.coe_mk]
  apply le_antisymm
  · apply le_trans (b := closure V.carrier)
    · rw[Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap] at h
      simp only [IrreducibleCloseds.coe_mk, le_eq_subset,
          IsOpenMap.preimage_closure_eq_closure_preimage h.2.2 h.1]
      rw [preimage_image_eq]
      exact h.2.1
    · rw [IsClosed.closure_eq V.3]
      rfl
  · apply le_trans subset_closure (closure_subset_preimage_closure_image h.continuous)

/-
/--
The map taking an irreducible closed set `T` to `closure (f '' T)` is injective when `f` is an
open embedding
-/
lemma closureImage_injective_of_openEmbedding (h : IsOpenEmbedding f) :
    Function.Injective <| closureImage f h.continuous := by
  exact Function.LeftInverse.injective <| closureImage_comap_rightInverse f h

/--
The map taking an irreducible closed set `T` to `closure (f '' T)` is surjective onto irreducible
closeds `V` satisfying `f ⁻¹' V ≠ ∅` when `f` is an open embedding.
-/
lemma closureImage_surjective_of_openEmbedding (h : IsOpenEmbedding f) :
    Function.Surjective <| closureImage f h.continuous := by
  exact Function.RightInverse.surjective <| closureImage_comap_leftInverse f h h2

/--
The map taking an irreducible closed set `T` to `closure (f '' T)` is bijective onto irreducible
closeds `V` satisfying `f ⁻¹' V ≠ ∅` when `f` is an open embedding.
-/
lemma closureImage_bijective_of_openEmbedding (h2 : IsOpenEmbedding f) :
  Function.Bijective <| closureImage f h :=
  ⟨closureImage_injective_of_openEmbedding f h h2, closureImage_surjective_of_openEmbedding f h h2⟩

/--
The map taking an irreducible closed set `T` to `closure (f '' T)` is strictly monotone when
`f` is an open embedding.
-/
lemma closureImage_strictMono_of_openEmbedding (h : IsOpenEmbedding f) :
  StrictMono <| closureImage f h.continuous := Monotone.strictMono_of_injective
   (closureImage_mono f h.continuous) (closureImage_injective_of_openEmbedding f h)-/


/--
Given `f : U → X` a continuous open embedding, the irreducble closeds of `U` are order isomorphic
to the irreducible closeds of `X` nontrivially intersecting the range of `f`.
-/
noncomputable
def closureImageOrderIso (h : IsOpenEmbedding f) :
  IrreducibleCloseds U ≃o {V : IrreducibleCloseds X | (f ⁻¹' V).Nonempty} where
    toFun := closureImageSubtype f (h.continuous)
    invFun := comapSubtype f h
    left_inv := closureImage_comap_rightInverse f h
    right_inv := closureImage_comap_leftInverse f h
    map_rel_iff' := by
      intro a b
      simp only [coe_setOf, mem_setOf_eq, Equiv.coe_fn_mk]
      constructor
      · intro c
        have eq : f ⁻¹' closure (f '' a.carrier) ≤ f ⁻¹' closure (f '' b.carrier) := fun _ b ↦ c b
        have (z : IrreducibleCloseds U) : z.carrier = f ⁻¹' (closure (f '' z.carrier)) := by
          suffices closure z.carrier = f ⁻¹' (closure (f '' z.carrier)) by
            nth_rewrite 1 [← IsClosed.closure_eq z.3]
            exact this
          exact Topology.IsEmbedding.closure_eq_preimage_closure_image h.isEmbedding z
        rwa [← this a, ← this b] at eq
      · exact fun c ↦ (closureImage_mono f h.continuous) c

end IrreducibleCloseds
