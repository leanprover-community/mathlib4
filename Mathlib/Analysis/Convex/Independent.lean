/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Extreme

/-!
# Convex independence

This file defines convex independent families of points.

Convex independence is closely related to affine independence. In both cases, no point can be
written as a combination of others. When the combination is affine (that is, any coefficients), this
yields affine independence. When the combination is convex (that is, all coefficients are
nonnegative), then this yields convex independence. In particular, affine independence implies
convex independence.

## Main declarations

* `ConvexIndependent p`: Convex independence of the indexed family `p : ι → E`. Every point of the
  family only belongs to convex hulls of sets of the family containing it.
* `convexIndependent_iff_finset`: Carathéodory's theorem allows us to only check finsets to
  conclude convex independence.
* `Convex.convexIndependent_extremePoints`: Extreme points of a convex set are convex independent.

## References

* https://en.wikipedia.org/wiki/Convex_position

## TODO

Prove `AffineIndependent.convexIndependent`. This requires some glue between `affineCombination`
and `Finset.centerMass`.

## Tags

independence, convex position
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open Affine Finset Function

variable {𝕜 E ι : Type*}

section OrderedSemiring

variable (𝕜) [Semiring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- An indexed family is said to be convex independent if every point only belongs to convex hulls
of sets containing it. -/
def ConvexIndependent (p : ι → E) : Prop :=
  ∀ (s : Set ι) (x : ι), p x ∈ convexHull 𝕜 (p '' s) → x ∈ s

variable {𝕜}

/-- A family with at most one point is convex independent. -/
theorem Subsingleton.convexIndependent [Subsingleton ι] (p : ι → E) : ConvexIndependent 𝕜 p := by
  intro s x hx
  have : (convexHull 𝕜 (p '' s)).Nonempty := ⟨p x, hx⟩
  rw [convexHull_nonempty_iff, Set.image_nonempty] at this
  rwa [Subsingleton.mem_iff_nonempty]

/-- A convex independent family is injective. -/
protected theorem ConvexIndependent.injective {p : ι → E} (hc : ConvexIndependent 𝕜 p) :
    Function.Injective p := by
  refine fun i j hij => hc {j} i ?_
  rw [hij, Set.image_singleton, convexHull_singleton]
  exact Set.mem_singleton _

/-- If a family is convex independent, so is any subfamily given by composition of an embedding into
index type with the original family. -/
theorem ConvexIndependent.comp_embedding {ι' : Type*} (f : ι' ↪ ι) {p : ι → E}
    (hc : ConvexIndependent 𝕜 p) : ConvexIndependent 𝕜 (p ∘ f) := by
  intro s x hx
  rw [← f.injective.mem_set_image]
  exact hc _ _ (by rwa [Set.image_image])

/-- If a family is convex independent, so is any subfamily indexed by a subtype of the index type.
-/
protected theorem ConvexIndependent.subtype {p : ι → E} (hc : ConvexIndependent 𝕜 p) (s : Set ι) :
    ConvexIndependent 𝕜 fun i : s => p i :=
  hc.comp_embedding (Embedding.subtype _)

/-- If an indexed family of points is convex independent, so is the corresponding set of points. -/
protected theorem ConvexIndependent.range {p : ι → E} (hc : ConvexIndependent 𝕜 p) :
    ConvexIndependent 𝕜 ((↑) : Set.range p → E) := by
  let f : Set.range p → ι := fun x => x.property.choose
  have hf : ∀ x, p (f x) = x := fun x => x.property.choose_spec
  let fe : Set.range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert hc.comp_embedding fe
  ext
  rw [Embedding.coeFn_mk, comp_apply, hf]

/-- A subset of a convex independent set of points is convex independent as well. -/
protected theorem ConvexIndependent.mono {s t : Set E} (hc : ConvexIndependent 𝕜 ((↑) : t → E))
    (hs : s ⊆ t) : ConvexIndependent 𝕜 ((↑) : s → E) :=
  hc.comp_embedding (s.embeddingOfSubset t hs)

/-- The range of an injective indexed family of points is convex independent iff that family is. -/
theorem Function.Injective.convexIndependent_iff_set {p : ι → E} (hi : Function.Injective p) :
    ConvexIndependent 𝕜 ((↑) : Set.range p → E) ↔ ConvexIndependent 𝕜 p :=
  ⟨fun hc =>
    hc.comp_embedding
      (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun _ _ h => hi (Subtype.mk_eq_mk.1 h)⟩ :
        ι ↪ Set.range p),
    ConvexIndependent.range⟩

/-- If a family is convex independent, a point in the family is in the convex hull of some of the
points given by a subset of the index type if and only if the point's index is in this subset. -/
@[simp]
protected theorem ConvexIndependent.mem_convexHull_iff {p : ι → E} (hc : ConvexIndependent 𝕜 p)
    (s : Set ι) (i : ι) : p i ∈ convexHull 𝕜 (p '' s) ↔ i ∈ s :=
  ⟨hc _ _, fun hi => subset_convexHull 𝕜 _ (Set.mem_image_of_mem p hi)⟩

/-- If a family is convex independent, a point in the family is not in the convex hull of the other
points. See `convexIndependent_set_iff_notMem_convexHull_diff` for the `Set` version. -/
theorem convexIndependent_iff_notMem_convexHull_diff {p : ι → E} :
    ConvexIndependent 𝕜 p ↔ ∀ i s, p i ∉ convexHull 𝕜 (p '' (s \ {i})) := by
  refine ⟨fun hc i s h => ?_, fun h s i hi => ?_⟩
  · rw [hc.mem_convexHull_iff] at h
    exact h.2 (Set.mem_singleton _)
  · by_contra H
    refine h i s ?_
    rw [Set.diff_singleton_eq_self H]
    exact hi

theorem convexIndependent_set_iff_inter_convexHull_subset {s : Set E} :
    ConvexIndependent 𝕜 ((↑) : s → E) ↔ ∀ t, t ⊆ s → s ∩ convexHull 𝕜 t ⊆ t := by
  constructor
  · rintro hc t h x ⟨hxs, hxt⟩
    refine hc { x | ↑x ∈ t } ⟨x, hxs⟩ ?_
    rw [Subtype.coe_image_of_subset h]
    exact hxt
  · intro hc t x h
    rw [← Subtype.coe_injective.mem_set_image]
    exact hc (t.image ((↑) : s → E)) (Subtype.coe_image_subset s t) ⟨x.prop, h⟩

/-- If a set is convex independent, a point in the set is not in the convex hull of the other
points. See `convexIndependent_iff_notMem_convexHull_diff` for the indexed family version. -/
theorem convexIndependent_set_iff_notMem_convexHull_diff {s : Set E} :
    ConvexIndependent 𝕜 ((↑) : s → E) ↔ ∀ x ∈ s, x ∉ convexHull 𝕜 (s \ {x}) := by
  rw [convexIndependent_set_iff_inter_convexHull_subset]
  constructor
  · rintro hs x hxs hx
    exact (hs _ Set.diff_subset ⟨hxs, hx⟩).2 (Set.mem_singleton _)
  · rintro hs t ht x ⟨hxs, hxt⟩
    by_contra h
    exact hs _ hxs (convexHull_mono (Set.subset_diff_singleton ht h) hxt)

end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s : Set E}

open scoped Classical in
/-- To check convex independence, one only has to check finsets thanks to Carathéodory's theorem. -/
theorem convexIndependent_iff_finset {p : ι → E} :
    ConvexIndependent 𝕜 p ↔
      ∀ (s : Finset ι) (x : ι), p x ∈ convexHull 𝕜 (s.image p : Set E) → x ∈ s := by
  refine ⟨fun hc s x hx => hc s x ?_, fun h s x hx => ?_⟩
  · rwa [Finset.coe_image] at hx
  have hp : Injective p := by
    rintro a b hab
    rw [← mem_singleton]
    refine h {b} a ?_
    rw [hab, image_singleton, coe_singleton, convexHull_singleton]
    exact Set.mem_singleton _
  rw [convexHull_eq_union_convexHull_finite_subsets] at hx
  simp_rw [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hx⟩ := hx
  rw [← hp.mem_set_image]
  refine ht ?_
  suffices x ∈ t.preimage p hp.injOn by rwa [mem_preimage, ← mem_coe] at this
  refine h _ x ?_
  rwa [t.image_preimage p hp.injOn, filter_true_of_mem]
  exact fun y hy => s.image_subset_range p (ht <| mem_coe.2 hy)

/-! ### Extreme points -/


theorem Convex.convexIndependent_extremePoints (hs : Convex 𝕜 s) :
    ConvexIndependent 𝕜 ((↑) : s.extremePoints 𝕜 → E) :=
  convexIndependent_set_iff_notMem_convexHull_diff.2 fun _ hx h =>
    (extremePoints_convexHull_subset
          (inter_extremePoints_subset_extremePoints_of_subset
            (convexHull_min (Set.diff_subset.trans extremePoints_subset) hs) ⟨h, hx⟩)).2
      (Set.mem_singleton _)

end LinearOrderedField
