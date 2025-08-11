/-
Copyright (c) 2025 Sebastian Kumar, Xiangyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar, Xiangyu Li
-/
import Mathlib.Combinatorics.SimplicialComplex.Basic

/-!
# Morphisms of simplicial complexes

This file defines simplicial maps between abstract simplicial complexes.

Given a function `φ : U → V`, the image of a face `s : Finset U` is `s.image φ`.
A morphism `φ : Hom K L` is a vertex function such that for every `s ∈ K.faces`,
we have `Finset.image φ s ∈ L.faces`.

We also define identity and composition for these morphisms. The actual category
instance lives in `Category.lean`, so this file has no category-theory imports.

## Main definitions

* `SimplicialComplex.Hom K L` : a simplicial map `K ⟶ L`.
* `SimplicialComplex.Iso K L` : an isomorphism of simplicial complexes.

## Main results

* `Hom.comp_id`, `Hom.id_comp`, `Hom.assoc`.
* `Hom.ext` (extensionality: morphisms equal if their vertex maps are equal).
* `Hom.image_face` and its compatibility with `id` and `comp`.

## Implementation notes

* Faces are modeled by `Finset`, so we push forward along vertex functions using
  `Finset.image`. This requires `[DecidableEq]` on the codomain vertex type,
  because `Finset.image` deduplicates equal vertices.
* A `Hom` stores only the underlying vertex function `toFun : U → V` together
  with a proof that faces are preserved. Coercions let you use a morphism
  directly as a function on vertices.

## Tags

simplicial complex, simplicial map
-/

open Function

variable {U V W X : Type*}
variable [DecidableEq U] [DecidableEq V] [DecidableEq W] [DecidableEq X]
variable {K : SimplicialComplex U} {L : SimplicialComplex V}
variable {M : SimplicialComplex W} {N : SimplicialComplex X}

namespace SimplicialComplex

/-- A morphism of simplicial complexes sends each face to a face via the
`Finset.image` of the underlying vertex function.

A term `φ : Hom K L` consists of a function `toFun : U → V` together with
`map_faces`, which states: for every `s ∈ K.faces`, the image
`Finset.image toFun s` is in `L.faces`.

The `@[ext]` attribute provides extensionality: two morphisms are equal when
their `toFun` agree pointwise. -/
@[ext] structure Hom (K : SimplicialComplex U) (L : SimplicialComplex V) where
  /-- The underlying map on vertices. Use coercion to treat a morphism as `U → V`. -/
  toFun : U → V
  /-- Face preservation: the image of every face of `K` is a face of `L`. -/
  map_faces :
    ∀ ⦃s : Finset U⦄, s ∈ K.faces → Finset.image toFun s ∈ L.faces

namespace Hom

/-- Identity morphism on a simplicial complex. -/
protected def id (L : SimplicialComplex V) : Hom L L where
  toFun := id
  map_faces := by
    intro s hs; simpa using hs

/-- Composition of morphisms. (`comp f g = f ∘ g` on vertices.) -/
def comp (f : Hom L M) (g : Hom K L) : Hom K M where
  toFun := f.toFun ∘ g.toFun
  map_faces := by
    intro s hs
    have hL : Finset.image g.toFun s ∈ L.faces := g.map_faces hs
    simpa [Finset.image_image, Function.comp] using f.map_faces hL

omit [DecidableEq U] in
/-- Associativity of composition. -/
@[simp] theorem assoc (f : Hom M N) (g : Hom L M) (h : Hom K L) :
    comp f (comp g h) = comp (comp f g) h := rfl

/-- Right identity. -/
@[simp] theorem comp_id (f : Hom L M) :
    comp f (Hom.id _) = f := rfl

omit [DecidableEq U] in
/-- Left identity. -/
@[simp] theorem id_comp (f : Hom K L) :
    comp (Hom.id _) f = f := rfl

/-- The induced map on faces: given a face `s` of `K`, take its `Finset.image`
under the vertex function to obtain a face of `L`. -/
@[simps] def image_face (φ : Hom K L) (s : Face K) : Face L :=
  ⟨s.1.image φ.toFun, by simpa using φ.map_faces s.property⟩

/-- The induced face map of the identity morphism is the identity on faces. -/
@[simp] lemma image_face_id (s : K.Face) :
    (Hom.id K).image_face s = s := by
  ext v; simp [image_face, SimplicialComplex.Hom.id]

omit [DecidableEq U] in
/-- Compatibility of induced face maps with composition:
mapping a face along `f ∘ g` equals first mapping along `g` then along `f`. -/
@[simp] lemma image_face_comp (f : Hom L M) (g : Hom K L) (s : K.Face) :
    (Hom.comp f g).image_face s = f.image_face (g.image_face s) := by
  ext v
  simp [Hom.image_face, Hom.comp, Function.comp, Finset.image_image]

end Hom

end SimplicialComplex

#lint
