/-
Copyright (c) 2025 Xiangyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiangyu Li
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Combinatorics.SimplicialComplex.Hom
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Face poset (as a thin category) of a simplicial complex

For a simplicial complex `X` on vertices `α`, the set of faces `X.faces : Set (Finset α)`
carries the natural order by inclusion of the underlying finsets. We view the subtype `X.faces`
as a poset/partial order and promote it to a **thin category**, with a unique morphism `A ⟶ B`
exactly when `A ≤ B` (i.e. `↑A ⊆ ↑B`). This category will index the geometric realisation diagram.

## Main definitions

* `Category (X.faces)` — a thin category where `Hom A B` is inhabited iff `A ≤ B`.
* `SimplicialComplex.Hom.face_functor (φ : Hom X Y)` — the functor on face categories
  induced by a simplicial map, sending a face `s` to its image `φ.image_face s`.

## Implementation notes

* Morphisms are implemented as `PLift ((A : Finset α) ⊆ (B : Finset α))`.
* Identities and composition use `subset_rfl` and `subset_trans`.
* This file stays lightweight: only `Category.Basic` and `Functor.Basic` are imported.

## Tags

simplicial complex, face poset, thin category, combinatorics
-/

namespace SimplicialComplex

variable {α β : Type*}
variable [DecidableEq α] [DecidableEq β]
variable {X : SimplicialComplex α} {Y : SimplicialComplex β}

omit [DecidableEq α] in
/-- Simplify `A ≤ B` to inclusion of the underlying finsets. -/
@[simp] lemma face_le_iff {A B : X.faces} :
    (A ≤ B) ↔ ((A : Finset α) ⊆ (B : Finset α)) := Iff.rfl

open CategoryTheory

/-- A thin category structure on `X.Face`, with at most one morphism `A ⟶ B` when `A ≤ B`. -/
instance : Category (X.faces) where
  Hom A B := PLift ((A : Finset α) ⊆ (B : Finset α))
  id _ := ⟨subset_rfl⟩
  comp f g := ⟨subset_trans f.down g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The functor on face-posets induced by a simplicial map. -/
noncomputable def Hom.face_functor (φ : Hom X Y) :
    X.faces ⥤ Y.faces where
  obj s := Hom.image_face φ s
  map {A B} f := by
    refine ⟨?subset⟩
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hxA, rfl⟩
    have hxB : (x : α) ∈ (B : Finset α) := f.down hxA
    exact Finset.mem_image.mpr ⟨x, hxB, rfl⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end SimplicialComplex
