/-
Copyright (c) 2025 Xiangyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiangyu Li
-/
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Combinatorics.SimplicialComplex.FacePoset
import Mathlib.Combinatorics.SimplicialComplex.Topology.GeomReal.Basic

/-!
# Face diagram for geometric realisation

For a simplicial complex `X`, we define the **face diagram**
`δ_X : X.faces ⥤ TopCat`. It sends a face `s` to its standard simplex
`Simplex s`, and an inclusion of faces to the extension map
`simplexEmbedding`. In later files we use this diagram to express the
geometric realisation `|X|` as a colimit.

## Main definitions

* `GeomReal.delta` : the face diagram `δ_X : X.faces ⥤ TopCat`.

## Implementation notes

The object part is `s ↦ TopCat.of (Simplex s)`. A morphism `A ⟶ B` is a face inclusion
and is mapped to the continuous extension `simplexEmbedding` between the corresponding
standard simplices.

## Tags

simplicial complex, geometric realisation, diagram, colimit
-/

namespace GeomReal

open CategoryTheory TopCat Simplex SimplicialComplex

variable {U : Type*}
variable (X : SimplicialComplex U)

/-- The face diagram `δ_X : X.faces ⥤ TopCat` that sends a face to its standard simplex and a
face inclusion to the corresponding extension map `simplexEmbedding`. -/
noncomputable def delta :
    X.faces ⥤ TopCat where
  obj s := of (Simplex s.1)
  map {A B} f :=
    ofHom <|ContinuousMap.mk
        (simplexEmbedding (f.down)) (simplexEmbedding_continuous (f.down))
  map_id := by intro A; rfl
  map_comp := by intros A B C f g; rfl

/-- Object-level description of `δ_X`. -/
@[simp] lemma delta_obj (s : X.faces) :
    (delta X).obj s = of (Simplex (U := U) s.1) :=
  rfl

/-- Morphism-level description of `δ_X`. -/
@[simp] lemma delta_map {A B : X.faces} (f : A ⟶ B) :
    (delta X).map f =
      ofHom
        (ContinuousMap.mk (simplexEmbedding (f.down))
                          (simplexEmbedding_continuous (f.down))) :=
  rfl

end GeomReal
