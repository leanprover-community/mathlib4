/-
Copyright (c) 2025 Xiangyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiangyu Li
-/
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Combinatorics.SimplicialComplex.Topology.GeomReal.Diagram
import Mathlib.Combinatorics.SimplicialComplex.Topology.GeomReal.Basic


/-!
# Geometric realisation as a colimit

We show that the geometric realisation `|X|` of a simplicial complex `X`, equipped with the
coherent (final) topology from the inclusions of standard simplices, is a **colimit** of the
face diagram `δ_X : X.faces ⥤ TopCat`.

## Main definitions

* `GeomReal.geom_real_cocone` : the cocone from `δ_X` to `|X|`.
* `GeomReal.desc`   : the mediating map from `|X|` to any cocone on `δ_X`.

## Main statements

* `GeomReal.geom_real_is_colimit`  : `geom_real_cocone X` is a colimit cocone.
* `GeomReal.geom_real_colimit_iso` : the canonical isomorphism `colimit (δ_X) ≅ |X|`.

## Implementation notes

The legs of the cocone are the inclusion maps `Simplex s → |X|`.
The mediating map to a cocone `s` is defined by sending a point `p : |X|`
to the value of the leg at the face supporting `p`, applied to the canonical
`toSimplex p`. Naturality is reduced to the compatibility of inclusions with
`simplexEmbedding`.

## Tags

simplicial complex, geometric realisation, colimit, category theory
-/

open CategoryTheory CategoryTheory.Limits

variable {U : Type*} [DecidableEq U]
variable {X : SimplicialComplex U}

namespace GeomReal

/-- The cocone from the face diagram `δ_X` to the geometric realisation `|X|`.

The vertex is `TopCat.of (GeomReal X)`, and the leg at a face `s` is the inclusion
`Simplex s → |X|`. Naturality follows from the fact that inclusions commute with
`simplexEmbedding` along face inclusions. -/
noncomputable def geom_real_cocone (X : SimplicialComplex U) :
    Cocone (delta X) :=
{ pt := TopCat.of (GeomReal X)
  ι :=
  { app := fun s =>
      TopCat.ofHom <|ContinuousMap.mk (inclusion s) (inclusion_continuous s)
    naturality := by
      intro A B f
      ext p
      simp [delta_map] } }

/-- The mediating map `|X| → s.pt` for a cocone `s : Cocone (δ_X)`.

Given `p : |X|` supported on a face `A ≤ X`, we apply the leg `s.ι.app A`
to the canonical `toSimplex p : Simplex A`. -/
noncomputable def desc {X : SimplicialComplex U} (s : Cocone (delta X)) :
    GeomReal X → s.pt := fun p => (s.ι.app ⟨p.face, p.face_mem⟩) (toSimplex p)

/-- Compatibility of `desc` with face inclusions.

Precomposing `desc s` with the inclusion of a face `t` equals the
corresponding leg of the cocone `s`. -/
lemma desc_comp_inclusion
    {X : SimplicialComplex U} (s : Cocone (delta X)) (t : X.faces) :
    (desc s) ∘ inclusion t = fun p => (s.ι.app t) p := by
  funext p
  set A' : Finset U := Simplex.supportFinset p
  have hsub : A' ⊆ t.1 := by
    intro v hv; exact (Finset.mem_filter.1 hv).1
  have hA' : (A' : Finset U) ∈ X.faces :=
    X.downward_closed t.property hsub
  let A : X.faces := ⟨A', hA'⟩
  let hAt : A ⟶ t := ⟨hsub⟩
  dsimp [desc, Function.comp]
  have hto :
      toSimplex (inclusion t p)
        = Simplex.shrink p := toSimplex_inclusion t p
  have hnat := s.ι.naturality hAt
  have hpoint :
      (s.ι.app A) (Simplex.shrink p)
        = (s.ι.app t)
            ((delta X).map hAt (Simplex.shrink p)) := by
    have := congrArg (fun (f : (delta X).obj A ⟶ _) =>
        (ConcreteCategory.hom f) (Simplex.shrink p)) hnat.symm
    simpa using this
  have hδ :
      (delta X).map hAt (Simplex.shrink p)
        = Simplex.simplexEmbedding hAt.down (Simplex.shrink p) := rfl
  have hse :
      Simplex.simplexEmbedding hAt.down (Simplex.shrink p) = p :=
    Simplex.simplexEmbedding_shrink p
  simpa [hto, hδ, hse] using hpoint

/-- Continuity of the mediating map `desc`. -/
lemma desc_continuous {X : SimplicialComplex U} (s : Cocone (delta X)) :
    Continuous (desc s) := by
  refine
    (continuous_iff (desc s)).2 ?_
  intro t
  change Continuous ((desc s) ∘ inclusion t)
  simpa [desc_comp_inclusion s t]
    using (s.ι.app t).hom.continuous

/-- `|X|` is a colimit of the face diagram `δ_X`.

This provides the universal property: for any cocone `s` on `δ_X`, there is a
unique continuous map `|X| → s.pt` compatible with the cocone legs. -/
noncomputable def geom_real_is_colimit (X : SimplicialComplex U) :
    IsColimit (geom_real_cocone X) :=
{ desc := fun s =>
    TopCat.ofHom <|
      ContinuousMap.mk
        (desc s)
        (desc_continuous s)
  fac := by
    intro s A
    ext p
    change desc s (inclusion A p) = (s.ι.app A) p
    set A' : X.faces :=
      ⟨(inclusion A p).face,
        (inclusion A p).face_mem⟩
    have hA' : (A' : Finset U) ⊆ (A : Finset U) := by
      intro v hv
      have hv_ne : p.weight v ≠ 0 := by
        have hv' : (inclusion A p).weight v ≠ 0 :=
          ((inclusion A p).support_eq v).1 hv
        simpa [inclusion] using hv'
      have hv_supp : v ∈ Simplex.supportFinset p :=
        (Simplex.mem_supportFinset p).2 hv_ne
      exact (Finset.mem_filter.1 hv_supp).1
    let f : A' ⟶ A := ⟨hA'⟩
    have nat :=
      congrArg
        (fun g =>
          (ConcreteCategory.hom g)
            (toSimplex (inclusion A p)))
        (s.ι.naturality f)
    simp [delta_map, toSimplex_inclusion] at nat
    simpa using nat.symm
  uniq := by
    intro s m hm
    ext p
    have h :=
      congrArg
        (fun k => (ConcreteCategory.hom k) (toSimplex p))
        (hm ⟨p.face, p.face_mem⟩)
    simpa [geom_real_cocone, desc, inclusion_toSimplex] using h}

/-- The canonical isomorphism `colimit δₓ ≅ |X|` in `TopCat`. -/
noncomputable def geom_real_colimit_iso (X : SimplicialComplex U) :
    colimit (delta X) ≅ TopCat.of (GeomReal X) :=
  IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit _) (geom_real_is_colimit X)

end GeomReal
