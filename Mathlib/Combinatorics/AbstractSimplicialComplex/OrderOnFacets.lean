/- Add copyright.-/
import Mathlib.Combinatorics.AbstractSimplicialComplex.Basic

universe u

variable {α : Type u} {K : AbstractSimplicialComplex α}

/-! We want to study shelling orders on abstract simplicial complexes. Roughly, a shelling order
is a well-order on the facets of `K` such that, if you add the facets according to the order,
you will control the homotopy type of the complex that you are building. They don't always exist,
and when they do it has nice consequences for the topology of `K`. In this file we will introduce
the complex of "old facets": if `r` is a partial order on `K.facets` and `s` is a facet of `K`,
then the corresponding complex of old faces is the set of faces of `s` that are contained in
some facet `t < s` (for the order `r`), i.e. the faces that would have been added before `s` when
the complex is constructed facets by facets followed the order `r`.-/

namespace AbstractSimplicialComplex

/-- If `r` is a partial order on the facets of an abstract simplicial complex `K` and `s` is a
facet of `K`, then the complex of old faces is the subcomplex of `K` whose faces are faces
of `s` that are also faces of a facets smaller than `s` for tge order `r`.-/
@[reducible] def oldFaces (r : PartialOrder K.facets) (s : K.facets) :
    AbstractSimplicialComplex α :=
  subcomplexGenerated (subcomplexGenerated K (Set.image (fun (s : K.facets) => (s.1 : Finset α))
  (@Set.Iio K.facets (@PartialOrder.toPreorder _ r) s))) {s.1}

lemma faces_oldFaces (r : PartialOrder K.facets) (s : K.facets) (t : Finset α) :
    t ∈ oldFaces r s ↔ t ∈ K.faces ∧ t ≤ s.1 ∧ ∃ (u : K.facets), r.lt u s ∧ t ≤ u.1 := by
  erw [faces_subcomplexGenerated, faces_subcomplexGenerated]
  constructor
  · intro ⟨⟨ht, ⟨⟨u, ⟨x, ⟨hxs, hxu⟩⟩⟩, htu⟩⟩, ⟨⟨v, hvs⟩, htv⟩⟩
    rw [and_iff_right ht]
    simp_rw [Set.mem_singleton_iff.mp hvs] at htv
    erw [and_iff_right htv]
    existsi x
    rw [@Set.mem_Iio _ r.toPreorder] at hxs
    rw [and_iff_right hxs]
    simp only at hxu
    rw [hxu]
    exact htu
  · intro ⟨ht, hts, ⟨u, ⟨hus, htu⟩⟩⟩
    constructor
    · rw [and_iff_right ht]
      simp only [Subtype.exists, Set.mem_image, exists_and_right, exists_eq_right, exists_prop]
      existsi u.1, ⟨u.2, (@Set.mem_Iio _ r.toPreorder _ _).mpr hus⟩
      exact htu
    · simp only [Subtype.exists, Set.mem_singleton_iff, exists_prop, exists_eq_left]
      exact hts

/-- For a `r` a partial order on the facets of `K` and `s` a facet of `K`, the complex of old
faces `oldFaces r s` is included in the boundary of s.-/
lemma oldFaces_included_in_boundaryFace (r : PartialOrder K.facets) (s : K.facets) :
    oldFaces r s ≤ boundaryFace ⟨s.1, facets_subset s.2⟩ := by
  intro t ht
  rw [faces_boundaryFace ⟨s.1, facets_subset s.2⟩ t]
  simp only [Subtype.mk_le_mk, Finset.le_eq_subset, ne_eq, Subtype.mk.injEq]
  have htof := (faces_oldFaces r s t).mp ht
  erw [and_iff_right htof.2.1, and_iff_right (K.nonempty_of_mem htof.1)]
  by_contra heq
  rw [heq] at htof
  obtain ⟨⟨u,huf⟩,hu⟩ := htof.2.2
  have hneq := @ne_of_lt _ r.toPreorder _ _ hu.1
  rw [ne_eq, ← SetCoe.ext_iff] at hneq
  exact hneq (Eq.symm (((K.mem_facets_iff s.1).mp s.2).2 (facets_subset huf) hu.2))

/-- For a `r` a partial order on the facets of `K` and `s` a facet of `K`, the complex of old
faces `oldFaces r s` is finite.-/
lemma finite_oldFaces (r : PartialOrder K.facets) (s : K.facets) : FiniteComplex (oldFaces r s) :=
  finite_isLowerSet (oldFaces_included_in_boundaryFace r s)
  (finite_boundaryFace ⟨s.1, facets_subset s.2⟩)

open Nat in
/-- Let `r` be a partial order on the facets of `K` and `s` be a facet of `K`. If the complex of
old faces `oldFaces r s` is nonempty, then `s` has cardinality at least `2`.-/
lemma not_vertex_of_nonempty_oldFaces (r : PartialOrder K.facets) (s : K.facets)
    (hne : (oldFaces r s).faces.Nonempty) : 2 ≤ Finset.card s.1 := by
  obtain ⟨t, htf⟩ := hne
  have htb := (faces_boundaryFace _ t).mp ((oldFaces_included_in_boundaryFace r s) htf)
  rw [and_comm (a := t.Nonempty), ← and_assoc, ← Finset.ssubset_iff_subset_ne] at htb
  exact succ_le_of_lt (lt_of_le_of_lt (succ_le_of_lt (pos_iff_ne_zero.mpr (face_card_nonzero htf)))
    (Finset.card_lt_card htb.1))

end AbstractSimplicialComplex
