/- Add copyright.-/
import Mathlib.Combinatorics.AbstractSimplicialComplex.Basic

universe u

variable {α : Type u} {K : AbstractSimplicialComplex α}

/-! We want to study shelling orders on abstract simplicial complexes. Roughly, a shelling order is a well-order on the facets of K such that,
if you add the facets according to the order, you will control the homotopy type of the complex that you are building. They don't always exist,
and when they do it has nice consequences for the topology of K. In this file we will introduce the complex of "old facets": if r is a partial
order on K.facets and s is a facet of K, then the corresponding complex of old faces is the set of faces of s that are containing in some facet
t < s (for the order r), i.e. the faces that would have been added before s when constructed the complex. -/

namespace AbstractSimplicialComplex

/--Definition of the subcomplex of old faces (determined by a partial order r on facets and a facet s).-/
@[reducible] def OldFaces (r : PartialOrder K.facets) (s : K.facets) : AbstractSimplicialComplex α :=
subcomplexGenerated (subcomplexGenerated K (Set.image (fun (s : K.facets) => (s.1 : Finset α)) (@Set.Iio K.facets
(@PartialOrder.toPreorder _ r) s))) {s.1}

lemma OldFaces_mem (r : PartialOrder K.facets) (s : K.facets) (t : Finset α) : t ∈ OldFaces r s ↔ t ∈ K.faces ∧ t ⊆ s.1 ∧ ∃ (u : K.facets),
r.lt u s ∧ t ⊆ u.1 := by
  erw [faces_subcomplexGenerated, faces_subcomplexGenerated]
  constructor
  . intro ht
    rw [and_iff_right ht.1.1]
    match ht.2 with
    | ⟨⟨u,hu1⟩,hu2⟩ => rw [Set.mem_singleton_iff] at hu1
                       simp_rw [hu1] at hu2
                       rw [and_iff_right hu2]
                       match ht.1.2 with
                       | ⟨⟨u,hu1⟩, hu2⟩ => rw [Set.mem_image] at hu1
                                           cases hu1 with
                                           | intro v hv => exists v
                                                           erw [and_iff_right hv.1]
                                                           simp_rw [←hv.2] at hu2
                                                           exact hu2
  . intro ht
    constructor
    . rw [and_iff_right ht.1]
      match ht.2.2 with
      | ⟨u, hu⟩ => exists ⟨u, by rw [Set.mem_image]; exact ⟨u, ⟨hu.1, rfl⟩⟩⟩; exact hu.2
    . exists ⟨s, Set.mem_singleton _⟩
      exact ht.2.1

/- Sanity check: the complex of old faces is included in the boundary of s.-/
lemma OldFaces_included_in_boundary (r : PartialOrder K.facets) (s : K.facets) : OldFaces r s ≤ Boundary ⟨s.1, facets_subset s.2⟩ := by
  intro t ht
  have htof := (OldFaces_mem r s t).mp ht
  rw [Boundary_mem ⟨s.1, facets_subset s.2⟩ t]
  simp only [Subtype.mk_le_mk, Finset.le_eq_subset, ne_eq, Subtype.mk.injEq]
  rw [and_iff_right htof.2.1, and_iff_right htof.1]
  by_contra heq
  rw [heq] at htof
  match htof.2.2 with
  | ⟨⟨u,huf⟩,hu⟩ => have hsf := s.2
                    rw [mem_facets_iff] at hsf
                    have hneq := @ne_of_lt _ (@PartialOrder.toPreorder _ r ) _ _ hu.1
                    rw [ne_eq, ←SetCoe.ext_iff] at hneq
                    exact hneq (Eq.symm (hsf.2 (facets_subset huf) hu.2))


/- Corollary: the complex of old faces is finite. -/
lemma OldFacesFinite (r : PartialOrder K.facets) (s : K.facets) : FiniteComplex (OldFaces r s) :=
Finite_IsLowerSet (OldFaces_included_in_boundary r s) (BoundaryFinite ⟨s.1, facets_subset s.2⟩)

/- Other corollary: if the complex of old faces is nonempty, then s has cardinality at least 2.-/
lemma OldFacesNonempty_implies_not_vertex (r : PartialOrder K.facets) (s : K.facets) (hne : (OldFaces r s).faces.Nonempty) :
2 ≤ Finset.card s.1 := by
  match hne with
  | ⟨t, htf⟩ => have htb := (OldFaces_included_in_boundary r s) htf
                rw [Boundary_mem] at htb
                change _ ∧ t ⊆ s.1 ∧ t ≠ s.1 at htb
                rw [←Finset.ssubset_iff_subset_ne] at htb
                have hlt := Finset.card_lt_card htb.2
                apply Nat.succ_le_of_lt
                apply lt_of_le_of_lt ?_ hlt
                apply Nat.succ_le_of_lt
                rw [Nat.pos_iff_ne_zero]
                exact face_card_nonzero htf




end AbstractSimplicialComplex
