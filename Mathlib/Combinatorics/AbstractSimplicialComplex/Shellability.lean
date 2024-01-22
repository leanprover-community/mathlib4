/- Copyright.-/
import Mathlib.Combinatorics.AbstractSimplicialComplex.Decomposability

/-! Shellability : an abstract simplicial complex `K` is shellable if there exists a well-order `r`
on its facets such that, for every non-minimal facet `s`, the corresponding complex of old faces
`oldFaces r s` (i.e. the complex of faces that are contained in a facet smaller than `s` for `r`)
is empty or pure of dimension `s.card - 2`. If `r` is a linear order on the facets of `K`, we
define `isShellingOrder r` to mean that `r` is such an order.

We have two goals in this file: to show that a shellable complex is decomposable, and to show that
a decomposable complex with a compatible well-order on its facets is shellable.-/

universe u

open AbstractSimplicalComplex

variable {α : Type u} {K : AbstractSimplicialComplex α} [DecidableEq α]

namespace AbstractSimplicialComplex

/-- Let `r` be a linear order on the facets of `K`. It is called a shelling order if it is a
well-order and if, for every facet `s`, the corresponding complex of old faces `oldFaces r s`
is empty or pure of dimension `s.card - 2`.-/
def isShellingOrder (r : LinearOrder K.facets) : Prop :=
  (WellFounded r.lt) ∧ ∀ (s : K.facets), (oldFaces r.toPartialOrder s).faces = ∅ ∨
  (Pure (oldFaces r.toPartialOrder s) ∧ (oldFaces r.toPartialOrder s).dimension =
  Finset.card s.1 - 2)

/-! A shellable complex is decomposable.-/

lemma orderOnFacets_restriction_aux (r : PartialOrder K.facets) (s : K.facets) :
    {a : α | a ∈ s.1 ∧ (Finset.erase s.1 a) ∈ (oldFaces r s).faces}.Finite := by
  apply Set.Finite.subset (Finset.finite_toSet s)
  rw [Set.subset_def]
  exact fun _ ha => ha.1

/-- Given a partial order `r` on the facets of `K`, we define the "restriction map" as the map
sending a facet `s` to the finset of elements `a` of `s` such that `s.erase a` is in
`oldFaces r s`. (We know that this set is finite by `orderOnFacets_restriction_aux`.)-/
noncomputable def orderOnFacets_restriction (r : PartialOrder K.facets) (s : K.facets) :=
  Set.Finite.toFinset (orderOnFacets_restriction_aux r s)

lemma orderOnFacets_restriction_def (r : PartialOrder K.facets) (s : K.facets) (a : α) :
    a ∈ orderOnFacets_restriction r s ↔ a ∈ s.1 ∧ Finset.erase s.1 a ∈ (oldFaces r s).faces := by
  unfold orderOnFacets_restriction
  rw [Set.Finite.mem_toFinset]
  simp only [Set.mem_setOf_eq]

/-- If `r` is a partial order on the facets of `K`, `s` is a facet and `a` is an element of `α`,
then `a` is in `orderOnFacets_restriction r s` if and only `a ∈ s`, `s ≠ {a}` and there exists a
facet `u` smaller than `s` for the order `r` and such that `s.erase a ⊆ u`. -/
lemma mem_orderOnFacets_restriction (r : PartialOrder K.facets) (s : K.facets) (a : α) :
    a ∈ orderOnFacets_restriction r s ↔ a ∈ s.1 ∧ s.1 ≠ {a} ∧ (∃ (u : K.facets),
    r.lt u s ∧ Finset.erase s.1 a ⊆ u.1) := by
  rw [orderOnFacets_restriction_def]
  simp only [ne_eq, Subtype.exists, exists_and_right, and_congr_right_iff]
  intro _
  erw [faces_oldFaces]
  constructor
  · intro ha
    have hne := K.nonempty_of_mem ha.1
    rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.erase_eq_empty_iff, not_or] at hne
    rw [and_iff_right hne.2]
    obtain ⟨u, ⟨hus, hau⟩⟩ := ha.2.2
    exists u
    simp only [Subtype.coe_eta, Subtype.coe_prop, exists_prop, true_and]
    exact ⟨hus, hau⟩
  · intro ha
    have hne : (Finset.erase s.1 a).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.erase_eq_empty_iff, not_or, ← ne_eq,
        ← Finset.nonempty_iff_ne_empty]
      exact ⟨K.nonempty_of_mem (facets_subset s.2), ha.1⟩
    have has : Finset.erase s.1 a ⊆ s.1 := Finset.erase_subset _ _
    rw [and_iff_right (K.down_closed (facets_subset s.2) has hne)]
    erw [and_iff_right has]
    obtain ⟨u, ⟨⟨huf, hus⟩, hau⟩⟩ := ha.2; exists ⟨u, huf⟩

/-- If `r` is a partial order on the facets of `K` and `s` is a facet, then
`orderOnFacets_restriction r s ≤ s`.-/
lemma orderOnFacets_restriction_smaller (r : PartialOrder K.facets) (s : K.facets) :
    orderOnFacets_restriction r s ⊆ s.1 := by
  rw [Finset.subset_iff]
  intro a haR
  rw [orderOnFacets_restriction_def] at haR
  exact haR.1

/-- If `r` is a partial order on the facets of `K`, `s` is a facet and `t` is a face such that
`t ⊆ s` and `orderOnFacets_restriction r s` is not contained in `t`, then `t` is a face of
`oldFaces r s`. -/
lemma oldFace_of_not_contains_restriction (r : PartialOrder K.facets) (s : K.facets) (t : K.faces)
    (hts : t.1 ⊆ s.1) (htR : ¬ orderOnFacets_restriction r s ⊆ t.1) :
    t.1 ∈ (oldFaces r s).faces := by
  rw [Finset.not_subset] at htR
  obtain ⟨a, ⟨haR, hat⟩⟩ := htR
  rw [orderOnFacets_restriction_def] at haR
  apply (oldFaces r s).down_closed haR.2 ?_ (K.nonempty_of_mem t.2)
  rw [Finset.subset_erase]
  exact ⟨hts, hat⟩

/-- If `r` is a partial order on the facets of `K`, `s` is a facet such that the complex of old
faces `oldFaces r s` is pure of dimension `s.card - 2`, then faces of `oldFaces r s` do not
contain `orderOnFacets_restriction r s`.-/
lemma oldFace_does_not_contain_restriction (r : PartialOrder K.facets) (s : K.facets)
    (hof : Pure (oldFaces r s) ∧ (oldFaces r s).dimension = Finset.card s.1 - 2) {t : Finset α}
    (htof : t ∈ (oldFaces r s).faces) : ¬ orderOnFacets_restriction r s ⊆ t := by
  obtain ⟨⟨u, huf⟩, hu⟩ := exists_facet_of_wf
    (@Finite.to_wellFoundedGT _ (finite_oldFaces r s) _).wf ⟨t, htof⟩
  have hus : u ⊆ s.1 :=
    ((faces_oldFaces r s u).mp ((mem_facets_iff _ u).mp huf).1).2.1
  have hcard : u.card = s.1.card - 1 := by
    have hdim := hof.1 huf
    rw [hof.2] at hdim
    erw [← ENat.coe_sub, WithTop.coe_eq_coe, Nat.cast_inj] at hdim
    apply_fun Nat.succ at hdim
    rw [← Nat.pred_eq_sub_one, Nat.succ_pred (face_card_nonzero (facets_subset huf)),
      ← Nat.succ_sub (not_vertex_of_nonempty_oldFaces r s ⟨u, facets_subset huf⟩),
      Nat.succ_eq_add_one, Nat.add_sub_add_right] at hdim
    exact hdim
  have hdiff : Finset.card (s.1 \ u) = 1 := by
    rw [Finset.card_sdiff hus, hcard, Nat.sub_sub_self]
    rw [Nat.succ_le_iff, Nat.pos_iff_ne_zero]
    exact face_card_nonzero (facets_subset s.2)
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hdiff
  have hau : u = s.1 \ {a} := by
    have h := Finset.sdiff_sdiff_eq_self hus
    rw [ha] at h
    exact Eq.symm h
  have haR : a ∈ orderOnFacets_restriction r s := by
    rw [orderOnFacets_restriction_def]
    have has : a ∈ s.1 := by
      rw [← Finset.singleton_subset_iff, ← ha]
      simp only [Finset.sdiff_subset]
    rw [and_iff_right has, Finset.erase_eq, ← hau]
    exact facets_subset huf
  rw [Finset.not_subset]
  exists a
  rw [and_iff_right haR]
  by_contra hat
  rw [← Finset.erase_eq] at hau
  have hau' := hu hat
  simp only at hau'
  rw [hau] at hau'
  exact Finset.not_mem_erase a s.1 hau'

/-! "Distinguished facet" map.-/

variable (K)

/-- We say that `K` satusfies `existsFacet` if every face is contained in a facet.-/
def existsFacet : Prop :=
  ∀ (t : K.faces), ∃ (s : K.facets), t.1 ⊆ s.1

variable {K}

/-- If the relation `fun s t ↦ t < s` is well-founded on `K.faces`, then `K` satisfies condition
existsFacet.-/
lemma existsFacet_of_wf (hwf : WellFounded (fun (s t : K.faces) ↦ t < s))  : existsFacet K := by
  intro s
  match exists_facet_of_wf hwf s with
  | ⟨t, htf⟩ => exists t

/-- If `r` is a well-order on the facets of `K`, the "distinguished facet" map sends a face `s`
to the `r`-smallest facet containing `s`. For this to exist, we must assume that every face
is contained in a facet.-/
noncomputable def orderOnFacets_distinguishedFacet (r : LinearOrder K.facets)
    (hr : WellFounded r.lt) (he : existsFacet K)
    (s : K.faces) : K.facets :=
  WellFounded.min hr {t : K.facets | s.1 ⊆ t.1} (by match he s with
                                                  | ⟨t, _⟩ => exists t)
/-- If the map `orderOnFacets_distinguishedFacet` is well-defined, then, for every face `t`
of `K`, we have `t ≤ orderOnfacets_distinguishedFacet r t`.-/
lemma orderOnFacets_distinguishedFacet_bigger (r : LinearOrder K.facets) (hr : WellFounded r.lt)
    (he : existsFacet K) (s : K.faces) : s.1 ⊆ (orderOnFacets_distinguishedFacet r hr he s).1 :=
  WellFounded.min_mem hr {t : K.facets | s.1 ⊆ t.1} (by match he s with
                                                       | ⟨t, _⟩ => exists t)

/-- If the map `orderOnFacets_distinguishedFacet` is well-defined, then, for every face `t`
of `K`, the facet `orderOnfacets_distinguishedFacet r t` is the `r`-smallest facet containing `t`.-/
lemma orderOnFacets_distinguishedFacet_smallest (r : LinearOrder K.facets) (hr : WellFounded r.lt)
    (he : existsFacet K) (s : K.faces) (u : K.facets) (hus : s.1 ⊆ u.1) :
    r.le (orderOnFacets_distinguishedFacet r hr he s) u := by
  have hnlt := WellFounded.not_lt_min hr {t : K.facets | s.1 ⊆ t.1} (by match he s with
                                                                         | ⟨t, _⟩ => exists t) hus
  rw [lt_iff_not_le, not_not] at hnlt
  exact hnlt

/- If `r` is a shelling order on the facets of `K` and `K` satisfies `existsFacet`, then the
maps `orderOnFacets_restriction r` and `orderOnFacets_distinguishedFacet r` form a decomposition
of `K`.-/
lemma isDecomposition_of_isShellingOrder {r : LinearOrder K.facets} (hshel : isShellingOrder r)
    (he : existsFacet K) : isDecomposition (orderOnFacets_restriction r.toPartialOrder)
    (orderOnFacets_distinguishedFacet r hshel.1 he) := by
  unfold isDecomposition
  rw [and_iff_right (fun s => orderOnFacets_restriction_smaller r.toPartialOrder s)]
  intro s t
  rw [← not_iff_not]
  constructor
  · intro hst
    by_cases hsub : s.1 ⊆ t.1
    · rw [and_comm, not_and] at hst
      have hsof := oldFace_of_not_contains_restriction r.toPartialOrder t s hsub (hst hsub)
      erw [faces_oldFaces] at hsof
      obtain ⟨u,⟨hut, hsu⟩⟩ := hsof.2.2
      by_contra habs
      rw [habs] at hut
      exact @not_le_of_lt _ r.toPartialOrder.toPreorder _ _ hut
        (orderOnFacets_distinguishedFacet_smallest r hshel.1 he s u hsu)
    · by_contra habs
      rw [habs] at hsub
      exact hsub (orderOnFacets_distinguishedFacet_bigger r hshel.1 he s)
  · intro hst
    rw [not_and_or]
    by_cases hsub : s.1 ⊆ t.1
    · apply Or.inl
      have hsof : s.1 ∈ (oldFaces r.toPartialOrder t).faces := by
        erw [faces_oldFaces]
        rw [and_iff_right s.2]; erw [and_iff_right hsub]
        exists orderOnFacets_distinguishedFacet r hshel.1 he s
        erw [and_iff_left (orderOnFacets_distinguishedFacet_bigger r hshel.1 he s)]
        by_contra habs
        rw [lt_iff_not_le, not_not] at habs
        exact hst (r.le_antisymm _ _ habs (orderOnFacets_distinguishedFacet_smallest r
          hshel.1 he s t hsub))
      have hofne : (oldFaces r.toPartialOrder t).faces ≠ ∅ := by
        rw [← Set.nonempty_iff_ne_empty]
        exists s.1
      have hpure := hshel.2 t
      rw [or_iff_right hofne] at hpure
      exact oldFace_does_not_contain_restriction r.toPartialOrder t hpure hsof
    · exact Or.inr hsub

/-- Suppose that we have maps `R` and `DF` that form a decomposition of `K` (in the sense
of `isDecomposition`), and let `r` be a well-order on the facets of `K` that is compatible with
`DF` (in the sense of `isCompatible`). Then `r` is a shelling order.-/
lemma isShellingOrder_of_compatible {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) {r : LinearOrder K.facets}
    (hcomp : compatibleOrder DF r.toPartialOrder) (hr : WellFounded r.lt) :
    isShellingOrder r := by
  unfold isShellingOrder
  rw [and_iff_right hr]
  intro s
  by_cases hof : (oldFaces r.toPartialOrder s).faces = ∅
  · exact Or.inl hof
  · rw [← ne_eq, ← Set.nonempty_iff_ne_empty] at hof
    exact Or.inr ⟨isDecomposition_oldFaces_pure hdec hcomp s,
      isDecomposition_dimension_oldFaces hdec hcomp s hof⟩

/-- A decomposable complex satisfies condition `existsFacet`.-/
lemma existsFacet_of_isDecomposition {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) : existsFacet K :=
  fun s => by exists (DF s); exact isDecomposition_DF_bigger_than_source hdec s

/-- Suppose that we have maps `R` and `DF` that form a decomposition of `K` (in the sense
of `isDecomposition`), and let `r` be a linear order on the facets of `K` that is compatible with
`DF` (in the sense of `isCompatible`). Then the map `orderOnFacets_distinguishedFacet r` is
equal to `DF`.-/
lemma distinguishedFacet_of_compatible {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) {r : LinearOrder K.facets}
    (hcomp : compatibleOrder DF r.toPartialOrder) (hr : WellFounded r.lt) :
    orderOnFacets_distinguishedFacet r hr (existsFacet_of_isDecomposition hdec) = DF := by
  funext s
  have h1 := orderOnFacets_distinguishedFacet_smallest r hr (existsFacet_of_isDecomposition hdec)
    s (DF s) (isDecomposition_DF_bigger_than_source hdec s)
  have h2 : s.1 ∉ oldFaces r.toPartialOrder (DF s) := by
    rw [compatibleOrder_oldFaces hcomp]
    exact isDecomposition_DF_bigger_than_source hdec s
    exact isDecomposition_DF_bigger_than_source hdec s
  rw [faces_oldFaces] at h2
  push_neg at h2
  apply @eq_of_le_of_not_lt _ r.toPartialOrder _ _ h1
  by_contra habs
  exact h2 s.2 (isDecomposition_DF_bigger_than_source hdec s) (orderOnFacets_distinguishedFacet
    r hr (existsFacet_of_isDecomposition hdec) s) habs
    (orderOnFacets_distinguishedFacet_bigger r hr (existsFacet_of_isDecomposition hdec) s)

/-- Suppose that we have maps `R` and `DF` that form a decomposition of `K` (in the sense
of `isDecomposition`), and let `r` be a linear order on the facets of `K` that is compatible with
`DF` (in the sense of `isCompatible`). Then the map `orderOnFacets_restriction r` defines the same
intervals as `R`.-/
lemma decompositionIntervals_of_compatible {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) {r : LinearOrder K.facets}
    (hcomp : compatibleOrder DF r.toPartialOrder) (hr : WellFounded r.lt) (s : K.facets) :
    decompositionInterval R s = decompositionInterval
    (orderOnFacets_restriction r.toPartialOrder) s := by
  ext t
  rw [mem_decompositionInterval hdec, mem_decompositionInterval
    (isDecomposition_of_isShellingOrder (isShellingOrder_of_compatible hdec hcomp hr)
    (existsFacet_of_isDecomposition hdec)),
    distinguishedFacet_of_compatible hdec hcomp hr]

end AbstractSimplicialComplex
