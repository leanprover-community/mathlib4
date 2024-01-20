/- Copyright-/
import Mathlib.Combinatorics.AbstractSimplicialComplex.Decomposability

/-! This files contains the definition of the Euler-Poincaré characteristic of a finite simplicial
complex, and its calculation for a decomposable complex (see
`Mathlinb.Cominnatorics.AbstractSimplicialComplex.Decomposability`).-/

universe u

open BigOperators

variable {α : Type u} {K L : AbstractSimplicialComplex α}

namespace AbstractSimplicialComplex

/-
/-- If `K` is finite, definition of the set of faces of `K` as a finset of `Finset α`.-/
noncomputable def finset_of_faces (hfin : FiniteComplex K) : Finset (Finset α) :=
  Set.Finite.toFinset (Set.finite_coe_iff.mp hfin)

/-- If `K` is finite, definition of the set of facets of `K` as a finset of `Finset α`.-/
noncomputable def finset_of_facets (hfin : FiniteComplex K) : Finset (Finset α) :=
  Set.Finite.toFinset (Set.finite_coe_iff.mp (@Finite.of_injective _ K.faces hfin
  (fun s => ⟨s.1, facets_subset s.2⟩) (fun _ _ h ↦ by
  simp only [Subtype.mk.injEq, SetCoe.ext_iff] at h; exact h)) )

/-- The Euler-Poincaré characteristic of a finite simplicial complex `K` is the sum over all faces
`s` of `K` of `-1` to the dimension of `s` (i.e. `s.card - 1`). -/
noncomputable def EulerPoincareCharacteristic (hfin : FiniteComplex K) : ℤ :=
  ∑ s in (finset_of_faces hfin), (-1 : ℤ)^(s.card - 1)

/-- If two abstract simplicial complexes have the same set of faces, then they have the same
Euler-Poincaré characteristic.-/
lemma EulerPoincareCharacteristic_congr (hKfin : FiniteComplex K) (hLfin : FiniteComplex L)
    (heq : K.faces = L.faces) :
    EulerPoincareCharacteristic hKfin = EulerPoincareCharacteristic hLfin := by
  have heq : finset_of_faces hKfin = finset_of_faces hLfin := by
    ext s
    unfold finset_of_faces
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, heq]
  rw [EulerPoincareCharacteristic, heq, EulerPoincareCharacteristic]
-/

/-- If `K` is finite, definition of the set of faces of `K` as a finset of `K.faces`.-/
noncomputable def finset_of_faces (hfin : FiniteComplex K) : Finset K.faces :=
  @Finset.univ K.faces (@Fintype.ofFinite _ hfin)

/-- If `K` is finite, then `K.facets` is finite.-/
lemma facets_finite (hfin : FiniteComplex K) : Finite K.facets :=
  @Finite.of_injective _ K.faces hfin
  (fun s => ⟨s.1, facets_subset s.2⟩) (fun _ _ h ↦ by
  simp only [Subtype.mk.injEq, SetCoe.ext_iff] at h; exact h)

/-- If `K` is finite, definition of the set of facets of `K` as a finset of `K.facets`.-/
noncomputable def finset_of_facets (hfin : FiniteComplex K) : Finset K.facets :=
  @Finset.univ K.facets (@Fintype.ofFinite _ (facets_finite hfin))

/-- The Euler-Poincaré characteristic of a finite simplicial complex `K` is the sum over all faces
`s` of `K` of `-1` to the dimension of `s` (i.e. `s.card - 1`). -/
noncomputable def EulerPoincareCharacteristic (hfin : FiniteComplex K) : ℤ :=
  ∑ s in @Finset.univ K.faces (@Fintype.ofFinite _ hfin), (-1 : ℤ)^(s.1.card - 1)

/-! The case of decomposable abstract simplicial complexes.-/

variable (R : K.facets → Finset α) (DF : K.faces → K.facets) (hdec : isDecomposition R DF)

/-- The set of `π₀` facets as a set of `Finset α`.-/
def π₀Facets : Set K.facets := {s | isPi0Facet R s}

/-- The set of homology facets as a set of `Finset α`.-/
def homologyFacets : Set (Finset α) := {s | ∃ (hsf : s ∈ K.facets), isHomologyFacet R ⟨s, hsf⟩}

/-- If `K` is finite, then it set of homology facets is finite.-/
lemma HomologyFacets_finite_of_finite (hfin : FiniteComplex K) : (homologyFacets R).Finite := by
  rw [← Set.finite_coe_iff]
  apply @Finite.of_injective _ K.faces hfin
    (fun s => ⟨s.1, facets_subset (by match s.2 with | ⟨hsf,_⟩ => exact hsf)⟩)
  exact fun _ _ heq ↦ by simp only [Subtype.mk.injEq, SetCoe.ext_iff] at heq; exact heq

lemma sum_fiber_pi0Facet [DecidableEq K.facets] (hfin : FiniteComplex K) {s : K.facets}
    (hs : isPi0Facet R s) : ∑ i in Finset.filter (fun t ↦ DF t = s) (finset_of_faces hfin),
    (-1) ^ (i.1.card - 1) = 1 := sorry

lemma sum_fiber_homologyFacet [DecidableEq K.facets] (hfin : FiniteComplex K) {s : K.facets}
    (hs : isHomologyFacet R s) : ∑ i in Finset.filter (fun t ↦ DF t = s) (finset_of_faces hfin),
    (-1) ^ (i.1.card - 1) = (-1)^(s.1.card - 1) := sorry

lemma sum_fiber_boringFacet [DecidableEq K.facets] (hfin : FiniteComplex K) {s : K.facets}
    (hs : ¬ isPi0Facet R s ∧ ¬ isHomologyFacet R s) :
    ∑ i in Finset.filter (fun t ↦ DF t = s) (finset_of_faces hfin), (-1) ^ (i.1.card - 1) = 0:=
  sorry

variable {R DF}
/- Finally we put everything to calculate the Euler-Poincaré characteristic of `K`, for `K` finite
and having a decomposition: it is equal to the cardinality of the set of `π₀` facets plus the sum
over homology facets of the function `fun s ↦ (-1)^(s.card - 1)`.-/
lemma EulerPoincareCharacteristicDecomposable [DecidableEq K.faces] [DecidableEq (Set K.faces)]
    (hfin : FiniteComplex K) :
    EulerPoincareCharacteristic hfin = (Finset.filter (fun (s : K.facets) ↦ isPi0Facet R s)
    (@Finset.univ K.facets (@Fintype.ofFinite _ (facets_finite hfin)))).card +
    ∑ s in Finset.filter (fun (s : K.facets) ↦ isHomologyFacet R s)
    (@Finset.univ K.facets (@Fintype.ofFinite _ (facets_finite hfin))),
    (-1 : ℤ)^(s.1.card - 1) := by
  classical
  letI : Finite (K.faces) := hfin
  letI : Finite (K.facets) := @Finite.of_injective _ K.faces hfin
    (fun s => ⟨s.1, facets_subset s.2⟩) (fun _ _ h ↦ by
    simp only [Subtype.mk.injEq, SetCoe.ext_iff] at h; exact h)
  letI : Fintype K.facets := Fintype.ofFinite K.facets
  unfold EulerPoincareCharacteristic
  rw [← Finset.sum_fiberwise (g := DF)]
  rw [← Finset.sum_add_sum_compl (Finset.filter (fun s ↦ isPi0Facet R s) (finset_of_facets hfin))]
  rw [Finset.sum_congr (s₁ := Finset.filter (fun s ↦ isPi0Facet R s) (finset_of_facets hfin))
    rfl (fun _ hs ↦ by erw [sum_fiber_pi0Facet R DF hfin (Finset.mem_filter.mp hs).2])]
  rw [Finset.sum_const, nsmul_one]
  congr 1
  erw [Finset.compl_filter]
  have hsub : Finset.filter (fun s ↦ isHomologyFacet R s) Finset.univ ⊆
      Finset.filter (fun s ↦ ¬ isPi0Facet R s) Finset.univ := by
    intro s
    simp only [Finset.filter_congr_decidable, Finset.mem_filter, Finset.mem_univ, true_and,
      isHomologyFacet]
    tauto
  rw [← Finset.sum_sdiff hsub]
  rw [Finset.sum_congr (s₁ := Finset.filter (fun s ↦ isHomologyFacet R s) Finset.univ)
    rfl (fun _ hs ↦ by erw [sum_fiber_homologyFacet R DF hfin (Finset.mem_filter.mp hs).2])]
  have heq : Finset.filter (fun s ↦ ¬ isPi0Facet R s) Finset.univ \
      Finset.filter (fun s ↦ isHomologyFacet R s) Finset.univ =
      Finset.filter (fun s ↦ ¬ isPi0Facet R s ∧ ¬ isHomologyFacet R s) Finset.univ := by
    ext s
    simp only [ne_eq, Finset.filter_congr_decidable, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and, not_and]
  rw [heq]
  rw [Finset.sum_congr rfl (fun _ hs ↦ by erw [sum_fiber_boringFacet R DF hfin
    (Finset.mem_filter.mp hs).2])]
  rw [Finset.sum_const, nsmul_zero, zero_add]

#exit

/-- The set of `π₀` facets as a set of `Finset α`.-/
def π₀Facets : Set (Finset α) := {s | ∃ (hsf : s ∈ K.facets), isPi0Facet R ⟨s, hsf⟩}

/-- The set of homology facets as a set of `Finset α`.-/
def homologyFacets : Set (Finset α) := {s | ∃ (hsf : s ∈ K.facets), isHomologyFacet R ⟨s, hsf⟩}

/-- If `K` is finite, then it set of `π₀` facets is finite.-/
lemma π₀Facets_finite_of_finite (hfin : FiniteComplex K) : (π₀Facets R).Finite := by
  rw [← Set.finite_coe_iff]
  apply @Finite.of_injective _ K.faces hfin
    (fun s => ⟨s.1, facets_subset (by match s.2 with | ⟨hsf,_⟩ => exact hsf)⟩)
  exact fun _ _ heq ↦ by simp only [Subtype.mk.injEq, SetCoe.ext_iff] at heq; exact heq

/-- If `K` is finite, then it set of homology facets is finite.-/
lemma HomologyFacets_finite_of_finite (hfin : FiniteComplex K) : (homologyFacets R).Finite := by
  rw [← Set.finite_coe_iff]
  apply @Finite.of_injective _ K.faces hfin
    (fun s => ⟨s.1, facets_subset (by match s.2 with | ⟨hsf,_⟩ => exact hsf)⟩)
  exact fun _ _ heq ↦ by simp only [Subtype.mk.injEq, SetCoe.ext_iff] at heq; exact heq

/-- If `DF` is a map from `K.faces` to `K.facets`, we extend it to a function from `Finset α` to
itself by sending every non-facet to `∅`.-/
noncomputable def extended_DF : Finset α → Finset α := by
  intro s
  by_cases hsf : s ∈ K.faces
  . exact (DF ⟨s, hsf⟩).1
  . exact (∅ : Finset α)

/- Then we construct a bijection between FacetsFinset(K) (that is, the set of facets of K seen as a finset of Finset α)
and the image by DFe (or DF) of FacesFinset(K) (that is, the set of faces of K seen as finset of Finset α)/
We will use Finset.sum_bij with this bijection, so we need it to send the sum of (-1)^(card s-1) over a fiber to DF to the function
Sum_on_DecompositionInterval, which we define using a version of the decomposition interval that is a Finset of Finset α (instead of K.faces).-/

/-- A map from the set of fibers of `extended_DF` to `Finset α`, sending an element of
`extended_DF ⁻¹' s` to `s`.-/
noncomputable def quotient_by_DF_to_finset : Quotient (Setoid.ker (extended_DF DF)) → Finset α :=
  Quotient.lift (fun s => extended_DF DF s)
  (by intro s t hst; change Setoid.Rel (Setoid.ker (extended_DF DF)) s t at hst
      rw [Setoid.ker_def] at hst; exact hst)

/-- If `x` is a fiber of `extended_DF` containing a face of `K`, then its image by the map
`quotient_by_DF_to_finset` is a facet.-/
lemma quotient_by_DF_to_finset_is_facet
    {x : Quotient (Setoid.ker (extended_DF DF))} (hx : x ∈ Set.image
    (@Quotient.mk'' _ (Setoid.ker (extended_DF DF))) K.faces) :
    quotient_by_DF_to_finset DF x ∈ K.facets := by
  unfold quotient_by_DF_to_finset Quotient.lift
  rw [Set.mem_image] at hx
  obtain ⟨s, ⟨hsf, hsx⟩⟩ := (Set.mem_image _ _ _).mp hx
  rw [← hsx]
  erw [Quot.liftBeta (extended_DF DF)
    (fun s t hst ↦ by change Setoid.Rel (Setoid.ker (extended_DF DF)) s t at hst
                      rw [Setoid.ker_def] at hst; exact hst)]
  unfold extended_DF
  simp only [hsf, dite_true, Subtype.coe_prop]

/- The sum of `(-1)^(t.card -1)` on the decomposition interval of `R` corresponding to `s`.
If `s` is not a facet, we set this equal to `0`.-/
noncomputable def sum_decompositionInterval (s : Finset α) : ℤ := by
  by_cases hsf : s ∈ K.facets
  . exact Finset.sum (decompositionInterval R ⟨s, hsf⟩) (fun t => (-1 :ℤ)^(t.1.card - 1))
  . exact (0 : ℤ)

-- TODO: add hypotheses and proof.
/-- The fibers of `extended_DF` are finie.-/
lemma extended_DF_finite_fibers (x : Quotient (Setoid.ker (extended_DF DF))) :
    ((@Quotient.mk'' _ (Setoid.ker (extended_DF DF))) ⁻¹' {x}).Finite := sorry

variable {R DF}
/-- Suppose that `R` and `DF` define a decomposition of `K`. If `x` is a fiber of `extended_DF DF`
that contains a face, if `s` is its image by `extended_DF` (which is known to be a facet by
`quotient_by_DF_to_finset_is_facet`), then the sum of `(-1)^(t.card - 1)` over the faces
`t` in `x` is equal to `sum_decompositionInterval R s`.-/
lemma comparison_sums [DecidableEq (Quotient (Setoid.ker (extended_DF DF)))]
    {x : Quotient (Setoid.ker (extended_DF DF))}
    (hx : x ∈ Set.image (@Quotient.mk'' _ (Setoid.ker (extended_DF DF))) K.faces) :
    ∑ t in  (extended_DF_finite_fibers DF x).toFinset, (-1 : ℤ)^(t.card -1) =
    sum_decompositionInterval R (quotient_by_DF_to_finset DF x) := by
  letI : Setoid (Finset α) := (Setoid.ker (extended_DF DF))
  unfold sum_decompositionInterval
  simp only [quotient_by_DF_to_finset_is_facet DF hx, dite_true]
  obtain ⟨t, ⟨htf, htx⟩⟩ := (Set.mem_image _ _ _).mp hx
  have fiber_of_x_is_faces : ∀ {s : Finset α},
       s ∈ (extended_DF_finite_fibers DF x).toFinset → s ∈ K.faces := by
    intro s hs
    by_contra h
    simp only [← htx, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
      Quotient.eq''] at hs
    change Setoid.Rel _ s t at hs
    rw [Setoid.ker_def] at hs
    simp only [extended_DF, h, dite_false, htf, dite_true] at hs
    exact Finset.nonempty_iff_ne_empty.mp (K.nonempty_of_mem (facets_subset (DF ⟨t, htf⟩).2))
      (Eq.symm hs)
  set i : (s : Finset α) → s ∈ (extended_DF_finite_fibers DF x).toFinset → K.faces :=
    fun s hs ↦ ⟨s, fiber_of_x_is_faces hs⟩
  set j : (s : K.faces) → s ∈ decompositionInterval R ⟨quotient_by_DF_to_finset DF x,
      quotient_by_DF_to_finset_is_facet DF hx⟩ → Finset α := fun s _ ↦ s.1
  rw [Finset.sum_bij' (i := i) (j := j)]
  · intro s hs
    rw [mem_decompositionInterval hdec, ← SetCoe.ext_iff]
    simp only [id_eq]
    unfold quotient_by_DF_to_finset
    have hsf := fiber_of_x_is_faces hs
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hs
    conv_lhs => rw [← hs, Quotient.mk''_eq_mk, Quotient.lift_mk]
    unfold extended_DF
    simp only [hsf, dite_true]
  · intro s hs
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
    rw [mem_decompositionInterval hdec, ← SetCoe.ext_iff] at hs
    simp only [quotient_by_DF_to_finset] at hs
    conv_lhs at hs => rw [← htx, Quotient.mk''_eq_mk, Quotient.lift_mk]
    rw [← htx]
    simp only [Quotient.eq'']
    change Setoid.Rel _ s.1 t
    rw [Setoid.ker_def, hs, extended_DF]
    simp only [Subtype.coe_prop, Subtype.coe_eta, dite_eq_ite, ite_true]
  · exact fun _ _ ↦ by simp only
  · exact fun _ _ ↦ by simp only [Subtype.coe_eta]
  · exact fun _ _ ↦ by simp only

variable (DF)
/-- The map from the set fibers of `extended_DF DF` to `Finset α` induced by `DF` is injective.-/
-- We should not need K to be finite for this.
lemma quotient_by_DF_to_finset_inj (x y : Quotient (Setoid.ker (extended_DF DF)))
    (hx : x ∈ Set.image (@Quotient.mk'' _ (Setoid.ker (extended_DF DF))) K.faces)
    (hy : y ∈ Set.image (@Quotient.mk'' _ (Setoid.ker (extended_DF DF))) K.faces)
    (heq : quotient_by_DF_to_finset DF x = quotient_by_DF_to_finset DF y) : x = y := by
  unfold quotient_by_DF_to_finset Quotient.lift at heq
  obtain ⟨s, ⟨hsf, hsx⟩⟩ := hx
  rw [← hsx] at heq
  erw [Quot.liftBeta (extended_DF DF)
    (by intro s t hst; change Setoid.Rel (Setoid.ker (extended_DF DF)) s t at hst
        rw [Setoid.ker_def] at hst; exact hst)] at heq
  obtain ⟨t, ⟨htf, hty⟩⟩ := hy
  rw [← hty] at heq
  erw [Quot.liftBeta (extended_DF DF)
    (by intro s t hst; change Setoid.Rel (Setoid.ker (extended_DF DF)) s t at hst
        rw [Setoid.ker_def] at hst; exact hst)] at heq
  rw [← hsx, ← hty]
  apply Quotient.sound
  change Setoid.Rel (Setoid.ker (extended_DF DF)) s t
  rw [Setoid.ker_def]
  exact heq

variable {DF}
/- If `R` and `DF` define a decomposition on `K`, then the map from fibers of `extended_DF DF`
containing at least a face to facets of `K` (see `quotient_by_DF_to_finset_is_facet`) is
surjective.-/
lemma quotient_by_DF_to_finset_surj {s : Finset α} (hsf : s ∈ K.facets) :
    ∃ (x : Quotient (Setoid.ker (extended_DF DF))),
    ∃ (_ : x ∈ Set.image (@Quotient.mk'' _ (Setoid.ker (extended_DF DF))) K.faces),
  s = quotient_by_DF_to_finset DF x := by
  letI : Setoid (Finset α) := (Setoid.ker (extended_DF DF))
  exists Quotient.mk (Setoid.ker (extended_DF DF)) s
  simp only [Set.mem_image, exists_prop]
  constructor
  . existsi s
    rw [and_iff_right (facets_subset hsf), Quotient.mk''_eq_mk]
  . unfold quotient_by_DF_to_finset
    simp only [Quotient.lift_mk]
    unfold extended_DF
    simp only [facets_subset hsf, dite_true]
    rw [← isDecomposition_DF_facet hdec ⟨s, hsf⟩]

/- The next step is to write FacetsFinset as a disjoint union of the finset of π₀ facets, the finset of homology facets and the finset of other
facets (which we call "boring facets"). -/
/- Definition of boring facets as the set of Finset α consisting of the non-π₀ non-homology facets.-/
def BoringFacets {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) :
Set (Finset α) := {s | ∃ (hsf : s ∈ K.facets), ¬(IsPi0Facet hdec ⟨s, hsf⟩) ∧ ¬(IsHomologyFacet hdec ⟨s, hsf⟩)}

/- If K is finite, so is its set of boring facets-/
lemma BoringFacets_finite {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (hfin : FiniteComplex K) :
(BoringFacets hdec).Finite := by
  rw [←Set.finite_coe_iff]
  apply @Finite.of_injective _ K.faces hfin (fun s => ⟨s.1, facets_subset (by match s.2 with | ⟨hsf,_⟩ => exact hsf)⟩)
  intro s t heq
  simp only [Subtype.mk.injEq] at heq
  rw [SetCoe.ext_iff] at heq
  exact heq

/- The finset of facets is equal to the union of the finset of boring facets, the finset of π₀ facets and the finset of homology facets.-/
lemma every_facet_is_boring_or_interesting {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (hfin : FiniteComplex K) :
FacetsFinset hfin = Set.Finite.toFinset (BoringFacets_finite hdec hfin) ∪ (Set.Finite.toFinset (π₀Facets_finite hdec hfin)
∪ Set.Finite.toFinset (HomologyFacets_finite hdec hfin)) := by
  ext s
  unfold FacetsFinset
  rw [Finset.mem_union, Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
  unfold BoringFacets π₀Facets HomologyFacets
  simp only [Set.mem_setOf_eq]
  constructor
  . intro hsf
    by_cases IsPi0Facet hdec ⟨s, hsf⟩
    . right; left; exists hsf
    . by_cases IsHomologyFacet hdec ⟨s, hsf⟩
      . right; right; exists hsf
      . left; exists hsf
  . intro hsf
    cases hsf with
    | inr hmed => cases hmed with
                  | inl hpi => exact hpi.1
                  | inr hhom => exact hhom.1
    | inl hbor => exact hbor.1


/- The new two lemmas say that the union of the previous lemma is disjoint.-/
lemma boring_is_not_interesting {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (hfin : FiniteComplex K) :
Disjoint (Set.Finite.toFinset (BoringFacets_finite hdec hfin)) (Set.Finite.toFinset (π₀Facets_finite hdec hfin)
∪ Set.Finite.toFinset (HomologyFacets_finite hdec hfin)) := by
  rw [Finset.disjoint_iff_ne]
  intro s hsbor t htint
  rw [Set.Finite.mem_toFinset] at hsbor
  unfold BoringFacets at hsbor
  rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at htint
  unfold π₀Facets HomologyFacets at htint
  simp only [Set.mem_setOf_eq] at hsbor htint
  by_contra hst
  match hsbor with
  | ⟨hsf, hsbor⟩ => match htint with
                    | Or.inl ⟨_, htpi⟩ => simp_rw [hst] at hsbor
                                          exact hsbor.1 htpi
                    | Or.inr ⟨_, hthom⟩ => simp_rw [hst] at hsbor
                                           exact hsbor.2 hthom


lemma pi0_and_homology_are_disjoint {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (hfin : FiniteComplex K) :
Disjoint (Set.Finite.toFinset (π₀Facets_finite hdec hfin)) (Set.Finite.toFinset (HomologyFacets_finite hdec hfin)) := by
  rw [Finset.disjoint_iff_ne]
  intro s hspi t hthom
  rw [Set.Finite.mem_toFinset] at hspi hthom
  unfold π₀Facets at hspi
  unfold HomologyFacets at hthom
  simp only [Set.mem_setOf_eq] at hspi hthom
  match hspi with
  | ⟨hsf, hspi⟩ => match hthom with
                   | ⟨htf, hthom⟩ => by_contra hst
                                     simp_rw [hst] at hspi
                                     unfold IsHomologyFacet at hthom
                                     exact hthom.1 hspi


/- Now we have to actually calculate some sums. First, if s is boring facet, we show that the sum on the corresponding interval is 0.-/

/- If s is nonempty finset, then the sum of (-1)^{card t} on the powerset of s is 0.-/
lemma AlternatingSumPowerset {s : Finset α} (hsne : s.Nonempty) :
Finset.sum (Finset.powerset s) (fun (t : Finset α) => (-1 : ℤ)^(t.card)) = 0 := by
  have h := Finset.sum_pow_mul_eq_add_pow (-1 : ℤ) (1 : ℤ) s
  rw [←Finset.card_pos] at hsne
  simp only [zero_pow hsne, one_pow, mul_one, add_left_neg] at h
  exact h

/- If s ⊂ t are finsets, then the sum of (-1)^{card x - 1} on the interval [s,t] is 0.-/
lemma Sum_on_FinsetInterval1 {s t : Finset α} (hst : s ⊂ t) : Finset.sum (Finset.Icc s t) (fun s => (-1 :ℤ)^(Finset.card s)) = 0 := by
  rw [@Finset.sum_bij ℤ (Finset α) (Finset α) _ (Finset.Icc s t) (Finset.powerset (t \ s)) (fun s => (-1)^(Finset.card s))
  (fun x => (-1)^(Finset.card x + Finset.card s)) (fun x _ => x \ s)
  (fun _ hx => by simp only [Finset.mem_powerset]
                  simp only [gt_iff_lt, Finset.lt_eq_subset, Finset.mem_Icc, Finset.le_eq_subset] at hx
                  exact Finset.sdiff_subset_sdiff hx.2 (le_refl _)
                  )
  (fun x hx => by simp only
                  simp only [gt_iff_lt, Finset.lt_eq_subset, Finset.mem_Icc, Finset.le_eq_subset] at hx
                  rw [←(Finset.card_sdiff_add_card_eq_card hx.1)])
  (fun x y hx hy heq => by simp only at heq
                           simp only [gt_iff_lt, Finset.lt_eq_subset, Finset.mem_Icc, Finset.le_eq_subset] at hx hy
                           rw [←(Finset.union_sdiff_of_subset hx.1), ←(Finset.union_sdiff_of_subset hy.1)]
                           rw [heq])
  (fun x hx => by exists x ∪ s
                  simp only [gt_iff_lt, Finset.lt_eq_subset, Finset.mem_Icc, Finset.le_eq_subset, exists_prop]
                  simp only [Finset.mem_powerset] at hx
                  constructor
                  . constructor
                    . exact Finset.subset_union_right _ _
                    . rw [←(Finset.union_sdiff_of_subset (le_of_lt hst)), Finset.union_comm]
                      exact Finset.union_subset_union (le_refl _) hx
                  . apply Eq.symm
                    apply Finset.union_sdiff_cancel_right
                    apply Finset.disjoint_of_subset_left hx
                    exact Finset.sdiff_disjoint
                     )
                  ]
  rw [@Finset.sum_congr ℤ (Finset α) (Finset.powerset (t \ s)) (Finset.powerset (t \ s))
  (fun x => (-1 : ℤ)^(Finset.card x + Finset.card s))
  (fun x => (-1 : ℤ)^(Finset.card s) * (-1 : ℤ)^(Finset.card x)) _ rfl
  (fun x _ => by simp only
                 rw [add_comm, pow_add])]
  rw [←Finset.mul_sum, AlternatingSumPowerset, mul_zero]
  rw [Finset.sdiff_nonempty]
  exact not_le_of_lt hst

/- If s is a nonempty finset, then the sum of (-1)^{card x - 1} on the interval (∅,s] is 1.-/
lemma Sum_on_FinsetInterval2 {s : Finset α} (hsne : s.Nonempty) : Finset.sum (Finset.Ioc ∅ s) (fun s => (-1 :ℤ)^(Finset.card s - 1)) = 1 := by
  rw [@Finset.sum_congr ℤ (Finset α) (Finset.Ioc ∅ s) _ (fun s => (-1)^(Finset.card s - 1)) (fun s => (-1 : ℤ) * (-1 : ℤ)^(Finset.card s)) _ rfl
  (fun s hs => by simp only [ge_iff_le, Finset.le_eq_subset, Finset.mem_Ioc, Finset.lt_eq_subset, Finset.empty_ssubset] at hs
                  simp only
                  conv => rhs
                          congr
                          rw [←(pow_one (-1 : ℤ))]
                  rw [←pow_add]
                  conv => lhs
                          rw [←(one_mul ((-1 : ℤ)^(Finset.card s - 1)))]
                          congr
                          rw [←neg_one_pow_two]
                  rw [←pow_add]
                  apply congr_arg
                  rw [add_comm, add_comm 1 _, Nat.add_succ, ←(Nat.succ_eq_add_one (Finset.card s)), Nat.succ_inj', ←Nat.succ_eq_add_one,
                         ←Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos (by rw [←Finset.card_pos] at hs; exact hs.1)]
  )]
  rw [←Finset.mul_sum]
  have hsum := AlternatingSumPowerset hsne
  have hunion : Finset.powerset s = {∅} ∪ Finset.Ioc ∅ s := by
    ext t
    simp only [Finset.mem_powerset, ge_iff_le, Finset.le_eq_subset, Finset.mem_union, Finset.mem_singleton,
  Finset.mem_Ioc, Finset.lt_eq_subset, Finset.empty_ssubset]
    constructor
    . exact fun ht => by by_cases hte : t = ∅
                         . exact Or.inl hte
                         . rw [←ne_eq, ←Finset.nonempty_iff_ne_empty] at hte
                           exact Or.inr ⟨hte, ht⟩
    . exact fun ht => by cases ht with
                         | inl hte => rw [hte]; simp only [Finset.empty_subset]
                         | inr htne => exact htne.2
  have hdisj : Disjoint {∅} (Finset.Ioc ∅ s) := by
    rw [Finset.disjoint_iff_ne]
    intro t ht u hu
    simp only [Finset.mem_singleton] at ht
    by_contra habs
    rw [ht] at habs
    rw [←habs] at hu
    simp only [ge_iff_le, Finset.le_eq_subset, Finset.mem_Ioc, lt_self_iff_false, Finset.empty_subset, and_true] at hu
  rw [←(Finset.disjUnion_eq_union _ _ hdisj)] at hunion
  rw [hunion] at hsum
  rw [Finset.sum_disjUnion hdisj] at hsum
  simp only [Finset.sum_singleton, Finset.card_empty, pow_zero, ge_iff_le, Finset.le_eq_subset] at hsum
  rw [add_comm, ←eq_neg_iff_add_eq_zero] at hsum
  rw [hsum]
  simp only

/- Suppose that we have a decomposition (R,DF). If s is a boring facet, then R(s) is nonempty and strictly contained in s.-/
lemma BoringFacet_image_by_R {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) {s : Finset α}
(hs : s ∈ BoringFacets hdec) : R ⟨s, hs.1⟩ ≠ ∅ ∧ R ⟨s, hs.1⟩ ⊂ s :=  by
  unfold BoringFacets at hs
  simp only [Set.mem_setOf_eq] at hs
  match hs with
  | ⟨hsf, ⟨hs1, hs2⟩⟩ => unfold IsHomologyFacet at hs2
                         push_neg at hs2
                         constructor
                         . unfold IsPi0Facet at hs1
                           by_contra hRe
                           have habs : DecompositionInterval hdec ⟨s, hsf⟩ = Finset.Iic ⟨s, facets_subset hsf⟩ := by
                             ext t
                             rw [DecompositionInterval_def]
                             rw [hRe]
                             simp only [Finset.le_eq_subset, Finset.empty_subset, true_and, Finset.mem_Iic]
                             exact ⟨fun h => h, fun h => h⟩
                           exact hs1 habs
                         . by_contra hRs
                           have heq := eq_of_le_of_not_lt (hdec.1 ⟨s, hsf⟩) hRs
                           have habs : DecompositionInterval hdec ⟨s, hsf⟩ = {⟨s, facets_subset hsf⟩} := by
                             ext t
                             rw [DecompositionInterval_def]
                             rw [heq]
                             simp only [Finset.le_eq_subset, Finset.mem_singleton]
                             constructor
                             . exact fun ⟨hst, hts⟩ => le_antisymm hts hst
                             . exact fun heq => by rw [heq]; exact ⟨le_refl _, le_refl _⟩
                           exact hs2 hs1 habs

/- Suppose that we have a decomposition (R,DF). If s is a boring facet, then the sum on the corresponding decomposition interval is 0.-/
lemma Sum_on_DecompositionInterval_BoringFacet {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{s : Finset α} (hs : s ∈ BoringFacets hdec) : Sum_on_DecompositionInterval R s = 0 := by
  unfold Sum_on_DecompositionInterval
  unfold DecompositionInterval'
  simp only [(BoringFacet_image_by_R hdec hs).1, ge_iff_le, Finset.le_eq_subset, gt_iff_lt, Finset.lt_eq_subset,
  dite_eq_ite, ite_false, dite_eq_right_iff]
  intro hsf
  rw [@Finset.sum_congr ℤ (Finset α) (Finset.Icc (R ⟨s,hsf⟩) s) _ (fun s => (-1 : ℤ)^(Finset.card s - 1))
      (fun s => (-1 : ℤ) * (-1 : ℤ)^(Finset.card s)) _ rfl
      (fun s hsi => by simp only
                       simp only [gt_iff_lt, Finset.lt_eq_subset, Finset.mem_Icc, Finset.le_eq_subset] at hsi
                       have hsne : s.Nonempty := by
                         by_contra hse
                         rw [Finset.not_nonempty_iff_eq_empty] at hse
                         rw [hse, Finset.subset_empty] at hsi
                         exact (BoringFacet_image_by_R hdec hs).1 hsi.1
                       rw [←(one_mul ((-1 : ℤ)^(Finset.card s - 1)))]
                       conv => lhs
                               congr
                               rw [←neg_one_pow_two]
                       rw [←pow_add]
                       conv => rhs
                               congr
                               rw [←(pow_one (-1 : ℤ))]
                       rw [←pow_add]
                       apply congr_arg
                       rw [add_comm, add_comm 1 _, Nat.add_succ, ←(Nat.succ_eq_add_one (Finset.card s)), Nat.succ_inj', ←Nat.succ_eq_add_one,
                         ←Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos (by rw [←Finset.card_pos] at hsne; exact hsne)]
      )]
  rw [←Finset.mul_sum, Sum_on_FinsetInterval1 (BoringFacet_image_by_R hdec hs).2, mul_zero]

/- Suppose that we have a decomposition (R,DF). If s is a π₀ facet, then the corresponding decomposition interval is (∅,s].-/
lemma π₀Facet_interval {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) {s : Finset α}
(hs : s ∈ π₀Facets hdec) : DecompositionInterval' R ⟨s, hs.1⟩ = Finset.Ioc ∅ s := by
  unfold π₀Facets at hs
  match hs with
  | ⟨hsf, hs⟩ => unfold IsPi0Facet at hs
                 ext t
                 rw [ComparisonIntervals hdec]
                 constructor
                 . exact fun ⟨htf, ht⟩ => by rw [hs] at ht
                                             simp only [Finset.mem_Iic, Subtype.mk_le_mk, Finset.le_eq_subset] at ht
                                             simp only [ge_iff_le, Finset.le_eq_subset, Finset.mem_Ioc, Finset.lt_eq_subset, Finset.empty_ssubset]
                                             exact ⟨K.nonempty_of_mem htf, ht⟩
                 . exact fun ht => by simp only [ge_iff_le, Finset.le_eq_subset, Finset.mem_Ioc, Finset.lt_eq_subset, Finset.empty_ssubset] at ht
                                      exists K.down_closed (facets_subset hsf) ht.2 ht.1
                                      rw [hs]
                                      simp only [Finset.mem_Iic, Subtype.mk_le_mk, Finset.le_eq_subset]
                                      exact ht.2

/- Suppose that we have a decomposition (R,DF). If s is a π₀ facet, then the sum on the corresponding decomposition interval is 1.-/
lemma Sum_on_DecompositionInterval_π₀Facet {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{s : Finset α} (hs : s ∈ π₀Facets hdec) : Sum_on_DecompositionInterval R s = 1 := by
  unfold Sum_on_DecompositionInterval
  simp only [hs.1, ge_iff_le, dite_true]
  rw [π₀Facet_interval hdec hs]
  exact Sum_on_FinsetInterval2 (K.nonempty_of_mem (facets_subset hs.1))

/- Suppose that we have a decomposition (R,DF). If s is a homology facet, then the corresponding decomposition interval is {s}.-/
lemma HomologyFacet_interval {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) {s : Finset α}
(hs : s ∈ HomologyFacets hdec) : DecompositionInterval' R ⟨s, hs.1⟩ = {s} := by
  unfold HomologyFacets at hs
  match hs with
  | ⟨hsf, hs⟩ => unfold IsHomologyFacet at hs
                 ext t
                 rw [ComparisonIntervals hdec]
                 constructor
                 . exact fun ⟨htf, ht⟩ => by rw [hs.2] at ht
                                             simp only [Finset.mem_singleton, Subtype.mk.injEq] at ht
                                             rw [ht]
                                             simp only [Finset.mem_singleton]
                 . exact fun ht => by simp only [Finset.mem_singleton] at ht
                                      rw [ht]
                                      exists (facets_subset hsf)
                                      rw [hs.2]
                                      simp only [Finset.mem_singleton]


/- Suppose that we have a decomposition (R,DF). If s is a homology facet, then the sum on the corresponding decomposition interval is
(-1)^{card(s) - 1}.-/
lemma Sum_on_DecompositionInterval_HomologyFacet {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{s : Finset α} (hs : s ∈ HomologyFacets hdec) : Sum_on_DecompositionInterval R s = (-1 : ℤ)^(Finset.card s - 1) := by
  unfold Sum_on_DecompositionInterval
  simp only [hs.1, ge_iff_le, dite_true]
  rw [HomologyFacet_interval hdec hs]
  simp only [ge_iff_le, Finset.sum_singleton]


/- Finally we put everything to calculate the Euler-Poincaré characteristic of K, for K finite and having a decomposition:
it is equal to the cardinality of the set of π₀ facets plus the sum over boring facets of the function s ↦ (-1)^{card(s) - 1}.-/
lemma EulerPoincareCharacteristicDecomposable (hfin : FiniteComplex K) {R : K.facets → Finset α}  {DF : K.faces → K.facets}
(hdec : IsDecomposition R DF) :
EulerPoincareCharacteristic hfin = Finset.card (Set.Finite.toFinset (π₀Facets_finite hdec hfin)) +
Finset.sum (Set.Finite.toFinset (HomologyFacets_finite hdec hfin)) (fun s => (-1 : ℤ)^(Finset.card s - 1)) := by
  unfold EulerPoincareCharacteristic
  rw [Finset.sum_partition (Setoid.ker (DFe DF))]
  rw [@Finset.sum_bij ℤ (Quotient (Setoid.ker (DFe DF))) (Finset α) _ (Finset.image (@Quotient.mk'' _ (Setoid.ker (DFe DF))) (FacesFinset hfin))
     (FacetsFinset hfin) _ (Sum_on_DecompositionInterval R)
     (fun x _ => Quotient_DFe_to_finset DF x) (fun _ hx => Quotient_DFe_to_finset_is_facet DF hfin hx)
     (fun x hx => ComparisonFunctionsonQuotient hdec hfin x hx) (Quotient_DFe_to_finset_inj DF hfin) (Quotient_DFe_to_finset_surj hdec hfin)]
  have hunion := every_facet_is_boring_or_interesting hdec hfin
  rw [←(Finset.disjUnion_eq_union _ _ (boring_is_not_interesting hdec hfin))] at hunion
  rw [hunion]
  rw [Finset.sum_disjUnion]
  rw [←(Finset.disjUnion_eq_union _ _ (pi0_and_homology_are_disjoint hdec hfin))]
  rw [Finset.sum_disjUnion]
  rw [Finset.sum_eq_zero (fun s hs => by rw [Set.Finite.mem_toFinset] at hs
                                         exact Sum_on_DecompositionInterval_BoringFacet hdec hs)]
  rw [zero_add]
  rw [Finset.sum_eq_card_nsmul (fun _ hs => by rw [Set.Finite.mem_toFinset] at hs
                                               exact Sum_on_DecompositionInterval_π₀Facet hdec hs)]
  erw [smul_eq_mul, mul_one]
  rw [@Finset.sum_congr _ _ _ _ (fun s => Sum_on_DecompositionInterval R s) (fun s => (-1 : ℤ)^(Finset.card s - 1)) _ rfl
                           (fun s hs => by rw [Set.Finite.mem_toFinset] at hs
                                           exact Sum_on_DecompositionInterval_HomologyFacet hdec hs)]



end AbstractSimplicialComplex
