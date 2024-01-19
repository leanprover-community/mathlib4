/- Copyright.-/
import Mathlib.Combinatorics.AbstractSimplicialComplex.FacePoset
import Mathlib.Combinatorics.AbstractSimplicialComplex.OrderOnFacets

universe u

variable {α : Type u} {K : AbstractSimplicialComplex α}

/-! An abstract simplicial `K` on `α` is called decomposable if there exists a map `R` (for
"restriction") from the set of facets of `K` to the set of finsets of `α` such that
`R s ⊆ s.1` for every `s` and the set of faces of `K` is the disjoint union of the intervals
`Set.Icc (R s) s`. (In particular, `R s` will always be empty or a face.) For every face `t` of
`K`, there is then a unique facet `s` such that `t` is in `Set.Icc (R s) s`. This defines a map
`DF` (for "distinguished facet") from the set of faces of `K` to the set of facets of `K`.

We will actually define decomposability using the maps `R` and `DF` rather than the disjoint
union decomposition, as it makes the definition simpler to manipulate. The map `R` uniquely
determines the map `DF`, and the map `DF` uniquely determines the intervals `Set.Icc (R s) s`
(but not map `R`, as `Set.Icc s s` and `Set.Icc ∅ s` if `s` is a `0`-dimensional face). -/

namespace AbstractSimplicialComplex

/-- Definition of decomposability : the conditions on a couple of maps `(R, DF)` as in the
introduction for it to define a decomposition of `K`: `R s ⊆ s.1` for every facet `s` and, for
every face `t` and every facet `s`, we have `R s ≤ t` if and only if `s ≤ t`.-/
def isDecomposition (R : K.facets → Finset α)  (DF : K.faces → K.facets) : Prop :=
  (∀ (s : K.facets), R s ⊆ s.1) ∧
  (∀ (s : K.faces) (t : K.facets), (R t ⊆ s.1 ∧ s.1 ⊆ t.1) ↔ t = DF s)

/-- If `(R, DF)` defines a decomposition of `K`, then `DF t` contains `t` for every face `t`.-/
lemma isDecomposition_DF_bigger_than_source {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) (t : K.faces) : t.1 ⊆ (DF t).1 :=
  ((hdec.2 t (DF t)).mpr rfl).2

/-- The conditions of `isDecomposition` imply that the set of faces of `K` is the union of the
intervals `Set.Icc (R s) s`.-/
lemma isDecomposition_union_intervals_eq_top {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) (s : K.faces) : ∃ (t : K.facets), R t ⊆ s.1 ∧ s.1 ⊆ t.1 :=
  ⟨DF s, (hdec.2 s (DF s)).mpr rfl⟩

/-- The conditions of `isDecomposition` imply that the intervals `Set.Icc (R s) s` are
pairwise disjoint.-/
lemma isDecomposition_disjoint_intervals {R : K.facets → Finset α} {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) (t : K.faces) {s₁ s₂ : K.facets} (hts₁ : R s₁ ⊆ t.1 ∧ t.1 ⊆ s₁.1)
    (hts₂ : R s₂ ⊆ t.1 ∧ t.1 ⊆ s₂.1) : s₁ = s₂ :=
  Eq.trans ((hdec.2 t s₁).mp hts₁) (Eq.symm ((hdec.2 t s₂).mp hts₂))

/-- If `R` and `DF` define a decomposition of `K`, then the map `DF` is the identity on facets.-/
lemma isDecomposition_DF_facet {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) (s : K.facets) : s = DF ⟨s.1, facets_subset s.2⟩ :=
  (hdec.2 ⟨s.1, facets_subset s.2⟩ s).mp ⟨hdec.1 s, by simp only [subset_refl]⟩

/--  If `R` and `DF` define a decomposition of `K`, then the image of a facet by `R` is either
empty or a face.-/
lemma isDecomposition_image_of_R {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) {s : K.facets} (hne : R s ≠ ∅) : R s ∈ K.faces :=
  K.down_closed (facets_subset s.2) (hdec.1 s)
  (by rw [←Finset.nonempty_iff_ne_empty] at hne; exact hne)

/-- Variant of the lemma `isDecomposition_image_of_R` where the conclusion is expressed as an
`or`.-/
lemma isDecomposition_image_of_R' {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) (s : K.facets) : R s = ∅ ∨ R s ∈ K.faces := by
  by_cases he : R s = ∅
  . exact Or.inl he
  . exact Or.inr (isDecomposition_image_of_R hdec he)

/-- If `R` and `DF` define a decomposition of `K`, and if `s` is a facet such that `R s` is not
empty, then `DF (R s)` is equal to `s`.-/
lemma isDecomposition_DF_comp_R {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) {s : K.facets} (hne : R s ≠ ∅) :
    s = DF (⟨R s, isDecomposition_image_of_R hdec hne⟩ : K.faces) := by
  rw [← (hdec.2)]
  simp only [Finset.Subset.refl, Finset.le_eq_subset, true_and]
  exact hdec.1 s

/-- If `R` and `DF` define a decomposition of `K`, then the map `R` determines the map `DF`.-/
lemma isDecomposition_R_determines_DF {R : K.facets → Finset α}  {DF₁ : K.faces → K.facets}
    {DF₂ : K.faces → K.facets} (hdec₁ : isDecomposition R DF₁) (hdec₂ : isDecomposition R DF₂) :
    DF₁ = DF₂ :=
  funext (fun s ↦ by rw [← hdec₂.2 s (DF₁ s), hdec₁.2 s (DF₁ s)])

variable (K)

/-- If `s` and `t` are finsets of `α`, definition of the intersection of the interval
`Set.Icc s t` and of `K.faces` as a finset of faces of K.-/
noncomputable def FinsetIcc (s t : Finset α) : Finset (K.faces) :=
  Set.Finite.toFinset (AbstractSimplicalComplex.FinsetIcc_finite K s t)

/-- If `s` and `t` are finsets of `α`, a face `u` of `K` is in `FinsetIcc s t` if and only
if `s ≤ u.1` and `u.1 ≤ t`.-/
lemma mem_FinsetIcc (s t : Finset α) (u : K.faces) :
    u ∈ FinsetIcc K s t ↔ s ≤ u.1 ∧ u.1 ≤ t := by
  unfold FinsetIcc
  simp only [Finset.le_eq_subset, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- If `s` is a finset of `α`, definition of the intersection of the interval
`Set.Iic s` and of `K.faces` as a finset of faces of K.-/
noncomputable def FinsetIic (s : Finset α) : Finset (K.faces) :=
  Set.Finite.toFinset (AbstractSimplicalComplex.FinsetIic_finite K s)

/-- If `s` is a finset of `α`, a face `u` of `K` is in `FinsetIic s` if and only if `u.1 ≤ s`.-/
lemma mem_FinsetIic (s : Finset α) (u : K.faces) :
    u ∈ FinsetIic K s ↔ u.1 ≤ s := by
  unfold FinsetIic
  simp only [Finset.le_eq_subset, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

variable {K}

/-- If `R` is a map from `K.facets` to `Finset α`, the "decomposition interval"
`Set.Icc (R s) s` as a finset of faces of `K`.-/
@[reducible] noncomputable def decompositionInterval (R : K.facets → Finset α) (s : K.facets) :
    Finset (K.faces) := FinsetIcc K (R s) s.1

/-- If `R` and `DF` define a decomposition of `K`, and if `s` is a facet and `t` is a face, then
`t` is in the decomposition interval `decompositionInterval R s` if and only if `DF t = s`.-/
lemma mem_decompositionInterval {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) (s : K.facets) (t : K.faces) :
    t ∈ decompositionInterval R s ↔ s = DF t := by
  rw [decompositionInterval, mem_FinsetIcc]
  erw [hdec.2 t s]

/-- If `R` and `DF` define a decomposition of `K`, then the map `DF` determines the decomposition
intervals `decompositionInterval R s`.-/
lemma isDecomposition_DF_determines_intervals {R₁ : K.facets → Finset α}
    {R₂ : K.facets → Finset α} {DF : K.faces → K.facets} (hdec₁ : isDecomposition R₁ DF)
    (hdec₂ : isDecomposition R₂ DF) (s : K.facets) :
    decompositionInterval R₁ s = decompositionInterval R₂ s :=
  Finset.ext (fun _ ↦ by rw [mem_decompositionInterval  hdec₁, mem_decompositionInterval hdec₂])

/-! Order on facets compatible with a decomposition.-/

/-- A partial order `r` on the facets of `K` is compatible with a map `DF` from the faces of `K`
to the facets of `K` if, for every face `t` and every facet `s`, `t ≤ s` implies that `DF t`
is less than or equal to `s` for the order `r`. If we know that `t ≤ DF t` (for example if
`DF` is part of a decomposition of `K`), this means that `DF t` is the smallest element
(for the order `r`) of the set of facets containing `t`.-/
@[reducible] def compatibleOrder (DF : K.faces → K.facets) (r : PartialOrder K.facets) : Prop :=
  ∀ (t : K.faces) (s : K.facets), t.1 ≤ s.1 → r.le (DF t) s

/-- Let `r` be a partial order on the facets of `K` and `DF` be a map from the set of faces of `K`
to the set of facets of `K`. If `r` is compatible with `DF` in the sense of `compatibleOrder`,
and if `s` is a facet and `t` is a face such that `t ≤ s` and `t ≤ DF t` (the second condition is
automatic when `DF` is part of a decomposition), then `DF t = s` if and only if `t` is not in the
complex of old faces `oldFaces r s`.-/
lemma compatibleOrder_oldFaces {DF : K.faces → K.facets} {r : PartialOrder K.facets}
    (hcomp : compatibleOrder DF r) {s : K.facets} {t : K.faces} (hts : t.1 ≤ s.1)
    (hDFt : t.1 ≤ (DF t).1) : t.1 ∉ oldFaces r s ↔ DF t = s := by
  rw [faces_oldFaces]
  push_neg
  simp only [Subtype.coe_prop, Finset.le_eq_subset, Subtype.forall, forall_true_left]
  constructor
  · exact fun ht ↦ @eq_of_le_of_not_lt _ r _ _ (hcomp t s hts)
      (fun ht' ↦ ht hts (DF t).1 (DF t).2 ht' hDFt)
  · exact fun ht _ u huf hus htu ↦
      @not_lt_of_le _ r.toPreorder _ _ (@le_of_eq_of_le _ _ _ _ r.toLE (Eq.symm ht)
      (hcomp t ⟨u, huf⟩ htu)) hus

/-- If `R` and `DF` define a decomposition of `K`, if `r` is a partial order on the facets of `K`
that is compatible with `DF`, if `s` is a facet and `t` is face such that `t ≤ s`, then `t` is
in the decomposition interval `decompositionInterval R s` if and only it is not in the complex
of old faces `oldFaces r s`.-/
lemma isDecomposition_oldFaces {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) {r : PartialOrder K.facets} (hcomp : compatibleOrder DF r)
    {s : K.facets} {t : K.faces} (hts : t.1 ≤ s.1) :
    t.1 ∉ oldFaces r s ↔ t ∈ decompositionInterval R s := by
  rw [compatibleOrder_oldFaces hcomp hts (isDecomposition_DF_bigger_than_source hdec t),
    mem_decompositionInterval hdec, eq_comm]

/-- Variant of `isDecomposition_oldFaces`, where we show instead that `t` is not in the complex
of old faces `oldFaces r s` if and only if `R s ≤ t`.-/
lemma isDecomposition_oldFaces' {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) {r : PartialOrder K.facets} (hcomp : compatibleOrder DF r)
    {s : K.facets} {t : K.faces} (hts : t.1 ⊆ s.1) :
    t.1 ∉ oldFaces r s ↔ R s ≤ t := by
  rw [isDecomposition_oldFaces hdec hcomp hts, mem_FinsetIcc]
  simp only [Finset.le_eq_subset, hts, and_true]

--Useless, replace with value.
/-
lemma OldFacesDecomposition_faces {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) {r : PartialOrder K.facets} (hcomp : compatibleOrder DF r)
    {s : K.facets} {t : K.faces} (hts : t.1 ⊆ s.1) :
    t.1 ∈ oldFaces r s ↔ ¬(R s ≤ t) :=
  iff_not_comm.mp (Iff.symm (isDecomposition_oldFaces' hdec hcomp hts))
-/

/-- If `R` and `DF` define a decomposition of `K`, if `r` is a partial order on the facets of `K`
that is compatible with `DF`, and if `s` is a facet, then the complex of old faces
`oldFaces r s` is empty if and only the decomposition interval `decompositionInterval R s` is
equal to the half-infinite interval `FinsetIic s`.-/
lemma isDecomposition_oldFaces_empty_iff {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) {r : PartialOrder K.facets} (hcomp : compatibleOrder DF r)
    (s : K.facets) :
    (oldFaces r s).faces = ∅ ↔ decompositionInterval R s = FinsetIic K s.1 := by
  constructor
  . intro he
    ext t
    rw [mem_FinsetIic]
    constructor
    · exact fun h ↦ by rw [(mem_decompositionInterval hdec s t).mp h]
                       exact isDecomposition_DF_bigger_than_source hdec t
    · intro hts
      refine (isDecomposition_oldFaces hdec hcomp hts).mp ?_
      change t.1 ∉ (oldFaces r s).faces
      simp only [he, Set.mem_empty_iff_false, not_false_eq_true]
  . intro heq
    rw [Set.eq_empty_iff_forall_not_mem]
    intro u
    by_cases huf : u ∈ K.faces
    · by_cases hus : u ≤ s
      · erw [isDecomposition_oldFaces hdec hcomp (t := ⟨u, huf⟩) hus, heq, mem_FinsetIic]
        exact hus
      · exact fun hu ↦ by erw [faces_oldFaces] at hu; exact hus hu.2.1
    · exact fun hu ↦ by erw [faces_oldFaces] at hu; exact huf hu.1

/-- If `R` and `DF` define a decomposition of `K`, if `r` is a partial order on the facets of `K`
that is compatible with `DF`, and if `s` is a facet, then the facets of the complex of old faces
`oldFaces r s` all have cardinality equal to `s.1.card - 1`. -/
lemma isDecomposition_dimension_facets_oldFaces {R : K.facets → Finset α}
    {DF : K.faces → K.facets} (hdec : isDecomposition R DF) {r : PartialOrder K.facets}
    (hcomp : compatibleOrder DF r) (s : K.facets) (t : (oldFaces r s).facets) :
    Finset.card t.1 = Finset.card s.1 - 1 := by
  have htf := facets_subset t.2
  have htf' := (OldFaces_mem r s t.1).mp htf
  erw [@OldFacesDecomposition_faces _ _ _ _ hdec _ hcomp s ⟨t.1, htf'.1⟩ htf'.2.1, Finset.not_subset] at htf
  match htf with
  | ⟨a, ⟨has, hat⟩⟩ => set u := s.1 \ {a}
                       have hus : u ⊆ s.1 := Finset.sdiff_subset _ _
                       have htu : t.1 ⊆ u := by rw [Finset.subset_sdiff, Finset.disjoint_singleton_right]
                                                exact ⟨htf'.2.1, hat⟩
                       have hune : u.Nonempty := by match K.nonempty_of_mem htf'.1 with | ⟨a, ha⟩ => exact ⟨a, htu ha⟩
                       have huK : u ∈ K.faces := K.down_closed (facets_subset s.2) hus hune
                       have huof : u ∈ (OldFaces r s).faces := by
                         erw [@OldFacesDecomposition_faces _ _ _ _ hdec _ hcomp s ⟨u, huK⟩ hus, Finset.not_subset]
                         exists a
                         rw [and_iff_right has]
                         apply Finset.not_mem_sdiff_of_mem_right
                         exact Finset.mem_singleton_self _
                       have has' : {a} ⊆ s.1 := by
                         rw [Finset.singleton_subset_iff]
                         exact (hdec.1 s) has
                       rw [((mem_facets_iff (OldFaces r s) t.1).mp t.2).2 huof htu, Finset.card_sdiff has']
                       rw [Finset.card_singleton]


/- If the partial order r is compatible with the map DF in a decomposition (R,DF), and if s is a facet,
then the complex of old faces is pure. -/
lemma OldFacesDecompositionIsPure {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{r : PartialOrder K.facets} (hcomp : CompatibleOrder DF r) (s : K.facets) : Pure (OldFaces r s) :=
Dimension_of_Noetherian_pure (Finite_implies_Noetherian (OldFacesFinite r s))
(fun t u htf huf => by rw [OldFacesDecompositionDimensionFacets hdec hcomp s ⟨t, htf⟩, OldFacesDecompositionDimensionFacets hdec hcomp s ⟨u, huf⟩])


/- If the partial order r is compatible with the map DF in a decomposition (R,DF), and if s is a facet,
then the complex of old faces is either empty or has dimension card s - 2.-/
lemma OldFacesDecompositionDimension {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF)
{r : PartialOrder K.facets} (hcomp : CompatibleOrder DF r) (s : K.facets) (hne : (OldFaces r s).faces.Nonempty) :
dimension (OldFaces r s) = Finset.card s.1 - 2 := by
  match (Noetherian_nonempty_implies_facets_exist (Finite_implies_Noetherian (OldFacesFinite r s)) hne) with
  | ⟨t, htf⟩ => rw [←((OldFacesDecompositionIsPure hdec hcomp s) htf), OldFacesDecompositionDimensionFacets hdec hcomp s ⟨t, htf⟩]
                erw [←ENat.coe_sub, WithTop.coe_eq_coe, Nat.cast_inj, Nat.sub_succ]


/- We define π₀ and homology facets for a decomposition, without reference to an order on the facets (if the decomposition is
compatible with a shelling order, we will recover the usual notion). π₀ facets are the facets s such that the corresponding
decomposition interval is the half-infinite interval [<-,s], and homology facets are non-π₀ facets s such that the corresponding
decomposition interval is equal to {s}.-/

def IsPi0Facet {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.facets) : Prop :=
DecompositionInterval hdec s = Finset.Iic ⟨s.1, facets_subset s.2⟩

def IsHomologyFacet {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.facets) : Prop :=
¬(IsPi0Facet hdec s) ∧ DecompositionInterval hdec s = {⟨s.1, facets_subset s.2⟩}

/- A 0-dimensional facet is always a π₀ facet.-/
lemma Vertex_IsPi0Facet {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.facets)
(hcard : Finset.card s.1 = 1) : IsPi0Facet hdec s := by
  ext t
  rw [DecompositionInterval_def]
  simp only [Finset.le_eq_subset, Finset.mem_Iic]
  constructor
  . exact fun h => h.2
  . intro h
    erw [and_iff_left h]
    rw [Finset.card_eq_one] at hcard
    match hcard with
    | ⟨a, has⟩ => change t.1 ⊆ s.1 at h
                  rw [has, Finset.Nonempty.subset_singleton_iff (K.nonempty_of_mem t.2), ←has] at h
                  rw [h]
                  exact hdec.1 _

/- A facet s is a π₀ facet if and only if it is 0-dimensional or its image by R is empty.-/
lemma IsPi0Facet_iff {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.facets) :
IsPi0Facet hdec s ↔ R s = ∅ ∨ Finset.card s.1 = 1 := by
  constructor
  . intro hpi
    by_contra habs
    push_neg at habs
    have hcard : Finset.card s.1 > 1 := by
      have h := face_card_nonzero (facets_subset s.2)
      rw [←Nat.pos_iff_ne_zero] at h
      have h := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h)
      rw [←Nat.one_eq_succ_zero, or_iff_right (Ne.symm habs.2)] at h
      exact h
    rw [←Finset.nonempty_iff_ne_empty] at habs
    match habs.1 with
    | ⟨a, haR⟩ => have has : a ∈ s.1 := (hdec.1 s) haR
                  have h : ∃ (b : α), b ∈ s.1 ∧ b ≠ a := by
                    by_contra habs
                    push_neg at habs
                    have hsin := Finset.eq_singleton_iff_unique_mem.mpr ⟨has, habs⟩
                    rw [hsin, Finset.card_singleton] at hcard
                    exact lt_irrefl _ hcard
                  match h with
                  | ⟨b, hbs, hba⟩ => set t := ({b} : Finset α)
                                     have htf : t ∈ K.faces :=
                                       K.down_closed (facets_subset s.2) (Finset.singleton_subset_iff.mpr hbs) (Finset.singleton_nonempty _)
                                     have htint : ¬(⟨t, htf⟩ ∈ DecompositionInterval hdec s) := by
                                       rw [DecompositionInterval_def, not_and_or]
                                       apply Or.inl
                                       by_contra habs
                                       have h:= habs haR
                                       simp only [Finset.mem_singleton] at h
                                       exact hba (Eq.symm h)
                                     rw [hpi] at htint
                                     simp only [Finset.mem_Iic, Subtype.mk_le_mk, Finset.le_eq_subset, Finset.singleton_subset_iff] at htint
                                     exact htint hbs
  . intro h
    cases h with
    | inl hR => ext t
                rw [DecompositionInterval_def, hR, Finset.mem_Iic]
                change _ ↔ t.1 ⊆ s.1
                simp only [Finset.le_eq_subset, Finset.empty_subset, true_and]
    | inr hcard => exact Vertex_IsPi0Facet hdec s hcard


/- A facet s is a homology facet if and only it is a fixed point of R and is not 0-dimensional.-/
lemma IsHomologyFacet_iff {R : K.facets → Finset α}  {DF : K.faces → K.facets} (hdec : IsDecomposition R DF) (s : K.facets) :
IsHomologyFacet hdec s ↔ R s = s.1 ∧ Finset.card s.1 > 1 := by
  unfold IsHomologyFacet
  constructor
  . intro ⟨h, hint⟩
    by_cases hcard : Finset.card s.1 ≤ 1
    . exfalso
      have hv : Finset.card s.1 = 1 := by
            refine le_antisymm hcard ?_
            rw [Nat.succ_le, Nat.pos_iff_ne_zero, ne_eq]
            exact face_card_nonzero (facets_subset s.2)
      exact h (Vertex_IsPi0Facet hdec s hv)
    . rw [←lt_iff_not_le] at hcard
      by_cases he : R s = ∅
      . exfalso
        rw [Finset.one_lt_card_iff] at hcard
        match hcard with
        | ⟨a, b, has, hbs, hab⟩ =>  set t := ({a} : Finset α)
                                    have htf : t ∈ K.faces :=
                                      K.down_closed (facets_subset s.2) (Finset.singleton_subset_iff.mpr has) (Finset.singleton_nonempty _)
                                    have htint : ⟨t, htf⟩ ∈ DecompositionInterval hdec s := by
                                      rw [DecompositionInterval_def]
                                      rw [he]
                                      simp only [Finset.le_eq_subset, Finset.subset_singleton_iff, true_or, Finset.singleton_subset_iff, true_and]
                                      exact has
                                    rw [hint] at htint
                                    simp only [Finset.mem_singleton, Subtype.mk.injEq] at htint
                                    rw [←htint, Finset.mem_singleton] at hbs
                                    exact hab (Eq.symm hbs)
      . have hR := Decomposition_image_of_R hdec he
        have hRint : ⟨R s, hR⟩ ∈ DecompositionInterval hdec s := by
          rw [DecompositionInterval_def]
          rw [and_iff_left (hdec.1 s)]
        rw [hint] at hRint
        simp only [Finset.mem_singleton, Subtype.mk.injEq] at hRint
        exact ⟨hRint, hcard⟩
  . intro ⟨hR,hcard⟩
    constructor
    . rw [gt_iff_lt, Finset.one_lt_card_iff] at hcard
      match hcard with
      | ⟨a, b, has, hbs, hab⟩ =>  set t := ({a} : Finset α)
                                  have htf : t ∈ K.faces :=
                                    K.down_closed (facets_subset s.2) (Finset.singleton_subset_iff.mpr has) (Finset.singleton_nonempty _)
                                  have htint : ¬(⟨t, htf⟩ ∈ DecompositionInterval hdec s) := by
                                    rw [DecompositionInterval_def, not_and_or]
                                    apply Or.inl
                                    by_contra habs
                                    have habs' := subset_antisymm habs (by rw [←hR] at has; exact Finset.singleton_subset_iff.mpr has)
                                    rw [habs'] at hR
                                    simp only at hR
                                    rw [←hR, Finset.mem_singleton] at hbs
                                    exact hab (Eq.symm hbs)
                                  unfold IsPi0Facet
                                  by_contra habs
                                  rw [habs] at htint
                                  simp only [Finset.mem_Iic, Subtype.mk_le_mk, Finset.le_eq_subset, Finset.singleton_subset_iff] at htint
                                  exact htint has
    . ext t
      rw [DecompositionInterval_def, hR]
      simp only [Finset.le_eq_subset, Finset.mem_singleton]
      rw [←SetCoe.ext_iff]
      constructor
      . exact fun h => subset_antisymm h.2 h.1
      . exact fun h => by rw [h]; exact ⟨subset_refl _, subset_refl _⟩


end AbstractSimplicialComplex
