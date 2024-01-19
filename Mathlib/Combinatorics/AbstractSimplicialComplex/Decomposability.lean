/- Copyright.-/
import Mathlib.Combinatorics.AbstractSimplicialComplex.FacePoset
import Mathlib.Combinatorics.AbstractSimplicialComplex.OrderOnFacets

universe u

open AbstractSimplicalComplex

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
  · exact Or.inl he
  · exact Or.inr (isDecomposition_image_of_R hdec he)

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
  · intro he
    ext t
    rw [mem_FinsetIic]
    constructor
    · exact fun h ↦ by rw [(mem_decompositionInterval hdec s t).mp h]
                       exact isDecomposition_DF_bigger_than_source hdec t
    · intro hts
      refine (isDecomposition_oldFaces hdec hcomp hts).mp ?_
      change t.1 ∉ (oldFaces r s).faces
      simp only [he, Set.mem_empty_iff_false, not_false_eq_true]
  · intro heq
    rw [Set.eq_empty_iff_forall_not_mem]
    intro u
    by_cases huf : u ∈ K.faces
    · by_cases hus : u ≤ s
      · erw [isDecomposition_oldFaces hdec hcomp (t := ⟨u, huf⟩) hus, heq, mem_FinsetIic]
        exact hus
      · exact fun hu ↦ by erw [faces_oldFaces] at hu; exact hus hu.2.1
    · exact fun hu ↦ by erw [faces_oldFaces] at hu; exact huf hu.1

open Finset in
/-- If `R` and `DF` define a decomposition of `K`, if `r` is a partial order on the facets of `K`
that is compatible with `DF`, and if `s` is a facet, then the facets of the complex of old faces
`oldFaces r s` all have cardinality equal to `s.1.card - 1`. -/
lemma isDecomposition_dimension_facets_oldFaces [DecidableEq α] {R : K.facets → Finset α}
    {DF : K.faces → K.facets} (hdec : isDecomposition R DF) {r : PartialOrder K.facets}
    (hcomp : compatibleOrder DF r) (s : K.facets) (t : (oldFaces r s).facets) :
    t.1.card = s.1.card - 1 := by
  have htf := facets_subset t.2
  have htf' := (faces_oldFaces r s t.1).mp (facets_subset t.2)
  erw [← not_iff_comm.mp (isDecomposition_oldFaces' hdec hcomp (t := ⟨t, htf'.1⟩) htf'.2.1),
    not_subset] at htf
  obtain ⟨a, ⟨has, hat⟩⟩ := htf
  set u := s.1.erase a
  have htu : t.1 ⊆ u := by rw [subset_erase]; exact ⟨htf'.2.1, hat⟩
  have huK : u ∈ K.faces := K.down_closed (facets_subset s.2) (erase_subset _ _)
    (let ⟨a, ha⟩ := K.nonempty_of_mem htf'.1; ⟨a, htu ha⟩)
  have huof : u ∈ (oldFaces r s).faces := by
    erw [← not_iff_comm.mp (isDecomposition_oldFaces' hdec hcomp (t := ⟨u, huK⟩)
      (erase_subset _ _)), not_subset]
    exact ⟨a, has, Finset.not_mem_erase a s.1⟩
  rw [((mem_facets_iff (oldFaces r s) t.1).mp t.2).2 huof htu,
    Finset.card_erase_of_mem ((hdec.1 s) has)]

/-- If `R` and `DF` define a decomposition of `K`, if `r` is a partial order on the facets of `K`
that is compatible with `DF`, and if `s` is a facet, then the complex of old faces oldFaces r s`
is pure.-/
lemma isDecomposition_oldFaces_pure {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) {r : PartialOrder K.facets} (hcomp : compatibleOrder DF r)
    (s : K.facets) : Pure (oldFaces r s) := by
  classical
  exact pure_of_wf_and_dimension_facets (@Finite.to_wellFoundedGT (oldFaces r s).faces
  (finite_oldFaces r s) _).wf (fun t htf u huf => by
    rw [isDecomposition_dimension_facets_oldFaces hdec hcomp s ⟨t, htf⟩,
    isDecomposition_dimension_facets_oldFaces hdec hcomp s ⟨u, huf⟩])

/-- If `R` and `DF` define a decomposition of `K`, if `r` is a partial order on the facets of `K`
that is compatible with `DF`, and if `s` is a facet, then the complex of old faces `oldFaces r s`
is either empty or has dimension `s.card - 2`.-/
lemma isDecomposition_dimension_oldFaces {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) {r : PartialOrder K.facets} (hcomp : compatibleOrder DF r)
    (s : K.facets) (hne : (oldFaces r s).faces.Nonempty) :
    dimension (oldFaces r s) = Finset.card s.1 - 2 := by
  classical
  obtain ⟨t, htf⟩ := hne
  obtain ⟨⟨u, huf⟩, htu⟩ := exists_facet_of_wf (@Finite.to_wellFoundedGT (oldFaces r s).faces
    (finite_oldFaces r s) _).wf ⟨t, htf⟩
  rw [← (isDecomposition_oldFaces_pure hdec hcomp s) huf,
    isDecomposition_dimension_facets_oldFaces hdec hcomp s ⟨u, huf⟩]
  erw [← ENat.coe_sub, WithTop.coe_eq_coe, Nat.cast_inj, Nat.sub_succ]


/-! `π₀` and homology facets of a decomposition. (The rationale for the name is that, if the
decomposition comes from a shelling, then `π₀` facets should add a new connected component to
the geometric realization of `K` and homology facets should contribute a cohomology class.)-/

/-- If `R` is a map from the set of facets of `K` to the set of finsets of `α`, then a `π₀` facet
is a facet `s` such that the decomposition interval `decompositionInterval R s` is equal to the
half-infinite interval `Set.Iic s`-/
@[reducible]
def isPi0Facet (R : K.facets → Finset α)  (s : K.facets) : Prop :=
  decompositionInterval R s = Set.Iic (⟨s.1, facets_subset s.2⟩ : K.faces)

/-- If `R` is a map from the set of facets of `K` to the set of finsets of `α`, then a homology
facet is a facet `s` thats is not a `π₀` facet and such that the decomposition interval
`decompositionInterval R s` is equal to the singleton `{s}`.-/
@[reducible]
def isHomologyFacet (R : K.facets → Finset α) (s : K.facets) : Prop :=
  ¬ isPi0Facet R s ∧ decompositionInterval R s = {⟨s.1, facets_subset s.2⟩}

/-- If `R` is a map from the set of facets of `K` to the set of finsets of `α` such that
`R s ≤ s` for every facet `s`, then a `0`-dimensional facet is always a `π₀` facet.-/
lemma isPi0Facet_of_vertex {R : K.facets → Finset α} (hR : ∀ (s : K.facets), R s ⊆ s.1)
    (s : K.facets) (hcard : Finset.card s.1 = 1) : isPi0Facet R s := by
  ext t
  simp only [Finset.mem_coe, Set.mem_Iic, decompositionInterval, mem_FinsetIcc,
    Finset.le_eq_subset, Finset.mem_Iic]
  constructor
  · exact fun h => h.2
  · intro h
    erw [and_iff_left h]
    rw [Finset.card_eq_one] at hcard
    obtain ⟨a, ha⟩:= hcard
    change t.1 ⊆ s.1 at h
    rw [ha, Finset.Nonempty.subset_singleton_iff (K.nonempty_of_mem t.2), ← ha] at h
    rw [h]
    exact hR _

/-- If `R` is a map from the set of facets of `K` to the set of finsets of `α` such that
`R s ≤ s` for every facet `s`, then a facet s is a `π₀` facet if and only if it is `0`-dimensional
or its image by `R` is empty.-/
lemma isPi0Facet_iff {R : K.facets → Finset α} (hR : ∀ (s : K.facets), R s ⊆ s.1) (s : K.facets) :
    isPi0Facet R s ↔ R s = ∅ ∨ Finset.card s.1 = 1 := by
  constructor; swap
  · intro h
    cases h with
    | inr h => exact isPi0Facet_of_vertex hR s h
    | inl h => unfold isPi0Facet decompositionInterval
               rw [h]
               ext t
               simp only [Finset.mem_coe, mem_FinsetIcc, Finset.le_eq_subset, Finset.empty_subset,
                 true_and, Set.mem_Iic]
               rfl
  · intro h
    by_contra habs
    push_neg at habs
    have hcard : Finset.card s.1 > 1 := by
      have h := face_card_nonzero (facets_subset s.2)
      rw [← Nat.pos_iff_ne_zero] at h
      have h := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h)
      rw [← Nat.one_eq_succ_zero, or_iff_right (Ne.symm habs.2)] at h
      exact h
    obtain ⟨a, haR⟩ := Finset.nonempty_iff_ne_empty.mpr habs.1
    have has : a ∈ s.1 := hR s haR
    have h : ∃ (b : α), b ∈ s.1 ∧ b ≠ a := by
      by_contra habs
      push_neg at habs
      rw [Finset.eq_singleton_iff_unique_mem.mpr ⟨has, habs⟩, Finset.card_singleton] at hcard
      exact lt_irrefl _ hcard
    obtain ⟨b, hbs, hba⟩ := h
    set t := ({b} : Finset α)
    have htf : t ∈ K.faces := K.down_closed (facets_subset s.2)
      (Finset.singleton_subset_iff.mpr hbs) (Finset.singleton_nonempty _)
    have htint : ¬ ⟨t, htf⟩ ∈ (decompositionInterval R s : Set K.faces) := by
      unfold decompositionInterval
      simp only [Finset.mem_coe, mem_FinsetIcc, Finset.le_eq_subset, Finset.subset_singleton_iff,
        Finset.singleton_subset_iff, not_and, hbs, not_true_eq_false, imp_false, not_or]
      rw [← ne_eq, ← Finset.nonempty_iff_ne_empty, and_iff_right ⟨a, haR⟩]
      intro heq
      refine hba (Eq.symm (Finset.eq_of_mem_singleton ?_))
      rw [← heq]
      exact haR
    unfold isPi0Facet at h
    rw [h] at htint
    simp only [Set.mem_Iic, Subtype.mk_le_mk, Finset.le_eq_subset,
      Finset.singleton_subset_iff] at htint
    exact htint hbs

/- A facet s is a homology facet if and only it is a fixed point of R and is not 0-dimensional.-/
lemma isHomologyFacet_iff {R : K.facets → Finset α}  {DF : K.faces → K.facets}
    (hdec : isDecomposition R DF) (s : K.facets) :
    isHomologyFacet R s ↔ R s = s.1 ∧ Finset.card s.1 > 1 := by
  unfold isHomologyFacet decompositionInterval
  constructor
  · intro ⟨h, hint⟩
    by_cases hcard : Finset.card s.1 ≤ 1
    · exfalso
      refine h (isPi0Facet_of_vertex hdec.1 s (le_antisymm hcard ?_))
      rw [Nat.succ_le, Nat.pos_iff_ne_zero, ne_eq]
      exact face_card_nonzero (facets_subset s.2)
    · rw [and_iff_left (lt_iff_not_le.mpr hcard)]
      by_cases he : R s = ∅
      · exfalso
        obtain ⟨a, b, has, hbs, hab⟩ := Finset.one_lt_card_iff.mp (lt_iff_not_le.mpr hcard)
        set t := ({a} : Finset α)
        have htf : t ∈ K.faces := K.down_closed (facets_subset s.2)
          (Finset.singleton_subset_iff.mpr has) (Finset.singleton_nonempty _)
        have htint : ⟨t, htf⟩ ∈ decompositionInterval R s := by
          unfold decompositionInterval
          rw [mem_FinsetIcc, he]
          simp only [Finset.le_eq_subset, Finset.subset_singleton_iff, true_or,
            Finset.singleton_subset_iff, has, and_self]
        rw [decompositionInterval, hint] at htint
        simp only [Finset.mem_singleton, Subtype.mk.injEq] at htint
        rw [← htint, Finset.mem_singleton] at hbs
        exact hab (Eq.symm hbs)
      · have hR : R s ∈ K.faces :=
          K.down_closed (facets_subset s.2) (hdec.1 s) (Finset.nonempty_iff_ne_empty.mpr he)
        have hRint : ⟨R s, hR⟩ ∈ decompositionInterval R s := by
          unfold decompositionInterval
          rw [mem_FinsetIcc]
          exact ⟨by rfl, hdec.1 s⟩
        rw [decompositionInterval, hint] at hRint
        simp only [Finset.mem_singleton, Subtype.mk.injEq] at hRint
        exact hRint
  · intro ⟨hR, hcard⟩
    constructor; swap
    · ext t
      simp only [hR, mem_FinsetIcc, Finset.le_eq_subset, Finset.mem_singleton]
      erw [← le_antisymm_iff (a := s.1) (b := t.1), eq_comm, ← SetCoe.ext_iff]
    · rw [gt_iff_lt, Finset.one_lt_card_iff] at hcard
      obtain ⟨a, b, has, hbs, hab⟩ := hcard
      set t := ({a} : Finset α)
      have htf : t ∈ K.faces := K.down_closed (facets_subset s.2)
        (Finset.singleton_subset_iff.mpr has) (Finset.singleton_nonempty _)
      have htint : ¬(⟨t, htf⟩ ∈ decompositionInterval R s) := by
        unfold decompositionInterval
        rw [mem_FinsetIcc]
        simp only [Finset.le_eq_subset, Finset.subset_singleton_iff, Finset.singleton_subset_iff,
          has, and_true, not_or, hR, ← Finset.nonempty_iff_ne_empty]
        rw [and_iff_right (K.nonempty_of_mem (facets_subset s.2))]
        intro heq
        rw [heq] at hbs
        simp only [Finset.mem_singleton] at hbs
        exact hab (Eq.symm hbs)
      unfold isPi0Facet
      intro heq
      rw [← Finset.mem_coe, heq] at htint
      simp only [Set.mem_Iic, Subtype.mk_le_mk, Finset.le_eq_subset,
        Finset.singleton_subset_iff] at htint
      exact htint has

end AbstractSimplicialComplex
