/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.FinitePresentation

/-!

# Rings of definition

Given a finitely presented algebra `A` over a ring `R`, we may
descend to a Noetherian subring `R₀` of `R` and a model of `A` over `R₀`.

In this file we provide basic API for working with polynomial rings over subrings. In particular
we provide infrastructure for producing `R₀` and descending polynomials
in `R` to polynomials in `R₀` given containment of the coefficients.

-/

universe u v w t

variable {R : Type u} [CommRing R]

section SetCoefficients

variable {σ : Type*}

/-- The set of coefficients of a set of multivariate polynomials. -/
def Set.coefficients (s : Set (MvPolynomial σ R)) : Set R :=
  Set.iUnion (ι := s) (fun (p : s) ↦ p.val.coefficients)

/-- The set of coefficients of a finite set of multivariate polynomials is finite. -/
theorem Set.coefficients_finite_of_finite (s : Set (MvPolynomial σ R)) (hf : Set.Finite s) :
    Set.Finite (s.coefficients) :=
  letI : Finite s := hf
  Set.finite_iUnion (fun p ↦ MvPolynomial.coefficients_finite p.val)

theorem Set.coefficients_subset_coefficients (s : Set (MvPolynomial σ R))
    (p : MvPolynomial σ R) (hS : p ∈ s) :
    p.coefficients ⊆ s.coefficients := fun r hr ↦ by
  simp only [Set.coefficients, Set.mem_iUnion]
  exact ⟨⟨p, hS⟩, hr⟩

section Map

variable {S : Type*} [CommRing S]
variable {f : R →+* S}

namespace MvPolynomial

/-- If the coefficients of `q : MvPolynomial σ S` are in the range of `f`, then `q` is in the
of `MvPolynomial.map f`. -/
theorem mem_range_of_coefficients (q : MvPolynomial σ S) (hc : q.coefficients ⊆ f.range) :
    q ∈ (MvPolynomial.map f).range := by
  have h (m : σ →₀ ℕ) : ∃ (r : R), f r = q.coeff m ∧ (q.coeff m = 0 → r = 0) := by
    by_cases h : m ∈ q.support
    · obtain ⟨r, hr⟩ := hc (MvPolynomial.coeff_mem_coefficients m h)
      exact ⟨r, by simp_all⟩
    · exact ⟨0, Eq.symm (by simpa using h), by simp⟩
  choose c hfc hcc using h
  let p : (σ →₀ ℕ) →₀ R := Finsupp.ofSupportFinite c <| by
    apply Set.Finite.subset (Finsupp.finite_support q) (fun m minc h ↦ ?_)
    exact minc (hcc m h)
  exact ⟨p, MvPolynomial.ext _ _ fun m ↦ MvPolynomial.coeff_map f p m ▸ hfc m⟩

/-- Subring version of `mem_range_of_coefficients`. -/
theorem mem_range_of_coefficients' {R₀ : Subring R} (p : MvPolynomial σ R) (hc : p.coefficients ⊆ R₀) :
    p ∈ (MvPolynomial.map R₀.subtype).range := by
  apply mem_range_of_coefficients
  rw [R₀.range_subtype]
  exact hc

/-- If the coefficients of `q : MvPolynomial σ S` are in the range of `f`, choose a preimage of
`q` under `MvPolynomial.map f` using choice. -/
noncomputable def choosePreimageOfCoeffs (q : MvPolynomial σ S) (hc : q.coefficients ⊆ f.range) :
    MvPolynomial σ R :=
  (q.mem_range_of_coefficients hc).choose

@[simp]
lemma choosePreimageOfCoeffs_map (q : MvPolynomial σ S) (hc : q.coefficients ⊆ f.range) :
    MvPolynomial.map f (q.choosePreimageOfCoeffs hc) = q :=
  (q.mem_range_of_coefficients hc).choose_spec

noncomputable def Set.choosePreimageOfCoeffs (s : Set (MvPolynomial σ S))
    (hc : s.coefficients ⊆ f.range) (p : s) : MvPolynomial σ R :=
  MvPolynomial.choosePreimageOfCoeffs p.val
    ((s.coefficients_subset_coefficients p.val p.property).trans hc)

/-- If the coefficients of `p : MvPolynomial σ R` are in a subring `R₀`, choose a representative
`p` in `MvPolynomial σ R₀` using choice. -/
noncomputable def choosePreimageOfCoeffs' {R₀ : Subring R} (p : MvPolynomial σ R)
    (hc : p.coefficients ⊆ R₀) : MvPolynomial σ R₀ :=
  choosePreimageOfCoeffs p (by rw [R₀.range_subtype]; exact hc)

@[simp]
lemma choosePreimageOfCoeffs'_map {R₀ : Subring R} (p : MvPolynomial σ R)
    (hc : p.coefficients ⊆ R₀) :
    MvPolynomial.map R₀.subtype (p.choosePreimageOfCoeffs' hc) = p :=
  (p.mem_range_of_coefficients ((by rw [R₀.range_subtype]; exact hc))).choose_spec

end MvPolynomial

end Map

end SetCoefficients

open TensorProduct

namespace Algebra

namespace RingOfDefinition

section HasCoefficients

variable {ι : Type*}

/-- A typeclass expressing that `p` has coefficients in a subring `R₀`. -/
class HasCoefficients (p : MvPolynomial ι R) (R₀ : Subring R) : Prop where
  has_coeffs : p.coefficients ⊆ R₀

/-- Choose a representative in `MvPolynomial ι R₀` of a polynomial `p : MvPolynomial ι R` with
coefficients contained in `R₀`. -/
noncomputable def _root_.MvPolynomial.repr (p : MvPolynomial ι R) (R₀ : Subring R)
    [HasCoefficients p R₀] : MvPolynomial ι R₀ :=
  p.choosePreimageOfCoeffs' (HasCoefficients.has_coeffs)

@[simp]
theorem map_repr (p : MvPolynomial ι R) (R₀ : Subring R) [HasCoefficients p R₀] :
    MvPolynomial.map R₀.subtype (p.repr R₀) = p := by
  simp [MvPolynomial.repr]

/-- The smallest subring of `R` containing all coefficients of a set `s` of polynomials. -/
def core (s : Set (MvPolynomial ι R)) : Subring R :=
  (Algebra.adjoin ℤ s.coefficients).toSubring

theorem core_finiteType_of_finite (s : Set (MvPolynomial ι R)) (hf : s.Finite) :
    FiniteType ℤ (core s) :=
  FiniteType.of_adjoin_finite _ (s.coefficients_finite_of_finite hf)

instance {s : Set (MvPolynomial ι R)} (p : s) : HasCoefficients p.val (core s) where
  has_coeffs := Set.Subset.trans
    (s.coefficients_subset_coefficients p.val p.property) Algebra.subset_adjoin

/-- Adjoin the coefficients of a set of polynomials to a subring. -/
def _root_.Subring.adjoinCoefficients (s : Set (MvPolynomial ι R)) (R₀ : Subring R) :
    Subring R :=
  (Algebra.adjoin R₀ s.coefficients).toSubring

instance (s : Set (MvPolynomial ι R)) (R₀ : Subring R) :
    Algebra R₀ (R₀.adjoinCoefficients s) :=
  inferInstanceAs <| Algebra R₀ (Algebra.adjoin R₀ s.coefficients)

/-- If the coefficients of a set `s` of polynomials are adjoined, every element of the set `s`
has coefficients in the new subring. -/
instance HasCoefficients.of_mem (s : Set (MvPolynomial ι R)) (p : s) (R₀ : Subring R) :
    HasCoefficients p.val (R₀.adjoinCoefficients s) where
  has_coeffs := Set.Subset.trans
    (s.coefficients_subset_coefficients p.val p.property)
    Algebra.subset_adjoin

/-- If `R₀` has the coefficients of a polynomial `p`, then after adjoining more coefficients,
the new subring still has the coefficients of `p`. -/
instance HasCoefficients.trans (p : MvPolynomial ι R) (R₀ : Subring R) [HasCoefficients p R₀]
    (s : Set (MvPolynomial ι R)) :
    HasCoefficients p (R₀.adjoinCoefficients s) where
  has_coeffs := by
    have : ((R₀.subtype).range : Set R) ⊆ (Algebra.adjoin R₀ s.coefficients).toSubring :=
      Set.Subset.trans (Set.subset_union_left _ _) Subsemiring.subset_closure
    rw [Subring.range_subtype] at this
    exact Set.Subset.trans HasCoefficients.has_coeffs this

instance {α : Type*} (f : α → MvPolynomial ι R) (R₀ : Subring R) (a : α) :
    HasCoefficients (f a) (R₀.adjoinCoefficients (Set.range f)) :=
  HasCoefficients.of_mem _ ⟨f a, Set.mem_range_self a⟩ _

theorem _root_.Subring.adjoinCoefficients_finiteType_of_finite (s : Set (MvPolynomial ι R))
      (hf : s.Finite) (R₀ : Subring R) :
    FiniteType R₀ (R₀.adjoinCoefficients s) :=
  FiniteType.of_adjoin_finite _ (s.coefficients_finite_of_finite hf)

theorem _root_.Subring.adjoinCoefficients_finiteType_of_finite' (s : Set (MvPolynomial ι R))
      (hf : s.Finite) (R₀ : Subring R) [FiniteType ℤ R₀] :
    FiniteType ℤ (R₀.adjoinCoefficients s) :=
  FiniteType.trans inferInstance (R₀.adjoinCoefficients_finiteType_of_finite s hf)

/- Lean automatically infers that any of the adjoined polynomials has coefficients in the new
ring. -/
example (t₁ t₂ t₃ t₄ : Set (MvPolynomial ι R)) (f : ℕ → MvPolynomial ι R) (p : t₁)
  (n : ℕ) :
    let R₀ := Subring.adjoinCoefficients t₄ <|
      Subring.adjoinCoefficients t₃ <|
      Subring.adjoinCoefficients (Set.range f) <|
      Subring.adjoinCoefficients t₂ <|
      core t₁;
    HasCoefficients (f n) R₀ ∧ HasCoefficients p.val R₀ :=
  ⟨inferInstance, inferInstance⟩

end HasCoefficients

/-- A relation of elements of a set `A` of a ring is a multivariate polynomial in
the elements of `A`. -/
def Relation (A : Set R) : Type _ := MvPolynomial A R

namespace Relation

variable {A : Set R}

noncomputable instance : CommRing (Relation A) :=
  inferInstanceAs <| CommRing <| MvPolynomial A R

/-- Evaluating a relation is computing the formal polynomial in `R`. -/
def eval : Relation A →+* R :=
  MvPolynomial.eval Subtype.val

/-- A relation is homogeneous if the underlying polynomial is. -/
def IsHomogeneous (r : Relation A) (n : ℕ) : Prop :=
  MvPolynomial.IsHomogeneous r n

theorem IsHomogeneous_iff (r : Relation A) (n : ℕ) :
    r.IsHomogeneous n ↔ MvPolynomial.IsHomogeneous r n := by
  rfl

variable {S : Type*} [CommRing S]
variable {f : R →+* S} {A : Set R} {B : Set S}

noncomputable def map (h : Set.MapsTo f A B) : Relation A →+* Relation B :=
  (MvPolynomial.map f).comp (MvPolynomial.rename h.restrict).toRingHom 

@[simp]
lemma map_apply (h : Set.MapsTo f A B) (p : Relation A) :
    map h p = MvPolynomial.map f (MvPolynomial.rename h.restrict p) :=
  rfl

lemma eval_comp_map (h : Set.MapsTo f A B) :
    f.comp eval = eval.comp (map h) := by
  change f.comp eval = (MvPolynomial.eval Subtype.val).comp (map h)
  dsimp only [eval, map]
  exact MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun a ↦ by simp)

lemma eval_map_apply (h : Set.MapsTo f A B) (p : Relation A) :
    eval (map h p) = f (eval p) := by
  change (eval.comp (map h)) p = (f.comp eval) p
  rw [eval_comp_map]

lemma isHomogeneous_of_map (h : Set.MapsTo f A B) (hinj : Function.Injective f)
    (r : Relation A) {n : ℕ} (homog : Relation.IsHomogeneous (Relation.map h r) n) :
    r.IsHomogeneous n := by
  simp only [map_apply] at homog
  have h1 : Function.Injective h.restrict := by
    rw [Set.MapsTo.restrict_inj]
    apply Set.injOn_of_injective hinj
  apply MvPolynomial.IsHomogeneous.of_map f hinj at homog
  rw [MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff h1] at homog
  exact homog

end Relation

section HasRelation

variable {ι : Type*} {s : Set (MvPolynomial ι R)} {t : Set (MvPolynomial ι R)}

/-- A typeclass expressing that `R₀` contains the coefficients of a relation `r`. -/
class HasRelation (r : Relation s) (R₀ : Subring R) : Prop where
  has_coeffs : ∀ p : (MvPolynomial.coefficients r), HasCoefficients p.val R₀

theorem coefficients_coefficients_subset (r : Relation s) (R₀ : Subring R) [HasRelation r R₀] :
    (MvPolynomial.coefficients r).coefficients ⊆ R₀ := by
  intro a ha
  simp only [Set.coefficients, Set.iUnion_coe_set, Set.mem_iUnion] at ha
  obtain ⟨p, hp, hpa⟩ := ha
  exact (HasRelation.has_coeffs ⟨p, hp⟩).has_coeffs hpa

/-- Adjoin the coefficients of a set of relations to a subring `R₀`. -/
def _root_.Subring.adjoinRelations (rs : Set (Relation s)) (R₀ : Subring R) : Subring R :=
  (Algebra.adjoin R₀ (rs.coefficients.coefficients)).toSubring

instance (rs : Set (Relation s)) (R₀ : Subring R) : Algebra R₀ (R₀.adjoinRelations rs) :=
  inferInstanceAs <| Algebra R₀ <| Algebra.adjoin R₀ (rs.coefficients.coefficients)

theorem _root_.Subring.adjoinRelations_finiteType_of_finite (rs : Set (Relation s))
      (hf : rs.Finite) (R₀ : Subring R) :
    FiniteType R₀ (R₀.adjoinRelations rs) := by
  apply FiniteType.of_adjoin_finite _
  apply rs.coefficients.coefficients_finite_of_finite
  apply rs.coefficients_finite_of_finite
  exact hf

theorem _root_.Subring.adjoinRelations_finiteType_of_finite' (rs : Set (Relation s))
      (hf : rs.Finite) (R₀ : Subring R) [FiniteType ℤ R₀] :
    FiniteType ℤ (R₀.adjoinRelations rs) :=
  FiniteType.trans inferInstance (R₀.adjoinRelations_finiteType_of_finite rs hf)

/-- After adjoining a set `rs` of relations to `R₀`, it has each element of `rs`. -/
instance HasRelation.of_mem (rs : Set (Relation s)) (r : rs) (R₀ : Subring R) :
    HasRelation r.val (R₀.adjoinRelations rs) where
  has_coeffs := fun ⟨p, hp⟩ ↦ by
    refine ⟨Set.Subset.trans ?_ Algebra.subset_adjoin⟩
    intro a ha
    simp_all only [Set.coefficients, Set.iUnion_coe_set, Set.mem_iUnion, exists_prop,
      Set.iUnion_exists, Set.biUnion_and']
    refine ⟨r.val, r.property, p, hp, ha⟩

/-- If `R₀` has the coefficients of a relation `r`, then after adjoining more coefficients,
the new subring still has the coefficients of `r`. -/
instance HasRelation.trans (r : Relation t) (rs : Set (Relation s)) (R₀ : Subring R)
    [HasRelation r R₀] : HasRelation r (R₀.adjoinRelations rs) where
  has_coeffs := fun ⟨p, hp⟩ ↦ by
    have : ((R₀.subtype).range : Set R) ⊆
        (Algebra.adjoin R₀ rs.coefficients.coefficients).toSubring :=
      Set.Subset.trans (Set.subset_union_left _ _) Subsemiring.subset_closure
    rw [Subring.range_subtype] at this
    exact ⟨Set.Subset.trans (HasRelation.has_coeffs ⟨p, hp⟩).has_coeffs this⟩

instance {α : Type*} (f : α → Relation s) (R₀ : Subring R) (a : α) :
    HasRelation (f a) (R₀.adjoinRelations (Set.range f)) :=
  HasRelation.of_mem _ ⟨f a, Set.mem_range_self a⟩ _

instance (p : MvPolynomial ι R) (rs : Set (Relation s)) (R₀ : Subring R)
    [HasCoefficients p R₀] : HasCoefficients p (R₀.adjoinRelations rs) where
  has_coeffs := by
    have : ((R₀.subtype).range : Set R) ⊆
        (Algebra.adjoin R₀ rs.coefficients.coefficients).toSubring :=
      Set.Subset.trans (Set.subset_union_left _ _) Subsemiring.subset_closure
    rw [Subring.range_subtype] at this
    exact Set.Subset.trans HasCoefficients.has_coeffs this

/- Lean automatically infers that any of the adjoined polynomials has coefficients in the new
ring. -/
example (t₁ t₂ : Set (MvPolynomial ι R)) (f : ℕ → MvPolynomial ι R)
  (rs : Set (Relation t₂)) (g : ℤ → Relation t₁) (r : rs) (n : ℕ) (m : ℤ) :
    let R₀ := Subring.adjoinRelations rs <|
      Subring.adjoinRelations (Set.range g) <|
      Subring.adjoinCoefficients (Set.range f) <|
      Subring.adjoinCoefficients t₂ <|
      core t₁;
    HasCoefficients (f n) R₀ ∧ HasRelation (g m) R₀ ∧ HasRelation r.val R₀ :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end HasRelation

/-- A model of `MvPolynomial σ R ⧸ I` is a choice of generators of `I` and a subring `R₀`
which contains the coefficients of the generators. -/
structure Model {σ : Type*} (I : Ideal (MvPolynomial σ R)) where
  s : Set (MvPolynomial σ R)
  hs : Ideal.span s = I
  R₀ : Subring R
  coeffs : ∀ p : s, HasCoefficients p.val R₀ := by infer_instance

namespace Model

attribute [instance] coeffs

variable {σ : Type*} {I : Ideal (MvPolynomial σ R)} (M : Model I)

theorem coefficients_subset (p : MvPolynomial σ R) (hp : p ∈ M.s) :
    p.coefficients ⊆ M.R₀ :=
  (M.coeffs ⟨p, hp⟩).has_coeffs

theorem coefficients_subset_range : M.s.coefficients ⊆ (algebraMap M.R₀ R).range := by
  intro x hx
  simp only [Set.coefficients] at hx
  simp at hx
  obtain ⟨p, hp, hpx⟩ := hx
  exact ⟨⟨x, coefficients_subset M p hp hpx⟩, rfl⟩

/-- Construct a model by giving a set `s` of generators of `I`. The underlying subring
is `core s`. -/
def mkOfGenerators (s : Set (MvPolynomial σ R)) (hs : Ideal.span s = I) : Model I where
  s := s
  hs := hs
  R₀ := core s

/-- Intersection of `M.s` with `M.R₀`. Informally this is equal to `M.s`, since the coefficients
of `M.s` lie in `M.R₀`. -/
def s₀ : Set (MvPolynomial σ M.R₀) := (MvPolynomial.map M.R₀.subtype) ⁻¹' M.s

/-- The ideal generated by the pulled back generators. -/
def I₀ : Ideal (MvPolynomial σ M.R₀) := Ideal.span M.s₀

/-- The model of `MvPolynomial σ M.R ⧸ I` over `M.R₀`. -/
def A₀ : Type _ := MvPolynomial σ M.R₀ ⧸ M.I₀

noncomputable instance : CommRing M.A₀ :=
  inferInstanceAs <| CommRing <| MvPolynomial σ M.R₀ ⧸ M.I₀

noncomputable instance : Algebra M.R₀ M.A₀ :=
  inferInstanceAs <| Algebra M.R₀ <| MvPolynomial σ M.R₀ ⧸ M.I₀

/-- `M.s₀` is mapped to `M.s` under the canonical map
`MvPolynomial σ R₀ → MvPolynomial σ R`. -/
theorem mapsTo : Set.MapsTo (MvPolynomial.map (M.R₀.subtype)) M.s₀ M.s :=
  Set.mapsTo_preimage (MvPolynomial.map M.R₀.subtype) M.s

theorem mapsTo_restrict_injective : Function.Injective M.mapsTo.restrict := by
  rw [Set.MapsTo.restrict_inj]
  apply Set.injOn_of_injective
    (MvPolynomial.map_injective M.R₀.subtype Subtype.val_injective)

theorem mapsTo_restrict_surjective : Function.Surjective M.mapsTo.restrict := by
  intro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := MvPolynomial.mem_range_of_coefficients' x (M.coefficients_subset x hx)
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  · show MvPolynomial.map M.R₀.subtype y ∈ M.s
    rw [hy]
    exact hx

/-- Restricting `MvPolynomial σ R₀ → MvPolynomial σ R` yields an equivalence `M.s₀ ≃ M.s`. -/
noncomputable def definingSetEquiv : M.s₀ ≃ M.s :=
  Equiv.ofBijective M.mapsTo.restrict ⟨M.mapsTo_restrict_injective, M.mapsTo_restrict_surjective⟩

@[simp]
theorem definingSetEquiv_apply (p : M.s₀) :
    M.definingSetEquiv p = MvPolynomial.map M.R₀.subtype p.val := by
  rfl

theorem finitePresentation_of_finite [Fintype σ] (hf : Set.Finite M.s) :
    FinitePresentation M.R₀ M.A₀ := by
  apply FinitePresentation.quotient
  have hf₀ : Set.Finite M.s₀ := (M.definingSetEquiv.set_finite_iff).mpr hf
  obtain ⟨s₀', hs₀'⟩ := Set.Finite.exists_finset_coe hf₀
  refine ⟨s₀', by rw [hs₀']; rfl⟩

end Model

namespace Relation

variable {σ : Type*} {I : Ideal (MvPolynomial σ R)} (M : Model I)

/-- If a relation `r` in `M.s` has coefficients in `M.R₀`, it is represented by a relation
in `M.s₀`. -/
theorem exists_repr (r : Relation M.s) [HasRelation r M.R₀] :
    ∃ (t : Relation M.s₀), Relation.map M.mapsTo t = r := by
  have hc : MvPolynomial.coefficients r ⊆ Set.range (MvPolynomial.map M.R₀.subtype) := by
    intro p hp
    have hc : MvPolynomial.coefficients p ⊆ M.R₀ :=
      Set.Subset.trans (Set.coefficients_subset_coefficients _ _ hp)
        (coefficients_coefficients_subset r _)
    obtain ⟨p₀, hp₀⟩ := MvPolynomial.mem_range_of_coefficients' p hc
    use p₀
  obtain ⟨t', ht'⟩ := MvPolynomial.mem_range_of_coefficients r hc
  use (MvPolynomial.rename M.definingSetEquiv.symm t')
  simp only [Relation.map_apply, MvPolynomial.map_rename, MvPolynomial.rename_rename]
  change MvPolynomial.rename (M.definingSetEquiv ∘ M.definingSetEquiv.symm) _ = _
  simpa

/-- Choose a representative of a relation in `M.s` with coefficients in `M.R₀`. -/
noncomputable def repr (r : Relation M.s) [HasRelation r M.R₀] :
    Relation M.s₀ :=
  (r.exists_repr M).choose

@[simp]
theorem repr_map (r : Relation M.s) [RingOfDefinition.HasRelation r M.R₀] :
    map M.mapsTo (r.repr M) = r :=
  (r.exists_repr M).choose_spec

theorem repr_homogeneous (r : Relation M.s) [HasRelation r M.R₀] {n : ℕ}
    (homog : r.IsHomogeneous n) : (Relation.repr M r).IsHomogeneous n := by
  apply Relation.isHomogeneous_of_map M.mapsTo
  · apply MvPolynomial.map_injective (SubringClass.subtype M.R₀) Subtype.val_injective
  · rwa [Relation.repr_map]

theorem eval_map (r : Relation M.s₀) :
    eval (map M.mapsTo r) = MvPolynomial.map M.R₀.subtype (eval r) := by
  rw [← eval_map_apply M.mapsTo]

/-- Equality of a relation in `M.s₀` can be tested in `R`. -/
theorem eval_eq_of_eval_eq (r : Relation M.s₀) (p : MvPolynomial σ M.R₀)
    (h : eval (map M.mapsTo r) = MvPolynomial.map M.R₀.subtype p) :
    eval r = p := by
  apply MvPolynomial.map_injective M.R₀.subtype Subtype.val_injective
  rwa [← Relation.eval_map]

end Relation

end RingOfDefinition
