/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.Supported
import Mathlib.RingTheory.Algebraic
import Mathlib.Data.MvPolynomial.Equiv

#align_import ring_theory.algebraic_independent from "leanprover-community/mathlib"@"949dc57e616a621462062668c9f39e4e17b64b69"

/-!
# Algebraic Independence

This file defines algebraic independence of a family of element of an `R` algebra.

## Main definitions

* `AlgebraicIndependent` - `AlgebraicIndependent R x` states the family of elements `x`
  is algebraically independent over `R`, meaning that the canonical map out of the multivariable
  polynomial ring is injective.

* `AlgebraicIndependent.repr` - The canonical map from the subalgebra generated by an
  algebraic independent family into the polynomial ring.

## References

* [Stacks: Transcendence](https://stacks.math.columbia.edu/tag/030D)

## TODO
Define the transcendence degree and show it is independent of the choice of a
transcendence basis.

## Tags
transcendence basis, transcendence degree, transcendence

-/


noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

open Classical BigOperators

universe x u v w

variable {ι : Type*} {ι' : Type*} (R : Type*) {K : Type*}

variable {A : Type*} {A' A'' : Type*} {V : Type u} {V' : Type*}

variable (x : ι → A)

variable [CommRing R] [CommRing A] [CommRing A'] [CommRing A'']

variable [Algebra R A] [Algebra R A'] [Algebra R A'']

variable {a b : R}

/-- `AlgebraicIndependent R x` states the family of elements `x`
  is algebraically independent over `R`, meaning that the canonical
  map out of the multivariable polynomial ring is injective. -/
def AlgebraicIndependent : Prop :=
  Injective (MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] A)
#align algebraic_independent AlgebraicIndependent

variable {R} {x}

theorem algebraicIndependent_iff_ker_eq_bot :
    AlgebraicIndependent R x ↔
      RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] A).toRingHom = ⊥ :=
  RingHom.injective_iff_ker_eq_bot _
#align algebraic_independent_iff_ker_eq_bot algebraicIndependent_iff_ker_eq_bot

theorem algebraicIndependent_iff :
    AlgebraicIndependent R x ↔
      ∀ p : MvPolynomial ι R, MvPolynomial.aeval (x : ι → A) p = 0 → p = 0 :=
  injective_iff_map_eq_zero _
#align algebraic_independent_iff algebraicIndependent_iff

theorem AlgebraicIndependent.eq_zero_of_aeval_eq_zero (h : AlgebraicIndependent R x) :
    ∀ p : MvPolynomial ι R, MvPolynomial.aeval (x : ι → A) p = 0 → p = 0 :=
  algebraicIndependent_iff.1 h
#align algebraic_independent.eq_zero_of_aeval_eq_zero AlgebraicIndependent.eq_zero_of_aeval_eq_zero

theorem algebraicIndependent_iff_injective_aeval :
    AlgebraicIndependent R x ↔ Injective (MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] A) :=
  Iff.rfl
#align algebraic_independent_iff_injective_aeval algebraicIndependent_iff_injective_aeval

@[simp]
theorem algebraicIndependent_empty_type_iff [IsEmpty ι] :
    AlgebraicIndependent R x ↔ Injective (algebraMap R A) := by
  have : aeval x = (Algebra.ofId R A).comp (@isEmptyAlgEquiv R ι _ _).toAlgHom := by
    ext i
    exact IsEmpty.elim' ‹IsEmpty ι› i
  rw [AlgebraicIndependent, this, ← Injective.of_comp_iff' _ (@isEmptyAlgEquiv R ι _ _).bijective]
  rfl
#align algebraic_independent_empty_type_iff algebraicIndependent_empty_type_iff

namespace AlgebraicIndependent

variable (hx : AlgebraicIndependent R x)

theorem algebraMap_injective : Injective (algebraMap R A) := by
  simpa [← MvPolynomial.algebraMap_eq, Function.comp] using
    (Injective.of_comp_iff (algebraicIndependent_iff_injective_aeval.1 hx) MvPolynomial.C).2
      (MvPolynomial.C_injective _ _)
#align algebraic_independent.algebra_map_injective AlgebraicIndependent.algebraMap_injective

theorem linearIndependent : LinearIndependent R x := by
  rw [linearIndependent_iff_injective_total]
  have : Finsupp.total ι A R x =
      (MvPolynomial.aeval x).toLinearMap.comp (Finsupp.total ι _ R X) := by
    ext
    simp
  rw [this]
  refine' hx.comp _
  rw [← linearIndependent_iff_injective_total]
  exact linearIndependent_X _ _
#align algebraic_independent.linear_independent AlgebraicIndependent.linearIndependent

protected theorem injective [Nontrivial R] : Injective x :=
  hx.linearIndependent.injective
#align algebraic_independent.injective AlgebraicIndependent.injective

theorem ne_zero [Nontrivial R] (i : ι) : x i ≠ 0 :=
  hx.linearIndependent.ne_zero i
#align algebraic_independent.ne_zero AlgebraicIndependent.ne_zero

theorem comp (f : ι' → ι) (hf : Function.Injective f) : AlgebraicIndependent R (x ∘ f) := by
  intro p q
  simpa [aeval_rename, (rename_injective f hf).eq_iff] using @hx (rename f p) (rename f q)
#align algebraic_independent.comp AlgebraicIndependent.comp

theorem coe_range : AlgebraicIndependent R ((↑) : range x → A) := by
  simpa using hx.comp _ (rangeSplitting_injective x)
#align algebraic_independent.coe_range AlgebraicIndependent.coe_range

theorem map {f : A →ₐ[R] A'} (hf_inj : Set.InjOn f (adjoin R (range x))) :
    AlgebraicIndependent R (f ∘ x) := by
  have : aeval (f ∘ x) = f.comp (aeval x) := by ext; simp
  have h : ∀ p : MvPolynomial ι R, aeval x p ∈ (@aeval R _ _ _ _ _ ((↑) : range x → A)).range := by
    intro p
    rw [AlgHom.mem_range]
    refine' ⟨MvPolynomial.rename (codRestrict x (range x) mem_range_self) p, _⟩
    simp [Function.comp, aeval_rename]
  intro x y hxy
  rw [this] at hxy
  rw [adjoin_eq_range] at hf_inj
  exact hx (hf_inj (h x) (h y) hxy)
#align algebraic_independent.map AlgebraicIndependent.map

theorem map' {f : A →ₐ[R] A'} (hf_inj : Injective f) : AlgebraicIndependent R (f ∘ x) :=
  hx.map (injOn_of_injective hf_inj _)
#align algebraic_independent.map' AlgebraicIndependent.map'

theorem of_comp (f : A →ₐ[R] A') (hfv : AlgebraicIndependent R (f ∘ x)) :
    AlgebraicIndependent R x := by
  have : aeval (f ∘ x) = f.comp (aeval x) := by ext; simp
  rw [AlgebraicIndependent, this, AlgHom.coe_comp] at hfv
  exact hfv.of_comp
#align algebraic_independent.of_comp AlgebraicIndependent.of_comp

end AlgebraicIndependent

open AlgebraicIndependent

theorem AlgHom.algebraicIndependent_iff (f : A →ₐ[R] A') (hf : Injective f) :
    AlgebraicIndependent R (f ∘ x) ↔ AlgebraicIndependent R x :=
  ⟨fun h => h.of_comp f, fun h => h.map (injOn_of_injective hf _)⟩
#align alg_hom.algebraic_independent_iff AlgHom.algebraicIndependent_iff

@[nontriviality]
theorem algebraicIndependent_of_subsingleton [Subsingleton R] : AlgebraicIndependent R x :=
  algebraicIndependent_iff.2 fun _ _ => Subsingleton.elim _ _
#align algebraic_independent_of_subsingleton algebraicIndependent_of_subsingleton

theorem algebraicIndependent_equiv (e : ι ≃ ι') {f : ι' → A} :
    AlgebraicIndependent R (f ∘ e) ↔ AlgebraicIndependent R f :=
  ⟨fun h => Function.comp_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective,
    fun h => h.comp _ e.injective⟩
#align algebraic_independent_equiv algebraicIndependent_equiv

theorem algebraicIndependent_equiv' (e : ι ≃ ι') {f : ι' → A} {g : ι → A} (h : f ∘ e = g) :
    AlgebraicIndependent R g ↔ AlgebraicIndependent R f :=
  h ▸ algebraicIndependent_equiv e
#align algebraic_independent_equiv' algebraicIndependent_equiv'

theorem algebraicIndependent_subtype_range {ι} {f : ι → A} (hf : Injective f) :
    AlgebraicIndependent R ((↑) : range f → A) ↔ AlgebraicIndependent R f :=
  Iff.symm <| algebraicIndependent_equiv' (Equiv.ofInjective f hf) rfl
#align algebraic_independent_subtype_range algebraicIndependent_subtype_range

alias ⟨AlgebraicIndependent.of_subtype_range, _⟩ := algebraicIndependent_subtype_range
#align algebraic_independent.of_subtype_range AlgebraicIndependent.of_subtype_range

theorem algebraicIndependent_image {ι} {s : Set ι} {f : ι → A} (hf : Set.InjOn f s) :
    (AlgebraicIndependent R fun x : s => f x) ↔ AlgebraicIndependent R fun x : f '' s => (x : A) :=
  algebraicIndependent_equiv' (Equiv.Set.imageOfInjOn _ _ hf) rfl
#align algebraic_independent_image algebraicIndependent_image

theorem algebraicIndependent_adjoin (hs : AlgebraicIndependent R x) :
    @AlgebraicIndependent ι R (adjoin R (range x))
      (fun i : ι => ⟨x i, subset_adjoin (mem_range_self i)⟩) _ _ _ :=
  AlgebraicIndependent.of_comp (adjoin R (range x)).val hs
#align algebraic_independent_adjoin algebraicIndependent_adjoin

/-- A set of algebraically independent elements in an algebra `A` over a ring `K` is also
algebraically independent over a subring `R` of `K`. -/
theorem AlgebraicIndependent.restrictScalars {K : Type*} [CommRing K] [Algebra R K] [Algebra K A]
    [IsScalarTower R K A] (hinj : Function.Injective (algebraMap R K))
    (ai : AlgebraicIndependent K x) : AlgebraicIndependent R x := by
  have : (aeval x : MvPolynomial ι K →ₐ[K] A).toRingHom.comp (MvPolynomial.map (algebraMap R K)) =
      (aeval x : MvPolynomial ι R →ₐ[R] A).toRingHom := by
    ext <;> simp [algebraMap_eq_smul_one]
  show Injective (aeval x).toRingHom
  rw [← this, RingHom.coe_comp]
  exact Injective.comp ai (MvPolynomial.map_injective _ hinj)
#align algebraic_independent.restrict_scalars AlgebraicIndependent.restrictScalars

/-- Every finite subset of an algebraically independent set is algebraically independent. -/
theorem algebraicIndependent_finset_map_embedding_subtype (s : Set A)
    (li : AlgebraicIndependent R ((↑) : s → A)) (t : Finset s) :
    AlgebraicIndependent R ((↑) : Finset.map (Embedding.subtype s) t → A) := by
  let f : t.map (Embedding.subtype s) → s := fun x =>
    ⟨x.1, by
      obtain ⟨x, h⟩ := x
      rw [Finset.mem_map] at h
      obtain ⟨a, _, rfl⟩ := h
      simp only [Subtype.coe_prop, Embedding.coe_subtype]⟩
  convert AlgebraicIndependent.comp li f _
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  rw [Finset.mem_map] at hx hy
  obtain ⟨a, _, rfl⟩ := hx
  obtain ⟨b, _, rfl⟩ := hy
  simp only [imp_self, Subtype.mk_eq_mk]
#align algebraic_independent_finset_map_embedding_subtype algebraicIndependent_finset_map_embedding_subtype

/-- If every finite set of algebraically independent element has cardinality at most `n`,
then the same is true for arbitrary sets of algebraically independent elements. -/
theorem algebraicIndependent_bounded_of_finset_algebraicIndependent_bounded {n : ℕ}
    (H : ∀ s : Finset A, (AlgebraicIndependent R fun i : s => (i : A)) → s.card ≤ n) :
    ∀ s : Set A, AlgebraicIndependent R ((↑) : s → A) → Cardinal.mk s ≤ n := by
  intro s li
  apply Cardinal.card_le_of
  intro t
  rw [← Finset.card_map (Embedding.subtype s)]
  apply H
  apply algebraicIndependent_finset_map_embedding_subtype _ li
#align algebraic_independent_bounded_of_finset_algebraic_independent_bounded algebraicIndependent_bounded_of_finset_algebraicIndependent_bounded

section Subtype

theorem AlgebraicIndependent.restrict_of_comp_subtype {s : Set ι}
    (hs : AlgebraicIndependent R (x ∘ (↑) : s → A)) : AlgebraicIndependent R (s.restrict x) :=
  hs
#align algebraic_independent.restrict_of_comp_subtype AlgebraicIndependent.restrict_of_comp_subtype

variable (R A)

theorem algebraicIndependent_empty_iff :
    AlgebraicIndependent R ((↑) : (∅ : Set A) → A) ↔ Injective (algebraMap R A) := by simp
#align algebraic_independent_empty_iff algebraicIndependent_empty_iff

variable {R A}

theorem AlgebraicIndependent.mono {t s : Set A} (h : t ⊆ s)
    (hx : AlgebraicIndependent R ((↑) : s → A)) : AlgebraicIndependent R ((↑) : t → A) := by
  simpa [Function.comp] using hx.comp (inclusion h) (inclusion_injective h)
#align algebraic_independent.mono AlgebraicIndependent.mono

end Subtype

theorem AlgebraicIndependent.to_subtype_range {ι} {f : ι → A} (hf : AlgebraicIndependent R f) :
    AlgebraicIndependent R ((↑) : range f → A) := by
  nontriviality R
  rwa [algebraicIndependent_subtype_range hf.injective]
#align algebraic_independent.to_subtype_range AlgebraicIndependent.to_subtype_range

theorem AlgebraicIndependent.to_subtype_range' {ι} {f : ι → A} (hf : AlgebraicIndependent R f) {t}
    (ht : range f = t) : AlgebraicIndependent R ((↑) : t → A) :=
  ht ▸ hf.to_subtype_range
#align algebraic_independent.to_subtype_range' AlgebraicIndependent.to_subtype_range'

theorem algebraicIndependent_comp_subtype {s : Set ι} :
    AlgebraicIndependent R (x ∘ (↑) : s → A) ↔
      ∀ p ∈ MvPolynomial.supported R s, aeval x p = 0 → p = 0 := by
  have : (aeval (x ∘ (↑) : s → A) : _ →ₐ[R] _) = (aeval x).comp (rename (↑)) := by ext; simp
  have : ∀ p : MvPolynomial s R, rename ((↑) : s → ι) p = 0 ↔ p = 0 :=
    (injective_iff_map_eq_zero' (rename ((↑) : s → ι) : MvPolynomial s R →ₐ[R] _).toRingHom).1
      (rename_injective _ Subtype.val_injective)
  simp [algebraicIndependent_iff, supported_eq_range_rename, *]
#align algebraic_independent_comp_subtype algebraicIndependent_comp_subtype

theorem algebraicIndependent_subtype {s : Set A} :
    AlgebraicIndependent R ((↑) : s → A) ↔
      ∀ p : MvPolynomial A R, p ∈ MvPolynomial.supported R s → aeval id p = 0 → p = 0 := by
  apply @algebraicIndependent_comp_subtype _ _ _ id
#align algebraic_independent_subtype algebraicIndependent_subtype

theorem algebraicIndependent_of_finite (s : Set A)
    (H : ∀ t ⊆ s, t.Finite → AlgebraicIndependent R ((↑) : t → A)) :
    AlgebraicIndependent R ((↑) : s → A) :=
  algebraicIndependent_subtype.2 fun p hp =>
    algebraicIndependent_subtype.1 (H _ (mem_supported.1 hp) (Finset.finite_toSet _)) _ (by simp)
#align algebraic_independent_of_finite algebraicIndependent_of_finite

theorem AlgebraicIndependent.image_of_comp {ι ι'} (s : Set ι) (f : ι → ι') (g : ι' → A)
    (hs : AlgebraicIndependent R fun x : s => g (f x)) :
    AlgebraicIndependent R fun x : f '' s => g x := by
  nontriviality R
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  exact (algebraicIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs
#align algebraic_independent.image_of_comp AlgebraicIndependent.image_of_comp

theorem AlgebraicIndependent.image {ι} {s : Set ι} {f : ι → A}
    (hs : AlgebraicIndependent R fun x : s => f x) :
    AlgebraicIndependent R fun x : f '' s => (x : A) := by
  convert AlgebraicIndependent.image_of_comp s f id hs
#align algebraic_independent.image AlgebraicIndependent.image

theorem algebraicIndependent_iUnion_of_directed {η : Type*} [Nonempty η] {s : η → Set A}
    (hs : Directed (· ⊆ ·) s) (h : ∀ i, AlgebraicIndependent R ((↑) : s i → A)) :
    AlgebraicIndependent R ((↑) : (⋃ i, s i) → A) := by
  refine' algebraicIndependent_of_finite (⋃ i, s i) fun t ht ft => _
  rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
  rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
  exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
#align algebraic_independent_Union_of_directed algebraicIndependent_iUnion_of_directed

theorem algebraicIndependent_sUnion_of_directed {s : Set (Set A)} (hsn : s.Nonempty)
    (hs : DirectedOn (· ⊆ ·) s) (h : ∀ a ∈ s, AlgebraicIndependent R ((↑) : a → A)) :
    AlgebraicIndependent R ((↑) : ⋃₀ s → A) := by
  letI : Nonempty s := Nonempty.to_subtype hsn
  rw [sUnion_eq_iUnion]
  exact algebraicIndependent_iUnion_of_directed hs.directed_val (by simpa using h)
#align algebraic_independent_sUnion_of_directed algebraicIndependent_sUnion_of_directed

theorem exists_maximal_algebraicIndependent (s t : Set A) (hst : s ⊆ t)
    (hs : AlgebraicIndependent R ((↑) : s → A)) :
    ∃ u : Set A, AlgebraicIndependent R ((↑) : u → A) ∧ s ⊆ u ∧ u ⊆ t ∧
      ∀ x : Set A, AlgebraicIndependent R ((↑) : x → A) → u ⊆ x → x ⊆ t → x = u := by
  rcases zorn_subset_nonempty { u : Set A | AlgebraicIndependent R ((↑) : u → A) ∧ s ⊆ u ∧ u ⊆ t }
      (fun c hc chainc hcn =>
        ⟨⋃₀ c, by
          refine' ⟨⟨algebraicIndependent_sUnion_of_directed hcn chainc.directedOn
              fun a ha => (hc ha).1, _, _⟩, _⟩
          · cases' hcn with x hx
            exact subset_sUnion_of_subset _ x (hc hx).2.1 hx
          · exact sUnion_subset fun x hx => (hc hx).2.2
          · intro s
            exact subset_sUnion_of_mem⟩)
      s ⟨hs, Set.Subset.refl s, hst⟩ with
    ⟨u, ⟨huai, _, hut⟩, hsu, hx⟩
  use u, huai, hsu, hut
  intro x hxai huv hxt
  exact hx _ ⟨hxai, _root_.trans hsu huv, hxt⟩ huv
#align exists_maximal_algebraic_independent exists_maximal_algebraicIndependent

section repr

variable (hx : AlgebraicIndependent R x)

/-- Canonical isomorphism between polynomials and the subalgebra generated by
  algebraically independent elements. -/
@[simps!]
def AlgebraicIndependent.aevalEquiv (hx : AlgebraicIndependent R x) :
    MvPolynomial ι R ≃ₐ[R] Algebra.adjoin R (range x) := by
  apply
    AlgEquiv.ofBijective (AlgHom.codRestrict (@aeval R A ι _ _ _ x) (Algebra.adjoin R (range x)) _)
  swap
  · intro x
    rw [adjoin_range_eq_range_aeval]
    exact AlgHom.mem_range_self _ _
  · constructor
    · exact (AlgHom.injective_codRestrict _ _ _).2 hx
    · rintro ⟨x, hx⟩
      rw [adjoin_range_eq_range_aeval] at hx
      rcases hx with ⟨y, rfl⟩
      use y
      ext
      simp
#align algebraic_independent.aeval_equiv AlgebraicIndependent.aevalEquiv

--@[simp] Porting note: removing simp because the linter complains about deterministic timeout
theorem AlgebraicIndependent.algebraMap_aevalEquiv (hx : AlgebraicIndependent R x)
    (p : MvPolynomial ι R) :
    algebraMap (Algebra.adjoin R (range x)) A (hx.aevalEquiv p) = aeval x p :=
  rfl
#align algebraic_independent.algebra_map_aeval_equiv AlgebraicIndependent.algebraMap_aevalEquiv

/-- The canonical map from the subalgebra generated by an algebraic independent family
  into the polynomial ring. -/
def AlgebraicIndependent.repr (hx : AlgebraicIndependent R x) :
    Algebra.adjoin R (range x) →ₐ[R] MvPolynomial ι R :=
  hx.aevalEquiv.symm
#align algebraic_independent.repr AlgebraicIndependent.repr

@[simp]
theorem AlgebraicIndependent.aeval_repr (p) : aeval x (hx.repr p) = p :=
  Subtype.ext_iff.1 (AlgEquiv.apply_symm_apply hx.aevalEquiv p)
#align algebraic_independent.aeval_repr AlgebraicIndependent.aeval_repr

theorem AlgebraicIndependent.aeval_comp_repr : (aeval x).comp hx.repr = Subalgebra.val _ :=
  AlgHom.ext <| hx.aeval_repr
#align algebraic_independent.aeval_comp_repr AlgebraicIndependent.aeval_comp_repr

theorem AlgebraicIndependent.repr_ker :
    RingHom.ker (hx.repr : adjoin R (range x) →+* MvPolynomial ι R) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).1 (AlgEquiv.injective _)
#align algebraic_independent.repr_ker AlgebraicIndependent.repr_ker

end repr

-- TODO - make this an `AlgEquiv`
/-- The isomorphism between `MvPolynomial (Option ι) R` and the polynomial ring over
the algebra generated by an algebraically independent family. -/
def AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin (hx : AlgebraicIndependent R x) :
    MvPolynomial (Option ι) R ≃+* Polynomial (adjoin R (Set.range x)) :=
  (MvPolynomial.optionEquivLeft _ _).toRingEquiv.trans
    (Polynomial.mapEquiv hx.aevalEquiv.toRingEquiv)
#align algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin

@[simp]
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply
    (hx : AlgebraicIndependent R x) (y) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin y =
      Polynomial.map (hx.aevalEquiv : MvPolynomial ι R →+* adjoin R (range x))
        (aeval (fun o : Option ι => o.elim Polynomial.X fun s : ι => Polynomial.C (X s)) y) :=
  rfl
#align algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_apply AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply

--@[simp] Porting note: removing simp because the linter complains about deterministic timeout
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C
    (hx : AlgebraicIndependent R x) (r) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin (C r) = Polynomial.C (algebraMap _ _ r) := by
  rw [AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply, aeval_C,
    IsScalarTower.algebraMap_apply R (MvPolynomial ι R), ← Polynomial.C_eq_algebraMap,
    Polynomial.map_C, RingHom.coe_coe, AlgEquiv.commutes]
set_option linter.uppercaseLean3 false in
#align algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_C AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C

--@[simp] Porting note: simp can prove it
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_none
    (hx : AlgebraicIndependent R x) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin (X none) = Polynomial.X := by
  rw [AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply, aeval_X, Option.elim,
    Polynomial.map_X]
set_option linter.uppercaseLean3 false in
#align algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_X_none AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_none

--@[simp] Porting note: simp can prove it
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_some
    (hx : AlgebraicIndependent R x) (i) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin (X (some i)) =
      Polynomial.C (hx.aevalEquiv (X i)) := by
  rw [AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply, aeval_X, Option.elim,
    Polynomial.map_C, RingHom.coe_coe]
set_option linter.uppercaseLean3 false in
#align algebraic_independent.mv_polynomial_option_equiv_polynomial_adjoin_X_some AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_some

theorem AlgebraicIndependent.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin
    (hx : AlgebraicIndependent R x) (a : A) :
    RingHom.comp
        (↑(Polynomial.aeval a : Polynomial (adjoin R (Set.range x)) →ₐ[_] A) :
          Polynomial (adjoin R (Set.range x)) →+* A)
        hx.mvPolynomialOptionEquivPolynomialAdjoin.toRingHom =
      ↑(MvPolynomial.aeval fun o : Option ι => o.elim a x : MvPolynomial (Option ι) R →ₐ[R] A) := by
  refine' MvPolynomial.ringHom_ext _ _ <;>
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgHom.coe_toRingHom, AlgHom.coe_toRingHom]
  · intro r
    rw [hx.mvPolynomialOptionEquivPolynomialAdjoin_C, aeval_C, Polynomial.aeval_C,
      IsScalarTower.algebraMap_apply R (adjoin R (range x)) A]
  · rintro (⟨⟩ | ⟨i⟩)
    · rw [hx.mvPolynomialOptionEquivPolynomialAdjoin_X_none, aeval_X, Polynomial.aeval_X,
        Option.elim]
    · rw [hx.mvPolynomialOptionEquivPolynomialAdjoin_X_some, Polynomial.aeval_C,
        hx.algebraMap_aevalEquiv, aeval_X, aeval_X, Option.elim]
#align algebraic_independent.aeval_comp_mv_polynomial_option_equiv_polynomial_adjoin AlgebraicIndependent.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin

theorem AlgebraicIndependent.option_iff (hx : AlgebraicIndependent R x) (a : A) :
    (AlgebraicIndependent R fun o : Option ι => o.elim a x) ↔
      ¬IsAlgebraic (adjoin R (Set.range x)) a := by
  rw [algebraicIndependent_iff_injective_aeval, isAlgebraic_iff_not_injective, Classical.not_not, ←
    AlgHom.coe_toRingHom, ← hx.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin,
    RingHom.coe_comp]
  exact Injective.of_comp_iff' (Polynomial.aeval a)
    (mvPolynomialOptionEquivPolynomialAdjoin hx).bijective
#align algebraic_independent.option_iff AlgebraicIndependent.option_iff

variable (R)

/-- A family is a transcendence basis if it is a maximal algebraically independent subset. -/
def IsTranscendenceBasis (x : ι → A) : Prop :=
  AlgebraicIndependent R x ∧
    ∀ (s : Set A) (_ : AlgebraicIndependent R ((↑) : s → A)) (_ : range x ≤ s), range x = s
#align is_transcendence_basis IsTranscendenceBasis

theorem exists_isTranscendenceBasis (h : Injective (algebraMap R A)) :
    ∃ s : Set A, IsTranscendenceBasis R ((↑) : s → A) := by
  cases' exists_maximal_algebraicIndependent (∅ : Set A) Set.univ (Set.subset_univ _)
      ((algebraicIndependent_empty_iff R A).2 h) with
    s hs
  use s, hs.1
  intro t ht hr
  simp only [Subtype.range_coe_subtype, setOf_mem_eq] at *
  exact Eq.symm (hs.2.2.2 t ht hr (Set.subset_univ _))
#align exists_is_transcendence_basis exists_isTranscendenceBasis

variable {R}

theorem AlgebraicIndependent.isTranscendenceBasis_iff {ι : Type w} {R : Type u} [CommRing R]
    [Nontrivial R] {A : Type v} [CommRing A] [Algebra R A] {x : ι → A}
    (i : AlgebraicIndependent R x) :
    IsTranscendenceBasis R x ↔
      ∀ (κ : Type v) (w : κ → A) (_ : AlgebraicIndependent R w) (j : ι → κ) (_ : w ∘ j = x),
        Surjective j := by
  fconstructor
  · rintro p κ w i' j rfl
    have p := p.2 (range w) i'.coe_range (range_comp_subset_range _ _)
    rw [range_comp, ← @image_univ _ _ w] at p
    exact range_iff_surjective.mp (image_injective.mpr i'.injective p)
  · intro p
    use i
    intro w i' h
    specialize p w ((↑) : w → A) i' (fun i => ⟨x i, range_subset_iff.mp h i⟩) (by ext; simp)
    have q := congr_arg (fun s => ((↑) : w → A) '' s) p.range_eq
    dsimp at q
    rw [← image_univ, image_image] at q
    simpa using q
#align algebraic_independent.is_transcendence_basis_iff AlgebraicIndependent.isTranscendenceBasis_iff

theorem IsTranscendenceBasis.isAlgebraic [Nontrivial R] (hx : IsTranscendenceBasis R x) :
    IsAlgebraic (adjoin R (range x)) A := by
  intro a
  rw [← not_iff_comm.1 (hx.1.option_iff _).symm]
  intro ai
  have h₁ : range x ⊆ range fun o : Option ι => o.elim a x := by
    rintro x ⟨y, rfl⟩
    exact ⟨some y, rfl⟩
  have h₂ : range x ≠ range fun o : Option ι => o.elim a x := by
    intro h
    have : a ∈ range x := by
      rw [h]
      exact ⟨none, rfl⟩
    rcases this with ⟨b, rfl⟩
    have : some b = none := ai.injective rfl
    simpa
  exact h₂ (hx.2 (Set.range fun o : Option ι => o.elim a x)
    ((algebraicIndependent_subtype_range ai.injective).2 ai) h₁)
#align is_transcendence_basis.is_algebraic IsTranscendenceBasis.isAlgebraic

section Field

variable [Field K] [Algebra K A]

/-Porting note: removing `simp`, not in simp normal form. Could make `Function.Injective f` a
simp lemma when `f` is a field hom, and then simp would prove this -/
theorem algebraicIndependent_empty_type [IsEmpty ι] [Nontrivial A] : AlgebraicIndependent K x := by
  rw [algebraicIndependent_empty_type_iff]
  exact RingHom.injective _
#align algebraic_independent_empty_type algebraicIndependent_empty_type

theorem algebraicIndependent_empty [Nontrivial A] :
    AlgebraicIndependent K ((↑) : (∅ : Set A) → A) :=
  algebraicIndependent_empty_type
#align algebraic_independent_empty algebraicIndependent_empty

end Field
