/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Algebraic Independence

This file contains basic results on algebraic independence of a family of elements of an `R`-algebra

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

open scoped Classical

variable {ι ι' R K A A' : Type*} {x : ι → A}
variable [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']

theorem algebraicIndependent_iff_ker_eq_bot :
    AlgebraicIndependent R x ↔
      RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] A).toRingHom = ⊥ :=
  RingHom.injective_iff_ker_eq_bot _

@[simp]
theorem algebraicIndependent_empty_type_iff [IsEmpty ι] :
    AlgebraicIndependent R x ↔ Injective (algebraMap R A) := by
  rw [algebraicIndependent_iff_injective_aeval, MvPolynomial.aeval_injective_iff_of_isEmpty]

namespace AlgebraicIndependent

variable (hx : AlgebraicIndependent R x)
include hx

theorem algebraMap_injective : Injective (algebraMap R A) := by
  simpa [Function.comp_def] using
    (Injective.of_comp_iff (algebraicIndependent_iff_injective_aeval.1 hx) MvPolynomial.C).2
      (MvPolynomial.C_injective _ _)

theorem linearIndependent : LinearIndependent R x := by
  rw [linearIndependent_iff_injective_linearCombination]
  have : Finsupp.linearCombination R x =
      (MvPolynomial.aeval x).toLinearMap.comp (Finsupp.linearCombination R X) := by
    ext
    simp
  rw [this]
  refine (algebraicIndependent_iff_injective_aeval.mp hx).comp ?_
  rw [← linearIndependent_iff_injective_linearCombination]
  exact linearIndependent_X _ _

protected theorem injective [Nontrivial R] : Injective x :=
  hx.linearIndependent.injective

theorem ne_zero [Nontrivial R] (i : ι) : x i ≠ 0 :=
  hx.linearIndependent.ne_zero i

theorem map {f : A →ₐ[R] A'} (hf_inj : Set.InjOn f (adjoin R (range x))) :
    AlgebraicIndependent R (f ∘ x) := by
  have : aeval (f ∘ x) = f.comp (aeval x) := by ext; simp
  have h : ∀ p : MvPolynomial ι R, aeval x p ∈ (@aeval R _ _ _ _ _ ((↑) : range x → A)).range := by
    intro p
    rw [AlgHom.mem_range]
    refine ⟨MvPolynomial.rename (codRestrict x (range x) mem_range_self) p, ?_⟩
    simp [Function.comp_def, aeval_rename]
  intro x y hxy
  rw [this] at hxy
  rw [adjoin_eq_range] at hf_inj
  exact hx (hf_inj (h x) (h y) hxy)

theorem map' {f : A →ₐ[R] A'} (hf_inj : Injective f) : AlgebraicIndependent R (f ∘ x) :=
  hx.map hf_inj.injOn

/-- If `x = {x_i : A | i : ι}` and `f = {f_i : MvPolynomial ι R | i : ι}` are algebraically
independent over `R`, then `{f_i(x) | i : ι}` is also algebraically independent over `R`.
For the partial converse, see `AlgebraicIndependent.of_aeval`. -/
theorem aeval_of_algebraicIndependent
    {f : ι → MvPolynomial ι R} (hf : AlgebraicIndependent R f) :
    AlgebraicIndependent R fun i ↦ aeval x (f i) := by
  rw [algebraicIndependent_iff] at hx hf ⊢
  intro p hp
  exact hf _ (hx _ (by rwa [← aeval_comp_bind₁, AlgHom.comp_apply] at hp))

omit hx in
/-- If `{f_i(x) | i : ι}` is algebraically independent over `R`, then
`{f_i : MvPolynomial ι R | i : ι}` is also algebraically independent over `R`.
In fact, the `x = {x_i : A | i : ι}` is also transcendental over `R` provided that `R`
is a field and `ι` is finite; the proof needs transcendence degree. -/
theorem of_aeval {f : ι → MvPolynomial ι R}
    (H : AlgebraicIndependent R fun i ↦ aeval x (f i)) :
    AlgebraicIndependent R f := by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
  exact H p (by rw [← aeval_comp_bind₁, AlgHom.comp_apply, bind₁, hp, map_zero])

end AlgebraicIndependent

theorem MvPolynomial.algebraicIndependent_X (σ R : Type*) [CommRing R] :
    AlgebraicIndependent R (X (R := R) (σ := σ)) := by
  rw [AlgebraicIndependent, aeval_X_left]
  exact injective_id

open AlgebraicIndependent

theorem AlgHom.algebraicIndependent_iff (f : A →ₐ[R] A') (hf : Injective f) :
    AlgebraicIndependent R (f ∘ x) ↔ AlgebraicIndependent R x :=
  ⟨fun h => h.of_comp f, fun h => h.map hf.injOn⟩

@[nontriviality]
theorem algebraicIndependent_of_subsingleton [Subsingleton R] : AlgebraicIndependent R x :=
  algebraicIndependent_iff.2 fun _ _ => Subsingleton.elim _ _

theorem algebraicIndependent_adjoin (hs : AlgebraicIndependent R x) :
    @AlgebraicIndependent ι R (adjoin R (range x))
      (fun i : ι => ⟨x i, subset_adjoin (mem_range_self i)⟩) _ _ _ :=
  AlgebraicIndependent.of_comp (adjoin R (range x)).val hs

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

section RingHom

variable {S B FRS FAB : Type*} [CommRing S] [CommRing B] [Algebra S B]

section

variable [FunLike FRS R S] [RingHomClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB)

theorem AlgebraicIndependent.of_ringHom_of_comp_eq (H : AlgebraicIndependent S (g ∘ x))
    (hf : Function.Injective f)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    AlgebraicIndependent R x := by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
  have := H (p.map f) <| by
    have : (g : A →+* B) _ = _ := congr(g $hp)
    rwa [map_zero, map_aeval, ← h, ← eval₂Hom_map_hom, ← aeval_eq_eval₂Hom] at this
  exact map_injective (f : R →+* S) hf (by rwa [map_zero])

theorem AlgebraicIndependent.ringHom_of_comp_eq (H : AlgebraicIndependent R x)
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    AlgebraicIndependent S (g ∘ x) := by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
  obtain ⟨q, rfl⟩ := map_surjective (f : R →+* S) hf p
  rw [H q (hg (by rwa [map_zero, ← RingHom.coe_coe g, map_aeval, ← h, ← eval₂Hom_map_hom,
    ← aeval_eq_eval₂Hom])), map_zero]

end

section

variable [EquivLike FRS R S] [RingEquivClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB)

theorem algebraicIndependent_ringHom_iff_of_comp_eq
    (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    AlgebraicIndependent S (g ∘ x) ↔ AlgebraicIndependent R x :=
  ⟨fun H ↦ H.of_ringHom_of_comp_eq f g (EquivLike.injective f) h,
    fun H ↦ H.ringHom_of_comp_eq f g (EquivLike.surjective f) hg h⟩

end

end RingHom

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
  simp only [f, imp_self, Subtype.mk_eq_mk]

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

section Subtype

theorem AlgebraicIndependent.restrict_of_comp_subtype {s : Set ι}
    (hs : AlgebraicIndependent R (x ∘ (↑) : s → A)) : AlgebraicIndependent R (s.restrict x) :=
  hs

variable (R A)

theorem algebraicIndependent_empty_iff :
    AlgebraicIndependent R ((↑) : (∅ : Set A) → A) ↔ Injective (algebraMap R A) := by simp

end Subtype

theorem AlgebraicIndependent.to_subtype_range {ι} {f : ι → A} (hf : AlgebraicIndependent R f) :
    AlgebraicIndependent R ((↑) : range f → A) := by
  nontriviality R
  rwa [algebraicIndependent_subtype_range hf.injective]

theorem AlgebraicIndependent.to_subtype_range' {ι} {f : ι → A} (hf : AlgebraicIndependent R f) {t}
    (ht : range f = t) : AlgebraicIndependent R ((↑) : t → A) :=
  ht ▸ hf.to_subtype_range

theorem algebraicIndependent_comp_subtype {s : Set ι} :
    AlgebraicIndependent R (x ∘ (↑) : s → A) ↔
      ∀ p ∈ MvPolynomial.supported R s, aeval x p = 0 → p = 0 := by
  have : (aeval (x ∘ (↑) : s → A) : _ →ₐ[R] _) = (aeval x).comp (rename (↑)) := by ext; simp
  have : ∀ p : MvPolynomial s R, rename ((↑) : s → ι) p = 0 ↔ p = 0 :=
    (injective_iff_map_eq_zero' (rename ((↑) : s → ι) : MvPolynomial s R →ₐ[R] _).toRingHom).1
      (rename_injective _ Subtype.val_injective)
  simp [algebraicIndependent_iff, supported_eq_range_rename, *]

theorem algebraicIndependent_subtype {s : Set A} :
    AlgebraicIndependent R ((↑) : s → A) ↔
      ∀ p : MvPolynomial A R, p ∈ MvPolynomial.supported R s → aeval id p = 0 → p = 0 := by
  apply @algebraicIndependent_comp_subtype _ _ _ id

theorem algebraicIndependent_of_finite (s : Set A)
    (H : ∀ t ⊆ s, t.Finite → AlgebraicIndependent R ((↑) : t → A)) :
    AlgebraicIndependent R ((↑) : s → A) :=
  algebraicIndependent_subtype.2 fun p hp =>
    algebraicIndependent_subtype.1 (H _ (mem_supported.1 hp) (Finset.finite_toSet _)) _ (by simp)

theorem AlgebraicIndependent.image_of_comp {ι ι'} (s : Set ι) (f : ι → ι') (g : ι' → A)
    (hs : AlgebraicIndependent R fun x : s => g (f x)) :
    AlgebraicIndependent R fun x : f '' s => g x := by
  nontriviality R
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  exact (algebraicIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs

theorem AlgebraicIndependent.image {ι} {s : Set ι} {f : ι → A}
    (hs : AlgebraicIndependent R fun x : s => f x) :
    AlgebraicIndependent R fun x : f '' s => (x : A) := by
  convert AlgebraicIndependent.image_of_comp s f id hs

theorem algebraicIndependent_iUnion_of_directed {η : Type*} [Nonempty η] {s : η → Set A}
    (hs : Directed (· ⊆ ·) s) (h : ∀ i, AlgebraicIndependent R ((↑) : s i → A)) :
    AlgebraicIndependent R ((↑) : (⋃ i, s i) → A) := by
  refine algebraicIndependent_of_finite (⋃ i, s i) fun t ht ft => ?_
  rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
  rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
  exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))

theorem algebraicIndependent_sUnion_of_directed {s : Set (Set A)} (hsn : s.Nonempty)
    (hs : DirectedOn (· ⊆ ·) s) (h : ∀ a ∈ s, AlgebraicIndependent R ((↑) : a → A)) :
    AlgebraicIndependent R ((↑) : ⋃₀ s → A) := by
  letI : Nonempty s := Nonempty.to_subtype hsn
  rw [sUnion_eq_iUnion]
  exact algebraicIndependent_iUnion_of_directed hs.directed_val (by simpa using h)

theorem exists_maximal_algebraicIndependent (s t : Set A) (hst : s ⊆ t)
    (hs : AlgebraicIndependent R ((↑) : s → A)) : ∃ u, s ⊆ u ∧
      Maximal (fun (x : Set A) ↦ AlgebraicIndependent R ((↑) : x → A) ∧ x ⊆ t) u := by
  refine zorn_subset_nonempty { u : Set A | AlgebraicIndependent R ((↑) : u → A) ∧ u ⊆ t}
    (fun c hc chainc hcn ↦ ⟨⋃₀ c, ⟨?_, ?_⟩, fun _ ↦ subset_sUnion_of_mem⟩) s ⟨hs, hst⟩
  · exact algebraicIndependent_sUnion_of_directed hcn chainc.directedOn (fun x hxc ↦ (hc hxc).1)
  exact fun x ⟨w, hyc, hwy⟩ ↦ (hc hyc).2 hwy

theorem AlgebraicIndependent.repr_ker (hx : AlgebraicIndependent R x) :
    RingHom.ker (hx.repr : adjoin R (range x) →+* MvPolynomial ι R) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).1 (AlgEquiv.injective _)

-- TODO - make this an `AlgEquiv`
/-- The isomorphism between `MvPolynomial (Option ι) R` and the polynomial ring over
the algebra generated by an algebraically independent family. -/
def AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin (hx : AlgebraicIndependent R x) :
    MvPolynomial (Option ι) R ≃+* Polynomial (adjoin R (Set.range x)) :=
  (MvPolynomial.optionEquivLeft _ _).toRingEquiv.trans
    (Polynomial.mapEquiv hx.aevalEquiv.toRingEquiv)

@[simp]
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply
    (hx : AlgebraicIndependent R x) (y) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin y =
      Polynomial.map (hx.aevalEquiv : MvPolynomial ι R →+* adjoin R (range x))
        (aeval (fun o : Option ι => o.elim Polynomial.X fun s : ι => Polynomial.C (X s)) y) :=
  rfl

/-- `simp`-normal form of `mvPolynomialOptionEquivPolynomialAdjoin_C` -/
@[simp]
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C'
    (hx : AlgebraicIndependent R x) (r) :
    Polynomial.C (hx.aevalEquiv (C r)) = Polynomial.C (algebraMap _ _ r) := by
  congr
  apply_fun Subtype.val using Subtype.val_injective
  simp

theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C
    (hx : AlgebraicIndependent R x) (r) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin (C r) = Polynomial.C (algebraMap _ _ r) := by
  simp

theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_none
    (hx : AlgebraicIndependent R x) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin (X none) = Polynomial.X := by
  rw [AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply, aeval_X, Option.elim,
    Polynomial.map_X]

theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_some
    (hx : AlgebraicIndependent R x) (i) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin (X (some i)) =
      Polynomial.C (hx.aevalEquiv (X i)) := by
  rw [AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply, aeval_X, Option.elim,
    Polynomial.map_C, RingHom.coe_coe]

theorem AlgebraicIndependent.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin
    (hx : AlgebraicIndependent R x) (a : A) :
    RingHom.comp
        (↑(Polynomial.aeval a : Polynomial (adjoin R (Set.range x)) →ₐ[_] A) :
          Polynomial (adjoin R (Set.range x)) →+* A)
        hx.mvPolynomialOptionEquivPolynomialAdjoin.toRingHom =
      ↑(MvPolynomial.aeval fun o : Option ι => o.elim a x : MvPolynomial (Option ι) R →ₐ[R] A) := by
  refine MvPolynomial.ringHom_ext ?_ ?_ <;>
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

section Field

variable [Field K] [Algebra K A]

/- Porting note: removing `simp`, not in simp normal form. Could make `Function.Injective f` a
simp lemma when `f` is a field hom, and then simp would prove this -/
theorem algebraicIndependent_empty_type [IsEmpty ι] [Nontrivial A] : AlgebraicIndependent K x := by
  rw [algebraicIndependent_empty_type_iff]
  exact RingHom.injective _

theorem algebraicIndependent_empty [Nontrivial A] :
    AlgebraicIndependent K ((↑) : (∅ : Set A) → A) :=
  algebraicIndependent_empty_type

end Field
