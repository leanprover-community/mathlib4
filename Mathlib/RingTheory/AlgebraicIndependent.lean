/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Algebraic Independence

This file defines algebraic independence of a family of element of an `R` algebra.

## Main definitions

* `AlgebraicIndependent` - `AlgebraicIndependent R x` states the family of elements `x`
  is algebraically independent over `R`, meaning that the canonical map out of the multivariable
  polynomial ring is injective.

* `AlgebraicIndependent.aevalEquiv` - The canonical isomorphism from the polynomial ring to the
  subalgebra generated by an algebraic independent family.

* `AlgebraicIndependent.repr` - The canonical map from the subalgebra generated by an
  algebraic independent family into the polynomial ring. It is the inverse of
  `AlgebraicIndependent.aevalEquiv`.

* `AlgebraicIndependent.aevalEquivField` - The canonical isomorphism from the rational function
  field ring to the intermediate field generated by an algebraic independent family.

* `AlgebraicIndependent.reprField` - The canonical map from the intermediate field generated by an
  algebraic independent family into the rational function field. It is the inverse of
  `AlgebraicIndependent.aevalEquivField`.

* `IsTranscendenceBasis R x` - a family `x` is a transcendence basis over `R` if it is a maximal
  algebraically independent subset.

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

universe x u v w

variable {ι : Type*} {ι' : Type*} (R : Type*) {K : Type*}
variable {A : Type*} {A' : Type*}
variable (x : ι → A)
variable [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']

/-- `AlgebraicIndependent R x` states the family of elements `x`
  is algebraically independent over `R`, meaning that the canonical
  map out of the multivariable polynomial ring is injective. -/
def AlgebraicIndependent : Prop :=
  Injective (MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] A)

variable {R} {x}

theorem algebraicIndependent_iff_ker_eq_bot :
    AlgebraicIndependent R x ↔
      RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] A).toRingHom = ⊥ :=
  RingHom.injective_iff_ker_eq_bot _

theorem algebraicIndependent_iff :
    AlgebraicIndependent R x ↔
      ∀ p : MvPolynomial ι R, MvPolynomial.aeval (x : ι → A) p = 0 → p = 0 :=
  injective_iff_map_eq_zero _

theorem AlgebraicIndependent.eq_zero_of_aeval_eq_zero (h : AlgebraicIndependent R x) :
    ∀ p : MvPolynomial ι R, MvPolynomial.aeval (x : ι → A) p = 0 → p = 0 :=
  algebraicIndependent_iff.1 h

theorem algebraicIndependent_iff_injective_aeval :
    AlgebraicIndependent R x ↔ Injective (MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] A) :=
  Iff.rfl

@[simp]
theorem algebraicIndependent_empty_type_iff [IsEmpty ι] :
    AlgebraicIndependent R x ↔ Injective (algebraMap R A) := by
  rw [algebraicIndependent_iff_injective_aeval, MvPolynomial.aeval_injective_iff_of_isEmpty]

/-- A one-element family `x` is algebraically independent if and only if
its element is transcendental. -/
@[simp]
theorem algebraicIndependent_unique_type_iff [Unique ι] :
    AlgebraicIndependent R x ↔ Transcendental R (x default) := by
  rw [transcendental_iff_injective, algebraicIndependent_iff_injective_aeval]
  let i := (renameEquiv R (Equiv.equivPUnit.{_, 1} ι)).trans (pUnitAlgEquiv R)
  have key : aeval (R := R) x = (Polynomial.aeval (R := R) (x default)).comp i := by
    ext y
    simp [i, Subsingleton.elim y default]
  simp [key]

/-- The one-element family `![x]` is algebraically independent if and only if
`x` is transcendental. -/
theorem algebraicIndependent_iff_transcendental {x : A} :
    AlgebraicIndependent R ![x] ↔ Transcendental R x := by
  simp

namespace AlgebraicIndependent

theorem of_comp (f : A →ₐ[R] A') (hfv : AlgebraicIndependent R (f ∘ x)) :
    AlgebraicIndependent R x := by
  have : aeval (f ∘ x) = f.comp (aeval x) := by ext; simp
  rw [AlgebraicIndependent, this, AlgHom.coe_comp] at hfv
  exact hfv.of_comp

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
  refine hx.comp ?_
  rw [← linearIndependent_iff_injective_linearCombination]
  exact linearIndependent_X _ _

protected theorem injective [Nontrivial R] : Injective x :=
  hx.linearIndependent.injective

theorem ne_zero [Nontrivial R] (i : ι) : x i ≠ 0 :=
  hx.linearIndependent.ne_zero i

theorem comp (f : ι' → ι) (hf : Function.Injective f) : AlgebraicIndependent R (x ∘ f) := by
  intro p q
  simpa [aeval_rename, (rename_injective f hf).eq_iff] using @hx (rename f p) (rename f q)

theorem coe_range : AlgebraicIndependent R ((↑) : range x → A) := by
  simpa using hx.comp _ (rangeSplitting_injective x)

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

/-- If a family `x` is algebraically independent, then any of its element is transcendental. -/
theorem transcendental (i : ι) : Transcendental R (x i) := by
  have := hx.comp ![i] (Function.injective_of_subsingleton _)
  have : AlgebraicIndependent R ![x i] := by rwa [← FinVec.map_eq] at this
  rwa [← algebraicIndependent_iff_transcendental]

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

/-- If `A/R` is algebraic, then all algebraically independent families are empty. -/
theorem isEmpty_of_isAlgebraic [Algebra.IsAlgebraic R A] : IsEmpty ι := by
  rcases isEmpty_or_nonempty ι with h | ⟨⟨i⟩⟩
  · exact h
  exact False.elim (hx.transcendental i (Algebra.IsAlgebraic.isAlgebraic _))

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

theorem algebraicIndependent_equiv (e : ι ≃ ι') {f : ι' → A} :
    AlgebraicIndependent R (f ∘ e) ↔ AlgebraicIndependent R f :=
  ⟨fun h => Function.comp_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective,
    fun h => h.comp _ e.injective⟩

theorem algebraicIndependent_equiv' (e : ι ≃ ι') {f : ι' → A} {g : ι → A} (h : f ∘ e = g) :
    AlgebraicIndependent R g ↔ AlgebraicIndependent R f :=
  h ▸ algebraicIndependent_equiv e

theorem algebraicIndependent_subtype_range {ι} {f : ι → A} (hf : Injective f) :
    AlgebraicIndependent R ((↑) : range f → A) ↔ AlgebraicIndependent R f :=
  Iff.symm <| algebraicIndependent_equiv' (Equiv.ofInjective f hf) rfl

alias ⟨AlgebraicIndependent.of_subtype_range, _⟩ := algebraicIndependent_subtype_range

theorem algebraicIndependent_image {ι} {s : Set ι} {f : ι → A} (hf : Set.InjOn f s) :
    (AlgebraicIndependent R fun x : s => f x) ↔ AlgebraicIndependent R fun x : f '' s => (x : A) :=
  algebraicIndependent_equiv' (Equiv.Set.imageOfInjOn _ _ hf) rfl

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
  exact map_injective f hf (by rwa [map_zero])

theorem AlgebraicIndependent.ringHom_of_comp_eq (H : AlgebraicIndependent R x)
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    AlgebraicIndependent S (g ∘ x) := by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
  obtain ⟨q, rfl⟩ := map_surjective f hf p
  erw [aeval_eq_eval₂Hom, eval₂Hom_map_hom, h, ← map_aeval] at hp
  rw [H q (hg (by rwa [map_zero])), map_zero]

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

variable {R A}

theorem AlgebraicIndependent.mono {t s : Set A} (h : t ⊆ s)
    (hx : AlgebraicIndependent R ((↑) : s → A)) : AlgebraicIndependent R ((↑) : t → A) := by
  simpa [Function.comp] using hx.comp (inclusion h) (inclusion_injective h)

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

namespace AlgebraicIndependent

section repr

variable (hx : AlgebraicIndependent R x)
include hx

/-- Canonical isomorphism between polynomials and the subalgebra generated by
  algebraically independent elements. -/
@[simps! apply_coe]
def aevalEquiv : MvPolynomial ι R ≃ₐ[R] Algebra.adjoin R (range x) :=
  (AlgEquiv.ofInjective (aeval x) (algebraicIndependent_iff_injective_aeval.1 hx)).trans
    (Subalgebra.equivOfEq _ _ (Algebra.adjoin_range_eq_range_aeval R x).symm)

--@[simp] Porting note: removing simp because the linter complains about deterministic timeout
theorem algebraMap_aevalEquiv (p : MvPolynomial ι R) :
    algebraMap (Algebra.adjoin R (range x)) A (hx.aevalEquiv p) = aeval x p :=
  rfl

/-- The canonical map from the subalgebra generated by an algebraic independent family
  into the polynomial ring. -/
def repr : Algebra.adjoin R (range x) →ₐ[R] MvPolynomial ι R :=
  hx.aevalEquiv.symm

@[simp]
theorem aeval_repr (p) : aeval x (hx.repr p) = p :=
  Subtype.ext_iff.1 (AlgEquiv.apply_symm_apply hx.aevalEquiv p)

theorem aeval_comp_repr : (aeval x).comp hx.repr = Subalgebra.val _ :=
  AlgHom.ext <| hx.aeval_repr

theorem repr_ker : RingHom.ker (hx.repr : adjoin R (range x) →+* MvPolynomial ι R) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).1 (AlgEquiv.injective _)

end repr

section reprField

variable {F E : Type*} {x : ι → E} [Field F] [Field E] [Algebra F E] (hx : AlgebraicIndependent F x)
include hx

/-- Canonical isomorphism between rational function field and the
  intermediate field generated by algebraically independent elements. -/
def aevalEquivField :
    FractionRing (MvPolynomial ι F) ≃ₐ[F] ↥(IntermediateField.adjoin F (range x)) :=
  let i := IsFractionRing.liftAlgHom (K := FractionRing (MvPolynomial ι F))
    (algebraicIndependent_iff_injective_aeval.2 hx)
  (show _ ≃ₐ[F] i.fieldRange from AlgEquiv.ofInjectiveField i).trans <|
    IntermediateField.equivOfEq <|
      IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq (g := aeval x) (f := i)
        (by ext <;> simp [i]) (Algebra.adjoin_range_eq_range_aeval F x).symm

@[simp]
theorem aevalEquivField_apply_coe (a : FractionRing (MvPolynomial ι F)) :
    hx.aevalEquivField a =
      IsFractionRing.lift (algebraicIndependent_iff_injective_aeval.2 hx) a := rfl

theorem aevalEquivField_algebraMap_apply_coe (a : MvPolynomial ι F) :
    hx.aevalEquivField (algebraMap _ _ a) = aeval x a := by
  simp

/-- The canonical map from the intermediate field generated by an algebraic independent family
  into the rational function field. -/
def reprField : IntermediateField.adjoin F (range x) →ₐ[F] FractionRing (MvPolynomial ι F) :=
  hx.aevalEquivField.symm

@[simp]
theorem lift_reprField (p) :
    IsFractionRing.lift (algebraicIndependent_iff_injective_aeval.2 hx) (hx.reprField p) = p :=
  Subtype.ext_iff.1 (AlgEquiv.apply_symm_apply hx.aevalEquivField p)

theorem liftAlgHom_comp_reprField :
    (IsFractionRing.liftAlgHom (algebraicIndependent_iff_injective_aeval.2 hx)).comp hx.reprField =
      IntermediateField.val _ :=
  AlgHom.ext <| hx.lift_reprField

end reprField

end AlgebraicIndependent

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

theorem AlgebraicIndependent.option_iff (hx : AlgebraicIndependent R x) (a : A) :
    (AlgebraicIndependent R fun o : Option ι => o.elim a x) ↔
      Transcendental (adjoin R (Set.range x)) a := by
  rw [algebraicIndependent_iff_injective_aeval, transcendental_iff_injective,
    ← AlgHom.coe_toRingHom, ← hx.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin,
    RingHom.coe_comp]
  exact Injective.of_comp_iff' (Polynomial.aeval a)
    (mvPolynomialOptionEquivPolynomialAdjoin hx).bijective

/-- Variant of `algebraicIndependent_of_finite` using `Transcendental`. -/
theorem algebraicIndependent_of_finite' (s : Set A)
    (hinj : Injective (algebraMap R A))
    (H : ∀ t ⊆ s, t.Finite → ∀ a ∈ s, a ∉ t → Transcendental (adjoin R t) a) :
    AlgebraicIndependent R ((↑) : s → A) := by
  classical
  refine algebraicIndependent_of_finite s fun t hts hfin ↦ hfin.induction_on'
    ((algebraicIndependent_empty_iff R A).2 hinj) fun {a} {u} ha hu ha' h ↦ ?_
  convert ((Subtype.range_coe ▸ h.option_iff a).2 <| H u (hu.trans hts) (hfin.subset hu)
    a (hts ha) ha').comp _ (Set.subtypeInsertEquivOption ha').injective
  ext x
  by_cases h : ↑x = a <;> simp [h, Set.subtypeInsertEquivOption]

/-- `Type` version of `algebraicIndependent_of_finite'`. -/
theorem algebraicIndependent_of_finite_type'
    (hinj : Injective (algebraMap R A))
    (H : ∀ t : Set ι, t.Finite → ∀ i : ι, i ∉ t → Transcendental (adjoin R (x '' t)) (x i)) :
    AlgebraicIndependent R x := by
  nontriviality R
  haveI := hinj.nontrivial
  have hx : Injective x := by
    simp_rw [Transcendental] at H
    contrapose! H
    obtain ⟨i, j, h1, h2⟩ := not_injective_iff.1 H
    refine ⟨{j}, by simp, i, by simp [h2], ?_⟩
    rw [h1, Set.image_singleton]
    exact isAlgebraic_algebraMap (⟨x j, Algebra.self_mem_adjoin_singleton R _⟩ : adjoin R {x j})
  rw [← Set.coe_comp_rangeFactorization x]
  refine .comp (algebraicIndependent_of_finite' _ hinj fun t ht hfin a ha ha' ↦ ?_) _
    (Set.rightInverse_rangeSplitting hx).injective
  change Finite t at hfin
  have := H (x ⁻¹' t) (Finite.of_injective _ (hx.restrictPreimage t))
    ((Equiv.ofInjective _ hx).symm ⟨_, ha⟩)
    (by rwa [Set.mem_preimage, Equiv.apply_ofInjective_symm hx])
  rwa [Set.image_preimage_eq_inter_range, Set.inter_eq_self_of_subset_left ht,
    Equiv.apply_ofInjective_symm hx] at this

namespace MvPolynomial

/-- If for each `i : ι`, `f_i : R[X]` is transcendental over `R`, then `{f_i(X_i) | i : ι}`
in `MvPolynomial ι R` is algebraically independent over `R`. -/
theorem algebraicIndependent_polynomial_aeval_X
    (f : ι → Polynomial R) (hf : ∀ i, Transcendental R (f i)) :
    AlgebraicIndependent R fun i ↦ Polynomial.aeval (X i : MvPolynomial ι R) (f i) := by
  set x := fun i ↦ Polynomial.aeval (X i : MvPolynomial ι R) (f i)
  refine algebraicIndependent_of_finite_type' (C_injective _ _) fun t _ i hi ↦ ?_
  have hle : adjoin R (x '' t) ≤ supported R t := by
    rw [Algebra.adjoin_le_iff, Set.image_subset_iff]
    intro _ h
    rw [Set.mem_preimage]
    refine Algebra.adjoin_mono ?_ (Polynomial.aeval_mem_adjoin_singleton R _)
    simp_rw [singleton_subset_iff, Set.mem_image_of_mem _ h]
  exact (transcendental_supported_polynomial_aeval_X R hi (hf i)).of_tower_top_of_subalgebra_le hle

end MvPolynomial

/-- If `{x_i : A | i : ι}` is algebraically independent over `R`, and for each `i`,
`f_i : R[X]` is transcendental over `R`, then `{f_i(x_i) | i : ι}` is also
algebraically independent over `R`. -/
theorem AlgebraicIndependent.polynomial_aeval_of_transcendental
    (hx : AlgebraicIndependent R x)
    {f : ι → Polynomial R} (hf : ∀ i, Transcendental R (f i)) :
    AlgebraicIndependent R fun i ↦ Polynomial.aeval (x i) (f i) := by
  convert aeval_of_algebraicIndependent hx (algebraicIndependent_polynomial_aeval_X _ hf)
  rw [← AlgHom.comp_apply]
  congr 1; ext1; simp

variable (R)

/-- A family is a transcendence basis if it is a maximal algebraically independent subset. -/
def IsTranscendenceBasis (x : ι → A) : Prop :=
  AlgebraicIndependent R x ∧
    ∀ (s : Set A) (_ : AlgebraicIndependent R ((↑) : s → A)) (_ : range x ≤ s), range x = s

theorem exists_isTranscendenceBasis (h : Injective (algebraMap R A)) :
    ∃ s : Set A, IsTranscendenceBasis R ((↑) : s → A) := by
  cases' exists_maximal_algebraicIndependent (∅ : Set A) Set.univ (Set.subset_univ _)
      ((algebraicIndependent_empty_iff R A).2 h) with
    s hs
  refine ⟨s, hs.2.1.1, fun t ht hst ↦ ?_⟩
  simp only [Subtype.range_coe_subtype, setOf_mem_eq] at *
  exact hs.2.eq_of_le ⟨ht, subset_univ _⟩ hst

/-- `Type` version of `exists_isTranscendenceBasis`. -/
theorem exists_isTranscendenceBasis' (R : Type u) {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] (h : Injective (algebraMap R A)) :
    ∃ (ι : Type v) (x : ι → A), IsTranscendenceBasis R x := by
  obtain ⟨s, h⟩ := exists_isTranscendenceBasis R h
  exact ⟨s, Subtype.val, h⟩

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
    exact range_eq_univ.mp (image_injective.mpr i'.injective p)
  · intro p
    use i
    intro w i' h
    specialize p w ((↑) : w → A) i' (fun i => ⟨x i, range_subset_iff.mp h i⟩) (by ext; simp)
    have q := congr_arg (fun s => ((↑) : w → A) '' s) p.range_eq
    dsimp at q
    rw [← image_univ, image_image] at q
    simpa using q

theorem IsTranscendenceBasis.isAlgebraic [Nontrivial R] (hx : IsTranscendenceBasis R x) :
    Algebra.IsAlgebraic (adjoin R (range x)) A := by
  constructor
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

/-- If `x` is a transcendence basis of `A/R`, then it is empty if and only if
`A/R` is algebraic. -/
theorem IsTranscendenceBasis.isEmpty_iff_isAlgebraic [Nontrivial R]
    (hx : IsTranscendenceBasis R x) :
    IsEmpty ι ↔ Algebra.IsAlgebraic R A := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ hx.1.isEmpty_of_isAlgebraic⟩
  have := hx.isAlgebraic
  rw [Set.range_eq_empty x, adjoin_empty] at this
  exact algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left R A

/-- If `x` is a transcendence basis of `A/R`, then it is not empty if and only if
`A/R` is transcendental. -/
theorem IsTranscendenceBasis.nonempty_iff_transcendental [Nontrivial R]
    (hx : IsTranscendenceBasis R x) :
    Nonempty ι ↔ Algebra.Transcendental R A := by
  rw [← not_isEmpty_iff, Algebra.transcendental_iff_not_isAlgebraic, hx.isEmpty_iff_isAlgebraic]

theorem IsTranscendenceBasis.isAlgebraic_field {F E : Type*} {x : ι → E}
    [Field F] [Field E] [Algebra F E] (hx : IsTranscendenceBasis F x) :
    Algebra.IsAlgebraic (IntermediateField.adjoin F (range x)) E := by
  haveI := hx.isAlgebraic
  set S := range x
  letI : Algebra (adjoin F S) (IntermediateField.adjoin F S) :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin F S)).toRingHom.toAlgebra
  haveI : IsScalarTower (adjoin F S) (IntermediateField.adjoin F S) E :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact Algebra.IsAlgebraic.tower_top_of_injective (R := adjoin F S)
    (Subalgebra.inclusion_injective _)

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
