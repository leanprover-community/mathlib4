/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Filippo A. E. Nuccio, Andrew Yang
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Functoriality of the prime spectrum

In this file we define the induced map on prime spectra induced by a ring homomorphism.

## Main definitions

* `PrimeSpectrum.comap`: The induced map on prime spectra by a ring homomorphism. The proof that
  it is continuous is in `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u v

variable (R : Type u) (S : Type v)

open PrimeSpectrum

/-- The pullback of an element of `PrimeSpectrum S` along a ring homomorphism `f : R →+* S`.
The bundled continuous version is `PrimeSpectrum.comap`. -/
def PrimeSpectrum.comap {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (p : PrimeSpectrum S) : PrimeSpectrum R :=
  ⟨Ideal.comap f p.asIdeal, inferInstance⟩

@[deprecated (since := "2025-12-10")] alias RingHom.specComap := PrimeSpectrum.comap

namespace PrimeSpectrum

open RingHom

variable {R S} {S' : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring S']

variable (f : R →+* S)

@[simp]
theorem comap_asIdeal (y : PrimeSpectrum S) :
    (comap f y).asIdeal = Ideal.comap f y.asIdeal :=
  rfl

@[deprecated (since := "2025-12-10")] alias specComap_asIdeal := comap_asIdeal

@[simp]
theorem comap_id : comap (RingHom.id R) = fun x => x :=
  rfl

@[deprecated (since := "2025-12-10")] alias specComap_id := comap_id

@[simp]
theorem comap_comp (f : R →+* S) (g : S →+* S') :
    comap (g.comp f) = (comap f).comp (comap g) :=
  rfl

@[deprecated (since := "2025-12-10")] alias specComap_comp := comap_comp

theorem comap_comp_apply (f : R →+* S) (g : S →+* S') (x : PrimeSpectrum S') :
    comap (g.comp f) x = comap f (comap g x) :=
  rfl

@[deprecated (since := "2025-12-10")] alias specComap_comp_apply := comap_comp_apply

theorem preimage_comap_zeroLocus_aux (f : R →+* S) (s : Set R) :
    comap f ⁻¹' zeroLocus s = zeroLocus (f '' s) := by
  ext x
  simp [mem_zeroLocus, Set.image_subset_iff, Set.mem_preimage, mem_zeroLocus]

@[simp]
theorem preimage_comap_zeroLocus (s : Set R) :
    comap f ⁻¹' zeroLocus s = zeroLocus (f '' s) :=
  preimage_comap_zeroLocus_aux f s

@[deprecated (since := "2025-12-10")] alias preimage_specComap_zeroLocus := preimage_comap_zeroLocus

theorem comap_injective_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Injective (comap f) := fun x y h =>
  PrimeSpectrum.ext
    (Ideal.comap_injective_of_surjective f hf
      (congr_arg PrimeSpectrum.asIdeal h : (comap f x).asIdeal = (comap f y).asIdeal))

@[deprecated (since := "2025-12-10")]
alias specComap_injective_of_surjective := comap_injective_of_surjective

instance [Algebra R S] (p : PrimeSpectrum S) :
    p.asIdeal.LiesOver (p.comap <| algebraMap R S).asIdeal where
  over := rfl

/-- `RingHom.comap` of an isomorphism of rings as an equivalence of their prime spectra. -/
@[simps apply]
def comapEquiv (e : R ≃+* S) : PrimeSpectrum R ≃o PrimeSpectrum S where
  toFun := comap e.symm.toRingHom
  invFun := comap e.toRingHom
  left_inv x := by
    rw [← comap_comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp]
    rfl
  right_inv x := by
    rw [← comap_comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RingEquiv.comp_symm]
    rfl
  map_rel_iff' {I J} := Ideal.comap_le_comap_iff_of_surjective _ e.symm.surjective ..

@[simp] lemma comapEquiv_symm (e : R ≃+* S) : (comapEquiv e).symm = comapEquiv e.symm := rfl

section Pi

variable {ι} (R : ι → Type*) [∀ i, CommSemiring (R i)]

/--
The canonical map from a disjoint union of prime spectra of commutative semirings to
the prime spectrum of the product semiring.
This is always an open embedding, see `PrimeSpectrum.isOpenEmbedding_sigmaToPi` and
a homeomorphism if `ι` is finite, see `PrimeSpectrum.sigmaHomeoPi`.
-/
def sigmaToPi : (Σ i, PrimeSpectrum (R i)) → PrimeSpectrum (Π i, R i)
  | ⟨i, p⟩ => comap (Pi.evalRingHom R i) p

@[simp]
lemma sigmaToPi_apply (i : ι) (p : PrimeSpectrum (R i)) :
    sigmaToPi R ⟨i, p⟩ = comap (Pi.evalRingHom R i) p :=
  rfl

@[deprecated (since := "2026-04-17")]
alias coe_sigmaToPi_asIdeal := sigmaToPi_apply

theorem sigmaToPi_injective : (sigmaToPi R).Injective := fun ⟨i, p⟩ ⟨j, q⟩ eq ↦ by
  classical
  obtain rfl | ne := eq_or_ne i j
  · congr; ext x
    simpa using congr_arg (Function.update (0 : ∀ i, R i) i x ∈ ·.asIdeal) eq
  · refine (p.1.ne_top_iff_one.mp p.2.ne_top ?_).elim
    have : Function.update (1 : ∀ i, R i) j 0 ∈ (sigmaToPi R ⟨j, q⟩).asIdeal := by simp
    simpa [← eq, Function.update_of_ne ne]

variable [Infinite ι] [∀ i, Nontrivial (R i)]

/-- An infinite product of nontrivial commutative semirings has a maximal ideal outside of the
range of `sigmaToPi`, i.e. is not of the form `πᵢ⁻¹(𝔭)` for some prime `𝔭 ⊂ R i`, where
`πᵢ : (Π i, R i) →+* R i` is the projection. For a complete description of all prime ideals,
see https://math.stackexchange.com/a/1563190. -/
theorem exists_maximal_notMem_range_sigmaToPi_of_infinite :
    ∃ (I : Ideal (Π i, R i)) (_ : I.IsMaximal), ⟨I, inferInstance⟩ ∉ Set.range (sigmaToPi R) := by
  classical
  let J : Ideal (Π i, R i) := -- `J := Π₀ i, R i` is an ideal in `Π i, R i`
  { __ := AddMonoidHom.mrange DFinsupp.coeFnAddMonoidHom
    smul_mem' := by
      rintro r _ ⟨x, rfl⟩
      refine ⟨.mk x.support fun i ↦ r i * x i, funext fun i ↦ show dite _ _ _ = _ from ?_⟩
      simp_rw +instances [DFinsupp.coeFnAddMonoidHom]
      refine dite_eq_left_iff.mpr fun h ↦ ?_
      rw [DFinsupp.notMem_support_iff.mp h, mul_zero] }
  have ⟨I, max, le⟩ := J.exists_le_maximal <| (Ideal.ne_top_iff_one _).mpr <| by
    -- take a maximal ideal I containing J
    rintro ⟨x, hx⟩
    have ⟨i, hi⟩ := x.support.exists_notMem
    simpa [DFinsupp.coeFnAddMonoidHom, DFinsupp.notMem_support_iff.mp hi] using congr_fun hx i
  refine ⟨I, max, fun ⟨⟨i, p⟩, eq⟩ ↦ ?_⟩
  -- then I is not in the range of `sigmaToPi`
  have : ⇑(DFinsupp.single i 1) ∉ (sigmaToPi R ⟨i, p⟩).asIdeal := by
    simpa using p.1.ne_top_iff_one.mp p.2.ne_top
  rw [eq] at this
  exact this (le ⟨.single i 1, rfl⟩)

theorem sigmaToPi_not_surjective_of_infinite : ¬ (sigmaToPi R).Surjective := fun surj ↦
  have ⟨_, _, notMem⟩ := exists_maximal_notMem_range_sigmaToPi_of_infinite R
  (Set.range_eq_univ.mpr surj ▸ notMem) ⟨⟩

lemma exists_comap_evalRingHom_eq
    {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)] [Finite ι]
    (p : PrimeSpectrum (Π i, R i)) :
    ∃ (i : ι) (q : PrimeSpectrum (R i)), comap (Pi.evalRingHom R i) q = p := by
  classical
  cases nonempty_fintype ι
  let e (i) : Π i, R i := Function.update 1 i 0
  have H : ∏ i, e i = 0 := by
    ext j
    rw [Finset.prod_apply, Pi.zero_apply, Finset.prod_eq_zero (Finset.mem_univ j)]
    simp [e]
  obtain ⟨i, hi⟩ : ∃ i, e i ∈ p.asIdeal := by
    simpa [← H, Ideal.IsPrime.prod_mem_iff] using p.asIdeal.zero_mem
  let h₁ : Function.Surjective (Pi.evalRingHom R i) := RingHomSurjective.is_surjective
  have h₂ : RingHom.ker (Pi.evalRingHom R i) ≤ p.asIdeal := by
    intro x hx
    convert p.asIdeal.mul_mem_left x hi
    ext j
    by_cases hj : i = j
    · subst hj; simpa [e]
    · simp [e, Function.update_of_ne (.symm hj)]
  have : (p.asIdeal.map (Pi.evalRingHom R i)).comap (Pi.evalRingHom R i) = p.asIdeal := by
    rwa [Ideal.comap_map_of_surjective _ h₁, sup_eq_left]
  exact ⟨i, ⟨_, Ideal.map_isPrime_of_surjective h₁ h₂⟩, PrimeSpectrum.ext this⟩

lemma sigmaToPi_bijective {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)] [Finite ι] :
    Function.Bijective (sigmaToPi R) := by
  refine ⟨sigmaToPi_injective R, ?_⟩
  intro q
  obtain ⟨i, q, rfl⟩ := exists_comap_evalRingHom_eq q
  exact ⟨⟨i, q⟩, rfl⟩

lemma iUnion_range_comap_comp_evalRingHom
    {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)] [Finite ι]
    {S : Type*} [CommRing S] (f : S →+* Π i, R i) :
    ⋃ i, Set.range (comap ((Pi.evalRingHom R i).comp f)) = Set.range (comap f) := by
  simp_rw [comap_comp]
  apply subset_antisymm
  · exact Set.iUnion_subset fun _ ↦ Set.range_comp_subset_range _ _
  · rintro _ ⟨p, rfl⟩
    obtain ⟨i, p, rfl⟩ := exists_comap_evalRingHom_eq p
    exact Set.mem_iUnion_of_mem i ⟨p, rfl⟩

@[deprecated (since := "2025-12-11")]
alias iUnion_range_specComap_comp_evalRingHom := iUnion_range_comap_comp_evalRingHom

end Pi

end PrimeSpectrum

section SpecOfSurjective

open Function RingHom

variable [CommRing R] [CommRing S]
variable (f : R →+* S)
variable {R}

theorem image_comap_zeroLocus_eq_zeroLocus_comap (hf : Surjective f) (I : Ideal S) :
    comap f '' zeroLocus I = zeroLocus (I.comap f) := by
  simp only [Set.ext_iff, Set.mem_image, mem_zeroLocus, SetLike.coe_subset_coe]
  refine fun p => ⟨?_, fun h_I_p => ?_⟩
  · rintro ⟨p, hp, rfl⟩ a ha
    exact hp ha
  · have hp : ker f ≤ p.asIdeal := (Ideal.comap_mono bot_le).trans h_I_p
    refine ⟨⟨p.asIdeal.map f, Ideal.map_isPrime_of_surjective hf hp⟩, fun x hx => ?_, ?_⟩
    · obtain ⟨x', rfl⟩ := hf x
      exact Ideal.mem_map_of_mem f (h_I_p hx)
    · ext x
      rw [comap_asIdeal, Ideal.mem_comap, Ideal.mem_map_iff_of_surjective f hf]
      refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
      rintro ⟨x', hx', heq⟩
      rw [← sub_sub_cancel x' x]
      refine p.asIdeal.sub_mem hx' (hp ?_)
      rwa [mem_ker, map_sub, sub_eq_zero]

@[deprecated (since := "2025-12-10")]
alias image_specComap_zeroLocus_eq_zeroLocus_comap := image_comap_zeroLocus_eq_zeroLocus_comap

theorem range_comap_of_surjective (hf : Surjective f) :
    Set.range (comap f) = zeroLocus (ker f) := by
  rw [← Set.image_univ]
  convert image_comap_zeroLocus_eq_zeroLocus_comap _ _ hf _
  rw [zeroLocus_bot]

@[deprecated (since := "2025-12-10")]
alias range_specComap_of_surjective := range_comap_of_surjective

variable {S}

/-- Let `f : R →+* S` be a surjective ring homomorphism, then `Spec S` is order-isomorphic to `Z(I)`
  where `I = ker f`. -/
noncomputable def Ideal.primeSpectrumOrderIsoZeroLocusOfSurj (hf : Surjective f) {I : Ideal R}
    (hI : RingHom.ker f = I) : PrimeSpectrum S ≃o (PrimeSpectrum.zeroLocus (R := R) I) where
  toFun p := ⟨p.comap f, hI.symm.trans_le (Ideal.ker_le_comap f)⟩
  invFun := fun ⟨⟨p, _⟩, hp⟩ ↦ ⟨p.map f, p.map_isPrime_of_surjective hf (hI.trans_le hp)⟩
  left_inv := by
    intro ⟨p, _⟩
    simp only [PrimeSpectrum.mk.injEq]
    exact p.map_comap_of_surjective f hf
  right_inv := by
    intro ⟨⟨p, _⟩, hp⟩
    simp only [Subtype.mk.injEq, PrimeSpectrum.ext_iff, comap_asIdeal]
    exact (p.comap_map_of_surjective f hf).trans <| sup_eq_left.mpr (hI.trans_le hp)
  map_rel_iff' {a b} := by
    change a.asIdeal.comap _ ≤ b.asIdeal.comap _ ↔ a ≤ b
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_comap_of_surjective f hf,
      PrimeSpectrum.asIdeal_le_asIdeal]

/-- `Spec (R / I)` is order-isomorphic to `Z(I)`. -/
noncomputable def Ideal.primeSpectrumQuotientOrderIsoZeroLocus (I : Ideal R) :
    PrimeSpectrum (R ⧸ I) ≃o (PrimeSpectrum.zeroLocus (R := R) I) :=
  primeSpectrumOrderIsoZeroLocusOfSurj (Quotient.mk I) Quotient.mk_surjective I.mk_ker

/-- `p` is in the image of `Spec S → Spec R` if and only if `p` extended to `S` and
restricted back to `R` is `p`. -/
lemma PrimeSpectrum.mem_range_comap_iff {p : PrimeSpectrum R} :
    p ∈ Set.range (comap f) ↔ (p.asIdeal.map f).comap f = p.asIdeal := by
  refine ⟨fun ⟨q, hq⟩ ↦ by simp [← hq], ?_⟩
  rw [Ideal.comap_map_eq_self_iff_of_isPrime]
  rintro ⟨q, _, hq⟩
  exact ⟨⟨q, inferInstance⟩, PrimeSpectrum.ext hq⟩

open TensorProduct

/-- A prime `p` is in the range of `Spec S → Spec R` if the fiber over `p` is nontrivial. -/
lemma PrimeSpectrum.nontrivial_iff_mem_rangeComap {S : Type*} [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) :
    Nontrivial (p.asIdeal.ResidueField ⊗[R] S) ↔ p ∈ Set.range (comap (algebraMap R S)) := by
  let k := p.asIdeal.ResidueField
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] S)
    use PrimeSpectrum.comap (Algebra.TensorProduct.includeRight).toRingHom ⟨m, hm.isPrime⟩
    ext : 1
    rw [← PrimeSpectrum.comap_comp_apply,
      ← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap, comap_comp_apply]
    simp [Ideal.eq_bot_of_prime, k, ← RingHom.ker_eq_comap_bot]
  · obtain ⟨q, rfl⟩ := h
    let f : k ⊗[R] S →ₐ[R] q.asIdeal.ResidueField :=
      Algebra.TensorProduct.lift (Ideal.ResidueField.mapₐ _ _ (Algebra.ofId _ _) rfl)
        (IsScalarTower.toAlgHom _ _ _) (fun _ _ ↦ Commute.all ..)
    exact RingHom.domain_nontrivial f.toRingHom

lemma RingHom.strictMono_comap_of_surjective {S : Type*} [CommRing S]
    {f : R →+* S} (hf : Function.Surjective f) : StrictMono (comap f) :=
  fun _ _ h ↦ (Ideal.relIsoOfSurjective _ hf).strictMono h

@[deprecated (since := "2025-12-10")]
alias RingHom.strictMono_specComap_of_surjective := RingHom.strictMono_comap_of_surjective

end SpecOfSurjective

section ResidueField

variable {R : Type*} [CommRing R]

lemma PrimeSpectrum.residueField_comap (I : PrimeSpectrum R) :
    Set.range (comap (algebraMap R I.asIdeal.ResidueField)) = {I} := by
  rw [Set.range_unique, Set.singleton_eq_singleton_iff]
  exact PrimeSpectrum.ext (Ideal.ext fun x ↦ Ideal.algebraMap_residueField_eq_zero)

@[deprecated (since := "2025-12-10")]
alias PrimeSpectrum.residueField_specComap := PrimeSpectrum.residueField_comap

end ResidueField

variable {R S} in
theorem IsLocalHom.of_comap_surjective [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (hf : Function.Surjective (comap f)) : IsLocalHom f where
  map_nonunit x hfx := by
    by_contra hx
    obtain ⟨p, hp, _⟩ := exists_max_ideal_of_mem_nonunits hx
    obtain ⟨⟨q, hqp⟩, hq⟩ := hf ⟨p, hp.isPrime⟩
    simp only [PrimeSpectrum.ext_iff, comap_asIdeal] at hq
    exact hqp.ne_top (q.eq_top_of_isUnit_mem (q.mem_comap.mp (by rwa [hq])) hfx)

@[deprecated (since := "2025-12-10")]
alias IsLocalHom.of_specComap_surjective := IsLocalHom.of_comap_surjective
