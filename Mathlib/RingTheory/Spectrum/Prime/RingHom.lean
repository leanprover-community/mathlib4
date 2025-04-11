/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Filippo A. E. Nuccio, Andrew Yang
-/
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Data.DFinsupp.Defs
/-!
# Functoriality of the prime spectrum

In this file we define the induced map on prime spectra induced by a ring homomorphism.

## Main definitions

* `RingHom.specComap`: The induced map on prime spectra by a ring homomorphism. The bundled
continuous version is `PrimeSpectrum.comap` in `Mathlib.RingTheory.Spectrum.Prime.Topology`.

-/

universe u v

variable (R : Type u) (S : Type v)

open PrimeSpectrum

/-- The pullback of an element of `PrimeSpectrum S` along a ring homomorphism `f : R →+* S`.
The bundled continuous version is `PrimeSpectrum.comap`. -/
abbrev RingHom.specComap {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    PrimeSpectrum S → PrimeSpectrum R :=
  fun y => ⟨Ideal.comap f y.asIdeal, inferInstance⟩

namespace PrimeSpectrum

open RingHom

variable {R S} {S' : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring S']

theorem preimage_specComap_zeroLocus_aux (f : R →+* S) (s : Set R) :
    f.specComap ⁻¹' zeroLocus s = zeroLocus (f '' s) := by
  ext x
  simp only [mem_zeroLocus, Set.image_subset_iff, Set.mem_preimage, mem_zeroLocus, Ideal.coe_comap]

variable (f : R →+* S)

@[simp]
theorem specComap_asIdeal (y : PrimeSpectrum S) :
    (f.specComap y).asIdeal = Ideal.comap f y.asIdeal :=
  rfl

@[simp]
theorem specComap_id : (RingHom.id R).specComap = fun x => x :=
  rfl

@[simp]
theorem specComap_comp (f : R →+* S) (g : S →+* S') :
    (g.comp f).specComap = f.specComap.comp g.specComap :=
  rfl

theorem specComap_comp_apply (f : R →+* S) (g : S →+* S') (x : PrimeSpectrum S') :
    (g.comp f).specComap x = f.specComap (g.specComap x) :=
  rfl

@[simp]
theorem preimage_specComap_zeroLocus (s : Set R) :
    f.specComap ⁻¹' zeroLocus s = zeroLocus (f '' s) :=
  preimage_specComap_zeroLocus_aux f s

theorem specComap_injective_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Injective f.specComap := fun x y h =>
  PrimeSpectrum.ext
    (Ideal.comap_injective_of_surjective f hf
      (congr_arg PrimeSpectrum.asIdeal h : (f.specComap x).asIdeal = (f.specComap y).asIdeal))

/-- `RingHom.specComap` of an isomorphism of rings as an equivalence of their prime spectra. -/
@[simps apply symm_apply]
def comapEquiv (e : R ≃+* S) : PrimeSpectrum R ≃ PrimeSpectrum S where
  toFun := e.symm.toRingHom.specComap
  invFun := e.toRingHom.specComap
  left_inv x := by
    rw [← specComap_comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp]
    rfl
  right_inv x := by
    rw [← specComap_comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RingEquiv.comp_symm]
    rfl

section Pi

variable {ι} (R : ι → Type*) [∀ i, CommSemiring (R i)]

/-- The canonical map from a disjoint union of prime spectra of commutative semirings to
the prime spectrum of the product semiring. -/
/- TODO: show this is always a topological embedding (even when ι is infinite)
and is a homeomorphism when ι is finite. -/
@[simps] def sigmaToPi : (Σ i, PrimeSpectrum (R i)) → PrimeSpectrum (Π i, R i)
  | ⟨i, p⟩ => (Pi.evalRingHom R i).specComap p

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
theorem exists_maximal_nmem_range_sigmaToPi_of_infinite :
    ∃ (I : Ideal (Π i, R i)) (_ : I.IsMaximal), ⟨I, inferInstance⟩ ∉ Set.range (sigmaToPi R) := by
  classical
  let J : Ideal (Π i, R i) := -- `J := Π₀ i, R i` is an ideal in `Π i, R i`
  { __ := AddMonoidHom.mrange DFinsupp.coeFnAddMonoidHom
    smul_mem' := by
      rintro r _ ⟨x, rfl⟩
      refine ⟨.mk x.support fun i ↦ r i * x i, funext fun i ↦ show dite _ _ _ = _ from ?_⟩
      simp_rw [DFinsupp.coeFnAddMonoidHom]
      refine dite_eq_left_iff.mpr fun h ↦ ?_
      rw [DFinsupp.not_mem_support_iff.mp h, mul_zero] }
  have ⟨I, max, le⟩ := J.exists_le_maximal <| (Ideal.ne_top_iff_one _).mpr <| by
    -- take a maximal ideal I containing J
    rintro ⟨x, hx⟩
    have ⟨i, hi⟩ := x.support.exists_not_mem
    simpa [DFinsupp.coeFnAddMonoidHom, DFinsupp.not_mem_support_iff.mp hi] using congr_fun hx i
  refine ⟨I, max, fun ⟨⟨i, p⟩, eq⟩ ↦ ?_⟩
  -- then I is not in the range of `sigmaToPi`
  have : ⇑(DFinsupp.single i 1) ∉ (sigmaToPi R ⟨i, p⟩).asIdeal := by
    simpa using p.1.ne_top_iff_one.mp p.2.ne_top
  rw [eq] at this
  exact this (le ⟨.single i 1, rfl⟩)

theorem sigmaToPi_not_surjective_of_infinite : ¬ (sigmaToPi R).Surjective := fun surj ↦
  have ⟨_, _, nmem⟩ := exists_maximal_nmem_range_sigmaToPi_of_infinite R
  (Set.range_eq_univ.mpr surj ▸ nmem) ⟨⟩

lemma exists_comap_evalRingHom_eq
    {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)] [Finite ι]
    (p : PrimeSpectrum (Π i, R i)) :
    ∃ (i : ι) (q : PrimeSpectrum (R i)), (Pi.evalRingHom R i).specComap q = p := by
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

lemma iUnion_range_specComap_comp_evalRingHom
    {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)] [Finite ι]
    {S : Type*} [CommRing S] (f : S →+* Π i, R i) :
    ⋃ i, Set.range ((Pi.evalRingHom R i).comp f).specComap = Set.range f.specComap := by
  simp_rw [specComap_comp]
  apply subset_antisymm
  · exact Set.iUnion_subset fun _ ↦ Set.range_comp_subset_range _ _
  · rintro _ ⟨p, rfl⟩
    obtain ⟨i, p, rfl⟩ := exists_comap_evalRingHom_eq p
    exact Set.mem_iUnion_of_mem i ⟨p, rfl⟩

end Pi

end PrimeSpectrum

section SpecOfSurjective

open Function RingHom

variable [CommRing R] [CommRing S]
variable (f : R →+* S)
variable {R}

theorem image_specComap_zeroLocus_eq_zeroLocus_comap (hf : Surjective f) (I : Ideal S) :
    f.specComap '' zeroLocus I = zeroLocus (I.comap f) := by
  simp only [Set.ext_iff, Set.mem_image, mem_zeroLocus, SetLike.coe_subset_coe]
  refine fun p => ⟨?_, fun h_I_p => ?_⟩
  · rintro ⟨p, hp, rfl⟩ a ha
    exact hp ha
  · have hp : ker f ≤ p.asIdeal := (Ideal.comap_mono bot_le).trans h_I_p
    refine ⟨⟨p.asIdeal.map f, Ideal.map_isPrime_of_surjective hf hp⟩, fun x hx => ?_, ?_⟩
    · obtain ⟨x', rfl⟩ := hf x
      exact Ideal.mem_map_of_mem f (h_I_p hx)
    · ext x
      rw [specComap_asIdeal, Ideal.mem_comap, Ideal.mem_map_iff_of_surjective f hf]
      refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
      rintro ⟨x', hx', heq⟩
      rw [← sub_sub_cancel x' x]
      refine p.asIdeal.sub_mem hx' (hp ?_)
      rwa [mem_ker, map_sub, sub_eq_zero]

theorem range_specComap_of_surjective (hf : Surjective f) :
    Set.range f.specComap = zeroLocus (ker f) := by
  rw [← Set.image_univ]
  convert image_specComap_zeroLocus_eq_zeroLocus_comap _ _ hf _
  rw [zeroLocus_bot]

variable {S} in
/-- `p` is in the image of `Spec S → Spec R` if and only if `p` extended to `S` and
restricted back to `R` is `p`. -/
lemma PrimeSpectrum.mem_range_comap_iff {p : PrimeSpectrum R} :
    p ∈ Set.range f.specComap ↔ (p.asIdeal.map f).comap f = p.asIdeal := by
  refine ⟨fun ⟨q, hq⟩ ↦ by simp [← hq], ?_⟩
  rw [Ideal.comap_map_eq_self_iff_of_isPrime]
  rintro ⟨q, _, hq⟩
  exact ⟨⟨q, inferInstance⟩, PrimeSpectrum.ext hq⟩

end SpecOfSurjective
