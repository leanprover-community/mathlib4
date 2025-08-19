/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Filippo A. E. Nuccio, Andrew Yang
-/
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Functoriality of the prime spectrum

In this file we define the induced map on prime spectra induced by a ring homomorphism.

## Main definitions

* `RingHom.specComap`: The induced map on prime spectra by a ring homomorphism. The bundled
  continuous version is `PrimeSpectrum.comap` in `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.

-/

universe u v

variable (R : Type u) (S : Type v)

open PrimeSpectrum

/-- The pullback of an element of `PrimeSpectrum S` along a ring homomorphism `f : R →+* S`.
The bundled continuous version is `PrimeSpectrum.comap`. -/
abbrev RingHom.specComap {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    PrimeSpectrum S → PrimeSpectrum R :=
  fun y ↦ ⟨Ideal.comap f y.asIdeal, inferInstance⟩

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
theorem specComap_id : (RingHom.id R).specComap = fun x ↦ x :=
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
    Function.Injective f.specComap := fun x y h ↦
  PrimeSpectrum.ext
    (Ideal.comap_injective_of_surjective f hf
      (congr_arg PrimeSpectrum.asIdeal h : (f.specComap x).asIdeal = (f.specComap y).asIdeal))

/-- `RingHom.specComap` of an isomorphism of rings as an equivalence of their prime spectra. -/
@[simps apply symm_apply]
def comapEquiv (e : R ≃+* S) : PrimeSpectrum R ≃o PrimeSpectrum S where
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
  map_rel_iff' {I J} := Ideal.comap_le_comap_iff_of_surjective _ e.symm.surjective ..

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
theorem exists_maximal_notMem_range_sigmaToPi_of_infinite :
    ∃ (I : Ideal (Π i, R i)) (_ : I.IsMaximal), ⟨I, inferInstance⟩ ∉ Set.range (sigmaToPi R) := by
  classical
  let J : Ideal (Π i, R i) := -- `J := Π₀ i, R i` is an ideal in `Π i, R i`
  { __ := AddMonoidHom.mrange DFinsupp.coeFnAddMonoidHom
    smul_mem' := by
      rintro r _ ⟨x, rfl⟩
      refine ⟨.mk x.support fun i ↦ r i * x i, funext fun i ↦ show dite _ _ _ = _ from ?_⟩
      simp_rw [DFinsupp.coeFnAddMonoidHom]
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

@[deprecated (since := "2025-05-24")]
alias exists_maximal_nmem_range_sigmaToPi_of_infinite :=
  exists_maximal_notMem_range_sigmaToPi_of_infinite

theorem sigmaToPi_not_surjective_of_infinite : ¬ (sigmaToPi R).Surjective := fun surj ↦
  have ⟨_, _, notMem⟩ := exists_maximal_notMem_range_sigmaToPi_of_infinite R
  (Set.range_eq_univ.mpr surj ▸ notMem) ⟨⟩

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
  refine fun p ↦ ⟨?_, fun h_I_p ↦ ?_⟩
  · rintro ⟨p, hp, rfl⟩ a ha
    exact hp ha
  · have hp : ker f ≤ p.asIdeal := (Ideal.comap_mono bot_le).trans h_I_p
    refine ⟨⟨p.asIdeal.map f, Ideal.map_isPrime_of_surjective hf hp⟩, fun x hx ↦ ?_, ?_⟩
    · obtain ⟨x', rfl⟩ := hf x
      exact Ideal.mem_map_of_mem f (h_I_p hx)
    · ext x
      rw [specComap_asIdeal, Ideal.mem_comap, Ideal.mem_map_iff_of_surjective f hf]
      refine ⟨?_, fun hx ↦ ⟨x, hx, rfl⟩⟩
      rintro ⟨x', hx', heq⟩
      rw [← sub_sub_cancel x' x]
      refine p.asIdeal.sub_mem hx' (hp ?_)
      rwa [mem_ker, map_sub, sub_eq_zero]

theorem range_specComap_of_surjective (hf : Surjective f) :
    Set.range f.specComap = zeroLocus (ker f) := by
  rw [← Set.image_univ]
  convert image_specComap_zeroLocus_eq_zeroLocus_comap _ _ hf _
  rw [zeroLocus_bot]

variable {S}

/-- Let `f : R →+* S` be a surjective ring homomorphism, then `Spec S` is order-isomorphic to `Z(I)`
  where `I = ker f`. -/
noncomputable def Ideal.primeSpectrumOrderIsoZeroLocusOfSurj (hf : Surjective f) {I : Ideal R}
    (hI : RingHom.ker f = I) : PrimeSpectrum S ≃o (PrimeSpectrum.zeroLocus (R := R) I) where
  toFun p := ⟨f.specComap p, hI.symm.trans_le (Ideal.ker_le_comap f)⟩
  invFun := fun ⟨⟨p, _⟩, hp⟩ ↦ ⟨p.map f, p.map_isPrime_of_surjective hf (hI.trans_le hp)⟩
  left_inv := by
    intro ⟨p, _⟩
    simp only [PrimeSpectrum.mk.injEq]
    exact p.map_comap_of_surjective f hf
  right_inv := by
    intro ⟨⟨p, _⟩, hp⟩
    simp only [Subtype.mk.injEq, PrimeSpectrum.mk.injEq]
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
    p ∈ Set.range f.specComap ↔ (p.asIdeal.map f).comap f = p.asIdeal := by
  refine ⟨fun ⟨q, hq⟩ ↦ by simp [← hq], ?_⟩
  rw [Ideal.comap_map_eq_self_iff_of_isPrime]
  rintro ⟨q, _, hq⟩
  exact ⟨⟨q, inferInstance⟩, PrimeSpectrum.ext hq⟩

open TensorProduct

/-- A prime `p` is in the range of `Spec S → Spec R` if the fiber over `p` is nontrivial. -/
lemma PrimeSpectrum.nontrivial_iff_mem_rangeComap {S : Type*} [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) :
    Nontrivial (p.asIdeal.ResidueField ⊗[R] S) ↔ p ∈ Set.range (algebraMap R S).specComap := by
  let k := p.asIdeal.ResidueField
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] S)
    use (Algebra.TensorProduct.includeRight).specComap ⟨m, hm.isPrime⟩
    ext : 1
    rw [← PrimeSpectrum.specComap_comp_apply,
      ← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap, specComap_comp_apply]
    simp [Ideal.eq_bot_of_prime, k, ← RingHom.ker_eq_comap_bot]
  · obtain ⟨q, rfl⟩ := h
    let f : k ⊗[R] S →ₐ[R] q.asIdeal.ResidueField :=
      Algebra.TensorProduct.lift (Ideal.ResidueField.mapₐ _ _ rfl)
        (IsScalarTower.toAlgHom _ _ _) (fun _ _ ↦ Commute.all ..)
    exact RingHom.domain_nontrivial f.toRingHom

end SpecOfSurjective

section ResidueField

variable {R : Type*} [CommRing R]

lemma PrimeSpectrum.residueField_specComap (I : PrimeSpectrum R) :
    Set.range (algebraMap R I.asIdeal.ResidueField).specComap = {I} := by
  rw [Set.range_unique, Set.singleton_eq_singleton_iff]
  exact PrimeSpectrum.ext (Ideal.ext fun x ↦ Ideal.algebraMap_residueField_eq_zero)

end ResidueField

variable {R S} in
theorem IsLocalHom.of_specComap_surjective [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (hf : Function.Surjective f.specComap) : IsLocalHom f where
  map_nonunit x hfx := by
    by_contra hx
    obtain ⟨p, hp, _⟩ := exists_max_ideal_of_mem_nonunits hx
    obtain ⟨⟨q, hqp⟩, hq⟩ := hf ⟨p, hp.isPrime⟩
    simp only [PrimeSpectrum.mk.injEq] at hq
    exact hqp.ne_top (q.eq_top_of_isUnit_mem (q.mem_comap.mp (by rwa [hq])) hfx)
