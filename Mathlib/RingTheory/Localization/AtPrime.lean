/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Localizations of commutative rings at the complement of a prime ideal

## Main definitions

 * `IsLocalization.AtPrime (P : Ideal R) [IsPrime P] (S : Type*)` expresses that `S` is a
   localization at (the complement of) a prime ideal `P`, as an abbreviation of
   `IsLocalization P.prime_compl S`

## Main results

 * `IsLocalization.AtPrime.isLocalRing`: a theorem (not an instance) stating a localization at the
   complement of a prime ideal is a local ring

## Implementation notes

See `RingTheory.Localization.Basic` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type*} [CommSemiring R] (S : Type*) [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

section AtPrime

variable (P : Ideal R) [hp : P.IsPrime]

/-- Given a prime ideal `P`, the typeclass `IsLocalization.AtPrime S P` states that `S` is
isomorphic to the localization of `R` at the complement of `P`. -/
protected abbrev IsLocalization.AtPrime :=
  IsLocalization P.primeCompl S

/-- Given a prime ideal `P`, `Localization.AtPrime P` is a localization of
`R` at the complement of `P`, as a quotient type. -/
protected abbrev Localization.AtPrime :=
  Localization P.primeCompl

namespace IsLocalization

theorem AtPrime.Nontrivial [IsLocalization.AtPrime S P] : Nontrivial S :=
  nontrivial_of_ne (0 : S) 1 fun hze => by
    rw [← (algebraMap R S).map_one, ← (algebraMap R S).map_zero] at hze
    obtain ⟨t, ht⟩ := (eq_iff_exists P.primeCompl S).1 hze
    have htz : (t : R) = 0 := by simpa using ht.symm
    exact t.2 (htz.symm ▸ P.zero_mem : ↑t ∈ P)

theorem AtPrime.isLocalRing [IsLocalization.AtPrime S P] : IsLocalRing S :=
  -- Porting note: since I couldn't get local instance running, I just specify it manually
  letI := AtPrime.Nontrivial S P
  IsLocalRing.of_nonunits_add
    (by
      intro x y hx hy hu
      obtain ⟨z, hxyz⟩ := isUnit_iff_exists_inv.1 hu
      have : ∀ {r : R} {s : P.primeCompl}, mk' S r s ∈ nonunits S → r ∈ P := fun {r s} =>
        not_imp_comm.1 fun nr => isUnit_iff_exists_inv.2 ⟨mk' S ↑s (⟨r, nr⟩ : P.primeCompl),
          mk'_mul_mk'_eq_one' _ _ <| show r ∈ P.primeCompl from nr⟩
      rcases mk'_surjective P.primeCompl x with ⟨rx, sx, hrx⟩
      rcases mk'_surjective P.primeCompl y with ⟨ry, sy, hry⟩
      rcases mk'_surjective P.primeCompl z with ⟨rz, sz, hrz⟩
      rw [← hrx, ← hry, ← hrz, ← mk'_add, ← mk'_mul, ← mk'_self S P.primeCompl.one_mem] at hxyz
      rw [← hrx] at hx
      rw [← hry] at hy
      obtain ⟨t, ht⟩ := IsLocalization.eq.1 hxyz
      simp only [mul_one, one_mul, Submonoid.coe_mul, Subtype.coe_mk] at ht
      suffices (t : R) * (sx * sy * sz) ∈ P from
        not_or_intro (mt hp.mem_or_mem <| not_or_intro sx.2 sy.2) sz.2
          (hp.mem_or_mem <| (hp.mem_or_mem this).resolve_left t.2)
      rw [← ht]
      exact
        P.mul_mem_left _ <| P.mul_mem_right _ <|
            P.add_mem (P.mul_mem_right _ <| this hx) <| P.mul_mem_right _ <| this hy)

@[deprecated (since := "2024-11-09")] alias AtPrime.localRing := AtPrime.isLocalRing

end IsLocalization

namespace Localization

/-- The localization of `R` at the complement of a prime ideal is a local ring. -/
instance AtPrime.isLocalRing : IsLocalRing (Localization P.primeCompl) :=
  IsLocalization.AtPrime.isLocalRing (Localization P.primeCompl) P

instance {R S : Type*} [CommRing R] [NoZeroDivisors R] {P : Ideal R} [CommRing S] [Algebra R S]
    [NoZeroSMulDivisors R S] [IsDomain S] [P.IsPrime] :
    NoZeroSMulDivisors (Localization.AtPrime P)
    (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) :=
  NoZeroSMulDivisors_of_isLocalization R S _ _ P.primeCompl_le_nonZeroDivisors

end Localization

end AtPrime

namespace IsLocalization

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The localization of an integral domain at the complement of a prime ideal is an integral domain.
-/
instance isDomain_of_local_atPrime {P : Ideal A} (_ : P.IsPrime) :
    IsDomain (Localization.AtPrime P) :=
  isDomain_localization P.primeCompl_le_nonZeroDivisors

namespace AtPrime

variable (I : Ideal R) [hI : I.IsPrime] [IsLocalization.AtPrime S I]

/-- The prime ideals in the localization of a commutative ring at a prime ideal I are in
order-preserving bijection with the prime ideals contained in I. -/
def orderIsoOfPrime : { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPrime ∧ p ≤ I } :=
  (IsLocalization.orderIsoOfPrime I.primeCompl S).trans <| .setCongr _ _ <| show setOf _ = setOf _
    by ext; simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left]

theorem isUnit_to_map_iff (x : R) : IsUnit ((algebraMap R S) x) ↔ x ∈ I.primeCompl :=
  ⟨fun h hx =>
    (isPrime_of_isPrime_disjoint I.primeCompl S I hI disjoint_compl_left).ne_top <|
      (Ideal.map (algebraMap R S) I).eq_top_of_isUnit_mem (Ideal.mem_map_of_mem _ hx) h,
    fun h => map_units S ⟨x, h⟩⟩

-- Can't use typeclasses to infer the `IsLocalRing` instance, so use an `optParam` instead
-- (since `IsLocalRing` is a `Prop`, there should be no unification issues.)
theorem to_map_mem_maximal_iff (x : R) (h : IsLocalRing S := isLocalRing S I) :
    algebraMap R S x ∈ IsLocalRing.maximalIdeal S ↔ x ∈ I :=
  not_iff_not.mp <| by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using
      isUnit_to_map_iff S I x

theorem comap_maximalIdeal (h : IsLocalRing S := isLocalRing S I) :
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = I :=
  Ideal.ext fun x => by simpa only [Ideal.mem_comap] using to_map_mem_maximal_iff _ I x

theorem isUnit_mk'_iff (x : R) (y : I.primeCompl) : IsUnit (mk' S x y) ↔ x ∈ I.primeCompl :=
  ⟨fun h hx => mk'_mem_iff.mpr ((to_map_mem_maximal_iff S I x).mpr hx) h, fun h =>
    isUnit_iff_exists_inv.mpr ⟨mk' S ↑y ⟨x, h⟩, mk'_mul_mk'_eq_one ⟨x, h⟩ y⟩⟩

theorem mk'_mem_maximal_iff (x : R) (y : I.primeCompl) (h : IsLocalRing S := isLocalRing S I) :
    mk' S x y ∈ IsLocalRing.maximalIdeal S ↔ x ∈ I :=
  not_iff_not.mp <| by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using
      isUnit_mk'_iff S I x y

end AtPrime

end IsLocalization

namespace Localization

open IsLocalization

attribute [local instance] Classical.propDecidable

variable (I : Ideal R) [hI : I.IsPrime]
variable {I}

/-- The unique maximal ideal of the localization at `I.primeCompl` lies over the ideal `I`. -/
theorem AtPrime.comap_maximalIdeal :
    Ideal.comap (algebraMap R (Localization.AtPrime I))
        (IsLocalRing.maximalIdeal (Localization I.primeCompl)) =
      I :=
  -- Porting note: need to provide full name
  IsLocalization.AtPrime.comap_maximalIdeal _ _

/-- The image of `I` in the localization at `I.primeCompl` is a maximal ideal, and in particular
it is the unique maximal ideal given by the local ring structure `AtPrime.isLocalRing` -/
theorem AtPrime.map_eq_maximalIdeal :
    Ideal.map (algebraMap R (Localization.AtPrime I)) I =
      IsLocalRing.maximalIdeal (Localization I.primeCompl) := by
  convert congr_arg (Ideal.map (algebraMap R (Localization.AtPrime I)))
  -- Porting note: `algebraMap R ...` can not be solve by unification
    (AtPrime.comap_maximalIdeal (hI := hI)).symm
  -- Porting note: can not find `hI`
  rw [map_comap I.primeCompl]

theorem le_comap_primeCompl_iff {J : Ideal P} [J.IsPrime] {f : R →+* P} :
    I.primeCompl ≤ J.primeCompl.comap f ↔ J.comap f ≤ I :=
  ⟨fun h x hx => by
    contrapose! hx
    exact h hx,
   fun h _ hx hfxJ => hx (h hfxJ)⟩

variable (I)

/-- For a ring hom `f : R →+* S` and a prime ideal `J` in `S`, the induced ring hom from the
localization of `R` at `J.comap f` to the localization of `S` at `J`.

To make this definition more flexible, we allow any ideal `I` of `R` as input, together with a proof
that `I = J.comap f`. This can be useful when `I` is not definitionally equal to `J.comap f`.
-/
noncomputable def localRingHom (J : Ideal P) [J.IsPrime] (f : R →+* P) (hIJ : I = J.comap f) :
    Localization.AtPrime I →+* Localization.AtPrime J :=
  IsLocalization.map (Localization.AtPrime J) f (le_comap_primeCompl_iff.mpr (ge_of_eq hIJ))

theorem localRingHom_to_map (J : Ideal P) [J.IsPrime] (f : R →+* P) (hIJ : I = J.comap f)
    (x : R) : localRingHom I J f hIJ (algebraMap _ _ x) = algebraMap _ _ (f x) :=
  map_eq _ _

theorem localRingHom_mk' (J : Ideal P) [J.IsPrime] (f : R →+* P) (hIJ : I = J.comap f) (x : R)
    (y : I.primeCompl) :
    localRingHom I J f hIJ (IsLocalization.mk' _ x y) =
      IsLocalization.mk' (Localization.AtPrime J) (f x)
        (⟨f y, le_comap_primeCompl_iff.mpr (ge_of_eq hIJ) y.2⟩ : J.primeCompl) :=
  map_mk' _ _ _

@[instance]
theorem isLocalHom_localRingHom (J : Ideal P) [hJ : J.IsPrime] (f : R →+* P)
    (hIJ : I = J.comap f) : IsLocalHom (localRingHom I J f hIJ) :=
  IsLocalHom.mk fun x hx => by
    rcases IsLocalization.mk'_surjective I.primeCompl x with ⟨r, s, rfl⟩
    rw [localRingHom_mk'] at hx
    rw [AtPrime.isUnit_mk'_iff] at hx ⊢
    exact fun hr => hx ((SetLike.ext_iff.mp hIJ r).mp hr)

theorem localRingHom_unique (J : Ideal P) [J.IsPrime] (f : R →+* P) (hIJ : I = J.comap f)
    {j : Localization.AtPrime I →+* Localization.AtPrime J}
    (hj : ∀ x : R, j (algebraMap _ _ x) = algebraMap _ _ (f x)) : localRingHom I J f hIJ = j :=
  map_unique _ _ hj

@[simp]
theorem localRingHom_id : localRingHom I I (RingHom.id R) (Ideal.comap_id I).symm = RingHom.id _ :=
  localRingHom_unique _ _ _ _ fun _ => rfl

-- Porting note: simplifier won't pick up this lemma, so deleted @[simp]
theorem localRingHom_comp {S : Type*} [CommSemiring S] (J : Ideal S) [hJ : J.IsPrime] (K : Ideal P)
    [hK : K.IsPrime] (f : R →+* S) (hIJ : I = J.comap f) (g : S →+* P) (hJK : J = K.comap g) :
    localRingHom I K (g.comp f) (by rw [hIJ, hJK, Ideal.comap_comap f g]) =
      (localRingHom J K g hJK).comp (localRingHom I J f hIJ) :=
  localRingHom_unique _ _ _ _ fun r => by
    simp only [Function.comp_apply, RingHom.coe_comp, localRingHom_to_map]

namespace AtPrime

section

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

noncomputable instance (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
  Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
    (Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over).toAlgebra

instance (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
  IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime P) := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp, Function.comp_apply,
      Localization.localRingHom_to_map, ← IsScalarTower.algebraMap_apply]

end

variable {ι : Type*} {R : ι → Type*} [∀ i, CommSemiring (R i)]
variable {i : ι} (I : Ideal (R i)) [I.IsPrime]

/-- `Localization.localRingHom` specialized to a projection homomorphism from a product ring. -/
noncomputable abbrev mapPiEvalRingHom :
    Localization.AtPrime (I.comap <| Pi.evalRingHom R i) →+* Localization.AtPrime I :=
  localRingHom _ _ _ rfl

theorem mapPiEvalRingHom_bijective : Function.Bijective (mapPiEvalRingHom I) :=
  Localization.mapPiEvalRingHom_bijective _

theorem mapPiEvalRingHom_comp_algebraMap :
    (mapPiEvalRingHom I).comp (algebraMap _ _) = (algebraMap _ _).comp (Pi.evalRingHom R i) :=
  IsLocalization.map_comp _

theorem mapPiEvalRingHom_algebraMap_apply {r : Π i, R i} :
    mapPiEvalRingHom I (algebraMap _ _ r) = algebraMap _ _ (r i) :=
  localRingHom_to_map ..

end AtPrime

end Localization

variable {R : Type*} [CommRing R] (q : Ideal R) [q.IsPrime] {S : Type*} [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S q]

lemma Ideal.isPrime_map_of_isLocalizationAtPrime {p : Ideal R} [p.IsPrime] (hpq : p ≤ q) :
    (p.map (algebraMap R S)).IsPrime := by
  have disj : Disjoint (q.primeCompl : Set R) p := by
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hpq]
  apply IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p (by simpa) disj

lemma Ideal.under_map_of_isLocalizationAtPrime {p : Ideal R} [p.IsPrime] (hpq : p ≤ q) :
    (p.map (algebraMap R S)).under R = p := by
  have disj : Disjoint (q.primeCompl : Set R) p := by
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hpq]
  exact IsLocalization.comap_map_of_isPrime_disjoint _ _ p (by simpa) disj

lemma IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes
    {R : Type*} [CommSemiring R] (p : Ideal R) (hp : p ∈ minimalPrimes R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization.AtPrime S p (hp := hp.1.1)] :
    Subsingleton (PrimeSpectrum S) :=
  have := hp.1.1
  have : Unique {i : Ideal R // i.IsPrime ∧ i ≤ p} := ⟨⟨p, hp.1.1, le_rfl⟩,
    fun i ↦ Subtype.ext <| (minimalPrimes_eq_minimals (R := R) ▸ hp).eq_of_le i.2.1 i.2.2⟩
  have := (IsLocalization.AtPrime.orderIsoOfPrime S p).subsingleton
  ⟨fun x y ↦ PrimeSpectrum.ext congr($(this.1 ⟨_, x.2⟩ ⟨_, y.2⟩))⟩
