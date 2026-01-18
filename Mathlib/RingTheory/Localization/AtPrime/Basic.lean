/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

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

@[expose] public section

open Module

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

theorem AtPrime.nontrivial [IsLocalization.AtPrime S P] : Nontrivial S :=
  nontrivial_of_ne (0 : S) 1 fun hze => by
    rw [← (algebraMap R S).map_one, ← (algebraMap R S).map_zero] at hze
    obtain ⟨t, ht⟩ := (eq_iff_exists P.primeCompl S).1 hze
    have htz : (t : R) = 0 := by simpa using ht.symm
    exact t.2 (htz.symm ▸ P.zero_mem : ↑t ∈ P)

@[deprecated (since := "2025-07-31")] alias AtPrime.Nontrivial := IsLocalization.AtPrime.nontrivial

theorem AtPrime.isLocalRing [IsLocalization.AtPrime S P] : IsLocalRing S :=
  letI := AtPrime.nontrivial S P -- Can't be a local instance because we can't figure out `P`.
  IsLocalRing.of_nonunits_add
    (by
      intro x y hx hy hu
      obtain ⟨z, hxyz⟩ := isUnit_iff_exists_inv.1 hu
      have : ∀ {r : R} {s : P.primeCompl}, mk' S r s ∈ nonunits S → r ∈ P := fun {r s} =>
        not_imp_comm.1 fun nr => isUnit_iff_exists_inv.2 ⟨mk' S ↑s (⟨r, nr⟩ : P.primeCompl),
          mk'_mul_mk'_eq_one' _ _ <| show r ∈ P.primeCompl from nr⟩
      rcases exists_mk'_eq P.primeCompl x with ⟨rx, sx, hrx⟩
      rcases exists_mk'_eq P.primeCompl y with ⟨ry, sy, hry⟩
      rcases exists_mk'_eq P.primeCompl z with ⟨rz, sz, hrz⟩
      rw [← hrx, ← hry, ← hrz, ← mk'_add, ← mk'_mul, ← mk'_self S P.primeCompl.one_mem] at hxyz
      rw [← hrx] at hx
      rw [← hry] at hy
      obtain ⟨t, ht⟩ := IsLocalization.eq.1 hxyz
      simp only [mul_one, one_mul, Submonoid.coe_mul] at ht
      suffices (t : R) * (sx * sy * sz) ∈ P from
        not_or_intro (mt hp.mem_or_mem <| not_or_intro sx.2 sy.2) sz.2
          (hp.mem_or_mem <| (hp.mem_or_mem this).resolve_left t.2)
      rw [← ht]
      exact
        P.mul_mem_left _ <| P.mul_mem_right _ <|
            P.add_mem (P.mul_mem_right _ <| this hx) <| P.mul_mem_right _ <| this hy)

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The localization of an integral domain at the complement of a prime ideal is an integral domain.
-/
instance isDomain_of_local_atPrime {P : Ideal A} (_ : P.IsPrime) :
    IsDomain (Localization.AtPrime P) :=
  isDomain_localization P.primeCompl_le_nonZeroDivisors

end IsLocalization

namespace Localization

/-- The localization of `R` at the complement of a prime ideal is a local ring. -/
instance AtPrime.isLocalRing : IsLocalRing (Localization P.primeCompl) :=
  IsLocalization.AtPrime.isLocalRing (Localization P.primeCompl) P

instance {R S : Type*} [CommRing R] [IsDomain R] {P : Ideal R} [CommRing S] [Algebra R S]
    [IsTorsionFree R S] [IsDomain S] [P.IsPrime] :
    IsTorsionFree (Localization.AtPrime P) <|
      Localization <| Algebra.algebraMapSubmonoid S P.primeCompl :=
  .of_isLocalization R S P.primeCompl_le_nonZeroDivisors

theorem _root_.IsLocalization.AtPrime.faithfulSMul (R : Type*) [CommRing R] [NoZeroDivisors R]
    [Algebra R S] (P : Ideal R) [hp : P.IsPrime] [IsLocalization.AtPrime S P] :
    FaithfulSMul R S := by
  rw [faithfulSMul_iff_algebraMap_injective, IsLocalization.injective_iff_isRegular P.primeCompl]
  exact fun ⟨_, h⟩ ↦ isRegular_of_ne_zero <| by aesop

instance {R : Type*} [CommRing R] [NoZeroDivisors R] (P : Ideal R) [hp : P.IsPrime] :
    FaithfulSMul R (Localization.AtPrime P) := IsLocalization.AtPrime.faithfulSMul _ _ P

end Localization

end AtPrime

namespace IsLocalization

variable {A : Type*} [CommRing A] [IsDomain A]

/-- This is an `IsLocalization.AtPrime` version for `IsLocalization.isDomain_of_local_atPrime`. -/
theorem isDomain_of_atPrime (S : Type*) [CommSemiring S] [Algebra A S]
    (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime S P] : IsDomain S :=
  isDomain_of_le_nonZeroDivisors S P.primeCompl_le_nonZeroDivisors

namespace AtPrime

variable (I : Ideal R) [hI : I.IsPrime] [IsLocalization.AtPrime S I]

/-- The prime ideals in the localization of a commutative ring at a prime ideal I are in
order-preserving bijection with the prime ideals contained in I. -/
@[simps!]
def orderIsoOfPrime : { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPrime ∧ p ≤ I } :=
  (IsLocalization.orderIsoOfPrime I.primeCompl S).trans <| .setCongr _ _ <| show setOf _ = setOf _
    by ext; simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left]

/-- The prime spectrum of the localization of a commutative ring R at a prime ideal I are in
order-preserving bijection with the interval (-∞, I] in the prime spectrum of R. -/
@[simps!] def primeSpectrumOrderIso : PrimeSpectrum S ≃o Set.Iic (⟨I, hI⟩ : PrimeSpectrum R) :=
  (PrimeSpectrum.equivSubtype S).trans <| (orderIsoOfPrime S I).trans
    ⟨⟨fun p ↦ ⟨⟨p, p.2.1⟩, p.2.2⟩, fun p ↦ ⟨p.1.1, p.1.2, p.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩, .rfl⟩

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

theorem liesOver_maximalIdeal (h : IsLocalRing S := isLocalRing S I) :
    (IsLocalRing.maximalIdeal S).LiesOver I :=
  (Ideal.liesOver_iff _ _).mpr (comap_maximalIdeal _ _).symm

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

variable (I : Ideal R) [hI : I.IsPrime]
variable {I}

/-- The unique maximal ideal of the localization at `I.primeCompl` lies over the ideal `I`. -/
theorem AtPrime.comap_maximalIdeal :
    Ideal.comap (algebraMap R (Localization.AtPrime I))
        (IsLocalRing.maximalIdeal (Localization I.primeCompl)) =
      I :=
  IsLocalization.AtPrime.comap_maximalIdeal _ _

/-- The image of `I` in the localization at `I.primeCompl` is a maximal ideal, and in particular
it is the unique maximal ideal given by the local ring structure `AtPrime.isLocalRing` -/
theorem AtPrime.map_eq_maximalIdeal :
    Ideal.map (algebraMap R (Localization.AtPrime I)) I =
      IsLocalRing.maximalIdeal (Localization I.primeCompl) := by
  convert congr_arg (Ideal.map _) AtPrime.comap_maximalIdeal.symm
  rw [map_comap I.primeCompl]

lemma AtPrime.eq_maximalIdeal_iff_comap_eq {J : Ideal (Localization.AtPrime I)} :
    Ideal.comap (algebraMap R (Localization.AtPrime I)) J = I ↔
    J = IsLocalRing.maximalIdeal (Localization.AtPrime I) where
  mp h := le_antisymm (IsLocalRing.le_maximalIdeal (fun hJ ↦ (hI.ne_top (h.symm ▸ hJ ▸ rfl)))) <| by
    simpa [← AtPrime.map_eq_maximalIdeal, ← h] using Ideal.map_comap_le
  mpr h := h.symm ▸ AtPrime.comap_maximalIdeal

theorem le_comap_primeCompl_iff {J : Ideal P} [J.IsPrime] {f : R →+* P} :
    I.primeCompl ≤ J.primeCompl.comap f ↔ J.comap f ≤ I :=
  ⟨fun h x hx => by
    contrapose hx
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
    rcases IsLocalization.exists_mk'_eq I.primeCompl x with ⟨r, s, rfl⟩
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

-- `simp` can't figure out `J` so this can't be a `@[simp]` lemma.
theorem localRingHom_comp {S : Type*} [CommSemiring S] (J : Ideal S) [hJ : J.IsPrime] (K : Ideal P)
    [hK : K.IsPrime] (f : R →+* S) (hIJ : I = J.comap f) (g : S →+* P) (hJK : J = K.comap g) :
    localRingHom I K (g.comp f) (by rw [hIJ, hJK, Ideal.comap_comap f g]) =
      (localRingHom J K g hJK).comp (localRingHom I J f hIJ) :=
  localRingHom_unique _ _ _ _ fun r => by
    simp only [Function.comp_apply, RingHom.coe_comp, localRingHom_to_map]

namespace AtPrime

section

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [Algebra R A] [Algebra R B] [IsScalarTower R A B] [Algebra B C] [IsScalarTower A B C]

noncomputable instance (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
  (Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over).toAlgebra

instance (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P) :=
  .of_algebraMap_eq <| by
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply R A (Localization.AtPrime p),
      Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R B (Localization.AtPrime P),
      IsScalarTower.algebraMap_apply R A B]

instance (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] (Q : Ideal C)
    [Q.IsPrime] [Q.LiesOver P] [Q.LiesOver p] :
    IsScalarTower (Localization.AtPrime p) (Localization.AtPrime P) (Localization.AtPrime Q) :=
  .of_algebraMap_eq' <| by
    simp [RingHom.algebraMap_toAlgebra, ← localRingHom_comp, ← IsScalarTower.algebraMap_eq]

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

section

variable (q : Ideal R) [q.IsPrime] (M : Submonoid R) {S : Type*} [CommSemiring S] [Algebra R S]
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
  exact IsLocalization.comap_map_of_isPrime_disjoint _ _ (by simpa) disj

lemma IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes
    {R : Type*} [CommSemiring R] (p : Ideal R) (hp : p ∈ minimalPrimes R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization.AtPrime S p (hp := hp.1.1)] :
    Subsingleton (PrimeSpectrum S) :=
  have := hp.1.1
  have : Unique (Set.Iic (⟨p, hp.1.1⟩ : PrimeSpectrum R)) := ⟨⟨⟨p, hp.1.1⟩, by exact
    fun ⦃x⦄ a ↦ a⟩, fun i ↦ Subtype.ext <| PrimeSpectrum.ext <|
    (minimalPrimes_eq_minimals (R := R) ▸ hp).eq_of_le i.1.2 i.2⟩
  (IsLocalization.AtPrime.primeSpectrumOrderIso S p).subsingleton

open Ideal in
/-- If `R'` (resp. `S'`) is the localization of `R` (resp. `S`) and
`P` lies over `p` then the image of `P` in `S'` lies over the image of `p` in `R'`. -/
lemma IsLocalization.liesOver_of_isPrime_of_disjoint {R' S' : Type*}
    (M : Submonoid R) (T : Submonoid S)
    [CommSemiring R'] [CommSemiring S'] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S']
    [IsLocalization M R'] [IsLocalization T S']
    (p : Ideal R) {P : Ideal S} [P.IsPrime] [P.LiesOver p]
    (disj : Disjoint (T : Set S) (P : Set S)) :
    (P.map (algebraMap S S')).LiesOver (p.map (algebraMap R R')) := by
  suffices h : Ideal.map (algebraMap R R') (under R (under R' (P.map (algebraMap S S')))) =
      Ideal.map (algebraMap R R') p by exact ⟨by rw [← h, IsLocalization.map_comap (M := M)]⟩
  rw [under_under, ← under_under (B := S), under_def, under_def,
    IsLocalization.comap_map_of_isPrime_disjoint _ _ ‹_› disj,
    LiesOver.over (P := P) (p := p)]

lemma Ideal.IsMaximal.of_isLocalization_of_disjoint [IsLocalization M S] {J : Ideal S}
    [(Ideal.comap (algebraMap R S) J).IsMaximal] : J.IsMaximal := by
  obtain ⟨m, maxm, hm⟩ := exists_le_maximal J <| by
    rintro rfl
    exact Ideal.IsMaximal.ne_top ‹_› (by simp)
  apply comap_mono (f := algebraMap R S) at hm
  rwa [← IsLocalization.map_comap M S J, IsMaximal.eq_of_le ‹_› (IsPrime.under R m).ne_top hm,
    Ideal.under_def, IsLocalization.map_comap M S m]

end

namespace IsLocalization.AtPrime

open Algebra IsLocalRing Ideal IsLocalization IsLocalization.AtPrime

variable (p : Ideal R) [p.IsPrime] (Rₚ : Type*) [CommSemiring Rₚ] [Algebra R Rₚ]
  [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] (Sₚ : Type*) [CommSemiring Sₚ] [Algebra S Sₚ]
  [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ] [Algebra Rₚ Sₚ]
  (P : Ideal S)

theorem isPrime_map_of_liesOver [P.IsPrime] [P.LiesOver p] : (P.map (algebraMap S Sₚ)).IsPrime :=
  isPrime_of_isPrime_disjoint _ _ _ inferInstance (Ideal.disjoint_primeCompl_of_liesOver P p)

theorem map_eq_maximalIdeal : p.map (algebraMap R Rₚ) = maximalIdeal Rₚ := by
  convert congr_arg (Ideal.map (algebraMap R Rₚ)) (comap_maximalIdeal Rₚ p).symm
  rw [map_comap p.primeCompl]

instance isMaximal_map : (p.map (algebraMap R Rₚ)).IsMaximal := by
  rw [map_eq_maximalIdeal]
  exact maximalIdeal.isMaximal Rₚ

theorem comap_map_of_isMaximal [P.IsMaximal] [P.LiesOver p] :
    Ideal.comap (algebraMap S Sₚ) (Ideal.map (algebraMap S Sₚ) P) = P :=
  comap_map_eq_self_of_isMaximal _ (isPrime_map_of_liesOver S p Sₚ P).ne_top

section isomorphisms

attribute [local instance] Ideal.Quotient.field

variable {S R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal]
variable (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]

open IsLocalRing

/-- The isomorphism `R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ`, where `Rₚ` satisfies
`IsLocalization.AtPrime Rₚ p`. In particular, localization preserves the residue field. -/
noncomputable
def equivQuotMaximalIdeal : R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ := by
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap R (Rₚ ⧸ maximalIdeal Rₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq R Rₚ, ← RingHom.comap_ker,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, IsLocalization.AtPrime.comap_maximalIdeal Rₚ p]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p s)⁻¹
    simp only [IsScalarTower.algebraMap_eq R Rₚ (Rₚ ⧸ _),
      Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]
    use x * s'
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    have : algebraMap R Rₚ s ∉ maximalIdeal Rₚ := by
      rw [← Ideal.mem_comap, IsLocalization.AtPrime.comap_maximalIdeal Rₚ p]
      exact s.prop
    refine ((inferInstanceAs <| (maximalIdeal Rₚ).IsPrime).mem_or_mem ?_).resolve_left this
    rw [mul_sub, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mul_cancel_left,
      ← map_mul, ← map_sub, ← Ideal.mem_comap, IsLocalization.AtPrime.comap_maximalIdeal Rₚ p,
      mul_left_comm, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, hs,
      mul_inv_cancel₀, mul_one, sub_self]
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact s.prop

@[simp]
theorem equivQuotMaximalIdeal_apply_mk (x : R) :
    equivQuotMaximalIdeal p Rₚ (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ (algebraMap R Rₚ x)) := rfl

@[simp]
theorem equivQuotMaximalIdeal_symm_apply_mk (x : R) (s : p.primeCompl) :
    (equivQuotMaximalIdeal p Rₚ).symm (Ideal.Quotient.mk _ (IsLocalization.mk' Rₚ x s)) =
        (Ideal.Quotient.mk p x) * (Ideal.Quotient.mk p s)⁻¹ := by
  have h₁ : Ideal.Quotient.mk p ↑s ≠ 0 := by
    simpa [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using Ideal.mem_primeCompl_iff.mp s.prop
  have h₂ : equivQuotMaximalIdeal p Rₚ (Ideal.Quotient.mk p ↑s) ≠ 0 := by
    rwa [RingEquiv.map_ne_zero_iff]
  rw [RingEquiv.symm_apply_eq, ← mul_left_inj' h₂, map_mul, mul_assoc, ← map_mul,
    inv_mul_cancel₀ h₁, map_one, mul_one, equivQuotMaximalIdeal_apply_mk, ← map_mul,
    mk'_spec, Ideal.Quotient.mk_algebraMap, equivQuotMaximalIdeal_apply_mk,
    Ideal.Quotient.mk_algebraMap]

@[deprecated (since := "2025-11-13")] alias _root_.equivQuotMaximalIdealOfIsLocalization :=
  equivQuotMaximalIdeal

variable {Sₚ : Type*} [CommRing S] [Algebra R S] [CommRing Sₚ] [Algebra S Sₚ] [Algebra R Sₚ]
variable [Algebra Rₚ Sₚ] [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
variable [IsScalarTower R S Sₚ]

local notation "pS" => Ideal.map (algebraMap R S) p
local notation "pSₚ" => Ideal.map (algebraMap Rₚ Sₚ) (maximalIdeal Rₚ)

lemma comap_map_eq_map :
    (Ideal.map (algebraMap R Sₚ) p).comap (algebraMap S Sₚ) = pS := by
  rw [IsScalarTower.algebraMap_eq R S Sₚ, ← Ideal.map_map, eq_comm]
  apply Ideal.le_comap_map.antisymm
  intro x hx
  obtain ⟨α, hα, hαx⟩ : ∃ α ∉ p, α • x ∈ pS := by
    have ⟨⟨y, s⟩, hy⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ).mp hx
    rw [← map_mul,
      IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid S p.primeCompl)] at hy
    obtain ⟨c, hc⟩ := hy
    obtain ⟨α, hα, e⟩ := (c * s).prop
    refine ⟨α, hα, ?_⟩
    rw [Algebra.smul_def, e, Submonoid.coe_mul, mul_assoc, mul_comm _ x, hc]
    exact Ideal.mul_mem_left _ _ y.prop
  obtain ⟨β, γ, hγ, hβ⟩ : ∃ β γ, γ ∈ p ∧ β * α = 1 + γ := by
    obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p α)⁻¹
    refine ⟨β, β * α - 1, ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one,
        map_mul, hβ, inv_mul_cancel₀, sub_self]
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [add_sub_cancel]
  have := Ideal.mul_mem_left _ (algebraMap _ _ β) hαx
  rw [← Algebra.smul_def, smul_smul, hβ, add_smul, one_smul] at this
  refine (Submodule.add_mem_iff_left pS ?_).mp this
  rw [Algebra.smul_def]
  apply Ideal.mul_mem_right
  exact Ideal.mem_map_of_mem _ hγ

@[deprecated (since := "2025-07-31")] alias
  _root_.comap_map_eq_map_of_isLocalization_algebraMapSubmonoid := comap_map_eq_map

variable [IsScalarTower R Rₚ Sₚ]

variable (S Sₚ) in
/--
The isomorphism `S ⧸ pS ≃+* Sₚ ⧸ p·Sₚ`, where `Sₚ` is the localization of `S` at the (image) of
the complement of `p`
-/
noncomputable def equivQuotientMapMaximalIdeal [p.IsMaximal] :
    S ⧸ pS ≃+* Sₚ ⧸ pSₚ := by
  haveI h : pSₚ = Ideal.map (algebraMap S Sₚ) pS := by
    rw [← map_eq_maximalIdeal p, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S (Sₚ ⧸ pSₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq S Sₚ, Ideal.Quotient.algebraMap_eq, ← RingHom.comap_ker,
      Ideal.mk_ker, h, Ideal.map_map, ← IsScalarTower.algebraMap_eq, comap_map_eq_map]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq
      (Algebra.algebraMapSubmonoid S p.primeCompl) x
    obtain ⟨α, hα : α ∉ p, e⟩ := s.prop
    obtain ⟨β, γ, hγ, hβ⟩ : ∃ β γ, γ ∈ p ∧ α * β = 1 + γ := by
      obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p α)⁻¹
      refine ⟨β, α * β - 1, ?_, ?_⟩
      · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one,
          map_mul, hβ, mul_inv_cancel₀, sub_self]
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      · rw [add_sub_cancel]
    use β • x
    rw [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ pSₚ), Ideal.Quotient.algebraMap_eq,
      RingHom.comp_apply, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    rw [h, IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
    refine ⟨⟨⟨γ • x, ?_⟩, s⟩, ?_⟩
    · rw [Algebra.smul_def]
      apply Ideal.mul_mem_right
      exact Ideal.mem_map_of_mem _ hγ
    simp only
    rw [mul_comm, mul_sub, IsLocalization.mul_mk'_eq_mk'_of_mul,
      IsLocalization.mk'_mul_cancel_left, ← map_mul, ← e, ← Algebra.smul_def, smul_smul,
      hβ, ← map_sub, add_smul, one_smul, add_comm x, add_sub_cancel_right]

@[deprecated (since := "2025-07-31")] alias
    _root_.quotMapEquivQuotMapMaximalIdealOfIsLocalization := equivQuotientMapMaximalIdeal

end isomorphisms

end IsLocalization.AtPrime
