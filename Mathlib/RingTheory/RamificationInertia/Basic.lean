/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Ramification index and inertia degree

This file proves that the sum of ramification times inertia equals the degree of the extension.

Typically this is only stated for extensions of Dedekind domains, but we prove it for any finite
flat extension of an integral domain.

## Main results

* `Ideal.sum_ramification_inerta_eq_finrank`: Let `R` be an integral domain, let `S` be a finite
  flat `R`-algebra, and let `p` be a prime ideal of `R`. Then the sum over all prime ideals `q` of
  `S` lying over `p` of ramification index of `q` times the inertia degree of `q` equals the rank
  of `S` as an `R`-module.
* `Ideal.sum_ramification_inerta_eq_card`: Let `S/R` be a finite flat extension of integral domains,
  and let `p` be prime ideal of `R`. Assume that `R` is the invariant subring of a finite group `G`
  acting on `S`. Then the sum over all prime ideals `q` of `S` lying over `p` of ramification index
  of `q` times the inertia degree of `q` equals the cardinality of `G`.

-/

@[expose] public section

section

namespace Ideal

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (S : Type*) [CommRing S] [Algebra R S]

open Algebra.TensorProduct

variable {S} in
/-- The localization of the fiber `p.Fiber S` is isomorphic to a quotient of a localization. -/
noncomputable def Fiber.localizationAlgEquivQuotient (q : Ideal (p.Fiber S)) [q.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime (q.comap includeRight))]
    [Localization.AtPrime.IsLiesOverAlgebra p (q.comap includeRight)] :
    letI r := q.comap includeRight
    letI Sr := Localization.AtPrime r
    Localization.AtPrime q ≃ₐ[Localization.AtPrime p] Sr ⧸ p.map (algebraMap R Sr) :=
  letI : Algebra S (p.Fiber S) := rightAlgebra
  letI Rp := Localization.AtPrime p
  letI Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  letI pS := p.map (algebraMap R S)
  letI SpS := S ⧸ pS
  letI r := q.comap includeRight
  letI Sr := Localization.AtPrime r
  -- `p.Fiber S` is isomorphic to the quotient `Sₚ ⧸ pSₚ`.
  letI e₁ : p.Fiber S ≃ₐ[S] Sp ⧸ pS.map (algebraMap S Sp) :=
    (Fiber.algEquivQuotient p).trans <| quotientEquivAlgOfEq S <| by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, map_map, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq R S Sp, ← map_map]
  -- `q'` is the prime ideal of `Sₚ ⧸ pSₚ` corresponding to `q`.
  letI q' : Ideal (Sp ⧸ pS.map (algebraMap S Sp)) := q.comap e₁.symm
  -- `q` and `q'` have isomorphic localizations.
  letI e₂ : Localization.AtPrime q ≃ₐ[R] Localization.AtPrime q' :=
    (Localization.localAlgEquiv q' q e₁.symm rfl).symm.restrictScalars R
  haveI : (q'.under SpS).LiesOver r := under_liesOver_of_liesOver SpS q' (q.under S)
  haveI : Algebra.algebraMapSubmonoid SpS r.primeCompl = (q'.under SpS).primeCompl :=
    algebraMapSubmonoid_primeCompl_of_liesOver_surjective (q'.under SpS) r Quotient.mk_surjective
  haveI : IsLocalization (Algebra.algebraMapSubmonoid SpS r.primeCompl)
      (Localization.AtPrime q') := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid SpS (Algebra.algebraMapSubmonoid S p.primeCompl))
        (Localization.AtPrime q') q'
  haveI := IsScalarTower.to₁₃₄ R S SpS (Localization.AtPrime q')
  haveI := IsScalarTower.to₁₃₄ R S SpS (Sr ⧸ pS.map (algebraMap S Sr))
  -- Localization commutes with quotients, so the localization at `q'` is isomorphic to a quotient.
  letI e₃ : Localization.AtPrime q' ≃ₐ[R] Sr ⧸ pS.map (algebraMap S Sr) :=
    (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid SpS r.primeCompl)
      (Localization.AtPrime q') (Sr ⧸ pS.map (algebraMap S Sr))).restrictScalars R
  -- These isomorphisms over `R` lift to `Rp` by the universal property of localization.
  letI e₄ : Localization.AtPrime q ≃ₐ[Rp] Sr ⧸ pS.map (algebraMap S Sr) :=
  { __ := e₂.trans e₃
    commutes' := by
      let f := (e₂.trans e₃).toAlgHom.comp (IsScalarTower.toAlgHom R Rp (Localization.AtPrime q))
      let g := IsScalarTower.toAlgHom R Rp (Sr ⧸ pS.map (algebraMap S Sr))
      have : f.toRingHom.comp (algebraMap R Rp) = g.toRingHom.comp (algebraMap R Rp) := by simp
      suffices f = g by rwa [DFunLike.ext_iff] at this
      apply Localization.algHom_ext
      rwa [DFunLike.ext_iff] at this ⊢ }
  e₄.trans <| quotientEquivAlgOfEq Rp (map_map _ _)

variable {S} in
theorem foo3 (q : Ideal (p.Fiber S)) [q.IsPrime]
    [Algebra (Localization.AtPrime p)
      (Localization.AtPrime (q.comap Algebra.TensorProduct.includeRight))]
    [Localization.AtPrime.IsLiesOverAlgebra p (q.comap Algebra.TensorProduct.includeRight)] :
    letI r := q.comap Algebra.TensorProduct.includeRight
    letI Sr := Localization.AtPrime r
    Module.length (Localization.AtPrime p) (Localization.AtPrime q) =
      Module.length (Localization.AtPrime p) (Sr ⧸ p.map (algebraMap R Sr)) := by
  apply LinearEquiv.length_eq
  exact (Ideal.Fiber.localizationAlgEquivQuotient p q).toLinearEquiv

theorem sum_ramification_inertia_eq_finrank_fiber
    [Algebra.QuasiFinite R S] [Module.Flat R S] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.1.ramificationIdx' R * q.1.inertiaDeg' R =
      Module.finrank p.ResidueField (p.Fiber S) := by
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum,
    ← (PrimeSpectrum.primesOverOrderIsoFiber R S p).symm.sum_comp]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  let r := q.1.comap Algebra.TensorProduct.includeRight
  let Sr := Localization.AtPrime r
  let A := Sr ⧸ p.map (algebraMap R Sr)
  let := Localization.AtPrime.algebraOfLiesOver p r
  transitivity (Module.length (Localization.AtPrime p) A).toNat
  · rw [IsLocalRing.length_restrictScalars (Localization.AtPrime p) (Localization.AtPrime r) A,
      ENat.toNat_mul, Module.length_eq_finrank, ramificationIdx'_eq p, ← inertiaDeg'_eq p r]
    rfl
  · rw [← foo3,
      Module.length_eq_of_surjective (IsLocalRing.residue_surjective (R := Localization.AtPrime p)),
      Module.length_eq_finrank, ENat.toNat_coe]

/-- Let `R` be an integral domain, let `S` be a finite flat `R`-algebra, and let `p` be a prime
ideal of `R`. Then the sum over all prime ideals `q` of `S` lying over `p` of ramification index
of `q` times the inertia degree of `q` equals the rank of `S` as an `R`-module. -/
theorem sum_ramification_inerta_eq_finrank
    [IsDomain R] [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.1.ramificationIdx' R * q.1.inertiaDeg' R = Module.finrank R S := by
  rw [sum_ramification_inertia_eq_finrank_fiber, finrank_fiber_eq_finrank]

/-- Let `S/R` be a finite flat extension of integral domains, and let `p` be prime ideal of `R`.
Assume that `R` is the invariant subring of a finite group `G` acting on `S`. Then the sum over
all prime ideals `q` of `S` lying over `p` of ramification index of `q` times the inertia degree
of `q` equals the cardinality of `G`. -/
theorem sum_ramification_inertia_eq_card
    [IsDomain R] [IsDomain S] [Module.Flat R S] [Module.Finite R S] [Fintype (p.primesOver S)]
    {G : Type*} [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] :
    ∑ q : p.primesOver S, q.1.ramificationIdx' R * q.1.inertiaDeg' R = Nat.card G := by
  have : Finite G := IsGaloisGroup.finite G R S
  let := FractionRing.liftAlgebra R (FractionRing S)
  let := IsFractionRing.mulSemiringAction G R S (FractionRing R) (FractionRing S)
  rw [sum_ramification_inerta_eq_finrank, (IsGaloisGroup.toFractionRing G R S).card_eq_finrank,
    Algebra.IsAlgebraic.finrank_of_isFractionRing R (FractionRing R) S (FractionRing S)]

end Ideal
