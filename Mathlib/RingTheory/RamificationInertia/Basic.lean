/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Flat.TorsionFree
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
  · rw [← (Ideal.Fiber.localizationAlgEquivQuotient p q.1).toLinearEquiv.length_eq,
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
