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

* `Ideal.sum_ramification_inertia_eq_finrank`: Let `R` be an integral domain, let `S` be a finite
  flat `R`-algebra, and let `p` be a prime ideal of `R`. Then the sum over all prime ideals `q` of
  `S` lying over `p` of the ramification index of `q` times the inertia degree of `q` equals the
  rank of `S` as an `R`-module.
* `Ideal.sum_ramification_inertia_eq_card`: Let `S/R` be a finite flat extension of domains,
  and let `p` be prime ideal of `R`. Assume that `R` is the invariant subring of a finite group `G`
  acting on `S`. Then the sum over all prime ideals `q` of `S` lying over `p` of the ramification
  index of `q` times the inertia degree of `q` equals the cardinality of `G`.

-/

@[expose] public section

section

namespace Ideal

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (S : Type*) [CommRing S] [Algebra R S]

open IsLocalRing Module OrderIso PrimeSpectrum in
theorem sum_ramification_inertia_eq_finrank_fiber
    [Algebra.QuasiFinite R S] [Flat R S] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.1.ramificationIdx' R * q.1.inertiaDeg' R =
      finrank p.ResidueField (p.Fiber S) := by
  let := Fintype.ofFinite (PrimeSpectrum (p.Fiber S))
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum, ← (primesOverOrderIsoFiber R S p).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [toEquiv_symm, coe_symm_toEquiv, coe_primesOverOrderIsoFiber_symm_apply]
  set r := q.1.comap Algebra.TensorProduct.includeRight
  let := Localization.AtPrime.algebraOfLiesOver p r
  rw [ramificationIdx'_eq p r, inertiaDeg'_eq p r]
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q.1
  let Sr := Localization.AtPrime r
  let κp := p.ResidueField
  let κr := r.ResidueField
  let A := Sr ⧸ p.map (algebraMap R Sr)
  suffices length Sr A * finrank κp κr = finrank κp Sq by simpa using congr_arg ENat.toNat this
  calc length Sr A * finrank κp κr = length Sr A * length κp κr := by rw [length_eq_finrank]
    _ = length Rp A := (length_restrictScalars Rp Sr A).symm
    _ = length Rp Sq := (Fiber.localizationAlgEquivQuotient p q.1).toLinearEquiv.length_eq.symm
    _ = length κp Sq := length_eq_of_surjective residue_surjective
    _ = finrank κp Sq := length_eq_finrank κp Sq

/-- Let `R` be an integral domain, let `S` be a finite flat `R`-algebra, and let `p` be a prime
ideal of `R`. Then the sum over all prime ideals `q` of `S` lying over `p` of the ramification
index of `q` times the inertia degree of `q` equals the rank of `S` as an `R`-module. -/
theorem sum_ramification_inertia_eq_finrank
    [IsDomain R] [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.1.ramificationIdx' R * q.1.inertiaDeg' R = Module.finrank R S := by
  rw [sum_ramification_inertia_eq_finrank_fiber, finrank_fiber_eq_finrank]

/-- Let `S/R` be a finite flat extension of integral domains, and let `p` be prime ideal of `R`.
Assume that `R` is the invariant subring of a finite group `G` acting on `S`. Then the sum over
all prime ideals `q` of `S` lying over `p` of the ramification index of `q` times the inertia
degree of `q` equals the cardinality of `G`. -/
theorem sum_ramification_inertia_eq_card
    [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)]
    {G : Type*} [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] :
    ∑ q : p.primesOver S, q.1.ramificationIdx' R * q.1.inertiaDeg' R = Nat.card G := by
  let := IsGaloisGroup.finite G R S
  rw [sum_ramification_inertia_eq_finrank, IsGaloisGroup.card_eq_finrank' G R S]

end Ideal
