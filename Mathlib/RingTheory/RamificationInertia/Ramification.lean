/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Ramification index

Given a prime ideal `q` of an `R`-algebra `S`, the ramification index of `q` over `R` is defined
to be the length of the quotient `Sq/pSq` as an `Sq`-module where `Sq` is the localization of `S` at
`q`, `p` is the preimage of `q` in `R`, and `pSq` is the image of `p` in `Sq`.

## Main definitions=

* `Ideal.ramificationIdx' q R`: The ramification index of `q` over `R`.

## Main statements

* `ramificationIdx_eq_ramificationIdx'`: The ramification index agrees with the usual definition in
  the case of Dedekind domains.
* `ramificationIdx'_tower`: Ramification index is multiplicative in towers.

-/

@[expose] public section

namespace Ideal

section

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

open Classical in
/-- Given a prime ideal `q` of an `R`-algebra `S`, the ramification index of `q` over `R` is defined
to be the length of the quotient `Sq/pSq` as an `Sq`-module where `Sq` is the localization of `S` at
`q`, `p` is the preimage of `q` in `R`, and `pSq` is the image of `p` in `Sq`.

When `q` is not prime, we use a junk value of `0`.

This will eventually replace the existing definition of `Ideal.ramificationIdx`. -/
noncomputable def ramificationIdx' : ℕ :=
  if _ : q.IsPrime then
    letI Sq := Localization.AtPrime q
    (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat
  else 0

theorem ramificationIdx'_def [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx' R = (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat :=
  dif_pos _

theorem ramificationIdx'_of_not_isPrime (hq : ¬ q.IsPrime) : q.ramificationIdx' R = 0 :=
  dif_neg hq

end

section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (p : Ideal R) (q : Ideal S) (r : Ideal T)

theorem ramificationIdx'_eq [q.LiesOver p] [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx' R = (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat := by
  rw [ramificationIdx'_def, over_def q p]

open Localization IsLocalization.AtPrime in
theorem ramificationIdx_eq_ramificationIdx'
    [IsDomain R] [IsDedekindDomain S] [Module.IsTorsionFree R S]
    [q.LiesOver p] [hq : q.IsPrime] (hp : p ≠ ⊥) :
    p.ramificationIdx q = q.ramificationIdx' R := by
  have : p.IsPrime := isPrime_of_liesOver q p
  have hq' : q ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp q
  have : q.IsMaximal := hq.isMaximal hq'
  have hpS : p.map (algebraMap R S) ≠ ⊥ := map_ne_bot_of_ne_bot hp
  obtain ⟨I, hqI, h⟩ := Ideal.eq_prime_pow_mul_coprime hpS q
  replace hqI : ¬ I ≤ q := by
    contrapose! hqI
    rw [sup_of_le_left hqI]
    exact hq.ne_top
  rw [← IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hpS hq hq'] at h
  apply_fun (map (algebraMap S (Localization.AtPrime q))) at h
  rw [map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_mul, Ideal.map_pow,
    map_eq_top_of_not_le (Localization.AtPrime q) hqI, mul_top, AtPrime.map_eq_maximalIdeal] at h
  have hSq := isDiscreteValuationRing_of_dedekind_domain S hq' (Localization.AtPrime q)
  rw [ramificationIdx'_eq p q, h, hSq.length_quotient_pow_maximalIdeal, ENat.toNat_coe]

/-- See `ramificationIdx'_tower` for a version that does not assume primality. -/
theorem ramificationIdx'_tower' [q.IsPrime] [r.IsPrime] [r.LiesOver q]
    [Module.Flat (Localization.AtPrime q) (Localization.AtPrime r)] :
    r.ramificationIdx' R = q.ramificationIdx' R * r.ramificationIdx' S := by
  have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
  let f := (Ideal.quotientEquivAlgOfEq (Localization.AtPrime r)
    (by rw [map_map, ← IsScalarTower.algebraMap_eq])).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime r)
        ((r.under R).map (algebraMap R (Localization.AtPrime q))))
  rw [ramificationIdx'_def, ramificationIdx'_eq (r.under R), ramificationIdx'_eq q,
    f.toLinearEquiv.length_eq, IsLocalRing.length_baseChange, ENat.toNat_mul,
    ← Localization.AtPrime.map_eq_maximalIdeal, map_map, ← IsScalarTower.algebraMap_eq]

/-- See `ramificationIdx'_tower` for a version that only assumes local flatness. -/
theorem ramificationIdx'_tower [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx' R = q.ramificationIdx' R * r.ramificationIdx' S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := isPrime_of_liesOver r q
    apply ramificationIdx'_tower'
  · rw [ramificationIdx'_of_not_isPrime r R hr, ramificationIdx'_of_not_isPrime r S hr, mul_zero]

end

end Ideal
