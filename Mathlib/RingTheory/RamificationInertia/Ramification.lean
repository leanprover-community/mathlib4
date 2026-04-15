/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Ramification index

Given a prime ideal `q` of an `R`-algebra `S`, the ramification index of `q` over `R` is defined
to be the length of the quotient `Sq/pSq` as an `Sq`-module where `Sq` is the localization of `S` at
`q`, `p` is the preimage of `q` in `R`, and `pSq` is the image of `p` in `Sq`.
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

open IsDiscreteValuationRing IsLocalRing Submodule.IsPrincipal in
noncomputable def foo''' (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Ideal R ≃o ENatᵒᵈ where
  toFun I := .toDual (addVal R (generator I))
  invFun n := n.ofDual.recTopCoe ⊥ (fun n ↦ maximalIdeal R ^ n)
  left_inv I := by
    let x := generator I
    suffices (addVal R x).recTopCoe ⊥ (fun n ↦ maximalIdeal R ^ n) = span {x} by
      rwa [span_singleton_generator] at this
    by_cases hx0 : x = 0
    · simp [hx0]
    · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
      rw [hu, IsDiscreteValuationRing.addVal_def' u hϖ, span_singleton_mul_left_unit u.isUnit,
        ENat.recTopCoe_coe, Irreducible.maximalIdeal_eq hϖ, span_singleton_pow]
  right_inv n := by
    let k := n.ofDual
    change addVal R (generator (k.recTopCoe ⊥ fun n ↦ maximalIdeal R ^ n)) = k
    induction k
    case top =>
      simp [(eq_bot_iff_generator_eq_zero _).mp rfl] -- `generator_bot` simp lemma
    case coe k =>
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
      rw [ENat.recTopCoe_coe, Irreducible.maximalIdeal_eq hϖ, span_singleton_pow,
        ← hϖ.addVal_pow k, IsDiscreteValuationRing.addVal_eq_iff_associated]
      exact associated_generator_span_self (ϖ ^ k)
  map_rel_iff' {I J} := by
    simp [IsDiscreteValuationRing.addVal_le_iff_dvd, ← span_singleton_le_span_singleton]

theorem foo {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (n : ℕ) :
    Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ n) = n := by
  rw [Module.length_quotient]
  refine (Order.coheight_orderIso (foo''' R).symm (.toDual n)).trans ?_
  rw [Order.coheight_toDual, Order.height_enat]

theorem ramificationIdx_eq_ramificationIdx' [IsDedekindDomain R] [IsDedekindDomain S]
    [Module.IsTorsionFree R S]
    [q.LiesOver p] [hq' : q.IsPrime] (hp : p ≠ ⊥) (hq : q ≠ ⊥) :
    p.ramificationIdx q = q.ramificationIdx' R := by
  have : p.IsPrime := isPrime_of_liesOver q p
  let pS := p.map (algebraMap R S)
  have hpS : pS ≠ ⊥ := map_ne_bot_of_ne_bot hp
  have : q.IsMaximal := hq'.isMaximal hq
  obtain ⟨I, hqI, h⟩ := Ideal.eq_prime_pow_mul_coprime hpS q
  let Sq := Localization.AtPrime q
  replace hqI : ¬ I ≤ q := by
    contrapose! hqI
    rw [sup_of_le_left hqI]
    exact hq'.ne_top
  replace hqI := IsLocalization.AtPrime.map_eq_top_of_not_le Sq hqI
  rw [← IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hpS hq' hq] at h
  replace h := congrArg (map (algebraMap S Sq)) h
  rw [map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_mul, Ideal.map_pow, hqI, mul_top,
    Localization.AtPrime.map_eq_maximalIdeal] at h
  rw [ramificationIdx'_eq p q, h]
  have : IsDiscreteValuationRing Sq :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hq Sq
  rw [foo, ENat.toNat_coe]

end

end Ideal
