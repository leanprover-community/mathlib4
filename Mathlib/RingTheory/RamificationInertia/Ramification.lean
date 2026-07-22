/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Ramification index

Let `S/R` be an extension of rings, and let `q` be a prime ideal of `S` lying over a prime ideal
`p` of `R`. Let `Sq` be the localization of `S` and `q`, and let `pSq` be the image of `p` in `Sq`.
Then the ramification index of `q` over `R` is defined to be the length of the quotient `Sq/pSq` as
an `Sq`-module.

## Main definitions

* `Ideal.ramificationIdx q R`: The ramification index of `q` over `R`.

## Main statements

* `ramificationIdx'_eq_ramificationIdx`: The ramification index agrees with the usual definition in
  the case of Dedekind domains.
* `ramificationIdx_tower`: Ramification index is multiplicative in towers.

-/

@[expose] public section

namespace Ideal

section

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

open Classical in
/-- Let `S/R` be an extension of rings, and let `q` be a prime ideal of `S` lying over a prime ideal
`p` of `R`. Let `Sq` be the localization of `S` and `q`, and let `pSq` be the image of `p` in `Sq`.
Then the ramification index of `q` over `R` is defined to be the length of the quotient `Sq/pSq` as
an `Sq`-module.

When `q` is not prime, we use a junk value of `0`.

This will eventually replace the existing definition of `Ideal.ramificationIdx'`. -/
noncomputable def ramificationIdx : ℕ :=
  if _ : q.IsPrime then
    letI Sq := Localization.AtPrime q
    (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat
  else 0

theorem ramificationIdx_def [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx R = (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat :=
  dif_pos _

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_def := ramificationIdx_def

theorem ramificationIdx_of_not_isPrime (hq : ¬ q.IsPrime) : q.ramificationIdx R = 0 :=
  dif_neg hq

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_of_not_isPrime :=
  ramificationIdx_of_not_isPrime

theorem ramificationIdx_pos [q.IsPrime] [Module.Finite R S] : 0 < q.ramificationIdx R := by
  let p := q.under R
  let Sq := Localization.AtPrime q
  rw [ramificationIdx_def]
  apply ENat.toNat_pos
  · rw [← pos_iff_ne_zero, Module.length_pos_iff, Submodule.Quotient.nontrivial_iff,
      IsScalarTower.algebraMap_eq R S, ← map_map, ← lt_top_iff_ne_top]
    grw [map_mono map_comap_le, Localization.AtPrime.map_eq_maximalIdeal]
    exact (IsLocalRing.maximalIdeal.isMaximal _).lt_top
  · let r := PrimeSpectrum.primesOverOrderIsoFiber R S p (primesOver.mk p q)
    have : q = r.1.comap Algebra.TensorProduct.includeRight := by
      rw [← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply, OrderIso.symm_apply_apply]
    let := Localization.AtPrime.algebraOfLiesOver p (r.1.comap Algebra.TensorProduct.includeRight)
    have : IsArtinianRing (Sq ⧸ map (algebraMap R Sq) p) := by
      convert (Fiber.localizationAlgEquivQuotient p r.1).toRingEquiv.isArtinianRing
    rwa [Module.length_eq_of_surjective (R := Sq ⧸ p.map (algebraMap R Sq)) Quotient.mk_surjective,
      Module.length_ne_top_iff, ← isArtinianRing_iff_isFiniteLength]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_pos := ramificationIdx_pos

theorem ramificationIdx_eq_one [q.IsPrime] [Algebra.EssFiniteType R S]
    [Algebra.IsUnramifiedAt R q] : q.ramificationIdx R = 1 := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  rw [ramificationIdx_def, ENat.toNat_eq_iff_eq_coe, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff,
    IsScalarTower.algebraMap_eq R Rp Sq, ← map_map, Localization.AtPrime.map_eq_maximalIdeal]
  exact Algebra.FormallyUnramified.map_maximalIdeal

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq_one := ramificationIdx_eq_one

variable {q R} in
theorem ramificationIdx_eq_one_iff [q.IsPrime] [Algebra.EssFiniteType R S]
    [Algebra.IsIntegral R S] [PerfectField (q.under R).ResidueField] :
    q.ramificationIdx R = 1 ↔ Algebra.IsUnramifiedAt R q := by
  refine ⟨fun h ↦ ?_, fun _ ↦ ramificationIdx_eq_one q R⟩
  rw [ramificationIdx_def, ENat.toNat_eq_iff_eq_coe, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff] at h
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have := Algebra.EssFiniteType.of_comp R Rp Sq
  suffices Algebra.FormallyUnramified Rp Sq from Algebra.FormallyUnramified.comp R Rp Sq
  rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq,
    ← Localization.AtPrime.map_eq_maximalIdeal, map_map, ← IsScalarTower.algebraMap_eq]
  exact ⟨Algebra.IsAlgebraic.isSeparable_of_perfectField, h⟩

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq_one_iff :=
  ramificationIdx_eq_one_iff

end

section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (p : Ideal R) (q : Ideal S) (r : Ideal T)

theorem ramificationIdx_eq [q.LiesOver p] [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx R = (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat := by
  rw [ramificationIdx_def, over_def q p]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq := ramificationIdx_eq

open Localization IsLocalization.AtPrime in
theorem ramificationIdx'_eq_ramificationIdx' [IsDedekindDomain S]
    [q.LiesOver p] [hq : q.IsPrime] (hpS : p.map (algebraMap R S) ≠ ⊥) :
    p.ramificationIdx' q = q.ramificationIdx R := by
  have hq' : q ≠ ⊥ := ne_bot_of_le_ne_bot hpS (map_le_of_le_comap (q.over_def p).le)
  have : q.IsMaximal := hq.isMaximal hq'
  obtain ⟨I, hqI, h⟩ := Ideal.eq_prime_pow_mul_coprime hpS q
  replace hqI : ¬ I ≤ q := by
    contrapose! hqI
    rw [sup_of_le_left hqI]
    exact hq.ne_top
  rw [← IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hpS hq hq'] at h
  apply_fun (map (algebraMap S (Localization.AtPrime q))) at h
  rw [map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_mul, Ideal.map_pow,
    map_eq_top_of_not_le (Localization.AtPrime q) hqI, mul_top, AtPrime.map_eq_maximalIdeal] at h
  have hSq := isDiscreteValuationRing_of_dedekind_domain S hq' (Localization.AtPrime q)
  rw [ramificationIdx_eq p q, h, hSq.length_quotient_pow_maximalIdeal, ENat.toNat_coe]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_ramificationIdx'' :=
  ramificationIdx'_eq_ramificationIdx'

theorem ramificationIdx'_eq_ramificationIdx [IsDomain R] [IsDedekindDomain S]
    [Module.IsTorsionFree R S] [q.LiesOver p] [hq : q.IsPrime] (hp : p ≠ ⊥) :
    p.ramificationIdx' q = q.ramificationIdx R := by
  have hpS : p.map (algebraMap R S) ≠ ⊥ := map_ne_bot_of_ne_bot hp
  exact ramificationIdx'_eq_ramificationIdx' p q hpS

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_ramificationIdx' :=
  ramificationIdx'_eq_ramificationIdx

namespace IsDedekindDomain

open UniqueFactorizationMonoid

theorem ramificationIdx_eq_factors_count [IsDedekindDomain S]
    [q.LiesOver p] (hp0 : p.map (algebraMap R S) ≠ ⊥) :
    q.ramificationIdx R = (factors (p.map (algebraMap R S))).count q := by
  by_cases hq : q.IsPrime; swap
  · rw [ramificationIdx_of_not_isPrime q R hq, eq_comm, Multiset.count_eq_zero]
    contrapose! hq
    exact isPrime_of_prime (prime_of_factor q hq)
  have hq0 : q ≠ ⊥ := ne_bot_of_le_ne_bot hp0 (map_le_of_le_comap (q.over_def p).le)
  rw [← ramificationIdx'_eq_ramificationIdx' p q hp0, ramificationIdx'_eq_factors_count hp0 ‹_› hq0]

open UniqueFactorizationMonoid in
theorem ramificationIdx_eq_normalizedFactors_count [IsDedekindDomain S]
    [q.LiesOver p] (hp0 : p.map (algebraMap R S) ≠ ⊥) :
    q.ramificationIdx R = (normalizedFactors (p.map (algebraMap R S))).count q := by
  rw [← factors_eq_normalizedFactors, ← ramificationIdx_eq_factors_count p q hp0]

open UniqueFactorizationMonoid in
theorem ramificationIdx_eq_multiplicity [IsDedekindDomain S]
    [q.IsPrime] [q.LiesOver p] (hp : p.map (algebraMap R S) ≠ ⊥) :
    q.ramificationIdx R = multiplicity q (p.map (algebraMap R S)) := by
  have hq : q ≠ ⊥ := ne_bot_of_le_ne_bot hp (map_le_of_le_comap (q.over_def p).le)
  rw [ramificationIdx_eq_normalizedFactors_count p q hp,
    multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_eq_count_normalizedFactors
      (prime_of_isPrime hq inferInstance).irreducible hp), normalize_eq]

end IsDedekindDomain

/-- See `ramificationIdx_tower` for a version that does not assume primality. -/
theorem ramificationIdx_tower' [q.IsPrime] [r.IsPrime] [r.LiesOver q]
    [Algebra (Localization.AtPrime q) (Localization.AtPrime r)]
    [Localization.AtPrime.IsLiesOverAlgebra q r]
    [Module.Flat (Localization.AtPrime q) (Localization.AtPrime r)] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S := by
  have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
  let f := (Ideal.quotientEquivAlgOfEq (Localization.AtPrime r)
    (by rw [map_map, ← IsScalarTower.algebraMap_eq])).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime r)
        ((r.under R).map (algebraMap R (Localization.AtPrime q))))
  rw [ramificationIdx_def, ramificationIdx_eq (r.under R), ramificationIdx_eq q,
    f.toLinearEquiv.length_eq, IsLocalRing.length_baseChange, ENat.toNat_mul,
    ← Localization.AtPrime.map_eq_maximalIdeal, map_map, ← IsScalarTower.algebraMap_eq]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_tower' := ramificationIdx_tower'

/-- See `ramificationIdx_tower'` for a version that only assumes local flatness. -/
theorem ramificationIdx_tower [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := isPrime_of_liesOver r q
    let := Localization.AtPrime.algebraOfLiesOver q r
    apply ramificationIdx_tower'
  · rw [ramificationIdx_of_not_isPrime r R hr, ramificationIdx_of_not_isPrime r S hr, mul_zero]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_tower := ramificationIdx_tower

theorem ramificationIdx_below_dvd [r.LiesOver q] [Module.Flat S T] :
    q.ramificationIdx R ∣ r.ramificationIdx R := by
  use r.ramificationIdx S
  rw [← ramificationIdx_tower]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_below_dvd := ramificationIdx_below_dvd

theorem ramificationIdx_above_dvd [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx S ∣ r.ramificationIdx R := by
  use q.ramificationIdx R
  rw [mul_comm, ← ramificationIdx_tower]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_above_dvd := ramificationIdx_above_dvd

theorem ramificationIdx_below_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] [Module.Flat S T] :
    q.ramificationIdx R ≤ r.ramificationIdx R :=
  Nat.le_of_dvd (r.ramificationIdx_pos R) (q.ramificationIdx_below_dvd r)

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_below_le :=
  ramificationIdx_below_le

theorem ramificationIdx_above_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] [Module.Flat S T] :
    r.ramificationIdx S ≤ r.ramificationIdx R :=
  Nat.le_of_dvd (r.ramificationIdx_pos R) (q.ramificationIdx_above_dvd r)

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_above_le := ramificationIdx_above_le

variable (R) in
open Pointwise in
@[simp]
theorem ramificationIdx_smul {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (g : G) : (g • q).ramificationIdx R = q.ramificationIdx R := by
  by_cases hq : q.IsPrime; swap
  · rw [ramificationIdx_of_not_isPrime, ramificationIdx_of_not_isPrime] <;> simpa
  · let p := q.under R
    let f₀ := MulSemiringAction.toAlgAut G R S g
    have hg : g • q = q.map f₀ := q.pointwise_smul_def
    let Sq := Localization.AtPrime q
    let Sq' := Localization.AtPrime (q.map f₀)
    let f : Sq ≃ₐ[R] Sq' :=
      Localization.localAlgEquiv q (q.map f₀) f₀ (comap_map_of_bijective f₀ f₀.bijective).symm
    let : Algebra Sq Sq' := f.toRingHom.toAlgebra
    have : IsScalarTower R Sq Sq' := IsScalarTower.of_algHom f.toAlgHom
    let e : (Sq ⧸ p.map (algebraMap R Sq)) ≃ₐ[Sq] Sq' ⧸ p.map (algebraMap R Sq') :=
      Ideal.quotientEquivAlg _ _ (AlgEquiv.ofBijective (Algebra.ofId Sq Sq') f.bijective)
        (by rw [IsScalarTower.algebraMap_eq R Sq Sq', Ideal.map_map,
          ← AlgEquiv.toAlgHom_toRingHom, AlgEquiv.toAlgHom_ofBijective, Algebra.toRingHom_ofId])
    rw [hg, ramificationIdx_eq p q, ramificationIdx_eq p (q.map f₀),
      e.toLinearEquiv.length_eq, Module.length_eq_of_surjective f.surjective]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_smul := ramificationIdx_smul

end

end Ideal
