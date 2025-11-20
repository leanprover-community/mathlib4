/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Primes in an extension of localization at prime

Let `R ⊆ S` be an extension of Dedekind domains and `p` be a prime ideal of `R`. Let `Rₚ` be the
localization of `R` at the complement of `p` and `Sₚ` the localization of `S` at the (image)
of the complement of `p`.

In this file, we study the relation between the (nonzero) prime ideals of `Sₚ` and the prime
ideals of `S` above `p`. In particular, we prove that (under suitable conditions) they are in
bijection.

## Main definitions and results

- `IsLocalization.AtPrime.mem_primesOver_of_isPrime`: The nonzero prime ideals of `Sₚ` are
  primes over the maximal ideal of `Rₚ`.

- `IsDedekindDomain.primesOverEquivPrimesOver`: the order-preserving bijection between the primes
  over `p` in `S` and the primes over the maximal ideal of `Rₚ` in `Sₚ`.

-/

@[expose] public section

open Algebra IsLocalRing Ideal Localization.AtPrime

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
  (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
  (Sₚ : Type*) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]
  [Algebra Rₚ Sₚ] (P : Ideal S) [hPp : P.LiesOver p]

namespace IsLocalization.AtPrime

/--
The nonzero prime ideals of `Sₚ` are prime ideals over the maximal ideal of `Rₚ`.
See `Localization.AtPrime.primesOverEquivPrimesOver` for the bijection between the prime ideals
of `Sₚ` over the maximal ideal of `Rₚ` and the primes ideals of `S` above `p`.
-/
theorem mem_primesOver_of_isPrime {Q : Ideal Sₚ} [Q.IsMaximal] [Algebra.IsIntegral Rₚ Sₚ] :
    Q ∈ (maximalIdeal Rₚ).primesOver Sₚ := by
  refine ⟨inferInstance, ?_⟩
  rw [liesOver_iff, ← eq_maximalIdeal]
  exact IsMaximal.under Rₚ Q

theorem liesOver_comap_of_liesOver {T : Type*} [CommRing T] [Algebra R T] [Algebra Rₚ T]
    [Algebra S T] [IsScalarTower R S T] [IsScalarTower R Rₚ T] (Q : Ideal T)
    [Q.LiesOver (maximalIdeal Rₚ)] : (comap (algebraMap S T) Q).LiesOver p := by
  have : Q.LiesOver p := by
    have : (maximalIdeal Rₚ).LiesOver p := liesOver_maximalIdeal Rₚ p _
    exact LiesOver.trans Q (IsLocalRing.maximalIdeal Rₚ) p
  exact comap_liesOver Q p <| IsScalarTower.toAlgHom R S T

variable [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]

include p in
theorem liesOver_map_of_liesOver [P.IsPrime] :
    (P.map (algebraMap S Sₚ)).LiesOver (IsLocalRing.maximalIdeal Rₚ) := by
  rw [liesOver_iff, eq_comm, ← map_eq_maximalIdeal p, over_def P p]
  exact under_map_eq_map_under _
    (over_def P p ▸ map_eq_maximalIdeal p Rₚ ▸ maximalIdeal.isMaximal Rₚ)
    (isPrime_map_of_liesOver S p Sₚ P).ne_top

end IsLocalization.AtPrime
namespace IsDedekindDomain

open IsLocalization AtPrime

variable [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] [IsDedekindDomain S]
  [NoZeroSMulDivisors R S]

/--
For `R ⊆ S` an extension of Dedekind domains and `p` a prime ideal of `R`, the bijection
between the primes of `S` over `p` and the primes over the maximal ideal of `Rₚ` in `Sₚ` where
`Rₚ` and `Sₚ` are resp. the localizations of `R` and `S` at the complement of `p`.
-/
noncomputable def primesOverEquivPrimesOver (hp : p ≠ ⊥) :
    p.primesOver S ≃o (maximalIdeal Rₚ).primesOver Sₚ where
  toFun P := ⟨map (algebraMap S Sₚ) P.1, isPrime_map_of_liesOver S p Sₚ P.1,
    liesOver_map_of_liesOver p Rₚ Sₚ P.1⟩
  map_rel_iff' {Q Q'} := by
    refine ⟨fun h ↦ ?_, fun h ↦ map_mono h⟩
    have : Q'.1.IsMaximal :=
      (primesOver.isPrime p Q').isMaximal (ne_bot_of_mem_primesOver hp Q'.prop)
    simpa [comap_map_of_isMaximal S p] using le_comap_of_map_le h
  invFun Q := ⟨comap (algebraMap S Sₚ) Q.1, IsPrime.under S Q.1,
    liesOver_comap_of_liesOver p Rₚ Q.1⟩
  left_inv P := by
    have : P.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
        (ne_bot_of_mem_primesOver hp P.prop) (primesOver.isPrime p P)
    exact SetCoe.ext <| IsLocalization.AtPrime.comap_map_of_isMaximal S p Sₚ P.1
  right_inv Q := SetCoe.ext <| map_comap (algebraMapSubmonoid S p.primeCompl) Sₚ Q

@[simp]
theorem primesOverEquivPrimesOver_apply (hp : p ≠ ⊥) (P : p.primesOver S) :
    primesOverEquivPrimesOver p Rₚ Sₚ hp P = Ideal.map (algebraMap S Sₚ) P := rfl

@[simp]
theorem primesOverEquivPrimesOver_symm_apply (hp : p ≠ ⊥) (Q : (maximalIdeal Rₚ).primesOver Sₚ) :
    ((primesOverEquivPrimesOver p Rₚ Sₚ hp).symm Q).1 = Ideal.comap (algebraMap S Sₚ) Q := rfl

end IsDedekindDomain
