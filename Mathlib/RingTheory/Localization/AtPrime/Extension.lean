/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.Localization.AtPrime.Basic


/-!
# Primes in an extension of localization at prime

Let `R ⊆ S` be an extension of rings and `p` be a prime ideal of `R`. Let `Rₚ` be the
localization of `R` at the complement of `p` and `Sₚ` the localization of `S` at the (image)
of the complement of `p`.

In this file, we study the relation between the (nonzero) prime ideals of `Sₚ` and the prime
ideals of `S` above `p`. In particular, we prove that (under suitable conditions) they are in
bijection.

# Main definitions and results

- `IsLocalization.AtPrime.mem_primesOver_of_isPrime`: The nonzero prime ideals of `Sₚ` are
  primes over the maximal ideal of `Rₚ`.

- `IsLocalization.AtPrime.primesOverEquivPrimesOver`: the bijection between the primes over
  `p` in `S` and the primes over the maximal ideal of `Rₚ` in `Sₚ`.

-/

namespace IsLocalization.AtPrime

open Algebra IsLocalRing Ideal Localization.AtPrime

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
  (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
  (Sₚ : Type*) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]
  [Algebra Rₚ Sₚ] (P : Ideal S) [hPp : P.LiesOver p]

include p in
theorem isPrime_map_of_liesOver [P.IsPrime] : (P.map (algebraMap S Sₚ)).IsPrime :=
  isPrime_of_isPrime_disjoint _ _ _ inferInstance (Ideal.disjoint_primeCompl_of_liesOver P p)

theorem map_eq_maximalIdeal : p.map (algebraMap R Rₚ) = maximalIdeal Rₚ := by
  convert congr_arg (Ideal.map (algebraMap R Rₚ)) (comap_maximalIdeal Rₚ p).symm
  rw [map_comap p.primeCompl]

/--
The nonzero prime ideals of `Sₚ` are prime ideals over the maximal ideal of `Rₚ`.
See `Localization.AtPrime.primesOverEquivPrimesOver` for the bijection between the prime ideals
of `Sₚ` over the maximal ideal of `Rₚ` and the primes ideals of `S` above `p`.
-/
theorem mem_primesOver_of_isPrime {Q : Ideal Sₚ} [Q.IsPrime] [Algebra.IsIntegral Rₚ Sₚ]
    [Ring.DimensionLEOne Sₚ] (hQ : Q ≠ ⊥) :
    Q ∈ (maximalIdeal Rₚ).primesOver Sₚ := by
  refine ⟨inferInstance, ?_⟩
  rw [liesOver_iff, ← eq_maximalIdeal]
  have : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ inferInstance
  exact IsMaximal.under Rₚ Q

variable [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]

include p in
theorem liesOver_map_of_liesOver [P.IsPrime] :
    (P.map (algebraMap S Sₚ)).LiesOver (IsLocalRing.maximalIdeal Rₚ) := by
  rw [liesOver_iff, eq_comm, ← map_eq_maximalIdeal p]
  exact under_map_eq_map P p ((liesOver_iff P p).mp hPp)
    (map_eq_maximalIdeal p Rₚ ▸ maximalIdeal.isMaximal Rₚ) (isPrime_map_of_liesOver p Sₚ _).ne_top

theorem exists_primesOver_map_eq_of_primesOver (Q : (maximalIdeal Rₚ).primesOver Sₚ) :
    ∃ q : p.primesOver S, q.val.map (algebraMap S Sₚ) = Q := by
  refine ⟨⟨comap (algebraMap S Sₚ) Q, ⟨IsPrime.under _ _, ?_⟩⟩, ?_⟩
  · have : Q.1.LiesOver p := by
      have : (maximalIdeal Rₚ).LiesOver p := (liesOver_iff _ _).mpr (comap_maximalIdeal _ _).symm
      exact LiesOver.trans Q.1 (IsLocalRing.maximalIdeal Rₚ) p
    exact comap_liesOver Q.1 p <| IsScalarTower.toAlgHom R S Sₚ
  · refine le_antisymm  map_comap_le fun x hx ↦ ?_
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := mk'_surjective (algebraMapSubmonoid S p.primeCompl) x
    refine (mk'_mem_map_algebraMap_iff _ _ _ _ _).mpr ⟨s, hs, ?_⟩
    exact Ideal.mul_mem_left _ _ <| mk'_mem_iff.mp hx

variable [IsDedekindDomain S] [NoZeroSMulDivisors R S] [NeZero p]

/--
The bijection between the primes over `p` in `S` and the primes over the maximal ideal of `Rₚ` in
`Sₚ`.
-/
noncomputable def primesOverEquivPrimesOver : p.primesOver S ≃ (maximalIdeal Rₚ).primesOver Sₚ :=
  Equiv.ofBijective (fun Q ↦ ⟨Q.1.map (algebraMap S Sₚ), isPrime_map_of_liesOver p Sₚ Q.1,
    liesOver_map_of_liesOver p Rₚ Sₚ Q.1⟩)
    ⟨fun P₁ P₂ h ↦ by
      have : P₁.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
        (ne_bot_of_mem_primesOver (NeZero.ne _) P₁.prop) (primesOver.isPrime p P₁)
      have : P₂.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
        (ne_bot_of_mem_primesOver (NeZero.ne _) P₂.prop) (primesOver.isPrime p P₂)
      have : (Ideal.map (algebraMap S Sₚ) P₁).IsPrime := isPrime_map_of_liesOver p Sₚ P₁.1
      have : (Ideal.map (algebraMap S Sₚ) P₂).IsPrime := isPrime_map_of_liesOver p Sₚ P₂.1
      simpa [comap_map_eq_self_of_isMaximal _ IsPrime.ne_top', SetCoe.ext_iff]
        using congr_arg (comap (algebraMap S Sₚ) ·) <| Subtype.mk_eq_mk.mp h,
    fun Q ↦ by simpa [Subtype.ext_iff_val] using exists_primesOver_map_eq_of_primesOver p Rₚ Sₚ Q⟩

@[simp]
theorem primesOverEquivPrimesOver_apply (P : p.primesOver S) :
    primesOverEquivPrimesOver p Rₚ Sₚ P = Ideal.map (algebraMap S Sₚ) P := rfl

end IsLocalization.AtPrime

section sanity_check

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] (p : Ideal R) [p.IsPrime]
variable (P : Ideal S) [hPp : P.LiesOver p] [NoZeroSMulDivisors R S]

open Ideal Algebra IsLocalRing IsLocalization AtPrime

local notation3 "Rₚ" => Localization.AtPrime p
local notation3 "Sₚ" => Localization  (algebraMapSubmonoid S p.primeCompl)

-- mem_primesOver_of_isPrime
example {Q : Ideal Sₚ} [Algebra.IsIntegral R S] [Q.IsPrime] (hQ : Q ≠ ⊥) :
    Q ∈ (maximalIdeal Rₚ).primesOver Sₚ := mem_primesOver_of_isPrime Rₚ Sₚ hQ

-- exists_primesOver_map_eq_of_primesOver
example (Q : (maximalIdeal Rₚ).primesOver Sₚ) :
    ∃ q : p.primesOver S, q.val.map (algebraMap S Sₚ) = Q :=
  exists_primesOver_map_eq_of_primesOver p Rₚ Sₚ Q

-- primesOverEquivPrimesOver
noncomputable example [NeZero p] : p.primesOver S ≃ (maximalIdeal Rₚ).primesOver Sₚ :=
  primesOverEquivPrimesOver p _ _

end sanity_check
