/-
Copyright (c) 2024 Uni Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uni Marx
-/
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Nilpotent
import Mathlib.RingTheory.Ideal.MinimalPrime

/-!
# Localization at minimal prime ideals
## Main results
- `AtMinimalPrime.prime_unique`: When localizing at a minimal prime ideal `I`, the resulting
  ring only has a single prime ideal.
## Tags
localization, prime, minimal, nilpotent
-/

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]

variable [Algebra R S]

section AtMinimalPrime
namespace Localization

open IsLocalization

attribute [local instance] Classical.propDecidable

variable {I : Ideal R} [hI : I.IsPrime] (hMin : I ∈ minimalPrimes R)

theorem AtMinimalPrime.prime_unique (J : Ideal (Localization I.primeCompl)) [hPrime : J.IsPrime] :
    J = LocalRing.maximalIdeal (Localization I.primeCompl) := by
  let i_sub : {p : Ideal (Localization I.primeCompl) // Ideal.IsPrime p} :=
    ⟨_, Ideal.IsMaximal.isPrime' <| LocalRing.maximalIdeal (Localization (Ideal.primeCompl I))⟩
  let j_sub : {p : Ideal (Localization I.primeCompl) // Ideal.IsPrime p} := ⟨_, hPrime⟩

  suffices h: j_sub ≤ i_sub → i_sub ≤ j_sub by
    apply le_antisymm (LocalRing.le_maximalIdeal hPrime.ne_top)
    rw [← Subtype.mk_le_mk]
    apply h
    exact LocalRing.le_maximalIdeal hPrime.ne_top

  rw [← (IsLocalization.orderIsoOfPrime I.primeCompl (Localization I.primeCompl)).le_iff_le,
     ← (IsLocalization.orderIsoOfPrime I.primeCompl (Localization I.primeCompl)).le_iff_le]
  unfold orderIsoOfPrime at *
  simp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk, Subtype.mk_le_mk,
             Localization.AtPrime.comap_maximalIdeal] at *
  exact hMin.2 ⟨Ideal.comap_isPrime (algebraMap R (Localization (Ideal.primeCompl I))) J, bot_le⟩

theorem AtMinimalPrime.nilpotent_iff_mem_maximal {x : _} :
    IsNilpotent x ↔ x ∈ LocalRing.maximalIdeal (Localization I.primeCompl) := by
  rw [nilpotent_iff_mem_prime]
  constructor
  · exact fun h => h (LocalRing.maximalIdeal _) (Ideal.IsMaximal.isPrime' _)
  · intro h J hJ
    rw [prime_unique hMin J]
    exact h

theorem AtMinimalPrime.nilpotent_iff_not_unit {x : Localization I.primeCompl} :
    IsNilpotent x ↔ x ∈ nonunits _ := by
  rw [← LocalRing.mem_maximalIdeal]
  exact AtMinimalPrime.nilpotent_iff_mem_maximal hMin

end Localization
end AtMinimalPrime
