/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

/-!
# Localization of a UFD

## Main results
* `localization_ufd` : The localization of a UFD is still a UFD.
-/

public section

variable {R : Type*} [CommRing R] [UniqueFactorizationMonoid R] [IsDomain R]

/-- If `S` is the localization of a UFD `R`, then `S` is also a UFD. -/
theorem isLocalization_ufd {M : Submonoid R} (hM : M ≤ nonZeroDivisors R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization M S] : UniqueFactorizationMonoid S := by
  have : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  rw [UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime]
  intro p hpb _
  obtain ⟨x, hxp, hpx⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot
    inferInstance (IsLocalization.bot_lt_comap_prime M S hM p hpb).ne'
  use algebraMap R S x, hxp
  refine Ideal.span_singleton_prime
    ((map_ne_zero_iff (algebraMap R S) (IsLocalization.injective S hM)).mpr hpx.ne_zero) |>.mp ?_
  rw [← Set.image_singleton, ← Ideal.map_span]
  exact IsLocalization.isPrime_of_isPrime_disjoint M S _ (Ideal.span_singleton_isPrime_of_prime hpx)
    <| (IsLocalization.map_algebraMap_ne_top_iff_disjoint M S (Ideal.span {x})).mp fun h ↦
      Ideal.IsPrime.ne_top' (top_unique (h.symm.trans_le (by simpa [Ideal.map_span] using hxp)))

/-- The localization of a UFD is still a UFD. -/
theorem localization_ufd {M : Submonoid R} (hM : M ≤ nonZeroDivisors R) :
    UniqueFactorizationMonoid (Localization M) :=
  isLocalization_ufd hM (Localization M)
