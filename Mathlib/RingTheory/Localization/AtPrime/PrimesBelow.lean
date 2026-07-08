/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Height

/-!
# Extensions of primes to a localization at a prime

Primes `𝔮` contained in a prime `𝔭` correspond to primes of the localization at `𝔭`. This
file records the resulting API for the extension `𝔮 ↦ 𝔮.map (algebraMap R A)` where
`A` is a localization of `R` at `𝔭.primeCompl`:

- `IsLocalization.isPrime_map_of_le`: the extension of `𝔮 ≤ 𝔭` is prime;
- `IsLocalization.comap_map_of_le`: `𝔮` is recovered from its extension;
- `IsLocalization.height_map_of_le`: the extension has the same height as `𝔮`.

We also provide `IsLocalization.exists_mul_mem_of_algebraMap_mem_map`, a workhorse for
descending membership in extended ideals along a localization: if the image of `r` lies in the
extension of `I`, then `r * t ∈ I` for some `t` in the localizing submonoid.
-/

namespace IsLocalization

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- If the image of `r` in a localization of `R` lies in the extension of an ideal `I`,
then `r * t ∈ I` for some `t` in the localizing submonoid. -/
lemma exists_mul_mem_of_algebraMap_mem_map (M : Submonoid R) [IsLocalization M A]
    {I : Ideal R} {r : R} (h : algebraMap R A r ∈ I.map (algebraMap R A)) :
    ∃ t ∈ M, r * t ∈ I := by
  obtain ⟨⟨⟨v, hv⟩, ⟨t, ht⟩⟩, hvt⟩ := (IsLocalization.mem_map_algebraMap_iff M A).mp h
  have hvt' : algebraMap R A (r * t) = algebraMap R A v := by
    rw [map_mul]; exact hvt
  obtain ⟨⟨c, hc⟩, hcc⟩ := (IsLocalization.eq_iff_exists (M := M) (S := A)).mp hvt'
  refine ⟨t * c, mul_mem ht hc, ?_⟩
  have hrtc : r * (t * c) = v * c := by
    rw [show r * (t * c) = c * (r * t) by ring, hcc]
    ring
  rw [hrtc]
  exact I.mul_mem_right c hv

variable (A) {𝔭 : Ideal R} [𝔭.IsPrime] [IsLocalization.AtPrime A 𝔭] {𝔮 : Ideal R} [𝔮.IsPrime]

omit [𝔮.IsPrime] in
lemma _root_.Ideal.disjoint_primeCompl_of_le (h : 𝔮 ≤ 𝔭) :
    Disjoint (𝔭.primeCompl : Set R) (𝔮 : Set R) :=
  Set.disjoint_left.mpr fun _ ht ht' => ht (h ht')

/-- The extension of a prime `𝔮 ≤ 𝔭` to the localization at `𝔭` is prime. -/
lemma isPrime_map_of_le (h : 𝔮 ≤ 𝔭) : (𝔮.map (algebraMap R A)).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint 𝔭.primeCompl A 𝔮 inferInstance
    (Ideal.disjoint_primeCompl_of_le h)

/-- A prime `𝔮 ≤ 𝔭` is recovered from its extension to the localization at `𝔭`. -/
lemma comap_map_of_le (h : 𝔮 ≤ 𝔭) :
    ((𝔮.map (algebraMap R A)).comap (algebraMap R A) : Ideal R) = 𝔮 :=
  IsLocalization.under_map_of_isPrime_disjoint 𝔭.primeCompl A inferInstance
    (Ideal.disjoint_primeCompl_of_le h)

/-- Extending a prime `𝔮 ≤ 𝔭` to the localization at `𝔭` preserves its height. -/
lemma height_map_of_le (h : 𝔮 ≤ 𝔭) : (𝔮.map (algebraMap R A)).height = 𝔮.height := by
  haveI := isPrime_map_of_le A h
  have h1 := IsLocalization.height_under 𝔭.primeCompl (𝔮.map (algebraMap R A))
  have h2 : (Ideal.under R (𝔮.map (algebraMap R A)) : Ideal R) = 𝔮 := comap_map_of_le A h
  rw [h2] at h1
  exact h1.symm

end IsLocalization
