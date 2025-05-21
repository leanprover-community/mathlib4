import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.RamificationInertia.Galois

set_option linter.style.header false

open Ideal NumberField Module NumberField.InfinitePlace Nat Real

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

namespace RingOfIntegers

theorem
  isPrincipalIdealRing_of_isPrincipal_of_pow_inertiaDeg_le_of_mem_primesOver_of_mem_Icc.Galois
    [IsGalois ℚ K] (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, p.Prime →
      ∃ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K),
        ⌊(M K)⌋₊ < p ^ ((span ({↑p} : Set ℤ)).inertiaDeg P) ∨
          Submodule.IsPrincipal P) :
      IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_isPrincipal_of_pow_inertiaDeg_le_of_mem_primesOver_of_mem_Icc
    (fun p hpmem hp P hP hple ↦ ?_)
  obtain ⟨Q, hQ, H⟩ := h p hpmem hp
  have := hP.1; have := hP.2; have := hQ.1; have := hQ.2
  have := (isPrime_of_prime (prime_span_singleton_iff.mpr (prime_iff_prime_int.mp hp))).isMaximal
    (by simp [hp.ne_zero])
  by_cases h : ⌊(M K)⌋₊ < p ^ ((span ({↑p} : Set ℤ)).inertiaDeg P)
  · linarith
  rw [inertiaDeg_eq_of_isGalois _ Q P ℚ K] at H
  obtain ⟨σ, rfl⟩ := exists_map_eq_of_isGalois (span ({↑p} : Set ℤ)) Q P ℚ K
  exact (H.resolve_left h).map_ringHom σ

end RingOfIntegers
