module

import Mathlib

instance (A B : Type*) [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Flat A B]
    [Algebra.IsIntegral A B] [FaithfulSMul A B] :
    Module.FaithfullyFlat A B := by
  refine Module.FaithfullyFlat.of_comap_surjective fun P ↦ ?_
  obtain ⟨P, hP₁, hP₂⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain P.1 (S := B)
    (by simp [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)])
  exact ⟨⟨P, hP₁⟩, PrimeSpectrum.ext_iff.mpr hP₂⟩
