import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.NumberTheory.RamificationInertia.Basic

theorem Ideal.ramificationIdx_eq_multiplicity {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    [IsDedekindDomain S] {f : R →+* S} (hf : Function.Injective f) {p : Ideal R} (hp : p ≠ ⊥)
    {P : Ideal S} (hP₁: P.IsPrime) (hP₂ : P ≠ ⊥)  :
    ramificationIdx f p P = multiplicity P (Ideal.map f p) := by
  classical
  have hp' : map f p ≠ ⊥ := (map_eq_bot_iff_of_injective hf).not.mpr hp
  rw [multiplicity_eq_of_emultiplicity_eq_some]
  rw [IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp' hP₁ hP₂, ← normalize_eq P,
    ← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors _ hp', normalize_eq]
  exact irreducible_iff_prime.mpr <| prime_of_isPrime hP₂ hP₁

#find_home! Ideal.ramificationIdx_eq_multiplicity 
