import Mathlib.RingTheory.Localization.AtPrime.Extension

open Algebra IsLocalRing Ideal Localization.AtPrime IsLocalization AtPrime

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
  (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
  (Sₚ : Type*) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]
  [Algebra Rₚ Sₚ] (P : Ideal S) [hPp : P.LiesOver p]

theorem IsLocalization.AtPrime.comap_map_of_isMaximal (P : Ideal S) [P.IsMaximal]
    [P.LiesOver p] :
    Ideal.comap (algebraMap S Sₚ) (Ideal.map (algebraMap S Sₚ) P) = P :=
  comap_map_eq_self_of_isMaximal _ (isPrime_map_of_liesOver p Sₚ P).ne_top

variable [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]

variable {T : Type*} [CommRing T] [Algebra R T] [Algebra Rₚ T] [Algebra S T]
  [IsScalarTower R S T] [IsScalarTower R Rₚ T]

theorem IsLocalization.AtPrime.comap_liesOver_of_liesOver (Q : Ideal T)
    [Q.LiesOver (maximalIdeal Rₚ)] : (comap (algebraMap S T) Q).LiesOver p := by
  have : Q.LiesOver p := by
    have : (maximalIdeal Rₚ).LiesOver p := (liesOver_iff _ _).mpr (comap_maximalIdeal _ _).symm
    exact LiesOver.trans Q (IsLocalRing.maximalIdeal Rₚ) p
  exact comap_liesOver Q p <| IsScalarTower.toAlgHom R S T

variable [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] [IsDedekindDomain S]
  [NoZeroSMulDivisors R S]

noncomputable def primesOverEquivPrimesOver' (hp : p ≠ ⊥) :
    p.primesOver S ≃ (maximalIdeal Rₚ).primesOver Sₚ := {
  toFun := by
    intro P
    refine ⟨map (algebraMap S Sₚ) P.1, isPrime_map_of_liesOver p Sₚ P.1,
      liesOver_map_of_liesOver p Rₚ Sₚ P.1⟩
  invFun := by
    intro Q
    refine ⟨comap (algebraMap S Sₚ) Q.1,  IsPrime.under S Q.1, comap_liesOver_of_liesOver p Rₚ Q.1⟩
  left_inv := by
    intro P
    have : P.val.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
        (ne_bot_of_mem_primesOver hp P.prop) (primesOver.isPrime p P)
    exact SetCoe.ext <| IsLocalization.AtPrime.comap_map_of_isMaximal p Sₚ P.1
  right_inv := by
    intro Q
    exact SetCoe.ext <| map_comap (algebraMapSubmonoid S p.primeCompl) Sₚ Q
}
