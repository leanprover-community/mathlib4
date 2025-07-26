import Mathlib

variable {R : Type*} [CommRing R] (p : Ideal R) [hp : p.IsPrime]

local notation3 "Rₚ" => Localization.AtPrime p

variable (S : Type*) [CommRing S] [Algebra R S] (P : Ideal S) [hP : P.IsPrime] [hPp : P.LiesOver p]

local notation3 "Mₛ" => Algebra.algebraMapSubmonoid S p.primeCompl
local notation3 "Sₚ" => Localization Mₛ

instance [IsDomain R] [IsDomain S] [FaithfulSMul R S] : NoZeroSMulDivisors S Sₚ := by
  rw [NoZeroSMulDivisors.iff_algebraMap_injective]
  rw [IsLocalization.injective_iff_isRegular Mₛ]
  rintro ⟨x, hx⟩
  rw [isRegular_iff_ne_zero']
  refine ne_of_mem_of_not_mem hx ?_
  simp [Algebra.algebraMapSubmonoid]

instance : Algebra (FractionRing Rₚ) (FractionRing Sₚ) :=
  FractionRing.liftAlgebra Rₚ (FractionRing Sₚ)
