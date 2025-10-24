import Mathlib.NumberTheory.RamificationInertia.Galois

open Ideal

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] (p : Ideal A) (P : Ideal B)
  [hPp : P.IsPrime] [hp : P.LiesOver p] (K L : Type*) [Field K] [Field L] [Algebra A K]
  [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
  [IsScalarTower A B L] [IsScalarTower A K L] [FiniteDimensional K L] [p.IsMaximal] [IsGalois K L]

variable {C : Type*} [CommRing C] [IsDomain C] [IsIntegrallyClosed C] (M : Type*) [Field M]
  [Algebra C M] [IsFractionRing C M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
  [Algebra A C] [Algebra B C] [Algebra.IsIntegral A C] [NoZeroSMulDivisors A C] [Module.Finite A C]
  [Algebra A M] [IsScalarTower A C M] [IsScalarTower A K M] [Module.Finite B C]
  [NoZeroSMulDivisors B C] [Algebra L M] [Algebra B M] [IsScalarTower B C M] [IsScalarTower B L M]
  [FiniteDimensional L M] [IsGalois L M] [P.IsMaximal]

example : p.inertiaDegIn B * P.inertiaDegIn C = p.inertiaDegIn C := by
  obtain ⟨⟨Q, _, _⟩⟩ := P.nonempty_primesOver (S := C)
  have : Q.LiesOver p := sorry
  rw [inertiaDegIn_eq_inertiaDeg p P K L, inertiaDegIn_eq_inertiaDeg p Q K M,
    inertiaDegIn_eq_inertiaDeg P Q L M]
