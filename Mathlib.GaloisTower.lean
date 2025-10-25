import Mathlib.NumberTheory.RamificationInertia.Galois

namespace Ideal

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] (p : Ideal A) (P : Ideal B)
  [hPp : P.IsPrime] [hp : P.LiesOver p] (K L M : Type*) [Field K] [Field L] [Algebra A K]
  [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
  [IsScalarTower A B L] [IsScalarTower A K L] [FiniteDimensional K L]

variable (C : Type*) [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Field M]
  [Algebra C M] [IsFractionRing C M] [Algebra K M] [FiniteDimensional K M]
  [Algebra A C] [Algebra B C] [Module.Finite A C]
  [Algebra A M] [IsScalarTower A C M] [IsScalarTower A K M] [Module.Finite B C]
  [NoZeroSMulDivisors B C] [Algebra L M] [Algebra B M] [IsScalarTower B C M] [IsScalarTower B L M]
  [FiniteDimensional L M] [IsGalois L M]  [IsScalarTower A B C]

theorem inertiaDegIn_mul_inertiaDegIn [p.IsMaximal] [P.IsMaximal] [IsGalois K L] [IsGalois K M] :
    p.inertiaDegIn B * P.inertiaDegIn C = p.inertiaDegIn C := by
  obtain ⟨⟨Q, _, _⟩⟩ := P.nonempty_primesOver (S := C)
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [inertiaDegIn_eq_inertiaDeg p P K L, inertiaDegIn_eq_inertiaDeg p Q K M,
    inertiaDegIn_eq_inertiaDeg P Q L M, inertiaDeg_algebra_tower p P Q]

variable {p P} in
theorem ramificationIdxIn_mul_ramificationIdxInIn [IsDedekindDomain B] [IsDedekindDomain C]
    [IsGalois K L] [IsGalois K M] (hp :  map (algebraMap A C) p ≠ ⊥)
    (hP : map (algebraMap B C) P ≠ ⊥) :
    p.ramificationIdxIn B * P.ramificationIdxIn C = p.ramificationIdxIn C := by
  obtain ⟨⟨Q, _, hQ⟩⟩ := P.nonempty_primesOver (S := C)
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [ramificationIdxIn_eq_ramificationIdx p P K L, ramificationIdxIn_eq_ramificationIdx p Q K M,
    ramificationIdxIn_eq_ramificationIdx P Q L M, ramificationIdx_algebra_tower hP hp]
  convert map_comap_le
  exact (liesOver_iff Q P).mp hQ

example [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C] [p.IsMaximal] [IsGalois K L]
    [NoZeroSMulDivisors A B] [NoZeroSMulDivisors A C]
    [IsGalois K M] [IsScalarTower K L M] [P.IsMaximal]
    (hp : p ≠ ⊥):
    (p.primesOver B).ncard * (P.primesOver C).ncard = (p.primesOver C).ncard := by
  have : p.ramificationIdxIn C * p.inertiaDegIn C ≠ 0 :=
    mul_ne_zero (ramificationIdxIn_ne_zero K M hp) (inertiaDegIn_ne_zero K M)
  have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
  rw [← Nat.mul_left_inj this, ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp C K M]
  calc
    _ = ((p.primesOver B).ncard *  (p.ramificationIdxIn B * p.inertiaDegIn B)) *
        ((P.primesOver C).ncard * (P.ramificationIdxIn C * P.inertiaDegIn C)) := by
      rw [← inertiaDegIn_mul_inertiaDegIn p P K L M C,
        ← ramificationIdxIn_mul_ramificationIdxInIn (p := p) (P := P) K L M C]
      ring
      · exact map_ne_bot_of_ne_bot hp
      · exact map_ne_bot_of_ne_bot hP
    _ = Module.finrank K M := by
      rw [ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B K L,
        ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hP C L M,
        Module.finrank_mul_finrank]

end Ideal
