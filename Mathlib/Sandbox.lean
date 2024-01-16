import Mathlib.RingTheory.Ideal.Norm

open nonZeroDivisors

variable {S : Type*} [CommRing S] [IsDomain S] [Nontrivial S] [IsDedekindDomain S]
  [Module.Free ℤ S]  [Module.Finite ℤ S]

theorem absNorm_ne_zero_of_nonZeroDivisors (I : (Ideal S)⁰) : Ideal.absNorm (I : Ideal S) ≠ 0 :=
  Ideal.absNorm_eq_zero_iff.not.mpr <| nonZeroDivisors.coe_ne_zero _
