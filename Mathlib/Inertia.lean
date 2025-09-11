import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.RingTheory.Frobenius

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]
  (P : Ideal B)

def Ideal.inertiaSubgroup : Subgroup (B ≃ₐ[A] B) :=
    AddSubgroup.inertia P.toAddSubgroup (B ≃ₐ[A] B)


