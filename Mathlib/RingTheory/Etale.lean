import Mathlib.RingTheory.FormallyEtale
import Mathlib.RingTheory.FinitePresentation

universe u

open TensorProduct
namespace Algebra

variable (R : Type u)

class Etale [CommSemiring R] (A : Type u) [Semiring A] [Algebra R A] : Prop where
  formallyEtale : FormallyEtale R A
  finitePresentation : FinitePresentation R A

namespace Etale
attribute [instance] formallyEtale
end Etale

#check Etale.formallyEtale



variable [CommRing R]

section

variable (A : Type u) [CommRing A] [Algebra R A] [Etale R A]
variable (B : Type u) [CommRing B] [Algebra A B] [Etale A B]
variable [Algebra R B] [IsScalarTower R A B]

theorem Etale.comp : Etale R B where
  formallyEtale := FormallyEtale.comp R A B
  finitePresentation := FinitePresentation.trans (A := A) Etale.finitePresentation
    Etale.finitePresentation

-- by
--    letI : FormallyEtale R A := Etale.formallyEtale
--   letI : FormallyEtale A B := Etale.formallyEtale
--    exact FormallyEtale.comp R A B


end
section

variable (A : Type u) [CommRing A] [Algebra R A] [Etale R A]
variable (B : Type u) [CommRing B] [Algebra R B]
instance Etale.baseChange : Etale B (B ⊗[R] A) where
  formallyEtale := FormallyEtale.base_change B
  finitePresentation := sorry

--


end
