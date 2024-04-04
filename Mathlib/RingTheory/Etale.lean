import Mathlib.RingTheory.FormallyEtale
import Mathlib.RingTheory.FinitePresentation
import Mathlib.StabilityFinitePres
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

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
  finitePresentation := FinitePresentation.baseChange _ finitePresentation

theorem Etale.Subsingleton_kaehlerDifferential [Etale R A] : Subsingleton (Ω[A⁄R]) := by
  rw [← Algebra.FormallyUnramified.iff_subsingleton_kaehlerDifferential]
  exact FormallyEtale.to_unramified

--renamed theorem, hopefully closer to naming conventions.
end

section

variable (r : R)
variable (A : Type u) [CommRing A] [Algebra R A] [IsLocalization.Away r A]

theorem Etale.of_isLocalization_Away (r : R) [IsLocalization.Away r A] : Etale R A where
  formallyEtale := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  finitePresentation := IsLocalization.Away.finitePresentation r

--TODO
-- 2. Localization R -> R_M is etale for M finitely generated
-- 3. If R=k is a field, A is etale iff A is a finite product of fields
--    this is a nice goal, I am afraid we need dimension theory for this (at least that's what the SP does)
--    but maybe there is a direct way
-- 4. Characterization of unramified via stalks
-- 5. Smooth implies Flat
-- 6. Standard etale morphisms
-- 7. etale implies smooth or relative dimenion zero
-- 8. Make category FinEt
-- 9. Open immersions are etale
-- 10. Open immersions =  etale and universally injective morphism

end
