import Mathlib.RingTheory.FormallyEtale
import Mathlib.RingTheory.FinitePresentation
import Mathlib.StabilityFinitePres
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Flat.Algebra

universe u

open TensorProduct
namespace Algebra


--Definitions smooth, unramified, etale
variable (R : Type u)

class Smooth [CommSemiring R] (A : Type u) [Semiring A] [Algebra R A] : Prop where
  formallySmooth : FormallySmooth R A
  finitePresentation : FinitePresentation R A

class Unramified [CommSemiring R] (A : Type u) [Semiring A] [Algebra R A] : Prop where
  formallyUnramified : FormallyUnramified R A
  finitePresentation : FinitePresentation R A

class Etale [CommSemiring R] (A : Type u) [Semiring A] [Algebra R A] : Prop where
  formallyEtale : FormallyEtale R A
  finitePresentation : FinitePresentation R A


namespace Smooth
attribute [instance] formallySmooth
end Smooth

namespace Unramified
attribute [instance] formallyUnramified
end Unramified

namespace Etale
attribute [instance] formallyEtale
end Etale

#check Etale.formallyEtale

variable [CommRing R]

section

variable (A: Type u) [CommRing A] [Algebra R A]
variable (B: Type u) [CommRing B] [Algebra A B]
variable [Algebra R B] [IsScalarTower R A B]

--Composition

theorem Smooth.comp [Smooth R A] [Smooth A B]: Smooth R B where
  formallySmooth := FormallySmooth.comp R A B
  finitePresentation := FinitePresentation.trans (A := A) Smooth.finitePresentation
    Smooth.finitePresentation

theorem Unframified.comp [Unramified R A] [Unramified A B]: Unramified R B where
  formallyUnramified := FormallyUnramified.comp R A B
  finitePresentation := FinitePresentation.trans (A := A) Unramified.finitePresentation
    Unramified.finitePresentation

theorem Etale.comp [Etale R A] [Etale A B]: Etale R B where
  formallyEtale := FormallyEtale.comp R A B
  finitePresentation := FinitePresentation.trans (A := A) Etale.finitePresentation
    Etale.finitePresentation

-- If `e : A ≃ₐ[R] B` and `A` is unramified / smooth / etale, then so is `B`.

theorem Smooth.of_equiv [Smooth R A] (e : A ≃ₐ[R] B) : Smooth R B where
  formallySmooth := FormallySmooth.of_equiv e
  finitePresentation := FinitePresentation.equiv Smooth.finitePresentation e

theorem Unramified.of_equiv [Unramified R A] (e : A ≃ₐ[R] B) : Unramified R B where
  formallyUnramified := FormallyUnramified.of_equiv e
  finitePresentation := FinitePresentation.equiv Unramified.finitePresentation e

theorem Etale.of_equiv [Etale R A] (e : A ≃ₐ[R] B) : Etale R B where
  formallyEtale := FormallyEtale.of_equiv e
  finitePresentation := FinitePresentation.equiv Etale.finitePresentation e

end


section

variable (A : Type u) [CommRing A] [Algebra R A]
variable (B : Type u) [CommRing B] [Algebra R B]


instance Smooth.baseChange [Smooth R A]: Smooth B (B ⊗[R] A) where
  formallySmooth := FormallySmooth.base_change B
  finitePresentation := FinitePresentation.baseChange _ finitePresentation

instance Unramified.baseChange [Unramified R A]: Unramified B (B ⊗[R] A) where
  formallyUnramified := FormallyUnramified.base_change B
  finitePresentation := FinitePresentation.baseChange _ finitePresentation

instance Etale.baseChange [Etale R A] : Etale B (B ⊗[R] A) where
  formallyEtale := FormallyEtale.base_change B
  finitePresentation := FinitePresentation.baseChange _ finitePresentation

theorem Etale.Subsingleton_kaehlerDifferential [Etale R A] : Subsingleton (Ω[A⁄R]) := by
  rw [← Algebra.FormallyUnramified.iff_subsingleton_kaehlerDifferential]
  exact FormallyEtale.to_unramified

end

section

variable (r : R)
variable (A : Type u) [CommRing A] [Algebra R A] [IsLocalization.Away r A]

theorem Etale.of_isLocalization_Away (r : R) [IsLocalization.Away r A] : Etale R A where
  formallyEtale := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  finitePresentation := IsLocalization.Away.finitePresentation r

end

--TODO
-- 2. Localization R -> R_M is etale for M finitely generated

-- 3. If R=k is a field, A is etale iff A is a finite product of fields
--    this is a nice goal, I am afraid we need dimension theory for this (at least that's what the SP does)
--    but maybe there is a direct way
-- 4. Characterization of unramified via stalks

-- 5. Smooth implies Flat
section

variable (A : Type u) [CommRing A] [Algebra R A]

theorem Smooth.to_flat [Smooth R A] : Flat R A := by sorry

end

-- 6. Standard etale morphisms
-- 7. etale implies smooth or relative dimenion zero
-- 8. Make category FinEt
-- 9. Open immersions are etale
-- 10. Open immersions =  etale and universally injective morphism
