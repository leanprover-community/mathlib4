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
--TODO
--1. Etale implies vanishing Kaehler Differentials
--- strategy: etale implies formally unramified, which is equivalent
-- to vanishing Kaehler differentials (latter is not yet formalized but
-- https://www.math.uni-bonn.de/people/ja/alggeoII/notes_II.pdf Lemma 5.1 should be helpful)
--
--theorem Etale.KaehlerDifferentialZero (Etale R A) : Ω[A⁄R] = 0 := sorry
--- there is a universe problem in the statement.

-- 2. Localization R -> R_f is etale
-- 3. If R=k is a field, A is etale iff A is a finite product of fields
--


end
