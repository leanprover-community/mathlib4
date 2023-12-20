import Mathlib.RingTheory.Flat
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Ideal.LocalRing

universe u v w

open TensorProduct

open Localization

namespace Module

namespace Flat

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]


--class or def?
class Faithful extends Flat R M where
  faithful := ∀ ⦃m : Ideal R⦄ (_ : m.IsMaximal), Nontrivial <| M ⊗[R] (R ⧸ m)
  --faithful := ∀ ⦃m : Ideal R⦄ (_ : m.IsMaximal), Nontrivial <| M ⧸ (m • ⊤ : Submodule R M)

namespace Faithful

--Faithfully flat iff relfects exact sequences (maybe put in cat file)
def ReflectsExact : Prop := sorry

--Faithfully flat iff tensor with any R-module is nonzero
def TensorNonzero : Prop :=
  ∀ {N : Type v} [AddCommGroup N] [Module R N], Nontrivial N → Nontrivial (N ⊗[R] M)

-- Faithfully flat iff tensor with all prime residues is nonzero
def PrimeResidues : Prop :=
  ∀ ⦃p : Ideal R⦄ (_ : p.IsPrime), Nontrivial <| M ⊗[R] FractionRing (R ⧸ p)
  -- @TensorProduct R _ M (LocalRing.ResidueField (Localization.AtPrime p)) _ _ _ <|
  -- ((LocalRing.residue (Localization.AtPrime p)).comp
  -- (algebraMap R <| Localization.AtPrime p)).toModule

-- Faithfully flat iff tensor with all maximal residues is nonzero
-- def MaximalResidues : Prop :=
--   ∀ ⦃m : Ideal R⦄ (_ : m.IsMaximal), Nontrivial <| M ⊗[R] (R ⧸ m)
  -- @TensorProduct R _ M (LocalRing.ResidueField (Localization.AtPrime m)) _ _ _ <|
  -- ((LocalRing.residue (Localization.AtPrime m)).comp
  -- (algebraMap R <| Localization.AtPrime m)).toModule



end Faithful

end Flat

end Module
