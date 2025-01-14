/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Splitting fields

In this file we prove the existence and uniqueness of splitting fields.

## Main definitions

* `Polynomial.SplittingField f`: A fixed splitting field of the polynomial `f`.

## Main statements

* `Polynomial.IsSplittingField.algEquiv`: Every splitting field of a polynomial `f` is isomorphic
  to `SplittingField f` and thus, being a splitting field is unique up to isomorphism.

-/

noncomputable section

universe u v w

variable {F : Type u} {K : Type v} {L : Type w}

namespace Polynomial

variable [Field K] [Field L] [Field F]

open Polynomial

section SplittingField

/-- A splitting field of a polynomial. -/
@[stacks 09HV "The construction of the splitting field."]
def SplittingField (f : K[X]) :=
  IntermediateField.adjoin K (f.rootSet (AlgebraicClosure K))

namespace SplittingField

variable (f : K[X])

instance commRing : CommRing (SplittingField f) :=
  inferInstance

instance inhabited : Inhabited (SplittingField f) :=
  ⟨37⟩

instance algebra : Algebra K (SplittingField f) :=
  inferInstance

instance algebra' {R : Type*} [CommSemiring R] [Algebra R K] : Algebra R (SplittingField f) :=
  inferInstance

instance isScalarTower {R : Type*} [CommSemiring R] [Algebra R K] :
    IsScalarTower R K (SplittingField f) :=
  f.SplittingField.isScalarTower

instance instGroupWithZero : GroupWithZero (SplittingField f) := inferInstance

instance instField : Field (SplittingField f) := inferInstance

instance instCharZero [CharZero K] : CharZero (SplittingField f) :=
  inferInstance

instance instCharP (p : ℕ) [CharP K p] : CharP (SplittingField f) p :=
  charP_of_injective_algebraMap (algebraMap K _).injective p

instance instExpChar (p : ℕ) [ExpChar K p] : ExpChar (SplittingField f) p :=
  expChar_of_injective_algebraMap (algebraMap K _).injective p

instance _root_.Polynomial.IsSplittingField.splittingField (f : K[X]) :
    IsSplittingField K (SplittingField f) f :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits_codomain f)

@[stacks 09HU "Splitting part"]
protected theorem splits : Splits (algebraMap K (SplittingField f)) f :=
  IsSplittingField.splits f.SplittingField f

variable [Algebra K L] (hb : Splits (algebraMap K L) f)

/-- Embeds the splitting field into any other field that splits the polynomial. -/
def lift : SplittingField f →ₐ[K] L :=
  IsSplittingField.lift f.SplittingField f hb

theorem adjoin_rootSet : Algebra.adjoin K (f.rootSet (SplittingField f)) = ⊤ :=
  Polynomial.IsSplittingField.adjoin_rootSet _ f

end SplittingField

end SplittingField

namespace IsSplittingField

variable (K L)
variable [Algebra K L]
variable {K}

instance (f : K[X]) : FiniteDimensional K f.SplittingField :=
  finiteDimensional f.SplittingField f

instance [Finite K] (f : K[X]) : Finite f.SplittingField :=
  Module.finite_of_finite K

instance (f : K[X]) : NoZeroSMulDivisors K f.SplittingField :=
  inferInstance

/-- Any splitting field is isomorphic to `SplittingFieldAux f`. -/
def algEquiv (f : K[X]) [h : IsSplittingField K L f] : L ≃ₐ[K] SplittingField f :=
  AlgEquiv.ofBijective (lift L f <| splits (SplittingField f) f) <|
    have := finiteDimensional L f
    ((Algebra.IsAlgebraic.of_finite K L).algHom_bijective₂ _ <| lift _ f h.1).1

end IsSplittingField

end Polynomial
