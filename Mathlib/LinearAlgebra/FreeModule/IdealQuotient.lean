/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-! # Ideals in free modules over PIDs

## Main results

 - `Ideal.quotientEquivPiSpan`: `S ⧸ I`, if `S` is finite free as a module over a PID `R`,
   can be written as a product of quotients of `R` by principal ideals.

-/

namespace Ideal

open scoped DirectSum

variable {ι R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [IsDomain R] [IsPrincipalIdealRing R] [IsDomain S] [Finite ι]

/-- We can write the quotient of an ideal over a PID as a product of quotients by principal ideals.
-/
noncomputable def quotientEquivPiSpan (I : Ideal S) (b : Basis ι R S) (hI : I ≠ ⊥) :
    (S ⧸ I) ≃ₗ[R] ∀ i, R ⧸ span ({I.smithCoeffs b hI i} : Set R) :=
  Submodule.quotientEquivPiSpan (I.restrictScalars R) b <| finrank_eq_finrank b I hI

/-- Ideal quotients over a free finite extension of `ℤ` are isomorphic to a direct product of
`ZMod`. -/
noncomputable def quotientEquivPiZMod (I : Ideal S) (b : Basis ι ℤ S) (hI : I ≠ ⊥) :
    S ⧸ I ≃+ ∀ i, ZMod (I.smithCoeffs b hI i).natAbs :=
  Submodule.quotientEquivPiZMod (I.restrictScalars ℤ) b <| finrank_eq_finrank b I hI

/-- A nonzero ideal over a free finite extension of `ℤ` has a finite quotient.

Can't be an instance because of the side condition `I ≠ ⊥`, and more importantly,
because the choice of `Fintype` instance is non-canonical.
-/
noncomputable def fintypeQuotientOfFreeOfNeBot [Module.Free ℤ S] [Module.Finite ℤ S]
    (I : Ideal S) (hI : I ≠ ⊥) : Fintype (S ⧸ I) :=
  let b := Module.Free.chooseBasis ℤ S
  Submodule.fintypeQuotientOfFreeOfRankEq (I.restrictScalars ℤ) <| finrank_eq_finrank b I hI

variable (F : Type*) [CommRing F] [Algebra F R] [Algebra F S] [IsScalarTower F R S]
  (b : Basis ι R S) {I : Ideal S} (hI : I ≠ ⊥)

/-- Decompose `S⧸I` as a direct sum of cyclic `R`-modules
  (quotients by the ideals generated by Smith coefficients of `I`). -/
noncomputable def quotientEquivDirectSum :
    (S ⧸ I) ≃ₗ[F] ⨁ i, R ⧸ span ({I.smithCoeffs b hI i} : Set R) :=
  Submodule.quotientEquivDirectSum F b (N := (I.restrictScalars R)) <| finrank_eq_finrank b I hI

theorem finrank_quotient_eq_sum {ι} [Fintype ι] (b : Basis ι R S) [Nontrivial F]
    [∀ i, Module.Free F (R ⧸ span ({I.smithCoeffs b hI i} : Set R))]
    [∀ i, Module.Finite F (R ⧸ span ({I.smithCoeffs b hI i} : Set R))] :
    Module.finrank F (S ⧸ I) =
      ∑ i, Module.finrank F (R ⧸ span ({I.smithCoeffs b hI i} : Set R)) := by
  -- slow, and dot notation doesn't work
  rw [LinearEquiv.finrank_eq <| quotientEquivDirectSum F b hI, Module.finrank_directSum]

end Ideal
