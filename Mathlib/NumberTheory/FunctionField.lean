/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Ashvni Narayanan
-/
module

public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.FieldTheory.RatFunc.Valuation -- for deprecation of `RatFunc.inftyValuation` and `RatFunc.FqtInfty`

/-!
# Function fields

This file defines a function field and the ring of integers corresponding to it.

## Main definitions

- `FunctionField F K` states that `K` is a function field over the field `F`,
  i.e. it is a finite extension of the field of rational functions in one variable over `F`.
- `FunctionField.ringOfIntegers` defines the ring of integers corresponding to a function field
  as the integral closure of `F[X]` in the function field.
- `FunctionField.inftyValuation` : The place at infinity on `F(t)` is the nonarchimedean
  valuation on `F(t)` with uniformizer `1/t`.
- `FunctionField.FqtInfty` : The completion `F((t⁻¹))` of `F(t)` with respect to the
  valuation at infinity.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. We also omit assumptions like
`IsScalarTower F[X] (FractionRing F[X]) K` in definitions,
adding them back in lemmas when they are needed.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags
function field, ring of integers
-/

@[expose] public section


noncomputable section

open scoped nonZeroDivisors Polynomial WithZero

variable (F K : Type*) [Field F] [Field K]

/-- `K` is a function field over the field `F` if it is a finite
extension of the field of rational functions in one variable over `F`.

Note that `K` can be a function field over multiple, non-isomorphic, `F`.
-/
abbrev FunctionField [Algebra (RatFunc F) K] : Prop :=
  FiniteDimensional (RatFunc F) K

/-- `K` is a function field over `F` iff it is a finite extension of `F(t)`. -/
theorem functionField_iff (Ft : Type*) [Field Ft] [Algebra F[X] Ft]
    [IsFractionRing F[X] Ft] [Algebra (RatFunc F) K] [Algebra Ft K] [Algebra F[X] K]
    [IsScalarTower F[X] Ft K] [IsScalarTower F[X] (RatFunc F) K] :
    FunctionField F K ↔ FiniteDimensional Ft K := by
  let e := IsLocalization.algEquiv F[X]⁰ (RatFunc F) Ft
  have : ∀ (c) (x : K), e c • x = c • x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def]
    congr
    refine congr_fun (f := fun c => algebraMap Ft K (e c)) ?_ c
    refine IsLocalization.ext (nonZeroDivisors F[X]) _ _ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
      simp only [map_one, map_mul, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  constructor <;> intro h
  · let b := Module.finBasis (RatFunc F) K
    exact (b.mapCoeffs e this).finiteDimensional_of_finite
  · let b := Module.finBasis Ft K
    refine (b.mapCoeffs e.symm ?_).finiteDimensional_of_finite
    intro c x; convert (this (e.symm c) x).symm; simp only [e.apply_symm_apply]

namespace FunctionField

theorem algebraMap_injective [Algebra F[X] K] [Algebra (RatFunc F) K]
    [IsScalarTower F[X] (RatFunc F) K] : Function.Injective (⇑(algebraMap F[X] K)) := by
  rw [IsScalarTower.algebraMap_eq F[X] (RatFunc F) K]
  exact (algebraMap (RatFunc F) K).injective.comp (IsFractionRing.injective F[X] (RatFunc F))

/-- The function field analogue of `NumberField.ringOfIntegers`:
`FunctionField.ringOfIntegers F K` is the integral closure of `F[X]` in `K`.

We don't actually assume `K` is a function field over `F` in the definition,
only when proving its properties.
-/
def ringOfIntegers [Algebra F[X] K] :=
  integralClosure F[X] K

namespace ringOfIntegers

variable [Algebra F[X] K]

instance : IsDomain (ringOfIntegers F K) :=
  (ringOfIntegers F K).isDomain

instance : IsIntegralClosure (ringOfIntegers F K) F[X] K :=
  integralClosure.isIntegralClosure _ _

variable [Algebra (RatFunc F) K] [IsScalarTower F[X] (RatFunc F) K]

theorem algebraMap_injective : Function.Injective (⇑(algebraMap F[X] (ringOfIntegers F K))) := by
  have hinj : Function.Injective (⇑(algebraMap F[X] K)) := by
    rw [IsScalarTower.algebraMap_eq F[X] (RatFunc F) K]
    exact (algebraMap (RatFunc F) K).injective.comp (IsFractionRing.injective F[X] (RatFunc F))
  rw [injective_iff_map_eq_zero (algebraMap F[X] (↥(ringOfIntegers F K)))]
  intro p hp
  rw [← Subtype.coe_inj, Subalgebra.coe_zero] at hp
  rw [injective_iff_map_eq_zero (algebraMap F[X] K)] at hinj
  exact hinj p hp

theorem not_isField : ¬IsField (ringOfIntegers F K) := by
  simpa [← (IsIntegralClosure.isIntegral_algebra F[X] K).isField_iff_isField
      (algebraMap_injective F K)] using
    Polynomial.not_isField F

variable [FunctionField F K]

instance : IsFractionRing (ringOfIntegers F K) K :=
  integralClosure.isFractionRing_of_finite_extension (RatFunc F) K

instance : IsIntegrallyClosed (ringOfIntegers F K) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension (RatFunc F)

instance [Algebra.IsSeparable (RatFunc F) K] : IsNoetherian F[X] (ringOfIntegers F K) :=
  IsIntegralClosure.isNoetherian _ (RatFunc F) K _

instance [Algebra.IsSeparable (RatFunc F) K] : IsDedekindDomain (ringOfIntegers F K) :=
  IsIntegralClosure.isDedekindDomain F[X] (RatFunc F) K _

end ringOfIntegers

section deprecated

@[deprecated RatFunc.inftyValuationDef (since := "2026-04-14")]
alias inftyValuationDef := RatFunc.inftyValuationDef

@[deprecated RatFunc.InftyValuation.map_zero' (since := "2026-04-14")]
alias InftyValuation.map_zero' := RatFunc.InftyValuation.map_zero'

@[deprecated RatFunc.InftyValuation.map_one' (since := "2026-04-14")]
alias InftyValuation.map_one' := RatFunc.InftyValuation.map_one'

@[deprecated RatFunc.InftyValuation.map_mul' (since := "2026-04-14")]
alias InftyValuation.map_mul' := RatFunc.InftyValuation.map_mul'

@[deprecated RatFunc.InftyValuation.map_add_le_max' (since := "2026-04-14")]
alias InftyValuation.map_add_le_max' := RatFunc.InftyValuation.map_add_le_max'

@[deprecated RatFunc.inftyValuation_of_nonzero (since := "2026-04-14")]
alias inftyValuation_of_nonzero := RatFunc.inftyValuation_of_nonzero

@[deprecated RatFunc.inftyValuation (since := "2026-04-14")]
alias inftyValuation := RatFunc.inftyValuation

@[deprecated RatFunc.inftyValuation_apply (since := "2026-04-14")]
alias inftyValuation_apply := RatFunc.inftyValuation_apply

@[deprecated RatFunc.inftyValuation.C (since := "2026-04-14")]
alias inftyValuation.C := RatFunc.inftyValuation.C

@[deprecated RatFunc.inftyValuation.X (since := "2026-04-14")]
alias inftyValuation.X := RatFunc.inftyValuation.X

@[deprecated RatFunc.inftyValuation.X_zpow (since := "2026-04-14")]
alias inftyValuation.X_zpow := RatFunc.inftyValuation.X_zpow

@[deprecated RatFunc.inftyValuation.X_inv (since := "2026-04-14")]
alias inftyValuation.X_inv := RatFunc.inftyValuation.X_inv

@[deprecated RatFunc.inftyValuation.polynomial (since := "2026-04-14")]
alias inftyValuation.polynomial := RatFunc.inftyValuation.polynomial

@[deprecated RatFunc.inftyValuedFqt (since := "2026-04-14")]
alias inftyValuedFqt := RatFunc.inftyValuedFqt

@[deprecated RatFunc.inftyValuedFqt.def (since := "2026-04-14")]
alias inftyValuedFqt.def := RatFunc.inftyValuedFqt.def

@[deprecated RatFunc.FqtInfty (since := "2026-04-14")]
alias FqtInfty := RatFunc.FqtInfty

@[deprecated RatFunc.valuedFqtInfty (since := "2026-04-14")]
alias valuedFqtInfty := RatFunc.valuedFqtInfty

@[deprecated RatFunc.valuedFqtInfty.def (since := "2026-04-14")]
alias valuedFqtInfty.def := RatFunc.valuedFqtInfty.def

end deprecated

end FunctionField
