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

/-! ### The place at infinity on F(t) -/


section InftyValuation

open Multiplicative WithZero

variable [DecidableEq (RatFunc F)]

/-- The valuation at infinity is the nonarchimedean valuation on `F(t)` with uniformizer `1/t`.
Explicitly, if `f/g ∈ F(t)` is a nonzero quotient of polynomials, its valuation at infinity is
`exp (degree(f) - degree(g))`. -/
def inftyValuationDef (r : RatFunc F) : ℤᵐ⁰ :=
  if r = 0 then 0 else exp r.intDegree

theorem InftyValuation.map_zero' : inftyValuationDef F 0 = 0 :=
  if_pos rfl

theorem InftyValuation.map_one' : inftyValuationDef F 1 = 1 :=
  (if_neg one_ne_zero).trans <| by simp

theorem InftyValuation.map_mul' (x y : RatFunc F) :
    inftyValuationDef F (x * y) = inftyValuationDef F x * inftyValuationDef F y := by
  rw [inftyValuationDef, inftyValuationDef, inftyValuationDef]
  by_cases hx : x = 0
  · rw [hx, zero_mul, if_pos (Eq.refl _), zero_mul]
  · by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos (Eq.refl _), mul_zero]
    · simp_all [RatFunc.intDegree_mul]

theorem InftyValuation.map_add_le_max' (x y : RatFunc F) :
    inftyValuationDef F (x + y) ≤ max (inftyValuationDef F x) (inftyValuationDef F y) := by
  by_cases hx : x = 0
  · rw [hx, zero_add]
    conv_rhs => rw [inftyValuationDef, if_pos (Eq.refl _)]
    rw [max_eq_right (WithZero.zero_le (inftyValuationDef F y))]
  · by_cases hy : y = 0
    · rw [hy, add_zero]
      conv_rhs => rw [max_comm, inftyValuationDef, if_pos (Eq.refl _)]
      rw [max_eq_right (WithZero.zero_le (inftyValuationDef F x))]
    · by_cases hxy : x + y = 0
      · rw [inftyValuationDef, if_pos hxy]; exact zero_le'
      · rw [inftyValuationDef, inftyValuationDef, inftyValuationDef, if_neg hx, if_neg hy,
          if_neg hxy]
        simpa using RatFunc.intDegree_add_le hy hxy

@[simp]
theorem inftyValuation_of_nonzero {x : RatFunc F} (hx : x ≠ 0) :
    inftyValuationDef F x = exp x.intDegree := by
  rw [inftyValuationDef, if_neg hx]

/-- The valuation at infinity on `F(t)`. -/
def inftyValuation : Valuation (RatFunc F) ℤᵐ⁰ where
  toFun := inftyValuationDef F
  map_zero' := InftyValuation.map_zero' F
  map_one' := InftyValuation.map_one' F
  map_mul' := InftyValuation.map_mul' F
  map_add_le_max' := InftyValuation.map_add_le_max' F

theorem inftyValuation_apply {x : RatFunc F} : inftyValuation F x = inftyValuationDef F x :=
  rfl

@[simp]
theorem inftyValuation.C {k : F} (hk : k ≠ 0) :
    inftyValuation F (RatFunc.C k) = 1 := by
  simp [inftyValuation_apply, hk]

@[simp]
theorem inftyValuation.X : inftyValuation F RatFunc.X = exp 1 := by
  simp [inftyValuation_apply, inftyValuationDef, if_neg RatFunc.X_ne_zero, RatFunc.intDegree_X]

lemma inftyValuation.X_zpow (m : ℤ) : inftyValuation F (RatFunc.X ^ m) = exp m := by simp

theorem inftyValuation.X_inv : inftyValuation F (1 / RatFunc.X) = exp (-1) := by
  rw [one_div, ← zpow_neg_one, inftyValuation.X_zpow]

-- Dropped attribute `@[simp]` due to issue described here:
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/.60synthInstance.2EmaxHeartbeats.60.20error.20but.20only.20in.20.60simpNF.60
theorem inftyValuation.polynomial {p : F[X]} (hp : p ≠ 0) :
    inftyValuationDef F (algebraMap F[X] (RatFunc F) p) = exp (p.natDegree : ℤ) := by
  rw [inftyValuationDef, if_neg (by simpa), RatFunc.intDegree_polynomial]

instance : Valuation.IsNontrivial (inftyValuation F) := ⟨RatFunc.X, by simp⟩

instance : Valuation.IsTrivialOn F (inftyValuation F) :=
  ⟨fun _ hx ↦ by simp [inftyValuation.C _ hx]⟩

/-- The valued field `F(t)` with the valuation at infinity. -/
@[implicit_reducible]
def inftyValuedFqt : Valued (RatFunc F) ℤᵐ⁰ :=
  Valued.mk' <| inftyValuation F

theorem inftyValuedFqt.def {x : RatFunc F} :
    (inftyValuedFqt F).v x = inftyValuationDef F x :=
  rfl

namespace FqtInfty

/- We temporarily disable the existing valued instance coming from the ideal `X` to avoid diamonds
with the uniform space structure coming from the valuation at infinity. -/
attribute [-instance] RatFunc.valuedRatFunc

/- Locally add the uniform space structure coming from the valuation at infinity. This instance
is scoped in the `FqtInfty` namescape in case it is needed in the future. -/
/-- The uniform space structure on `RatFunc F` coming from the valuation at infinity. -/
scoped instance : UniformSpace (RatFunc F) := (inftyValuedFqt F).toUniformSpace

/-- The completion `F((t⁻¹))` of `F(t)` with respect to the valuation at infinity. -/
def _root_.FunctionField.FqtInfty := UniformSpace.Completion (RatFunc F)
deriving Field, Algebra (RatFunc F), Coe (RatFunc F), Inhabited

end FqtInfty

/-- The valuation at infinity on `k(t)` extends to a valuation on `FqtInfty`. -/
instance valuedFqtInfty : Valued (FqtInfty F) ℤᵐ⁰ := (inftyValuedFqt F).valuedCompletion

theorem valuedFqtInfty.def {x : FqtInfty F} :
  Valued.v x = (inftyValuedFqt F).extensionValuation x := rfl

end InftyValuation

end FunctionField
