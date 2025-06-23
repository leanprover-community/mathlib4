/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Ashvni Narayanan
-/
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Function fields

This file defines a function field and the ring of integers corresponding to it.

## Main definitions

- `FunctionField Fq F` states that `F` is a function field over the (finite) field `Fq`,
  i.e. it is a finite extension of the field of rational functions in one variable over `Fq`.
- `FunctionField.ringOfIntegers` defines the ring of integers corresponding to a function field
  as the integral closure of `Fq[X]` in the function field.
- `FunctionField.inftyValuation` : The place at infinity on `Fq(t)` is the nonarchimedean
  valuation on `Fq(t)` with uniformizer `1/t`.
- `FunctionField.FqtInfty` : The completion `Fq((t⁻¹))` of `Fq(t)` with respect to the
  valuation at infinity.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. We also omit assumptions like `Finite Fq` or
`IsScalarTower Fq[X] (FractionRing Fq[X]) F` in definitions,
adding them back in lemmas when they are needed.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags
function field, ring of integers
-/


noncomputable section

open scoped nonZeroDivisors Polynomial Multiplicative

variable (Fq F : Type*) [Field Fq] [Field F]

/-- `F` is a function field over the finite field `Fq` if it is a finite
extension of the field of rational functions in one variable over `Fq`.

Note that `F` can be a function field over multiple, non-isomorphic, `Fq`.
-/
abbrev FunctionField [Algebra (RatFunc Fq) F] : Prop :=
  FiniteDimensional (RatFunc Fq) F

/-- `F` is a function field over `Fq` iff it is a finite extension of `Fq(t)`. -/
theorem functionField_iff (Fqt : Type*) [Field Fqt] [Algebra Fq[X] Fqt]
    [IsFractionRing Fq[X] Fqt] [Algebra (RatFunc Fq) F] [Algebra Fqt F] [Algebra Fq[X] F]
    [IsScalarTower Fq[X] Fqt F] [IsScalarTower Fq[X] (RatFunc Fq) F] :
    FunctionField Fq F ↔ FiniteDimensional Fqt F := by
  let e := IsLocalization.algEquiv Fq[X]⁰ (RatFunc Fq) Fqt
  have : ∀ (c) (x : F), e c • x = c • x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def]
    congr
    refine congr_fun (f := fun c => algebraMap Fqt F (e c)) ?_ c
    refine IsLocalization.ext (nonZeroDivisors Fq[X]) _ _ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
      simp only [map_one, map_mul, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  constructor <;> intro h
  · let b := Module.finBasis (RatFunc Fq) F
    exact FiniteDimensional.of_fintype_basis (b.mapCoeffs e this)
  · let b := Module.finBasis Fqt F
    refine FiniteDimensional.of_fintype_basis (b.mapCoeffs e.symm ?_)
    intro c x; convert (this (e.symm c) x).symm; simp only [e.apply_symm_apply]

namespace FunctionField

theorem algebraMap_injective [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F] : Function.Injective (⇑(algebraMap Fq[X] F)) := by
  rw [IsScalarTower.algebraMap_eq Fq[X] (RatFunc Fq) F]
  exact (algebraMap (RatFunc Fq) F).injective.comp (IsFractionRing.injective Fq[X] (RatFunc Fq))

@[deprecated (since := "2025-03-03")]
alias _root_.algebraMap_injective := FunctionField.algebraMap_injective

/-- The function field analogue of `NumberField.ringOfIntegers`:
`FunctionField.ringOfIntegers Fq Fqt F` is the integral closure of `Fq[t]` in `F`.

We don't actually assume `F` is a function field over `Fq` in the definition,
only when proving its properties.
-/
def ringOfIntegers [Algebra Fq[X] F] :=
  integralClosure Fq[X] F

namespace ringOfIntegers

variable [Algebra Fq[X] F]

instance : IsDomain (ringOfIntegers Fq F) :=
  (ringOfIntegers Fq F).isDomain

instance : IsIntegralClosure (ringOfIntegers Fq F) Fq[X] F :=
  integralClosure.isIntegralClosure _ _

variable [Algebra (RatFunc Fq) F] [IsScalarTower Fq[X] (RatFunc Fq) F]

theorem algebraMap_injective : Function.Injective (⇑(algebraMap Fq[X] (ringOfIntegers Fq F))) := by
  have hinj : Function.Injective (⇑(algebraMap Fq[X] F)) := by
    rw [IsScalarTower.algebraMap_eq Fq[X] (RatFunc Fq) F]
    exact (algebraMap (RatFunc Fq) F).injective.comp (IsFractionRing.injective Fq[X] (RatFunc Fq))
  rw [injective_iff_map_eq_zero (algebraMap Fq[X] (↥(ringOfIntegers Fq F)))]
  intro p hp
  rw [← Subtype.coe_inj, Subalgebra.coe_zero] at hp
  rw [injective_iff_map_eq_zero (algebraMap Fq[X] F)] at hinj
  exact hinj p hp

theorem not_isField : ¬IsField (ringOfIntegers Fq F) := by
  simpa [← (IsIntegralClosure.isIntegral_algebra Fq[X] F).isField_iff_isField
      (algebraMap_injective Fq F)] using
    Polynomial.not_isField Fq

variable [FunctionField Fq F]

instance : IsFractionRing (ringOfIntegers Fq F) F :=
  integralClosure.isFractionRing_of_finite_extension (RatFunc Fq) F

instance : IsIntegrallyClosed (ringOfIntegers Fq F) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension (RatFunc Fq)

instance [Algebra.IsSeparable (RatFunc Fq) F] : IsNoetherian Fq[X] (ringOfIntegers Fq F) :=
  IsIntegralClosure.isNoetherian _ (RatFunc Fq) F _

instance [Algebra.IsSeparable (RatFunc Fq) F] : IsDedekindDomain (ringOfIntegers Fq F) :=
  IsIntegralClosure.isDedekindDomain Fq[X] (RatFunc Fq) F _

end ringOfIntegers

/-! ### The place at infinity on Fq(t) -/


section InftyValuation

variable [DecidableEq (RatFunc Fq)]

/-- The valuation at infinity is the nonarchimedean valuation on `Fq(t)` with uniformizer `1/t`.
Explicitly, if `f/g ∈ Fq(t)` is a nonzero quotient of polynomials, its valuation at infinity is
`Multiplicative.ofAdd(degree(f) - degree(g))`. -/
def inftyValuationDef (r : RatFunc Fq) : ℤₘ₀ :=
  if r = 0 then 0 else ↑(Multiplicative.ofAdd r.intDegree)

theorem InftyValuation.map_zero' : inftyValuationDef Fq 0 = 0 :=
  if_pos rfl

theorem InftyValuation.map_one' : inftyValuationDef Fq 1 = 1 :=
  (if_neg one_ne_zero).trans <| by rw [RatFunc.intDegree_one, ofAdd_zero, WithZero.coe_one]

theorem InftyValuation.map_mul' (x y : RatFunc Fq) :
    inftyValuationDef Fq (x * y) = inftyValuationDef Fq x * inftyValuationDef Fq y := by
  rw [inftyValuationDef, inftyValuationDef, inftyValuationDef]
  by_cases hx : x = 0
  · rw [hx, zero_mul, if_pos (Eq.refl _), zero_mul]
  · by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos (Eq.refl _), mul_zero]
    · rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← WithZero.coe_mul, WithZero.coe_inj,
        ← ofAdd_add, RatFunc.intDegree_mul hx hy]

theorem InftyValuation.map_add_le_max' (x y : RatFunc Fq) :
    inftyValuationDef Fq (x + y) ≤ max (inftyValuationDef Fq x) (inftyValuationDef Fq y) := by
  by_cases hx : x = 0
  · rw [hx, zero_add]
    conv_rhs => rw [inftyValuationDef, if_pos (Eq.refl _)]
    rw [max_eq_right (WithZero.zero_le (inftyValuationDef Fq y))]
  · by_cases hy : y = 0
    · rw [hy, add_zero]
      conv_rhs => rw [max_comm, inftyValuationDef, if_pos (Eq.refl _)]
      rw [max_eq_right (WithZero.zero_le (inftyValuationDef Fq x))]
    · by_cases hxy : x + y = 0
      · rw [inftyValuationDef, if_pos hxy]; exact zero_le'
      · rw [inftyValuationDef, inftyValuationDef, inftyValuationDef, if_neg hx, if_neg hy,
          if_neg hxy]
        rw [le_max_iff, WithZero.coe_le_coe, Multiplicative.ofAdd_le, WithZero.coe_le_coe,
          Multiplicative.ofAdd_le, ← le_max_iff]
        exact RatFunc.intDegree_add_le hy hxy

@[simp]
theorem inftyValuation_of_nonzero {x : RatFunc Fq} (hx : x ≠ 0) :
    inftyValuationDef Fq x = Multiplicative.ofAdd x.intDegree := by
  rw [inftyValuationDef, if_neg hx]

/-- The valuation at infinity on `Fq(t)`. -/
def inftyValuation : Valuation (RatFunc Fq) ℤₘ₀ where
  toFun := inftyValuationDef Fq
  map_zero' := InftyValuation.map_zero' Fq
  map_one' := InftyValuation.map_one' Fq
  map_mul' := InftyValuation.map_mul' Fq
  map_add_le_max' := InftyValuation.map_add_le_max' Fq

@[simp]
theorem inftyValuation_apply {x : RatFunc Fq} : inftyValuation Fq x = inftyValuationDef Fq x :=
  rfl

theorem inftyValuation.C {k : Fq} (hk : k ≠ 0) :
    inftyValuationDef Fq (RatFunc.C k) = Multiplicative.ofAdd (0 : ℤ) := by
  simp [hk]

@[simp]
theorem inftyValuation.X : inftyValuationDef Fq RatFunc.X = Multiplicative.ofAdd (1 : ℤ) := by
  rw [inftyValuationDef, if_neg RatFunc.X_ne_zero, RatFunc.intDegree_X]

-- Dropped attribute `@[simp]` due to issue described here:
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/.60synthInstance.2EmaxHeartbeats.60.20error.20but.20only.20in.20.60simpNF.60
theorem inftyValuation.polynomial {p : Fq[X]} (hp : p ≠ 0) :
    inftyValuationDef Fq (algebraMap Fq[X] (RatFunc Fq) p) =
      Multiplicative.ofAdd (p.natDegree : ℤ) := by
  have hp' : algebraMap Fq[X] (RatFunc Fq) p ≠ 0 := by simpa
  rw [inftyValuationDef, if_neg hp', RatFunc.intDegree_polynomial]

/-- The valued field `Fq(t)` with the valuation at infinity. -/
def inftyValuedFqt : Valued (RatFunc Fq) ℤₘ₀ :=
  Valued.mk' <| inftyValuation Fq

theorem inftyValuedFqt.def {x : RatFunc Fq} :
    @Valued.v (RatFunc Fq) _ _ _ (inftyValuedFqt Fq) x = inftyValuationDef Fq x :=
  rfl

/-- The completion `Fq((t⁻¹))` of `Fq(t)` with respect to the valuation at infinity. -/
def FqtInfty :=
  @UniformSpace.Completion (RatFunc Fq) <| (inftyValuedFqt Fq).toUniformSpace

instance : Field (FqtInfty Fq) :=
  letI := inftyValuedFqt Fq
  UniformSpace.Completion.instField

instance : Inhabited (FqtInfty Fq) :=
  ⟨(0 : FqtInfty Fq)⟩

/-- The valuation at infinity on `k(t)` extends to a valuation on `FqtInfty`. -/
instance valuedFqtInfty : Valued (FqtInfty Fq) ℤₘ₀ :=
  @Valued.valuedCompletion _ _ _ _ (inftyValuedFqt Fq)

theorem valuedFqtInfty.def {x : FqtInfty Fq} :
    Valued.v x = @Valued.extension (RatFunc Fq) _ _ _ (inftyValuedFqt Fq) x :=
  rfl

end InftyValuation

end FunctionField
