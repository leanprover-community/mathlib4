/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Algebra instances

This file contains several `Algebra` and `IsScalarTower` instances related to extensions
of a field with a valuation, as well as their unit balls.

# Main Definitions
* `ValuationSubring.algebra` : Given an algebra between two field extensions `L` and `E` of a
  field `K` with a valuation, create an algebra between their two rings of integers.

# Main Results

* `integralClosure_algebraMap_injective` : the unit ball of a field `K` with respect to a
  valuation injects into its integral closure in a field extension `L` of `K`.
-/

open Function Valuation
open scoped WithZero

variable {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰) (L : Type*) [Field L] [Algebra K L]

namespace ValuationSubring

-- Implementation note : this instance was automatic in Lean3
instance : Algebra v.valuationSubring L := Algebra.ofSubring v.valuationSubring.toSubring

theorem algebraMap_injective : Injective (algebraMap v.valuationSubring L) :=
  (FaithfulSMul.algebraMap_injective K L).comp (IsFractionRing.injective _ _)

theorem isIntegral_of_mem_ringOfIntegers {x : L} (hx : x ∈ integralClosure v.valuationSubring L) :
    IsIntegral v.valuationSubring (⟨x, hx⟩ : integralClosure v.valuationSubring L) := by
  obtain ⟨P, hPm, hP⟩ := hx
  refine ⟨P, hPm, ?_⟩
  rw [← Polynomial.aeval_def, ← Subalgebra.coe_eq_zero, Polynomial.aeval_subalgebra_coe,
    Polynomial.aeval_def, Subtype.coe_mk, hP]

theorem isIntegral_of_mem_ringOfIntegers' {x : (integralClosure v.valuationSubring L)} :
    IsIntegral v.valuationSubring (x : integralClosure v.valuationSubring L) := by
  apply isIntegral_of_mem_ringOfIntegers

variable (E : Type _) [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E]

instance : IsScalarTower v.valuationSubring L E := Subring.instIsScalarTowerSubtypeMem _

/-- Given an algebra between two field extensions `L` and `E` of a field `K` with a valuation `v`,
  create an algebra between their two rings of integers. -/
instance algebra :
    Algebra (integralClosure v.valuationSubring L) (integralClosure v.valuationSubring E) :=
  RingHom.toAlgebra
    { toFun := fun k => ⟨algebraMap L E k, IsIntegral.algebraMap k.2⟩
      map_zero' :=
        Subtype.ext <| by simp only [Subalgebra.coe_zero, map_zero]
      map_one' := Subtype.ext <| by simp only [Subalgebra.coe_one, map_one]
      map_add' := fun x y =>
        Subtype.ext <| by simp only [map_add, Subalgebra.coe_add]
      map_mul' := fun x y =>
        Subtype.ext <| by simp only [Subalgebra.coe_mul, map_mul] }

/-- A ring equivalence between the integral closure of the valuation subring of `K` in `L`
  and a ring `R` satisfying `isIntegralClosure R v.valuationSubring L`. -/
protected noncomputable def equiv (R : Type*) [CommRing R] [Algebra v.valuationSubring R]
    [Algebra R L] [IsScalarTower v.valuationSubring R L]
    [IsIntegralClosure R v.valuationSubring L] : integralClosure v.valuationSubring L ≃+* R := by
  have := IsScalarTower.subalgebra' (valuationSubring v) L L
    (integralClosure (valuationSubring v) L)
  exact (IsIntegralClosure.equiv v.valuationSubring R L
    (integralClosure v.valuationSubring L)).symm.toRingEquiv

theorem integralClosure_algebraMap_injective :
    Injective (algebraMap v.valuationSubring (integralClosure v.valuationSubring L)) :=
  FaithfulSMul.algebraMap_injective ↥v.valuationSubring ↥(integralClosure (↥v.valuationSubring) L)

end ValuationSubring
