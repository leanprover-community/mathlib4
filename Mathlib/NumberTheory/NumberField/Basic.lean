/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Anne Baanen
-/
import Mathlib.Data.Int.Parity
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

#align_import number_theory.number_field.basic from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Number fields
This file defines a number field and the ring of integers corresponding to it.

## Main definitions
 - `NumberField` defines a number field as a field which has characteristic zero and is finite
    dimensional over ℚ.
 - `ringOfIntegers` defines the ring of integers (or number ring) corresponding to a number field
    as the integral closure of ℤ in the number field.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]

## Tags
number field, ring of integers
-/


/-- A number field is a field which has characteristic zero and is finite
dimensional over ℚ. -/
class NumberField (K : Type*) [Field K] : Prop where
  [to_charZero : CharZero K]
  [to_finiteDimensional : FiniteDimensional ℚ K]
#align number_field NumberField

open Function Module

open scoped Classical BigOperators nonZeroDivisors

/-- `ℤ` with its usual ring structure is not a field. -/
theorem Int.not_isField : ¬IsField ℤ := fun h =>
  Int.not_even_one <|
    (h.mul_inv_cancel two_ne_zero).imp fun a => by rw [← two_mul]; exact Eq.symm
#align int.not_is_field Int.not_isField

namespace NumberField

variable (K L : Type*) [Field K] [Field L] [nf : NumberField K]

-- See note [lower instance priority]
attribute [instance] NumberField.to_charZero NumberField.to_finiteDimensional

protected theorem isAlgebraic : Algebra.IsAlgebraic ℚ K :=
  Algebra.IsAlgebraic.of_finite _ _
#align number_field.is_algebraic NumberField.isAlgebraic

instance [NumberField L] [Algebra K L] : FiniteDimensional K L :=
  Module.Finite.of_restrictScalars_finite ℚ K L

/-- The ring of integers (or number ring) corresponding to a number field
is the integral closure of ℤ in the number field. -/
def ringOfIntegers :=
  integralClosure ℤ K
#align number_field.ring_of_integers NumberField.ringOfIntegers

@[inherit_doc] scoped notation "𝓞" => NumberField.ringOfIntegers

theorem mem_ringOfIntegers (x : K) : x ∈ 𝓞 K ↔ IsIntegral ℤ x :=
  Iff.rfl
#align number_field.mem_ring_of_integers NumberField.mem_ringOfIntegers

theorem isIntegral_of_mem_ringOfIntegers {K : Type*} [Field K] {x : K} (hx : x ∈ 𝓞 K) :
    IsIntegral ℤ (⟨x, hx⟩ : 𝓞 K) := by
  obtain ⟨P, hPm, hP⟩ := hx
  refine' ⟨P, hPm, _⟩
  rw [← Polynomial.aeval_def, ← Subalgebra.coe_eq_zero, Polynomial.aeval_subalgebra_coe,
    Polynomial.aeval_def, Subtype.coe_mk, hP]
#align number_field.is_integral_of_mem_ring_of_integers NumberField.isIntegral_of_mem_ringOfIntegers

/-- Given an algebra between two fields, create an algebra between their two rings of integers. -/
instance inst_ringOfIntegersAlgebra [Algebra K L] : Algebra (𝓞 K) (𝓞 L) :=
  RingHom.toAlgebra
    { toFun := fun k => ⟨algebraMap K L k, IsIntegral.algebraMap k.2⟩
      map_zero' := Subtype.ext <| by simp only [Subtype.coe_mk, Subalgebra.coe_zero, map_zero]
      map_one' := Subtype.ext <| by simp only [Subtype.coe_mk, Subalgebra.coe_one, map_one]
      map_add' := fun x y =>
        Subtype.ext <| by simp only [map_add, Subalgebra.coe_add, Subtype.coe_mk]
      map_mul' := fun x y =>
        Subtype.ext <| by simp only [Subalgebra.coe_mul, map_mul, Subtype.coe_mk] }
#align number_field.ring_of_integers_algebra NumberField.inst_ringOfIntegersAlgebra

-- no diamond
example : Algebra.id (𝓞 K) = inst_ringOfIntegersAlgebra K K := rfl

namespace RingOfIntegers

variable {K}

instance [NumberField K] : IsFractionRing (𝓞 K) K :=
  integralClosure.isFractionRing_of_finite_extension ℚ _

instance : IsIntegralClosure (𝓞 K) ℤ K :=
  integralClosure.isIntegralClosure _ _

instance [NumberField K] : IsIntegrallyClosed (𝓞 K) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension ℚ

theorem isIntegral_coe (x : 𝓞 K) : IsIntegral ℤ (x : K) :=
  x.2
#align number_field.ring_of_integers.is_integral_coe NumberField.RingOfIntegers.isIntegral_coe

theorem map_mem {F L : Type*} [Field L] [CharZero K] [CharZero L]
    [FunLike F K L] [AlgHomClass F ℚ K L] (f : F)
    (x : 𝓞 K) : f x ∈ 𝓞 L :=
  (mem_ringOfIntegers _ _).2 <| map_isIntegral_int f <| RingOfIntegers.isIntegral_coe x
#align number_field.ring_of_integers.map_mem NumberField.RingOfIntegers.map_mem

/-- The ring of integers of `K` are equivalent to any integral closure of `ℤ` in `K` -/
protected noncomputable def equiv (R : Type*) [CommRing R] [Algebra R K]
    [IsIntegralClosure R ℤ K] : 𝓞 K ≃+* R :=
  (IsIntegralClosure.equiv ℤ R K _).symm.toRingEquiv
#align number_field.ring_of_integers.equiv NumberField.RingOfIntegers.equiv

variable (K)

instance : CharZero (𝓞 K) :=
  CharZero.of_module _ K

instance : IsNoetherian ℤ (𝓞 K) :=
  IsIntegralClosure.isNoetherian _ ℚ K _

/-- The ring of integers of a number field is not a field. -/
theorem not_isField : ¬IsField (𝓞 K) := by
  have h_inj : Function.Injective (algebraMap ℤ (𝓞 K)) := RingHom.injective_int (algebraMap ℤ (𝓞 K))
  intro hf
  exact Int.not_isField
    (((IsIntegralClosure.isIntegral_algebra ℤ K).isField_iff_isField h_inj).mpr hf)
#align number_field.ring_of_integers.not_is_field NumberField.RingOfIntegers.not_isField

instance : IsDedekindDomain (𝓞 K) :=
  IsIntegralClosure.isDedekindDomain ℤ ℚ K _

instance : Free ℤ (𝓞 K) :=
  IsIntegralClosure.module_free ℤ ℚ K (𝓞 K)

instance : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) K :=
  IsIntegralClosure.isLocalization_of_isSeparable ℤ ℚ K (𝓞 K)

/-- A ℤ-basis of the ring of integers of `K`. -/
noncomputable def basis : Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℤ (𝓞 K) :=
  Free.chooseBasis ℤ (𝓞 K)
#align number_field.ring_of_integers.basis NumberField.RingOfIntegers.basis

end RingOfIntegers

/-- A basis of `K` over `ℚ` that is also a basis of `𝓞 K` over `ℤ`. -/
noncomputable def integralBasis : Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ K :=
  Basis.localizationLocalization ℚ (nonZeroDivisors ℤ) K (RingOfIntegers.basis K)
#align number_field.integral_basis NumberField.integralBasis

@[simp]
theorem integralBasis_apply (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    integralBasis K i = algebraMap (𝓞 K) K (RingOfIntegers.basis K i) :=
  Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) K (RingOfIntegers.basis K) i
#align number_field.integral_basis_apply NumberField.integralBasis_apply

theorem mem_span_integralBasis {x : K} :
    x ∈ Submodule.span ℤ (Set.range (integralBasis K)) ↔ x ∈ 𝓞 K := by
  rw [integralBasis, Basis.localizationLocalization_span, Subalgebra.range_isScalarTower_toAlgHom,
    Subalgebra.mem_toSubmodule]

theorem RingOfIntegers.rank : FiniteDimensional.finrank ℤ (𝓞 K) = FiniteDimensional.finrank ℚ K :=
  IsIntegralClosure.rank ℤ ℚ K (𝓞 K)
#align number_field.ring_of_integers.rank NumberField.RingOfIntegers.rank

end NumberField

namespace Rat

open NumberField

instance numberField : NumberField ℚ where
  to_charZero := inferInstance
  to_finiteDimensional := by
  -- The vector space structure of `ℚ` over itself can arise in multiple ways:
  -- all fields are vector spaces over themselves (used in `Rat.finiteDimensional`)
  -- all char 0 fields have a canonical embedding of `ℚ` (used in `NumberField`).
  -- Show that these coincide:
    convert (inferInstance : FiniteDimensional ℚ ℚ)
#align rat.number_field Rat.numberField

/-- The ring of integers of `ℚ` as a number field is just `ℤ`. -/
noncomputable def ringOfIntegersEquiv : ringOfIntegers ℚ ≃+* ℤ :=
  RingOfIntegers.equiv ℤ
#align rat.ring_of_integers_equiv Rat.ringOfIntegersEquiv

end Rat

namespace AdjoinRoot

section

open scoped Polynomial

attribute [-instance] algebraRat

/-- The quotient of `ℚ[X]` by the ideal generated by an irreducible polynomial of `ℚ[X]`
is a number field. -/
instance {f : Polynomial ℚ} [hf : Fact (Irreducible f)] : NumberField (AdjoinRoot f) where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  to_finiteDimensional := by convert (AdjoinRoot.powerBasis hf.out.ne_zero).finiteDimensional

end

end AdjoinRoot
