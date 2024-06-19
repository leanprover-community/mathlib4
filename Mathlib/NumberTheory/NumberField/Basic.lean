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
 - `RingOfIntegers` defines the ring of integers (or number ring) corresponding to a number field
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

open scoped Classical nonZeroDivisors

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
is the integral closure of ℤ in the number field.

This is defined as its own type, rather than a `Subalgebra`, for performance reasons:
looking for instances of the form `SMul (RingOfIntegers _) (RingOfIntegers _)` makes
much more effective use of the discrimination tree than instances of the form
`SMul (Subtype _) (Subtype _)`.
The drawback is we have to copy over instances manually.
-/
def RingOfIntegers : Type _ :=
  integralClosure ℤ K
#align number_field.ring_of_integers NumberField.RingOfIntegers

@[inherit_doc] scoped notation "𝓞" => NumberField.RingOfIntegers

#noalign number_field.mem_ring_of_integers

namespace RingOfIntegers

instance : CommRing (𝓞 K) :=
  inferInstanceAs (CommRing (integralClosure _ _))
instance : IsDomain (𝓞 K) :=
  inferInstanceAs (IsDomain (integralClosure _ _))
instance : CharZero (𝓞 K) :=
  inferInstanceAs (CharZero (integralClosure _ _))
instance : Algebra (𝓞 K) K :=
  inferInstanceAs (Algebra (integralClosure _ _) _)
instance : NoZeroSMulDivisors (𝓞 K) K :=
  inferInstanceAs (NoZeroSMulDivisors (integralClosure _ _) _)
instance : Nontrivial (𝓞 K) :=
  inferInstanceAs (Nontrivial (integralClosure _ _))
instance {L : Type*} [Ring L] [Algebra K L] : Algebra (𝓞 K) L :=
  inferInstanceAs (Algebra (integralClosure _ _) L)
instance {L : Type*} [Ring L] [Algebra K L] :  IsScalarTower (𝓞 K) K L :=
  inferInstanceAs (IsScalarTower (integralClosure _ _) K L)

variable {K}

/-- The canonical coercion from `𝓞 K` to `K`. -/
@[coe]
abbrev val (x : 𝓞 K) : K := algebraMap _ _ x

/-- This instance has to be `CoeHead` because we only want to apply it from `𝓞 K` to `K`. -/
instance : CoeHead (𝓞 K) K := ⟨val⟩

lemma coe_eq_algebraMap (x : 𝓞 K) : (x : K) = algebraMap _ _ x := rfl

@[ext] theorem ext {x y : 𝓞 K} (h : (x : K) = (y : K)) : x = y :=
  Subtype.ext h

theorem ext_iff {x y : 𝓞 K} : x = y ↔ (x : K) = (y : K) :=
  Subtype.ext_iff

@[norm_cast]
theorem eq_iff {x y : 𝓞 K} : (x : K) = (y : K) ↔ x = y :=
  NumberField.RingOfIntegers.ext_iff.symm

@[simp] lemma map_mk (x : K) (hx) : algebraMap (𝓞 K) K ⟨x, hx⟩ = x := rfl

lemma coe_mk {x : K} (hx) : ((⟨x, hx⟩ : 𝓞 K) : K) = x := rfl

lemma mk_eq_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) = ⟨y, hy⟩ ↔ x = y := by simp

@[simp] lemma mk_one : (⟨1, one_mem _⟩ : 𝓞 K) = 1 :=
  rfl

@[simp] lemma mk_zero : (⟨0, zero_mem _⟩ : 𝓞 K) = 0 :=
  rfl
-- TODO: these lemmas don't seem to fire?
@[simp] lemma mk_add_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) + ⟨y, hy⟩ = ⟨x + y, add_mem hx hy⟩ :=
  rfl

@[simp] lemma mk_mul_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩ :=
  rfl

@[simp] lemma mk_sub_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) - ⟨y, hy⟩ = ⟨x - y, sub_mem hx hy⟩ :=
  rfl

@[simp] lemma neg_mk (x : K) (hx) : (-⟨x, hx⟩ : 𝓞 K) = ⟨-x, neg_mem hx⟩ :=
  rfl

end RingOfIntegers

/-- Given an algebra between two fields, create an algebra between their two rings of integers. -/
instance inst_ringOfIntegersAlgebra [Algebra K L] : Algebra (𝓞 K) (𝓞 L) :=
  RingHom.toAlgebra
    { toFun := fun k => ⟨algebraMap K L (algebraMap _ K k), IsIntegral.algebraMap k.2⟩
      map_zero' := by ext; simp only [RingOfIntegers.map_mk, map_zero]
      map_one' := by ext; simp only [RingOfIntegers.map_mk, map_one]
      map_add' := fun x y => by ext; simp only [RingOfIntegers.map_mk, map_add]
      map_mul' := fun x y => by ext; simp only [RingOfIntegers.map_mk, map_mul] }
#align number_field.ring_of_integers_algebra NumberField.inst_ringOfIntegersAlgebra

-- diamond at `reducible_and_instances` #10906
example : Algebra.id (𝓞 K) = inst_ringOfIntegersAlgebra K K := rfl

namespace RingOfIntegers

variable {K}

/-- The canonical map from `𝓞 K` to `K` is injective.

This is a convenient abbreviation for `NoZeroSMulDivisors.algebraMap_injective`.
-/
lemma coe_injective : Function.Injective (algebraMap (𝓞 K) K) :=
  NoZeroSMulDivisors.algebraMap_injective _ _

/-- The canonical map from `𝓞 K` to `K` is injective.

This is a convenient abbreviation for `map_eq_zero_iff` applied to
`NoZeroSMulDivisors.algebraMap_injective`.
-/
@[simp] lemma coe_eq_zero_iff {x : 𝓞 K} : algebraMap _ K x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ coe_injective

/-- The canonical map from `𝓞 K` to `K` is injective.

This is a convenient abbreviation for `map_ne_zero_iff` applied to
`NoZeroSMulDivisors.algebraMap_injective`.
-/
lemma coe_ne_zero_iff {x : 𝓞 K} : algebraMap _ K x ≠ 0 ↔ x ≠ 0 :=
  map_ne_zero_iff _ coe_injective

theorem isIntegral_coe (x : 𝓞 K) : IsIntegral ℤ (algebraMap _ K x) :=
  x.2
#align number_field.ring_of_integers.is_integral_coe NumberField.RingOfIntegers.isIntegral_coe

theorem isIntegral (x : 𝓞 K) : IsIntegral ℤ x := by
  obtain ⟨P, hPm, hP⟩ := x.isIntegral_coe
  refine ⟨P, hPm, ?_⟩
  rwa [IsScalarTower.algebraMap_eq (S := 𝓞 K), ← Polynomial.hom_eval₂, coe_eq_zero_iff] at hP
#align number_field.is_integral_of_mem_ring_of_integers NumberField.RingOfIntegers.isIntegral

instance [NumberField K] : IsFractionRing (𝓞 K) K :=
  integralClosure.isFractionRing_of_finite_extension ℚ _

instance : IsIntegralClosure (𝓞 K) ℤ K :=
  integralClosure.isIntegralClosure _ _

instance [NumberField K] : IsIntegrallyClosed (𝓞 K) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension ℚ

#noalign number_field.ring_of_integers.map_mem

/-- The ring of integers of `K` are equivalent to any integral closure of `ℤ` in `K` -/
protected noncomputable def equiv (R : Type*) [CommRing R] [Algebra R K]
    [IsIntegralClosure R ℤ K] : 𝓞 K ≃+* R :=
  (IsIntegralClosure.equiv ℤ R K _).symm.toRingEquiv
#align number_field.ring_of_integers.equiv NumberField.RingOfIntegers.equiv

variable (K)

instance [CharZero K] : CharZero (𝓞 K) :=
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

variable {K} {M : Type*}

/-- Given `f : M → K` such that `∀ x, IsIntegral ℤ (f x)`, the corresponding function
`M → 𝓞 K`. -/
def restrict (f : M → K) (h : ∀ x, IsIntegral ℤ (f x)) (x : M) : 𝓞 K :=
  ⟨f x, h x⟩

/-- Given `f : M →+ K` such that `∀ x, IsIntegral ℤ (f x)`, the corresponding function
`M →+ 𝓞 K`. -/
def restrict_addMonoidHom [AddZeroClass M] (f : M →+ K) (h : ∀ x, IsIntegral ℤ (f x)) :
    M →+ 𝓞 K where
  toFun := restrict f h
  map_zero' := by simp only [restrict, map_zero, mk_zero]
  map_add' x y := by simp only [restrict, map_add, mk_add_mk _]

/-- Given `f : M →* K` such that `∀ x, IsIntegral ℤ (f x)`, the corresponding function
`M →* 𝓞 K`. -/
@[to_additive existing] -- TODO: why doesn't it figure this out by itself?
def restrict_monoidHom [MulOneClass M] (f : M →* K) (h : ∀ x, IsIntegral ℤ (f x)) : M →* 𝓞 K where
  toFun := restrict f h
  map_one' := by simp only [restrict, map_one, mk_one]
  map_mul' x y := by simp only [restrict, map_mul, mk_mul_mk _]

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

@[simp]
theorem integralBasis_repr_apply (x : (𝓞 K)) (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    (integralBasis K).repr (algebraMap _ _ x) i =
      (algebraMap ℤ ℚ) ((RingOfIntegers.basis K).repr x i) :=
  Basis.localizationLocalization_repr_algebraMap ℚ (nonZeroDivisors ℤ) K _ x i

theorem mem_span_integralBasis {x : K} :
    x ∈ Submodule.span ℤ (Set.range (integralBasis K)) ↔ x ∈ (algebraMap (𝓞 K) K).range := by
  rw [integralBasis, Basis.localizationLocalization_span, LinearMap.mem_range,
      IsScalarTower.coe_toAlgHom', RingHom.mem_range]

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
noncomputable def ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ :=
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
  to_finiteDimensional := by convert (AdjoinRoot.powerBasis hf.out.ne_zero).finite

end

end AdjoinRoot
