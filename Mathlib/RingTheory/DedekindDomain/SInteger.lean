/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation

#align_import ring_theory.dedekind_domain.S_integer from "leanprover-community/mathlib"@"00ab77614e085c9ef49479babba1a7d826d3232e"

/-!
# `S`-integers and `S`-units of fraction fields of Dedekind domains

Let `K` be the field of fractions of a Dedekind domain `R`, and let `S` be a set of prime ideals in
the height one spectrum of `R`. An `S`-integer of `K` is defined to have `v`-adic valuation at most
one for all primes ideals `v` away from `S`, whereas an `S`-unit of `Kˣ` is defined to have `v`-adic
valuation exactly one for all prime ideals `v` away from `S`.

This file defines the subalgebra of `S`-integers of `K` and the subgroup of `S`-units of `Kˣ`, where
`K` can be specialised to the case of a number field or a function field separately.

## Main definitions

 * `Set.integer`: `S`-integers.
 * `Set.unit`: `S`-units.
 * TODO: localised notation for `S`-integers.

## Main statements

 * `Set.unitEquivUnitsInteger`: `S`-units are units of `S`-integers.
 * TODO: proof that `S`-units is the kernel of a map to a product.
 * TODO: proof that `∅`-integers is the usual ring of integers.
 * TODO: finite generation of `S`-units and Dirichlet's `S`-unit theorem.

## References

 * [D Marcus, *Number Fields*][marcus1977number]
 * [J W S Cassels, A Frölich, *Algebraic Number Theory*][cassels1967algebraic]
 * [J Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

S integer, S-integer, S unit, S-unit
-/


namespace Set

noncomputable section

open IsDedekindDomain

open scoped nonZeroDivisors

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  (S : Set <| HeightOneSpectrum R) (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## `S`-integers -/


/-- The `R`-subalgebra of `S`-integers of `K`. -/
@[simps!]
def integer : Subalgebra R K :=
  {
    (⨅ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation.valuationSubring.toSubring).copy
        {x : K | ∀ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation x ≤ 1} <|
      Set.ext fun _ => by simp [SetLike.mem_coe, Subring.mem_iInf] with
    algebraMap_mem' := fun x v _ => v.valuation_le_one x }
#align set.integer Set.integer

theorem integer_eq :
    (S.integer K).toSubring =
      ⨅ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation.valuationSubring.toSubring :=
  SetLike.ext' <| by
    -- Porting note: was `simpa only [integer, Subring.copy_eq]`
    ext; simp
#align set.integer_eq Set.integer_eq

theorem integer_valuation_le_one (x : S.integer K) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    v.valuation (x : K) ≤ 1 :=
  x.property v hv
#align set.integer_valuation_le_one Set.integer_valuation_le_one

/-! ## `S`-units -/


/-- The subgroup of `S`-units of `Kˣ`. -/
@[simps!]
def unit : Subgroup Kˣ :=
  (⨅ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation.valuationSubring.unitGroup).copy
      {x : Kˣ | ∀ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation (x : K) = 1} <|
    Set.ext fun _ => by
      -- Porting note: was
      -- simpa only [SetLike.mem_coe, Subgroup.mem_iInf, Valuation.mem_unitGroup_iff]
      simp only [mem_setOf, SetLike.mem_coe, Subgroup.mem_iInf, Valuation.mem_unitGroup_iff]
#align set.unit Set.unit

theorem unit_eq :
    S.unit K = ⨅ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation.valuationSubring.unitGroup :=
  Subgroup.copy_eq _ _ _
#align set.unit_eq Set.unit_eq

theorem unit_valuation_eq_one (x : S.unit K) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    v.valuation ((x : Kˣ) : K) = 1 :=
  x.property v hv
#align set.unit_valuation_eq_one Set.unit_valuation_eq_one

-- Porting note: `apply_inv_coe` fails the simpNF linter
/-- The group of `S`-units is the group of units of the ring of `S`-integers. -/
@[simps apply_val_coe symm_apply_coe]
def unitEquivUnitsInteger : S.unit K ≃* (S.integer K)ˣ where
  toFun x :=
    ⟨⟨((x : Kˣ) : K), fun v hv => (x.property v hv).le⟩,
      ⟨((x⁻¹ : Kˣ) : K), fun v hv => (x⁻¹.property v hv).le⟩,
      Subtype.ext x.val.val_inv, Subtype.ext x.val.inv_val⟩
  invFun x :=
    ⟨Units.mk0 x fun hx => x.ne_zero (ZeroMemClass.coe_eq_zero.mp hx),
    fun v hv =>
      eq_one_of_one_le_mul_left (x.val.property v hv) (x.inv.property v hv) <|
        Eq.ge <| by
          -- Porting note: was
          -- rw [← map_mul]; convert v.valuation.map_one; exact subtype.mk_eq_mk.mp x.val_inv⟩
          rw [Units.val_mk0, ← map_mul, Subtype.mk_eq_mk.mp x.val_inv, v.valuation.map_one]⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl
#align set.unit_equiv_units_integer Set.unitEquivUnitsInteger

end

end Set
