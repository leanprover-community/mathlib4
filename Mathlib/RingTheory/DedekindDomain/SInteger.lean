/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation

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
    (⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.toSubring).copy
        {x : K | ∀ (v) (_ : v ∉ S), v.valuation K x ≤ 1} <|
      Set.ext fun _ => by simp [SetLike.mem_coe, Subring.mem_iInf] with
    algebraMap_mem' := fun x v _ => v.valuation_le_one x }

theorem integer_eq :
    (S.integer K).toSubring =
      ⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.toSubring :=
  SetLike.ext' <| by ext; simp

theorem integer_valuation_le_one (x : S.integer K) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    v.valuation K x ≤ 1 :=
  x.property v hv

/-- If `S` is the whole set of places of `K`, then the `S`-integers are the whole of `K`. -/
@[simp] lemma set_integer_top : (univ : Set (HeightOneSpectrum R)).integer K = ⊤ := by
  ext
  tauto

/--
If `S` is the empty set, then the `S`-integers are the minimal `R`-subalgebra of `K` (which is
just `R` itself).
-/
@[simp]
lemma set_integer_empty : (∅ : Set (HeightOneSpectrum R)).integer K = ⊥ := by
  ext x
  simp only [integer, mem_empty_iff_false, not_false_eq_true, true_implies]
  refine ⟨IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K x, ?_⟩
  rintro ⟨y, rfl⟩ v
  exact v.valuation_le_one y

variable (R) in
/-- Canonical `R`-algebra isomorphism from `R` to the `∅`-integers of `K`. -/
noncomputable def setIntegerEmptyEquiv : R ≃ₐ[R] (∅ : Set (HeightOneSpectrum R)).integer K :=
  .ofBijective ((Algebra.ofId R K : R →ₐ[R] K).codRestrict _
    (fun r ↦ by simpa only [set_integer_empty] using ⟨r, rfl⟩))
    ⟨fun x y ↦ by simp [← SetLike.coe_eq_coe, Algebra.ofId_apply],
      fun ⟨x, hx⟩ ↦ by simpa [← SetLike.coe_eq_coe, set_integer_empty, Algebra.mem_bot] using hx⟩

lemma setIntegerEmptyEquiv_apply (r : R) :
    setIntegerEmptyEquiv R K r = algebraMap R K r :=
  rfl

/-! ## `S`-units -/


/-- The subgroup of `S`-units of `Kˣ`. -/
@[simps!]
def unit : Subgroup Kˣ :=
  (⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.unitGroup).copy
      {x : Kˣ | ∀ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation K x = 1} <|
    Set.ext fun _ => by
      -- Porting note: was
      -- simpa only [SetLike.mem_coe, Subgroup.mem_iInf, Valuation.mem_unitGroup_iff]
      simp only [mem_setOf, SetLike.mem_coe, Subgroup.mem_iInf, Valuation.mem_unitGroup_iff]

theorem unit_eq :
    S.unit K = ⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.unitGroup :=
  Subgroup.copy_eq _ _ _

theorem unit_valuation_eq_one (x : S.unit K) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    v.valuation K (x : Kˣ) = 1 :=
  x.property v hv

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
          rw [Units.val_mk0, ← map_mul, Subtype.mk_eq_mk.mp x.val_inv, map_one]⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

end

end Set
