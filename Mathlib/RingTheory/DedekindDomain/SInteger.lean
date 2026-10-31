/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

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
* `Localization.submonoid`: the submonoid of non-zero elements of `R` that are not contained in any
    prime ideal away from `S`.

## Main statements

* `IsDedekindDomain.isLocalizationSInteger`: The ring of `S`-integers is a localization of `R` if
  every class in the class group has finite order.
* `IsDedekindDomain.isDedekindDomainSInteger`: The ring of `S`-integers of a Dedekind domain with
  every class in the class group of finite order is a Dedekind domain.
* `Set.unitEquivUnitsInteger`: `S`-units are units of `S`-integers.
* `IsDedekindDomain.integer_empty`: `∅`-integers is the usual ring of integers.
* TODO: proof that `S`-units is the kernel of a map to a product.
* TODO: finite generation of `S`-units and Dirichlet's `S`-unit theorem.

## References

* [D Marcus, *Number Fields*][marcus1977number]
* [J W S Cassels, A Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

S integer, S-integer, S unit, S-unit
-/

@[expose] public section


noncomputable section

open IsDedekindDomain

open scoped nonZeroDivisors

universe u v

variable {R : Type u} [CommRing R]
  (S : Set <| HeightOneSpectrum R) (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## `S`-integers -/

namespace Set

variable [IsDedekindDomain R]

/-- The `R`-subalgebra of `S`-integers of `K`. -/
@[simps!]
def integer : Subalgebra R K :=
  {
    (⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.toSubring).copy
        {x : K | ∀ (v) (_ : v ∉ S), v.valuation K x ≤ 1} <|
      Set.ext fun _ => by simp [SetLike.mem_coe] with
    algebraMap_mem' := fun x v _ => v.valuation_le_one x }

theorem integer_eq :
    (S.integer K).toSubring =
      ⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.toSubring :=
  SetLike.ext' <| by ext; simp

theorem integer_valuation_le_one (x : S.integer K) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    v.valuation K x ≤ 1 :=
  x.property v hv

end Set

/-- The submonoid of non-zero elements of `R` that are not contained in any non-zero prime ideal
    away from `S`. -/
def Localization.submonoid : Submonoid R := Ideal.sInfPrimeCompl
  ((fun v : HeightOneSpectrum R ↦ v.asIdeal) '' Sᶜ)
  (by rintro _ ⟨v, _, rfl⟩; exact v.isPrime) ⊓ nonZeroDivisors R

@[simp]
lemma Localization.mem_submonoid_iff {r : R} :
    r ∈ Localization.submonoid S ↔ (∀ v ∈ Sᶜ, r ∉ v.asIdeal) ∧ r ∈ nonZeroDivisors R := by
  simp [Localization.submonoid]

@[simp]
lemma Localization.submonoid_eq_primeCompl (P : HeightOneSpectrum R) :
    submonoid {P}ᶜ = Ideal.primeCompl P ⊓ nonZeroDivisors R := by
  ext
  simp

lemma Localization.submonoid_le_nonZeroDivisors : Localization.submonoid S ≤ R⁰ := inf_le_right

namespace IsDedekindDomain

variable (R) [IsDedekindDomain R]

/-- If `S` is the whole set of places of `K`, then the `S`-integers are the whole of `K`. -/
@[simp] lemma integer_univ : (Set.univ : Set (HeightOneSpectrum R)).integer K = ⊤ := by
  ext
  tauto

/-- If `S` is the empty set, then the `S`-integers are the minimal `R`-subalgebra of `K` (which is
just `R` itself, via `Algebra.botEquivOfInjective` and `IsFractionRing.injective`). -/
@[simp] lemma integer_empty : (∅ : Set (HeightOneSpectrum R)).integer K = ⊥ := by
  ext x
  simp only [Set.integer, Set.mem_empty_iff_false, not_false_eq_true, true_implies]
  refine ⟨HeightOneSpectrum.mem_integers_of_valuation_le_one K x, ?_⟩
  rintro ⟨y, rfl⟩ v
  exact v.valuation_le_one y

open Ideal IsDedekindDomain.HeightOneSpectrum in
lemma exists_mul_algebraMap_eq_algebraMap [Fact (IsMulTorsion (ClassGroup R))]
    (z : S.integer K) : ∃ x : R × Localization.submonoid S,
      z * algebraMap R (S.integer K) x.2 = algebraMap R (S.integer K) x.1 := by
  -- `D` is the ideal of denominators of `z`.
  let D : Ideal R := (1 : Submodule R K).colon (Submodule.span R {(z : K)})
  have hD {r : R} : r ∈ D ↔ ∃ b : R, algebraMap R K b = algebraMap R K r * z := by
    simp [D, Submodule.mem_colon_singleton, Submodule.mem_one, Algebra.smul_def]
  have hD_ne_zero : D ≠ 0 := by
    obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj R⁰ (z : K)
    exact fun h0 ↦ nonZeroDivisors.ne_zero b.2 <| by
      simpa [h0] using hD.2 ⟨a, ((mul_comm _ _).trans h).symm⟩
  -- `D` is not contained in any prime `v ∉ S`, since `z` is a `v`-integer for such `v`.
  have hD_not_le {v : HeightOneSpectrum R} (hv : v ∉ S) : ¬ D ≤ v.asIdeal := fun hle ↦ by
    obtain ⟨n, d, hnd⟩ :=
      exists_primeCompl_mul_eq_of_integer v (z : K) (Set.integer_valuation_le_one S K z hv)
    exact d.2 (hle (hD.2 ⟨n, ((mul_comm _ _).trans hnd).symm⟩))
  -- Since the class group is torsion, `D ^ n = (α)` for some `n ≠ 0` and `α ∈ R`.
  have hD_mem : D ∈ (Ideal R)⁰ := mem_nonZeroDivisors_iff_ne_zero.2 hD_ne_zero
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 <|
    (Fact.out : IsMulTorsion (ClassGroup R)) (ClassGroup.mk0 ⟨D, hD_mem⟩)
  obtain ⟨α, hα⟩ : (D ^ n).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hD_mem n), ← hpow, ← map_pow]; rfl
  have hα_mem : α ∈ D := pow_le_self hn.ne' (hα ▸ Submodule.mem_span_singleton_self α)
  obtain ⟨β, hβ⟩ := hD.1 hα_mem
  have hα_mem' : α ∈ Localization.submonoid S := by
    rw [Localization.mem_submonoid_iff, mem_nonZeroDivisors_iff_ne_zero]
    refine ⟨?_, ?_⟩
    · rintro v hv hαv
      exact hD_not_le hv <| IsPrime.le_of_pow_le <|
        hα.trans_le ((span_singleton_le_iff_mem v.asIdeal).2 hαv)
    · rintro rfl
      exact hD_ne_zero (pow_eq_zero_iff hn.ne' |>.1 (by simpa using hα))
  exact ⟨(β, ⟨α, hα_mem'⟩), SetLike.coe_eq_coe.mp ((hβ.trans (mul_comm _ _)).symm)⟩

instance [Finite (ClassGroup R)] : Fact (IsMulTorsion (ClassGroup R)) := ⟨isMulTorsion_of_finite⟩

/-- When every class in the class group has finite order, the ring of `S`-integers is a localization
  of `R` at the multiplicative set `S`. -/
instance isLocalizationSInteger [Fact (IsMulTorsion (ClassGroup R))] :
    IsLocalization (Localization.submonoid S) <| S.integer K where
  map_units := by
    rintro ⟨r, hr⟩
    have h₀ : algebraMap R K r ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr.2
    refine ⟨⟨⟨_, fun v _ ↦ v.valuation_le_one r⟩, ⟨(algebraMap R K r)⁻¹,
        fun _ _ ↦ by simp_all [HeightOneSpectrum.valuation_of_algebraMap,
          HeightOneSpectrum.intValuation_eq_one_iff.2]⟩,
      by simp [Subtype.ext_iff, h₀], by simp [Subtype.ext_iff, h₀]⟩, rfl⟩
  surj := exists_mul_algebraMap_eq_algebraMap R S K
  exists_of_eq := fun h ↦
    ⟨1, by simpa using (IsFractionRing.injective R K (congrArg Subtype.val h))⟩

/-- The ring of `S`-integers is a Dedekind domain when every element in class group has finite
  order. -/
instance isDedekindDomainSInteger [Fact (IsMulTorsion (ClassGroup R))] :
    IsDedekindDomain (S.integer K) :=
  IsLocalization.isDedekindDomain _ (Localization.submonoid_le_nonZeroDivisors S) _

end IsDedekindDomain

/-! ## `S`-units -/

namespace Set

variable [IsDedekindDomain R]

/-- The subgroup of `S`-units of `Kˣ`. -/
@[simps!]
def unit : Subgroup Kˣ :=
  (⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.unitGroup).copy
      {x : Kˣ | ∀ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation K x = 1} <|
    Set.ext fun _ => by
      simp only [mem_ofPred, SetLike.mem_coe, Subgroup.mem_iInf, Valuation.mem_unitGroup_iff]

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
          rw [← map_mul, Units.val_mk0, Subtype.mk_eq_mk.mp x.val_inv, map_one]⟩
  map_mul' _ _ := by ext; rfl

end Set
