/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

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

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  (S : Set <| HeightOneSpectrum R) (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## `S`-integers -/

namespace Set

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

/-- The submonoid of non-zero elements of `R` that are not contained in any prime ideal in `S`. -/
def Submonoid : Submonoid R := {
  carrier := (⋂ (v : HeightOneSpectrum R) (_ : v ∉ S), (v.asIdeal.carrier)ᶜ) ∩ (nonZeroDivisors R)
  mul_mem' := by
    rintro _ _ ⟨ha, ha0⟩ ⟨hb, hb0⟩
    simp only [mem_iInter, mem_inter_iff] at ha hb ⊢
    exact ⟨fun v hv ↦ v.isPrime.mul_notMem (ha v hv) (hb v hv), (nonZeroDivisors R).mul_mem ha0 hb0⟩
  one_mem' := by simpa using fun i (_ : i ∉ S) ↦ i.asIdeal.one_notMem
}

end Set

namespace IsDedekindDomain

variable (R)

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

open IsDedekindDomain.HeightOneSpectrum Set in
private lemma sur [Fact (Monoid.IsTorsion (ClassGroup R))] :
    ∀ z : S.integer K, ∃ x : R × S.Submonoid,
    z * (algebraMap R (S.integer K)) x.2 = (algebraMap R (S.integer K)) x.1 := by
  intro z
  simp only [Prod.exists, Subtype.exists, exists_prop]
  -- We know that `v(z) ≤ 1` for all `ν ∉ S`.
  have h_outside : ∀ v ∉ S, v.valuation K z ≤ 1 := fun _ h ↦ integer_valuation_le_one S K z h
  -- Let T be the finite set of places in S that have `v(z) > 1`.
  let T : Finset (HeightOneSpectrum R) :=
    (HeightOneSpectrum.Support.finite (R := R) (K := K) (k := (z : K))).toFinset
  have hT_subset : ∀ v ∈ T, v ∈ S := by
    intro v hv
    contrapose! hv
    simpa [T, HeightOneSpectrum.Support] using h_outside v hv
  -- I is the product of the prime ideals that divide the denominator of z.
  let I : Ideal R := ∏ v ∈ T, v.asIdeal
  have hI_ne_zero : I ≠ 0 := by
    simpa only [I, Finset.prod_ne_zero_iff, bot_eq_zero] using fun v _ ↦ v.ne_bot
  -- Here we use the fact that the ClassGroup has finite order, so there exist n > 0 and α such that
  -- I^n = (α).
  obtain ⟨n, hn, ⟨α, hα⟩⟩ : ∃ n : ℕ, 0 < n ∧ (I ^ n).IsPrincipal := by
    let I₀ : (Ideal R)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne_zero⟩
    obtain ⟨n, hn, _⟩ := isOfFinOrder_iff_pow_eq_one.1
      ((Fact.out : Monoid.IsTorsion (ClassGroup R)) (ClassGroup.mk0 I₀))
    refine ⟨n, hn, ?_⟩
    simp_all [← MonoidHom.map_pow ClassGroup.mk0 I₀ n, ClassGroup.mk0_eq_one_iff, I₀]
  have hα_ne_zero : α ≠ 0 := by
    contrapose! hI_ne_zero
    subst hI_ne_zero
    rw [Submodule.span_zero_singleton, ← Ideal.zero_eq_bot] at hα
    exact eq_zero_of_pow_eq_zero hα

  -- This α : R has to satisfy v(α) ≥ 1 if v ∈ T [and v(α) ≥ 0 elsewise].
  have h1 : ∀ v ∈ T, v.valuation K (algebraMap R K α) < 1 := by
    intro v hv
    rw [valuation_lt_one_iff_mem, ← Ideal.span_singleton_le_iff_mem]
    change R ∙ α ≤ v.asIdeal
    rw [← hα]
    exact (Ideal.pow_le_self hn.ne').trans <|
      (Ideal.prod_le_inf (s := T) (f := fun w : HeightOneSpectrum R => w.asIdeal)).trans
        (Finset.inf_le hv)

  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ v ∈ T,
      v.valuation K ((algebraMap R K α ^ m) * z) ≤ 1 := by
    let m : ℕ := ∑ v ∈ T, (WithZero.log (v.valuation K (z : K))).toNat
    refine ⟨m, ?_⟩
    intro v hv
    let a : WithZero (Multiplicative ℤ) := v.valuation K (algebraMap R K α)
    let b : WithZero (Multiplicative ℤ) := v.valuation K (z : K)
    have hval :
        v.valuation K ((algebraMap R K α ^ m) * z) = a ^ m * b := by
      simp [a, b, Valuation.map_mul]
    rw [hval]
    by_cases hb : b = 0
    · simp [hb]
    have ha : a ≠ 0 := by
      simpa [a, Valuation.ne_zero_iff] using
        (FaithfulSMul.algebraMap_eq_zero_iff R K).not.mpr hα_ne_zero
    have hloga_le : WithZero.log a ≤ (-1 : ℤ) := by
      have : WithZero.log a < 0 := by
        simpa using (WithZero.log_lt_log ha one_ne_zero).2 (by simpa [a] using h1 v hv)
      omega
    have hlogb_le : WithZero.log b ≤ (m : ℤ) := by
      refine (Int.self_le_toNat _).trans ?_
      dsimp [b, m]
      exact_mod_cast Finset.single_le_sum
        (s := T) (f := fun w : HeightOneSpectrum R =>
          (WithZero.log (w.valuation K (z : K))).toNat)
        (fun w hw => Nat.zero_le _) hv
    have hlog : WithZero.log (a ^ m * b) ≤ 0 := by
      rw [WithZero.log_mul (pow_ne_zero m ha) hb, WithZero.log_pow]
      simpa using add_le_add (nsmul_le_nsmul_right hloga_le m) hlogb_le
    rw [← WithZero.log_le_log (mul_ne_zero (pow_ne_zero m ha) hb) one_ne_zero]
    simpa using hlog

  obtain ⟨β, hβ⟩ : ∃ β : R, (algebraMap R K β) = ((algebraMap R K α ^ m) * z) := by
    have hx : ∀ v : HeightOneSpectrum R, v.valuation K ((algebraMap R K α ^ m) * z) ≤ 1 := by
      intro v
      by_cases hvT : v ∈ T
      · exact hm v hvT
      · have hzle : v.valuation K z ≤ 1 := by
          by_cases hvS : v ∈ S
          · exact le_of_not_gt (by simpa [T, HeightOneSpectrum.Support] using hvT)
          · exact h_outside v hvS
        simpa [Valuation.map_mul] using
          mul_le_mul' (by simpa [map_pow] using (v.valuation_le_one (K := K) (α ^ m))) hzle
    simpa [Set.mem_range] using
      (HeightOneSpectrum.mem_integers_of_valuation_le_one (R := R) (K := K)
        ((algebraMap R K α ^ m) * z) hx)
  refine ⟨β, α ^ m, ?_, ?_⟩
  · refine Submonoid.pow_mem S.Submonoid ?_ m
    simp only [Set.Submonoid, Submodule.carrier_eq_coe, Submonoid.mem_mk, Subsemigroup.mem_mk,
      mem_inter_iff, mem_iInter, mem_compl_iff, SetLike.mem_coe, mem_nonZeroDivisors_iff_ne_zero,
      ne_eq]
    refine ⟨?_, hα_ne_zero⟩
    intro v hvS hvα
    obtain ⟨w, hwT, hwle⟩ :=
      (Ideal.IsPrime.prod_le (s := T) (f := fun w : HeightOneSpectrum R => w.asIdeal)
        v.isPrime).1 <| Ideal.IsPrime.le_of_pow_le (by
          rw [hα]
          exact (Ideal.span_singleton_le_iff_mem v.asIdeal).2 hvα)
    have hw_eq : w = v :=
      HeightOneSpectrum.ext (Ideal.IsMaximal.eq_of_le w.isMaximal v.isPrime.ne_top' hwle)
    exact hvS (hT_subset v (by simpa [hw_eq] using hwT))
  · ext
    simpa [mul_comm, mul_left_comm, mul_assoc] using hβ.symm


end IsDedekindDomain
/-! ## `S`-units -/

namespace Set

/-- The subgroup of `S`-units of `Kˣ`. -/
@[simps!]
def unit : Subgroup Kˣ :=
  (⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.unitGroup).copy
      {x : Kˣ | ∀ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation K x = 1} <|
    Set.ext fun _ => by
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
          rw [← map_mul, Units.val_mk0, Subtype.mk_eq_mk.mp x.val_inv, map_one]⟩
  map_mul' _ _ := by ext; rfl

end Set
