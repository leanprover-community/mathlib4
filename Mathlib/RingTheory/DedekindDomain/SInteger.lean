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
  -- I is the denominator ideal of z.
  let I := ∏ v ∈ T, v.asIdeal ^ (WithZero.log (v.valuation K z)).toNat
  have hI_ne_zero : I ≠ 0 := by
    simpa only [I, Finset.prod_ne_zero_iff, bot_eq_zero] using fun v _ ↦
      pow_ne_zero _ v.ne_bot
  /- Here we use the fact that the ClassGroup has finite order, so there exist `n > 0` and `α` such
  that `I ^ n = (α)`. This can be con  -/
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
  have hα_mem_pow {v : HeightOneSpectrum R} (hvT : v ∈ T) :
      α ∈ v.asIdeal ^ (WithZero.log (v.valuation K z)).toNat := by
    rw [← Ideal.span_singleton_le_iff_mem]
    calc
      Ideal.span {α} = R ∙ α := by rw [← Ideal.submodule_span_eq]
      _ = I ^ n := hα.symm
      _ ≤ I := Ideal.pow_le_self hn.ne'
      _ ≤ T.inf fun v ↦ v.asIdeal ^ (WithZero.log (v.valuation K z)).toNat :=
        Ideal.prod_le_inf
      _ ≤ v.asIdeal ^ (WithZero.log (v.valuation K z)).toNat :=
        Finset.inf_le hvT
  have hαz_valuation_le_one (v : HeightOneSpectrum R) :
      v.valuation K ((algebraMap R K α) * z) ≤ 1 := by
      by_cases hvT : v ∈ T
      · let e := (WithZero.log (v.valuation K z)).toNat
        calc
          (valuation K v) ((algebraMap R K) α * z)
            = v.valuation K (algebraMap R K α) * v.valuation K z := by rw [Valuation.map_mul]
          _ ≤ WithZero.exp (-(e : ℤ)) * WithZero.exp (e : ℤ) := by
                refine mul_le_mul' ?_ ?_
                · simpa [e, HeightOneSpectrum.valuation_of_algebraMap] using
                    (v.intValuation_le_pow_iff_mem α e).2 (by simpa [e] using hα_mem_pow hvT)
                · by_cases hz : v.valuation K z = 0
                  · simp [hz]
                  · exact (WithZero.log_le_iff_le_exp hz).1 (Int.self_le_toNat _)
          _ = 1 := by rw [← WithZero.exp_add]; simp
      · have hzle : v.valuation K z ≤ 1 :=
          by simpa [T, HeightOneSpectrum.Support] using hvT
        simpa [Valuation.map_mul] using
          mul_le_mul' (v.valuation_le_one α) hzle
  -- we can write `z * α = β` for some `β ∈ R`.
  obtain ⟨β, hβ⟩ : ∃ β : R, (algebraMap R K β) = ((algebraMap R K α) * z) :=
    mem_range.mp <| mem_integers_of_valuation_le_one (K := K) ((algebraMap R K α) * z)
    hαz_valuation_le_one
  refine ⟨β, α, ?_, ?_⟩
  ·
    simp only [Set.Submonoid, Submodule.carrier_eq_coe, Submonoid.mem_mk, Subsemigroup.mem_mk,
      mem_inter_iff, mem_iInter, mem_compl_iff, SetLike.mem_coe, mem_nonZeroDivisors_iff_ne_zero,
      ne_eq]
    refine ⟨?_, hα_ne_zero⟩
    intro v hvS hvα
    obtain ⟨w, hwT, hwle⟩ :=
      (Ideal.IsPrime.prod_le (s := T) (f := fun w : HeightOneSpectrum R =>
          w.asIdeal ^ (WithZero.log (w.valuation K (z : K))).toNat)
        v.isPrime).1 <| Ideal.IsPrime.le_of_pow_le (by
          rw [hα]
          exact (Ideal.span_singleton_le_iff_mem v.asIdeal).2 hvα)
    have hwle' : w.asIdeal ≤ v.asIdeal := Ideal.IsPrime.le_of_pow_le hwle
    have hw_eq : w = v :=
      HeightOneSpectrum.ext (Ideal.IsMaximal.eq_of_le w.isMaximal v.isPrime.ne_top' hwle')
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
