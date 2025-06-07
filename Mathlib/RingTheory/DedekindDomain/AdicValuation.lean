/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Data.Int.WithZero
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Adic valuations on Dedekind domains
Given a Dedekind domain `R` of Krull dimension 1 and a maximal ideal `v` of `R`, we define the
`v`-adic valuation on `R` and its extension to the field of fractions `K` of `R`.
We prove several properties of this valuation, including the existence of uniformizers.

We define the completion of `K` with respect to the `v`-adic valuation, denoted
`v.adicCompletion`, and its ring of integers, denoted `v.adicCompletionIntegers`.

## Main definitions
- `IsDedekindDomain.HeightOneSpectrum.intValuation v` is the `v`-adic valuation on `R`.
- `IsDedekindDomain.HeightOneSpectrum.valuation v` is the `v`-adic valuation on `K`.
- `IsDedekindDomain.HeightOneSpectrum.adicCompletion v` is the completion of `K` with respect
  to its `v`-adic valuation.
- `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers v` is the ring of integers of
  `v.adicCompletion`.
- `IsDedekindDomain.HeightOneSpectrum.adicAbv v`is the `v`-adic absolute value on `K` defined as `b`
  raised to negative `v`-adic valuation, for some `b` in `ℝ≥0`.

## Main results
- `IsDedekindDomain.HeightOneSpectrum.intValuation_le_one` : The `v`-adic valuation on `R` is
  bounded above by 1.
- `IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd` : The `v`-adic valuation of
  `r ∈ R` is less than 1 if and only if `v` divides the ideal `(r)`.
- `IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd` : The `v`-adic valuation of
  `r ∈ R` is less than or equal to `Multiplicative.ofAdd (-n)` if and only if `vⁿ` divides the
  ideal `(r)`.
- `IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer` : There exists `π ∈ R`
  with `v`-adic valuation `Multiplicative.ofAdd (-1)`.
- `IsDedekindDomain.HeightOneSpectrum.valuation_of_mk'` : The `v`-adic valuation of `r/s ∈ K`
  is the valuation of `r` divided by the valuation of `s`.
- `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap` : The `v`-adic valuation on `K`
  extends the `v`-adic valuation on `R`.
- `IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer` : There exists `π ∈ K` with
  `v`-adic valuation `Multiplicative.ofAdd (-1)`.

## Implementation notes
We are only interested in Dedekind domains with Krull dimension 1.

## References
* [G. J. Janusz, *Algebraic Number Fields*][janusz1996]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags
dedekind domain, dedekind ring, adic valuation
-/

noncomputable section

open scoped Multiplicative

open Multiplicative IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K S : Type*} [Field K] [CommSemiring S]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

namespace IsDedekindDomain.HeightOneSpectrum

/-! ### Adic valuations on the Dedekind domain R -/

open scoped Classical in
/-- The additive `v`-adic valuation of `r ∈ R` is the exponent of `v` in the factorization of the
ideal `(r)`, if `r` is nonzero, or infinity, if `r = 0`. `intValuationDef` is the corresponding
multiplicative valuation. -/
def intValuationDef (r : R) : ℤₘ₀ :=
  if r = 0 then 0
  else
    ↑(Multiplicative.ofAdd
      (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ))

theorem intValuationDef_if_pos {r : R} (hr : r = 0) : v.intValuationDef r = 0 :=
  if_pos hr

@[simp]
theorem intValuationDef_zero : v.intValuationDef 0 = 0 :=
  if_pos rfl

open scoped Classical in
theorem intValuationDef_if_neg {r : R} (hr : r ≠ 0) :
    v.intValuationDef r =
      Multiplicative.ofAdd
        (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ) :=
  if_neg hr


/-- The `v`-adic valuation of `0 : R` equals 0. -/
theorem intValuation.map_zero' : v.intValuationDef 0 = 0 :=
  v.intValuationDef_if_pos (Eq.refl 0)

/-- The `v`-adic valuation of `1 : R` equals 1. -/
theorem intValuation.map_one' : v.intValuationDef 1 = 1 := by
  classical
  rw [v.intValuationDef_if_neg (zero_ne_one.symm : (1 : R) ≠ 0), Ideal.span_singleton_one, ←
    Ideal.one_eq_top, Associates.mk_one, Associates.factors_one,
    Associates.count_zero (by apply v.associates_irreducible), Int.ofNat_zero, neg_zero, ofAdd_zero,
    WithZero.coe_one]

/-- The `v`-adic valuation of a product equals the product of the valuations. -/
theorem intValuation.map_mul' (x y : R) :
    v.intValuationDef (x * y) = v.intValuationDef x * v.intValuationDef y := by
  classical
  simp only [intValuationDef]
  by_cases hx : x = 0
  · rw [hx, zero_mul, if_pos (Eq.refl _), zero_mul]
  · by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos (Eq.refl _), mul_zero]
    · rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← WithZero.coe_mul, WithZero.coe_inj, ←
        ofAdd_add, ← Ideal.span_singleton_mul_span_singleton, ← Associates.mk_mul_mk, ← neg_add,
        Associates.count_mul (by apply Associates.mk_ne_zero'.mpr hx)
          (by apply Associates.mk_ne_zero'.mpr hy) (by apply v.associates_irreducible)]
      rfl

theorem intValuation.le_max_iff_min_le {a b c : ℕ} :
    Multiplicative.ofAdd (-c : ℤ) ≤
      max (Multiplicative.ofAdd (-a : ℤ)) (Multiplicative.ofAdd (-b : ℤ)) ↔
      min a b ≤ c := by
  rw [le_max_iff, ofAdd_le, ofAdd_le, neg_le_neg_iff, neg_le_neg_iff, Int.ofNat_le, Int.ofNat_le, ←
    min_le_iff]

/-- The `v`-adic valuation of a sum is bounded above by the maximum of the valuations. -/
theorem intValuation.map_add_le_max' (x y : R) :
    v.intValuationDef (x + y) ≤ max (v.intValuationDef x) (v.intValuationDef y) := by
  classical
  by_cases hx : x = 0
  · rw [hx, zero_add]
    conv_rhs => rw [intValuationDef, if_pos (Eq.refl _)]
    rw [max_eq_right (WithZero.zero_le (v.intValuationDef y))]
  · by_cases hy : y = 0
    · rw [hy, add_zero]
      conv_rhs => rw [max_comm, intValuationDef, if_pos (Eq.refl _)]
      rw [max_eq_right (WithZero.zero_le (v.intValuationDef x))]
    · by_cases hxy : x + y = 0
      · rw [intValuationDef, if_pos hxy]; exact zero_le'
      · rw [v.intValuationDef_if_neg hxy, v.intValuationDef_if_neg hx, v.intValuationDef_if_neg hy,
          WithZero.le_max_iff, intValuation.le_max_iff_min_le]
        set nmin :=
          min ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span { x })).factors)
            ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span { y })).factors)
        have h_dvd_x : x ∈ v.asIdeal ^ nmin := by
          rw [← Associates.le_singleton_iff x nmin _,
            Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hx) _]
          · exact min_le_left _ _
          apply v.associates_irreducible
        have h_dvd_y : y ∈ v.asIdeal ^ nmin := by
          rw [← Associates.le_singleton_iff y nmin _,
            Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hy) _]
          · exact min_le_right _ _
          apply v.associates_irreducible
        have h_dvd_xy : Associates.mk v.asIdeal ^ nmin ≤ Associates.mk (Ideal.span {x + y}) := by
          rw [Associates.le_singleton_iff]
          exact Ideal.add_mem (v.asIdeal ^ nmin) h_dvd_x h_dvd_y
        rw [Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hxy) _] at h_dvd_xy
        · exact h_dvd_xy
        apply v.associates_irreducible

/-- The `v`-adic valuation on `R`. -/
def intValuation : Valuation R ℤₘ₀ where
  toFun := v.intValuationDef
  map_zero' := intValuation.map_zero' v
  map_one' := intValuation.map_one' v
  map_mul' := intValuation.map_mul' v
  map_add_le_max' := intValuation.map_add_le_max' v

theorem intValuation_apply {r : R} (v : IsDedekindDomain.HeightOneSpectrum R) :
    intValuation v r = intValuationDef v r := rfl

open scoped Classical in
theorem intValuation_def {r : R} :
    v.intValuation r = if r = 0 then 0 else
    ↑(Multiplicative.ofAdd
      (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ)) :=
  rfl

@[deprecated intValuation_apply (since := "2025-04-26")]
theorem intValuation_toFun (r : R) :
    v.intValuation r = v.intValuationDef r := rfl

open scoped Classical in
theorem intValuation_if_neg {r : R} (hr : r ≠ 0) :
    v.intValuation r =
      Multiplicative.ofAdd
        (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ) :=
  intValuationDef_if_neg _ hr

/-- Nonzero elements have nonzero adic valuation. -/
theorem intValuation_ne_zero (x : R) (hx : x ≠ 0) : v.intValuation x ≠ 0 := by
  rw [v.intValuation_if_neg hx]
  exact WithZero.coe_ne_zero

/-- Nonzero divisors have nonzero valuation. -/
theorem intValuation_ne_zero' (x : nonZeroDivisors R) : v.intValuation x ≠ 0 :=
  v.intValuation_ne_zero x (nonZeroDivisors.coe_ne_zero x)

/-- Nonzero divisors have valuation greater than zero. -/
theorem intValuation_zero_lt (x : nonZeroDivisors R) : 0 < v.intValuation x := by
  rw [v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero x)]
  exact WithZero.zero_lt_coe _

@[deprecated (since := "2025-05-11")]
alias intValuation_zero_le := intValuation_zero_lt

/-- The `v`-adic valuation on `R` is bounded above by 1. -/
theorem intValuation_le_one (x : R) : v.intValuation x ≤ 1 := by
  by_cases hx : x = 0
  · rw [hx, Valuation.map_zero]; exact WithZero.zero_le 1
  · rw [v.intValuation_if_neg hx, ← WithZero.coe_one, ← ofAdd_zero, WithZero.coe_le_coe, ofAdd_le,
      Right.neg_nonpos_iff]
    exact Int.natCast_nonneg _

/-- The `v`-adic valuation of `r ∈ R` is less than 1 if and only if `v` divides the ideal `(r)`. -/
theorem intValuation_lt_one_iff_dvd (r : R) :
    v.intValuation r < 1 ↔ v.asIdeal ∣ Ideal.span {r} := by
  classical
  by_cases hr : r = 0
  · simp [hr]
  · rw [v.intValuation_if_neg hr, ← WithZero.coe_one, ← ofAdd_zero, WithZero.coe_lt_coe, ofAdd_lt,
      neg_lt_zero, ← Int.ofNat_zero, Int.ofNat_lt, zero_lt_iff]
    have h : (Ideal.span {r} : Ideal R) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hr
    apply Associates.count_ne_zero_iff_dvd h (by apply v.irreducible)

/-- The `v`-adic valuation of `r ∈ R` is less than 1 if and only if `r ∈ v`. -/
theorem intValuation_lt_one_iff_mem (r : R) :
    v.intValuation r < 1 ↔ r ∈ v.asIdeal := by
  rw [intValuation_lt_one_iff_dvd, Ideal.dvd_span_singleton]

/-- The `v`-adic valuation of `r ∈ R` is less than `Multiplicative.ofAdd (-n)` if and only if
`vⁿ` divides the ideal `(r)`. -/
theorem intValuation_le_pow_iff_dvd (r : R) (n : ℕ) :
    v.intValuation r ≤ Multiplicative.ofAdd (-(n : ℤ)) ↔ v.asIdeal ^ n ∣ Ideal.span {r} := by
  classical
  by_cases hr : r = 0
  · simp_rw [hr, Valuation.map_zero, Ideal.dvd_span_singleton, zero_le', Submodule.zero_mem]
  · rw [v.intValuation_if_neg hr, WithZero.coe_le_coe, ofAdd_le, neg_le_neg_iff, Int.ofNat_le,
      Ideal.dvd_span_singleton, ← Associates.le_singleton_iff,
      Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hr)
        (by apply v.associates_irreducible)]

/-- The `v`-adic valuation of `r ∈ R` is less than `Multiplicative.ofAdd (-n)` if and only if
`r ∈ vⁿ`. -/
theorem intValuation_le_pow_iff_mem (r : R) (n : ℕ) :
    v.intValuation r ≤ Multiplicative.ofAdd (-(n : ℤ)) ↔ r ∈ v.asIdeal ^ n := by
  rw [intValuation_le_pow_iff_dvd, Ideal.dvd_span_singleton]

/-- There exists `π ∈ R` with `v`-adic valuation `Multiplicative.ofAdd (-1)`. -/
theorem intValuation_exists_uniformizer :
    ∃ π : R, v.intValuation π = Multiplicative.ofAdd (-1 : ℤ) := by
  classical
  have hv : _root_.Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  have hlt : v.asIdeal ^ 2 < v.asIdeal := by
    rw [← Ideal.dvdNotUnit_iff_lt]
    exact
      ⟨v.ne_bot, v.asIdeal, (not_congr Ideal.isUnit_iff).mpr (Ideal.IsPrime.ne_top v.isPrime),
        sq v.asIdeal⟩
  obtain ⟨π, mem, notMem⟩ := SetLike.exists_of_lt hlt
  have hπ : Associates.mk (Ideal.span {π}) ≠ 0 := by
    rw [Associates.mk_ne_zero']
    intro h
    rw [h] at notMem
    exact notMem (Submodule.zero_mem (v.asIdeal ^ 2))
  use π
  rw [intValuation_if_neg _ (Associates.mk_ne_zero'.mp hπ), WithZero.coe_inj]
  apply congr_arg
  rw [neg_inj, ← Int.ofNat_one, Int.natCast_inj]
  rw [← Ideal.dvd_span_singleton, ← Associates.mk_le_mk_iff_dvd] at mem notMem
  rw [← pow_one (Associates.mk v.asIdeal), Associates.prime_pow_dvd_iff_le hπ hv] at mem
  rw [Associates.mk_pow, Associates.prime_pow_dvd_iff_le hπ hv, not_le] at notMem
  exact Nat.eq_of_le_of_lt_succ mem notMem

/-- The `I`-adic valuation of a generator of `I` equals `(-1 : ℤₘ₀)` -/
theorem intValuation_singleton {r : R} (hr : r ≠ 0) (hv : v.asIdeal = Ideal.span {r}) :
    v.intValuation r = Multiplicative.ofAdd (-1 : ℤ) := by
  classical
  rw [v.intValuation_if_neg hr, ← hv, Associates.count_self, Int.ofNat_one,
    ofAdd_neg, WithZero.coe_inv]
  apply v.associates_irreducible

/-! ### Adic valuations on the field of fractions `K` -/

variable (K) in
/-- The `v`-adic valuation of `x ∈ K` is the valuation of `r` divided by the valuation of `s`,
where `r` and `s` are chosen so that `x = r/s`. -/
def valuation (v : HeightOneSpectrum R) : Valuation K ℤₘ₀ :=
  v.intValuation.extendToLocalization
    (fun r hr => Set.mem_compl <| v.intValuation_ne_zero' ⟨r, hr⟩) K

theorem valuation_def (x : K) :
    v.valuation K x =
      v.intValuation.extendToLocalization
        (fun r hr => Set.mem_compl (v.intValuation_ne_zero' ⟨r, hr⟩)) K x :=
  rfl

/-- The `v`-adic valuation of `r/s ∈ K` is the valuation of `r` divided by the valuation of `s`. -/
theorem valuation_of_mk' {r : R} {s : nonZeroDivisors R} :
    v.valuation K (IsLocalization.mk' K r s) = v.intValuation r / v.intValuation s := by
  rw [valuation_def, Valuation.extendToLocalization_mk', div_eq_mul_inv]

open scoped algebraMap in
/-- The `v`-adic valuation on `K` extends the `v`-adic valuation on `R`. -/
theorem valuation_of_algebraMap (r : R) : v.valuation K r = v.intValuation r := by
  rw [valuation_def, Valuation.extendToLocalization_apply_map_apply]

open scoped algebraMap in
@[deprecated valuation_of_algebraMap (since := "2025-05-11")]
lemma valuation_eq_intValuationDef (r : R) : v.valuation K r = v.intValuationDef r :=
  Valuation.extendToLocalization_apply_map_apply ..

open scoped algebraMap in
/-- The `v`-adic valuation on `R` is bounded above by 1. -/
theorem valuation_le_one (r : R) : v.valuation K r ≤ 1 := by
  rw [valuation_of_algebraMap]; exact v.intValuation_le_one r

open scoped algebraMap in
/-- The `v`-adic valuation of `r ∈ R` is less than 1 if and only if `v` divides the ideal `(r)`. -/
theorem valuation_lt_one_iff_dvd (r : R) :
    v.valuation K r < 1 ↔ v.asIdeal ∣ Ideal.span {r} := by
  rw [valuation_of_algebraMap]; exact v.intValuation_lt_one_iff_dvd r

open scoped algebraMap in
/-- The `v`-adic valuation of `r ∈ R` is less than 1 if and only if `r ∈ v`. -/
theorem valuation_lt_one_iff_mem (r : R) :
    v.valuation K r < 1 ↔ r ∈ v.asIdeal := by
  rw [valuation_of_algebraMap]; exact v.intValuation_lt_one_iff_mem r

variable (K)

/-- There exists `π ∈ K` with `v`-adic valuation `Multiplicative.ofAdd (-1)`. -/
theorem valuation_exists_uniformizer : ∃ π : K,
    v.valuation K π = Multiplicative.ofAdd (-1 : ℤ) := by
  obtain ⟨r, hr⟩ := v.intValuation_exists_uniformizer
  use algebraMap R K r
  rw [valuation_def, Valuation.extendToLocalization_apply_map_apply]
  exact hr

/-- Uniformizers are nonzero. -/
theorem valuation_uniformizer_ne_zero : Classical.choose (v.valuation_exists_uniformizer K) ≠ 0 :=
  haveI hu := Classical.choose_spec (v.valuation_exists_uniformizer K)
  (Valuation.ne_zero_iff _).mp (ne_of_eq_of_ne hu WithZero.coe_ne_zero)

theorem mem_integers_of_valuation_le_one (x : K)
    (h : ∀ v : HeightOneSpectrum R, v.valuation K x ≤ 1) : x ∈ (algebraMap R K).range := by
  obtain ⟨⟨n, d, hd⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) x
  obtain rfl : x = IsLocalization.mk' K n ⟨d, hd⟩ := IsLocalization.eq_mk'_iff_mul_eq.mpr hx
  obtain rfl | hn0 := eq_or_ne n 0
  · simp
  have hd0 := nonZeroDivisors.ne_zero hd
  suffices Ideal.span {d} ∣ (Ideal.span {n} : Ideal R) by
    obtain ⟨z, rfl⟩ := Ideal.span_singleton_le_span_singleton.1 (Ideal.le_of_dvd this)
    use z
    rw [map_mul, mul_comm, mul_eq_mul_left_iff] at hx
    exact (hx.resolve_right fun h => by simp [hd0] at h).symm
  classical
  have ine {r : R} : r ≠ 0 → Ideal.span {r} ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp
  rw [← Associates.mk_le_mk_iff_dvd, ← Associates.factors_le, Associates.factors_mk _ (ine hn0),
    Associates.factors_mk _ (ine hd0), WithTop.coe_le_coe, Multiset.le_iff_count]
  rintro ⟨v, hv⟩
  obtain ⟨v, rfl⟩ := Associates.mk_surjective v
  have hv' := hv
  rw [Associates.irreducible_mk, irreducible_iff_prime] at hv
  specialize h ⟨v, Ideal.isPrime_of_prime hv, hv.ne_zero⟩
  simp_rw [valuation_of_mk', intValuation_if_neg _ hn0, intValuation_if_neg _ hd0,
    ← WithZero.coe_div, ← WithZero.coe_one, WithZero.coe_le_coe, Associates.factors_mk _ (ine hn0),
    Associates.factors_mk _ (ine hd0), Associates.count_some hv'] at h
  simpa using h

/-! ### Completions with respect to adic valuations

Given a Dedekind domain `R` with field of fractions `K` and a maximal ideal `v` of `R`, we define
the completion of `K` with respect to its `v`-adic valuation, denoted `v.adicCompletion`, and its
ring of integers, denoted `v.adicCompletionIntegers`. -/

variable {K}

/-- `K` as a valued field with the `v`-adic valuation. -/
def adicValued : Valued K ℤₘ₀ :=
  Valued.mk' (v.valuation K)

theorem adicValued_apply {x : K} : v.adicValued.v x = v.valuation K x :=
  rfl

@[simp]
theorem adicValued_apply' (x : WithVal (v.valuation K)) : v.adicValued.v x = v.valuation K x :=
  rfl

variable (K)

/-- The completion of `K` with respect to its `v`-adic valuation. -/
abbrev adicCompletion := (v.valuation K).Completion

theorem valuedAdicCompletion_def {x : v.adicCompletion K} : Valued.v x = Valued.extension x :=
  rfl

-- Porting note: replaced by `Coe`
-- instance AdicCompletion.hasLiftT : HasLiftT K (v.adicCompletion K) :=
--   (inferInstance : HasLiftT K (@UniformSpace.Completion K v.adicValued.toUniformSpace))

/-- The ring of integers of `adicCompletion`. -/
def adicCompletionIntegers : ValuationSubring (v.adicCompletion K) :=
  Valued.v.valuationSubring

instance : Inhabited (adicCompletionIntegers K v) :=
  ⟨0⟩

variable (R)

theorem mem_adicCompletionIntegers {x : v.adicCompletion K} :
    x ∈ v.adicCompletionIntegers K ↔ Valued.v x ≤ 1 :=
  Iff.rfl

theorem notMem_adicCompletionIntegers {x : v.adicCompletion K} :
    x ∉ v.adicCompletionIntegers K ↔ 1 < Valued.v x := by
  rw [not_congr <| mem_adicCompletionIntegers R K v]
  exact not_le

@[deprecated (since := "2025-05-23")]
alias not_mem_adicCompletionIntegers := notMem_adicCompletionIntegers

section AlgebraInstances

instance (priority := 100) adicValued.has_uniform_continuous_const_smul' :
    UniformContinuousConstSMul R (WithVal <| v.valuation K) :=
  uniformContinuousConstSMul_of_continuousConstSMul R (WithVal <| v.valuation K)

section Algebra
variable [Algebra S K]

instance adicValued.uniformContinuousConstSMul :
    UniformContinuousConstSMul S (WithVal <| v.valuation K) := by
  refine ⟨fun l ↦ ?_⟩
  simp_rw [Algebra.smul_def]
  exact (Ring.uniformContinuousConstSMul (WithVal <| v.valuation K)).uniformContinuous_const_smul _

open UniformSpace in
instance : Algebra S (v.adicCompletion K) where
  toSMul := Completion.instSMul _ _
  algebraMap := Completion.coeRingHom.comp (algebraMap _ _)
  commutes' r x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_mul_left _) (continuous_mul_right _)
    | ih x =>
      change (↑(algebraMap S (WithVal <| v.valuation K) r) : v.adicCompletion K) * x
        = x * (↑(algebraMap S (WithVal <| v.valuation K) r) : v.adicCompletion K)
      norm_cast
      rw [Algebra.commutes]
  smul_def' r x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_const_smul _) (continuous_mul_left _)
    | ih x =>
      change _ = (↑(algebraMap S (WithVal <| v.valuation K) r) : v.adicCompletion K) * x
      norm_cast
      rw [← Algebra.smul_def]

theorem coe_smul_adicCompletion (r : S) (x : WithVal (v.valuation K)) :
    (↑(r • x) : v.adicCompletion K) = r • (↑x : v.adicCompletion K) :=
  UniformSpace.Completion.coe_smul r x

theorem algebraMap_adicCompletion : ⇑(algebraMap S <| v.adicCompletion K) = (↑) ∘ algebraMap S K :=
  rfl

end Algebra

theorem coe_algebraMap_mem (r : R) : ↑((algebraMap R K) r) ∈ adicCompletionIntegers K v := by
  rw [mem_adicCompletionIntegers]
  letI : Valued K ℤₘ₀ := adicValued v
  dsimp only [adicCompletion]
  rw [Valued.valuedCompletion_apply]
  exact v.valuation_le_one _

instance : Algebra R (v.adicCompletionIntegers K) where
  smul r x :=
    ⟨r • (x : v.adicCompletion K), by
      have h :
        (algebraMap R (adicCompletion K v)) r = (algebraMap R K r : adicCompletion K v) := rfl
      rw [Algebra.smul_def]
      refine ValuationSubring.mul_mem _ _ _ ?_ x.2
      rw [h]
      exact coe_algebraMap_mem _ _ v r⟩
  algebraMap :=
  { toFun r :=
      ⟨(algebraMap R K r : adicCompletion K v), coe_algebraMap_mem _ _ v r⟩
    map_one' := by simp only [map_one]; rfl
    map_mul' x y := by
      ext
      simp only [map_mul, UniformSpace.Completion.coe_mul, MulMemClass.mk_mul_mk]
    map_zero' := by simp only [map_zero]; rfl
    map_add' x y := by
      ext
      simp only [map_add, UniformSpace.Completion.coe_add, AddMemClass.mk_add_mk] }
  commutes' r x := by
    rw [mul_comm]
  smul_def' r x := by
    ext
    simp only [Subring.coe_mul, Algebra.smul_def]
    rfl

variable {R K} in
open scoped algebraMap in -- to make the coercions from `R` fire
/-- The valuation on the completion agrees with the global valuation on elements of the
integer ring. -/
theorem valuedAdicCompletion_eq_valuation (r : R) :
    Valued.v (r : v.adicCompletion K) = v.valuation K r := by
  convert Valued.valuedCompletion_apply (r : K)

variable {R K} in
/-- The valuation on the completion agrees with the global valuation on elements of the field. -/
theorem valuedAdicCompletion_eq_valuation' (k : K) :
    Valued.v (k : v.adicCompletion K) = v.valuation K k := by
  convert Valued.valuedCompletion_apply k

variable {R K} in
open scoped algebraMap in -- to make the coercion from `R` fire
/-- A global integer is in the local integers. -/
lemma coe_mem_adicCompletionIntegers (r : R) :
    (r : adicCompletion K v) ∈ adicCompletionIntegers K v := by
  rw [mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation]
  exact valuation_le_one v r

@[simp]
theorem coe_smul_adicCompletionIntegers (r : R) (x : v.adicCompletionIntegers K) :
    (↑(r • x) : v.adicCompletion K) = r • (x : v.adicCompletion K) :=
  rfl

instance : NoZeroSMulDivisors R (v.adicCompletionIntegers K) where
  eq_zero_or_eq_zero_of_smul_eq_zero {c x} hcx := by
    rw [Algebra.smul_def, mul_eq_zero] at hcx
    refine hcx.imp_left fun hc => ?_
    rw [← map_zero (algebraMap R (v.adicCompletionIntegers K))] at hc
    exact
      IsFractionRing.injective R _ (UniformSpace.Completion.coe_injective _ (Subtype.ext_iff.mp hc))

instance adicCompletion.instIsScalarTower' :
    IsScalarTower R (v.adicCompletionIntegers K) (v.adicCompletion K) where
  smul_assoc x y z := by simp only [Algebra.smul_def]; apply mul_assoc

end AlgebraInstances

open nonZeroDivisors algebraMap in
variable {R K} in
lemma adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers (v : HeightOneSpectrum R)
    (a : v.adicCompletion K) : ∃ b ∈ R⁰, a * b ∈ v.adicCompletionIntegers K := by
  by_cases ha : a ∈ v.adicCompletionIntegers K
  · use 1
    simp [ha, Submonoid.one_mem]
  · rw [notMem_adicCompletionIntegers] at ha
    -- Let the additive valuation of a be -d with d>0
    obtain ⟨d, hd⟩ : ∃ d : ℤ, Valued.v a = ofAdd d :=
      Option.ne_none_iff_exists'.mp <| (lt_trans zero_lt_one ha).ne'
    rw [hd, WithZero.one_lt_coe, ← ofAdd_zero, ofAdd_lt] at ha
    -- let ϖ be a uniformiser
    obtain ⟨ϖ, hϖ⟩ := intValuation_exists_uniformizer v
    have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp at hϖ
    -- use ϖ^d
    refine ⟨ϖ^d.natAbs, pow_mem (mem_nonZeroDivisors_of_ne_zero hϖ0) _, ?_⟩
    -- now manually translate the goal (an inequality in ℤₘ₀) to an inequality in ℤ
    rw [mem_adicCompletionIntegers, algebraMap.coe_pow, map_mul, hd, map_pow,
      valuedAdicCompletion_eq_valuation, valuation_of_algebraMap, hϖ, ← WithZero.coe_pow,
      ← WithZero.coe_mul, WithZero.coe_le_one, ← toAdd_le, toAdd_mul, toAdd_ofAdd, toAdd_pow,
      toAdd_ofAdd, toAdd_one,
      show d.natAbs • (-1) = (d.natAbs : ℤ) • (-1) by simp only [nsmul_eq_mul,
        Int.natCast_natAbs, smul_eq_mul],
      ← Int.eq_natAbs_of_nonneg ha.le, smul_eq_mul]
    -- and now it's easy
    omega

section AbsoluteValue

open WithZeroMulInt

variable {R K} in
/-- The `v`-adic absolute value function on `K` defined as `b` raised to negative `v`-adic
valuation, for some `b` in `ℝ≥0` -/
def adicAbvDef (v : HeightOneSpectrum R) {b : NNReal} (hb : 1 < b) :=
  fun x ↦ toNNReal (ne_zero_of_lt hb) (v.valuation K x)

variable {R K} in
lemma isNonarchimedean_adicAbvDef {b : NNReal} (hb : 1 < b) :
    IsNonarchimedean (α := K) (fun x ↦ v.adicAbvDef hb x) := by
  intro x y
  simp only [adicAbvDef]
  have h_mono := (toNNReal_strictMono hb).monotone
  rw [← h_mono.map_max]
  exact h_mono ((v.valuation _).map_add x y)

variable {R K} in
/-- The `v`-adic absolute value on `K` defined as `b` raised to negative `v`-adic
valuation, for some `b` in `ℝ≥0` -/
def adicAbv (v : HeightOneSpectrum R) {b : NNReal} (hb : 1 < b) : AbsoluteValue K ℝ where
  toFun x := v.adicAbvDef hb x
  map_mul' _ _ := by simp [adicAbvDef]
  nonneg' _ := NNReal.zero_le_coe
  eq_zero' _ := by simp [adicAbvDef]
  add_le' _ _ := (isNonarchimedean_adicAbvDef v hb).add_le fun _ ↦ zero_le _

variable {R K} in
/-- The `v`-adic absolute value is nonarchimedean -/
theorem isNonarchimedean_adicAbv (v : HeightOneSpectrum R) {b : NNReal} (hb : 1 < b) :
    IsNonarchimedean (α := K) (v.adicAbv hb) := isNonarchimedean_adicAbvDef v hb

variable {R K} in
theorem adicAbv_coe_le_one {b : NNReal} (hb : 1 < b) (r : R) :
    v.adicAbv hb (algebraMap R K r) ≤ 1 := by
  simpa [adicAbv, adicAbvDef, toNNReal_le_one_iff hb] using valuation_le_one v r

variable {R K} in
theorem adicAbv_coe_lt_one_iff {b : NNReal} (hb : 1 < b) (r : R) :
    v.adicAbv hb (algebraMap R K r) < 1 ↔ r ∈ v.asIdeal := by
  simpa [adicAbv, adicAbvDef, toNNReal_lt_one_iff hb] using valuation_lt_one_iff_mem v r

variable {R K} in
theorem adicAbv_coe_eq_one_iff {b : NNReal} (hb : 1 < b) (r : R) :
    v.adicAbv hb (algebraMap R K r) = 1 ↔ r ∉ v.asIdeal := by
  rw [← not_iff_not, not_not, ← v.adicAbv_coe_lt_one_iff (K := K), ne_iff_lt_iff_le]
  exact adicAbv_coe_le_one v hb r

end AbsoluteValue

end IsDedekindDomain.HeightOneSpectrum
