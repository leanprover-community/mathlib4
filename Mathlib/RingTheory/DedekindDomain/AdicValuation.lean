/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Algebra.Order.Group.TypeTags

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
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags
dedekind domain, dedekind ring, adic valuation
-/


noncomputable section

open scoped Multiplicative Topology

open Multiplicative IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
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

/-- Nonzero elements have nonzero adic valuation. -/
theorem intValuation_ne_zero (x : R) (hx : x ≠ 0) : v.intValuationDef x ≠ 0 := by
  rw [intValuationDef, if_neg hx]
  exact WithZero.coe_ne_zero

@[deprecated (since := "2024-07-09")]
alias int_valuation_ne_zero := intValuation_ne_zero

/-- Nonzero divisors have nonzero valuation. -/
theorem intValuation_ne_zero' (x : nonZeroDivisors R) : v.intValuationDef x ≠ 0 :=
  v.intValuation_ne_zero x (nonZeroDivisors.coe_ne_zero x)

@[deprecated (since := "2024-07-09")]
alias int_valuation_ne_zero' := intValuation_ne_zero'

/-- Nonzero divisors have valuation greater than zero. -/
theorem intValuation_zero_le (x : nonZeroDivisors R) : 0 < v.intValuationDef x := by
  rw [v.intValuationDef_if_neg (nonZeroDivisors.coe_ne_zero x)]
  exact WithZero.zero_lt_coe _

@[deprecated (since := "2024-07-09")]
alias int_valuation_zero_le := intValuation_zero_le

/-- The `v`-adic valuation on `R` is bounded above by 1. -/
theorem intValuation_le_one (x : R) : v.intValuationDef x ≤ 1 := by
  rw [intValuationDef]
  by_cases hx : x = 0
  · rw [if_pos hx]; exact WithZero.zero_le 1
  · rw [if_neg hx, ← WithZero.coe_one, ← ofAdd_zero, WithZero.coe_le_coe, ofAdd_le,
      Right.neg_nonpos_iff]
    exact Int.natCast_nonneg _

@[deprecated (since := "2024-07-09")]
alias int_valuation_le_one := intValuation_le_one

/-- The `v`-adic valuation of `r ∈ R` is less than 1 if and only if `v` divides the ideal `(r)`. -/
theorem intValuation_lt_one_iff_dvd (r : R) :
    v.intValuationDef r < 1 ↔ v.asIdeal ∣ Ideal.span {r} := by
  classical
  rw [intValuationDef]
  split_ifs with hr
  · simp [hr]
  · rw [← WithZero.coe_one, ← ofAdd_zero, WithZero.coe_lt_coe, ofAdd_lt, neg_lt_zero, ←
      Int.ofNat_zero, Int.ofNat_lt, zero_lt_iff]
    have h : (Ideal.span {r} : Ideal R) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hr
    apply Associates.count_ne_zero_iff_dvd h (by apply v.irreducible)

@[deprecated (since := "2024-07-09")]
alias int_valuation_lt_one_iff_dvd := intValuation_lt_one_iff_dvd

/-- The `v`-adic valuation of `r ∈ R` is less than `Multiplicative.ofAdd (-n)` if and only if
`vⁿ` divides the ideal `(r)`. -/
theorem intValuation_le_pow_iff_dvd (r : R) (n : ℕ) :
    v.intValuationDef r ≤ Multiplicative.ofAdd (-(n : ℤ)) ↔ v.asIdeal ^ n ∣ Ideal.span {r} := by
  classical
  rw [intValuationDef]
  split_ifs with hr
  · simp_rw [hr, Ideal.dvd_span_singleton, zero_le', Submodule.zero_mem]
  · rw [WithZero.coe_le_coe, ofAdd_le, neg_le_neg_iff, Int.ofNat_le, Ideal.dvd_span_singleton, ←
      Associates.le_singleton_iff,
      Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hr)
        (by apply v.associates_irreducible)]

@[deprecated (since := "2024-07-09")]
alias int_valuation_le_pow_iff_dvd := intValuation_le_pow_iff_dvd

/-- The `v`-adic valuation of `0 : R` equals 0. -/
theorem intValuation.map_zero' : v.intValuationDef 0 = 0 :=
  v.intValuationDef_if_pos (Eq.refl 0)

@[deprecated (since := "2024-07-09")]
alias IntValuation.map_zero' := intValuation.map_zero'

/-- The `v`-adic valuation of `1 : R` equals 1. -/
theorem intValuation.map_one' : v.intValuationDef 1 = 1 := by
  classical
  rw [v.intValuationDef_if_neg (zero_ne_one.symm : (1 : R) ≠ 0), Ideal.span_singleton_one, ←
    Ideal.one_eq_top, Associates.mk_one, Associates.factors_one,
    Associates.count_zero (by apply v.associates_irreducible), Int.ofNat_zero, neg_zero, ofAdd_zero,
    WithZero.coe_one]

@[deprecated (since := "2024-07-09")]
alias IntValuation.map_one' := intValuation.map_one'

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

@[deprecated (since := "2024-07-09")]
alias IntValuation.map_mul' := intValuation.map_mul'

theorem intValuation.le_max_iff_min_le {a b c : ℕ} :
    Multiplicative.ofAdd (-c : ℤ) ≤
      max (Multiplicative.ofAdd (-a : ℤ)) (Multiplicative.ofAdd (-b : ℤ)) ↔
      min a b ≤ c := by
  rw [le_max_iff, ofAdd_le, ofAdd_le, neg_le_neg_iff, neg_le_neg_iff, Int.ofNat_le, Int.ofNat_le, ←
    min_le_iff]

@[deprecated (since := "2024-07-09")]
alias IntValuation.le_max_iff_min_le := intValuation.le_max_iff_min_le

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

@[deprecated (since := "2024-07-09")]
alias IntValuation.map_add_le_max' := intValuation.map_add_le_max'

/-- The `v`-adic valuation on `R`. -/
@[simps]
def intValuation : Valuation R ℤₘ₀ where
  toFun := v.intValuationDef
  map_zero' := intValuation.map_zero' v
  map_one' := intValuation.map_one' v
  map_mul' := intValuation.map_mul' v
  map_add_le_max' := intValuation.map_add_le_max' v


theorem intValuation_apply {r : R} (v : IsDedekindDomain.HeightOneSpectrum R) :
    intValuation v r = intValuationDef v r := rfl

/-- There exists `π ∈ R` with `v`-adic valuation `Multiplicative.ofAdd (-1)`. -/
theorem intValuation_exists_uniformizer :
    ∃ π : R, v.intValuationDef π = Multiplicative.ofAdd (-1 : ℤ) := by
  classical
  have hv : _root_.Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  have hlt : v.asIdeal ^ 2 < v.asIdeal := by
    rw [← Ideal.dvdNotUnit_iff_lt]
    exact
      ⟨v.ne_bot, v.asIdeal, (not_congr Ideal.isUnit_iff).mpr (Ideal.IsPrime.ne_top v.isPrime),
        sq v.asIdeal⟩
  obtain ⟨π, mem, nmem⟩ := SetLike.exists_of_lt hlt
  have hπ : Associates.mk (Ideal.span {π}) ≠ 0 := by
    rw [Associates.mk_ne_zero']
    intro h
    rw [h] at nmem
    exact nmem (Submodule.zero_mem (v.asIdeal ^ 2))
  use π
  rw [intValuationDef, if_neg (Associates.mk_ne_zero'.mp hπ), WithZero.coe_inj]
  apply congr_arg
  rw [neg_inj, ← Int.ofNat_one, Int.natCast_inj]
  rw [← Ideal.dvd_span_singleton, ← Associates.mk_le_mk_iff_dvd] at mem nmem
  rw [← pow_one (Associates.mk v.asIdeal), Associates.prime_pow_dvd_iff_le hπ hv] at mem
  rw [Associates.mk_pow, Associates.prime_pow_dvd_iff_le hπ hv, not_le] at nmem
  exact Nat.eq_of_le_of_lt_succ mem nmem

@[deprecated (since := "2024-07-09")]
alias int_valuation_exists_uniformizer := intValuation_exists_uniformizer

/-- The `I`-adic valuation of a generator of `I` equals `(-1 : ℤₘ₀)` -/
theorem intValuation_singleton {r : R} (hr : r ≠ 0) (hv : v.asIdeal = Ideal.span {r}) :
    v.intValuation r = Multiplicative.ofAdd (-1 : ℤ) := by
  classical
  rw [intValuation_apply, v.intValuationDef_if_neg hr, ← hv, Associates.count_self, Int.ofNat_one,
    ofAdd_neg, WithZero.coe_inv]
  apply v.associates_irreducible

theorem intValuation_uniformizer_ne_zero {v : HeightOneSpectrum R} {π : R}
    (hπ : v.intValuation π = Multiplicative.ofAdd (-1 : ℤ)) :
    π ≠ 0 := by
  contrapose! hπ
  rw [hπ, intValuation_apply, intValuationDef_zero]
  exact WithZero.zero_ne_coe

/-! ### Adic valuations on the field of fractions `K` -/


/-- The `v`-adic valuation of `x ∈ K` is the valuation of `r` divided by the valuation of `s`,
where `r` and `s` are chosen so that `x = r/s`. -/
def valuation (v : HeightOneSpectrum R) : Valuation K ℤₘ₀ :=
  v.intValuation.extendToLocalization
    (fun r hr => Set.mem_compl <| v.intValuation_ne_zero' ⟨r, hr⟩) K

theorem valuation_def (x : K) :
    v.valuation x =
      v.intValuation.extendToLocalization
        (fun r hr => Set.mem_compl (v.intValuation_ne_zero' ⟨r, hr⟩)) K x :=
  rfl

/-- The `v`-adic valuation of `r/s ∈ K` is the valuation of `r` divided by the valuation of `s`. -/
theorem valuation_of_mk' {r : R} {s : nonZeroDivisors R} :
    v.valuation (IsLocalization.mk' K r s) = v.intValuation r / v.intValuation s := by
  erw [valuation_def, (IsLocalization.toLocalizationMap (nonZeroDivisors R) K).lift_mk',
    div_eq_mul_inv, mul_eq_mul_left_iff]
  left
  rw [Units.val_inv_eq_inv_val, inv_inj]
  rfl

/-- The `v`-adic valuation on `K` extends the `v`-adic valuation on `R`. -/
theorem valuation_of_algebraMap (r : R) : v.valuation (algebraMap R K r) = v.intValuation r := by
  rw [valuation_def, Valuation.extendToLocalization_apply_map_apply]

open scoped algebraMap in
lemma valuation_eq_intValuationDef (r : R) : v.valuation (r : K) = v.intValuationDef r :=
  Valuation.extendToLocalization_apply_map_apply ..

/-- The `v`-adic valuation on `R` is bounded above by 1. -/
theorem valuation_le_one (r : R) : v.valuation (algebraMap R K r) ≤ 1 := by
  rw [valuation_of_algebraMap]; exact v.intValuation_le_one r

/-- The `v`-adic valuation of `r ∈ R` is less than 1 if and only if `v` divides the ideal `(r)`. -/
theorem valuation_lt_one_iff_dvd (r : R) :
    v.valuation (algebraMap R K r) < 1 ↔ v.asIdeal ∣ Ideal.span {r} := by
  rw [valuation_of_algebraMap]; exact v.intValuation_lt_one_iff_dvd r

variable (K)

/-- There exists `π ∈ K` with `v`-adic valuation `Multiplicative.ofAdd (-1)`. -/
theorem valuation_exists_uniformizer : ∃ π : K, v.valuation π = Multiplicative.ofAdd (-1 : ℤ) := by
  obtain ⟨r, hr⟩ := v.intValuation_exists_uniformizer
  use algebraMap R K r
  rw [valuation_def, Valuation.extendToLocalization_apply_map_apply]
  exact hr

/-- Uniformizers are nonzero. -/
theorem valuation_uniformizer_ne_zero : Classical.choose (v.valuation_exists_uniformizer K) ≠ 0 :=
  haveI hu := Classical.choose_spec (v.valuation_exists_uniformizer K)
  (Valuation.ne_zero_iff _).mp (ne_of_eq_of_ne hu WithZero.coe_ne_zero)

theorem mem_integers_of_valuation_le_one (x : K)
    (h : ∀ v : HeightOneSpectrum R, v.valuation x ≤ 1) : x ∈ (algebraMap R K).range := by
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
  simp_rw [valuation_of_mk', intValuation, ← Valuation.toFun_eq_coe,
    intValuationDef_if_neg _ hn0, intValuationDef_if_neg _ hd0, ← WithZero.coe_div,
    ← WithZero.coe_one, WithZero.coe_le_coe, Associates.factors_mk _ (ine hn0),
    Associates.factors_mk _ (ine hd0), Associates.count_some hv'] at h
  simpa using h

/-! ### Completions with respect to adic valuations

Given a Dedekind domain `R` with field of fractions `K` and a maximal ideal `v` of `R`, we define
the completion of `K` with respect to its `v`-adic valuation, denoted `v.adicCompletion`, and its
ring of integers, denoted `v.adicCompletionIntegers`. -/


variable {K}

/-- `K` as a valued field with the `v`-adic valuation. -/
def adicValued : Valued K ℤₘ₀ :=
  Valued.mk' v.valuation

theorem adicValued_apply {x : K} : v.adicValued.v x = v.valuation x :=
  rfl

variable (K)

/-- The completion of `K` with respect to its `v`-adic valuation. -/
def adicCompletion :=
  @UniformSpace.Completion K v.adicValued.toUniformSpace

instance : Field (v.adicCompletion K) := inferInstanceAs <|
  Field (@UniformSpace.Completion K v.adicValued.toUniformSpace)

instance : Algebra K (v.adicCompletion K) :=
  RingHom.toAlgebra (@UniformSpace.Completion.coeRingHom K _ v.adicValued.toUniformSpace _ _)

instance : Inhabited (v.adicCompletion K) :=
  ⟨0⟩

instance valuedAdicCompletion : Valued (v.adicCompletion K) ℤₘ₀ := inferInstanceAs <|
  Valued (@UniformSpace.Completion K v.adicValued.toUniformSpace) ℤₘ₀

theorem valuedAdicCompletion_def {x : v.adicCompletion K} :
    Valued.v x = @Valued.extension K _ _ _ (adicValued v) x :=
  rfl

instance adicCompletion_completeSpace : CompleteSpace (v.adicCompletion K) := inferInstanceAs <|
  CompleteSpace (@UniformSpace.Completion K v.adicValued.toUniformSpace)

-- Porting note: replaced by `Coe`
-- instance AdicCompletion.hasLiftT : HasLiftT K (v.adicCompletion K) :=
--   (inferInstance : HasLiftT K (@UniformSpace.Completion K v.adicValued.toUniformSpace))

instance adicCompletion.instCoe : Coe K (v.adicCompletion K) :=
  inferInstanceAs <| Coe K (@UniformSpace.Completion K v.adicValued.toUniformSpace)

/-- The ring of integers of `adicCompletion`. -/
def adicCompletionIntegers : ValuationSubring (v.adicCompletion K) :=
  Valued.v.valuationSubring

instance : Inhabited (adicCompletionIntegers K v) :=
  ⟨0⟩

variable (R)

theorem mem_adicCompletionIntegers {x : v.adicCompletion K} :
    x ∈ v.adicCompletionIntegers K ↔ (Valued.v x : ℤₘ₀) ≤ 1 :=
  Iff.rfl

theorem not_mem_adicCompletionIntegers {x : v.adicCompletion K} :
    x ∉ v.adicCompletionIntegers K ↔ 1 < (Valued.v x : ℤₘ₀) := by
  rw [not_congr <| mem_adicCompletionIntegers R K v]
  exact not_le

section AlgebraInstances

instance (priority := 100) adicValued.has_uniform_continuous_const_smul' :
    @UniformContinuousConstSMul R K v.adicValued.toUniformSpace _ :=
  @uniformContinuousConstSMul_of_continuousConstSMul R K _ _ _ v.adicValued.toUniformSpace _ _

instance adicValued.uniformContinuousConstSMul :
    @UniformContinuousConstSMul K K v.adicValued.toUniformSpace _ :=
  @Ring.uniformContinuousConstSMul K _ v.adicValued.toUniformSpace _ _

instance adicCompletion.algebra' : Algebra R (v.adicCompletion K) := inferInstanceAs <|
  Algebra R (@UniformSpace.Completion K v.adicValued.toUniformSpace)

theorem coe_smul_adicCompletion (r : R) (x : K) :
    (↑(r • x) : v.adicCompletion K) = r • (↑x : v.adicCompletion K) :=
  @UniformSpace.Completion.coe_smul R K v.adicValued.toUniformSpace _ _ r x

instance : Algebra K (v.adicCompletion K) :=
  @UniformSpace.Completion.algebra' K _ v.adicValued.toUniformSpace _ _

theorem algebraMap_adicCompletion' :
    ⇑(algebraMap R <| v.adicCompletion K) = (↑) ∘ algebraMap R K :=
  rfl

theorem algebraMap_adicCompletion :
    ⇑(algebraMap K <| v.adicCompletion K) = ((↑) : K → adicCompletion K v) :=
  rfl

instance : IsScalarTower R K (v.adicCompletion K) := inferInstanceAs <|
  IsScalarTower R K (@UniformSpace.Completion K v.adicValued.toUniformSpace)

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
    Valued.v (r : v.adicCompletion K) = v.valuation (r : K) := by
  convert Valued.valuedCompletion_apply (r : K)

variable {R K} in
/-- The valuation on the completion agrees with the global valuation on elements of the field. -/
theorem valuedAdicCompletion_eq_valuation' (k : K) :
    Valued.v (k : v.adicCompletion K) = v.valuation k := by
  convert Valued.valuedCompletion_apply k

variable {R K} in
open scoped algebraMap in -- to make the coercion from `R` fire
/-- A global integer is in the local integers. -/
lemma coe_mem_adicCompletionIntegers (r : R) :
    (r : adicCompletion K v) ∈ adicCompletionIntegers K v := by
  rw [mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation, valuation_eq_intValuationDef]
  exact intValuation_le_one v r

@[simp]
theorem coe_smul_adicCompletionIntegers (r : R) (x : v.adicCompletionIntegers K) :
    (↑(r • x) : v.adicCompletion K) = r • (x : v.adicCompletion K) :=
  rfl

instance : NoZeroSMulDivisors R (v.adicCompletionIntegers K) where
  eq_zero_or_eq_zero_of_smul_eq_zero {c x} hcx := by
    rw [Algebra.smul_def, mul_eq_zero] at hcx
    refine hcx.imp_left fun hc => ?_
    letI : UniformSpace K := v.adicValued.toUniformSpace
    rw [← map_zero (algebraMap R (v.adicCompletionIntegers K))] at hc
    exact
      IsFractionRing.injective R K (UniformSpace.Completion.coe_injective K (Subtype.ext_iff.mp hc))

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
  · rw [not_mem_adicCompletionIntegers] at ha
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
      valuedAdicCompletion_eq_valuation, valuation_eq_intValuationDef, hϖ, ← WithZero.coe_pow,
      ← WithZero.coe_mul, WithZero.coe_le_one, ← toAdd_le, toAdd_mul, toAdd_ofAdd, toAdd_pow,
      toAdd_ofAdd, toAdd_one,
      show d.natAbs • (-1) = (d.natAbs : ℤ) • (-1) by simp only [nsmul_eq_mul,
        Int.natCast_natAbs, smul_eq_mul],
      ← Int.eq_natAbs_of_zero_le ha.le, smul_eq_mul]
    -- and now it's easy
    omega

variable {R}

theorem AdicCompletion.valued_eq_intValuationDef (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap _ (v.adicCompletion K) r) = v.intValuationDef r := by
  rw [v.valuedAdicCompletion_eq_valuation, valuation_eq_intValuationDef]

theorem AdicCompletion.valued_le_one (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap _ (v.adicCompletion K) r) ≤ 1 :=
  valued_eq_intValuationDef K _ r ▸ v.intValuation_le_one r

theorem AdicCompletion.valued_ne_zero (v : HeightOneSpectrum R) (r : nonZeroDivisors R) :
    Valued.v (algebraMap _ (v.adicCompletion K) r.1) ≠ 0 :=
  valued_eq_intValuationDef K _ r.1 ▸ v.intValuation_ne_zero' _

open Filter WithZero Multiplicative in
/-- Powers of `x` tend to zero in `Kᵥ` if `x` has valuation `≤ -1`. -/
theorem AdicCompletion.tendsto_zero_pow_of_le_neg_one (v : HeightOneSpectrum R)
    {x : v.adicCompletion K} (hx : Valued.v x ≤ ofAdd (-1 : ℤ)) :
    Tendsto (fun (n : ℕ) => x ^ n) atTop (𝓝 0) := by
  simp only [HasBasis.tendsto_right_iff (Valued.hasBasis_nhds_zero _ _), Set.mem_setOf_eq,
    map_pow, eventually_atTop]
  have h_lt : ofAdd (-1 : ℤ) < (1 : ℤₘ₀) := by
    rw [← coe_one, coe_lt_coe, ← ofAdd_zero, ofAdd_lt]; linarith
  intro γ _
  by_cases hγ : γ.val ≤ 1
  · let m := - toAdd (unitsWithZeroEquiv γ) + 1 |>.toNat
    refine ⟨m, fun b hb => lt_of_le_of_lt
      (pow_le_pow_of_le_one zero_le' (le_trans hx <| le_of_lt h_lt) hb) ?_⟩
    replace hγ : 0 ≤ -toAdd (unitsWithZeroEquiv γ) + 1 := by
      rw [coe_unitsWithZeroEquiv_eq_units_val, ← coe_one, coe_le_coe, ← toAdd_le, toAdd_one] at hγ
      linarith
    apply lt_of_le_of_lt <| pow_le_pow_left₀ zero_le' hx m
    rw [coe_unitsWithZeroEquiv_eq_units_val, ← coe_pow, coe_lt_coe, ← ofAdd_nsmul,
      nsmul_eq_mul, Int.toNat_of_nonneg hγ]
    simp
    rw [← ofAdd_zero, ofAdd_lt]
    exact zero_lt_one
  · refine ⟨1, fun b hb => lt_of_le_of_lt
      (pow_le_pow_of_le_one zero_le' (le_trans hx <| le_of_lt h_lt) hb) ?_⟩
    apply lt_trans _ (lt_of_not_le hγ)
    apply lt_of_le_of_lt (pow_one (Valued.v x) ▸ hx)
    exact h_lt

open Valued Filter in
/-- There exists a non-zero integer of value `< γ` for a given `γ`. -/
theorem AdicCompletion.exists_nonZeroDivisor_valued_lt (v : HeightOneSpectrum R) (γ : ℤₘ₀ˣ) :
    ∃ (r : nonZeroDivisors R), Valued.v (algebraMap _ (v.adicCompletion K) r.1) < γ := by
  let ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have := tendsto_zero_pow_of_le_neg_one K v (le_of_eq (valued_eq_intValuationDef K _ π ▸ hπ))
  let ⟨a, ha⟩ := eventually_atTop.1 <|
    (HasBasis.tendsto_right_iff (hasBasis_nhds_zero _ _)).1 this γ trivial
  use ⟨algebraMap _ _ π ^ a,
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ <| v.intValuation_uniformizer_ne_zero hπ)⟩
  convert ha _ le_rfl
  simp

open scoped Classical in
/-- Given a collection of values `γ v` at primes `v `, we can find a global
non-zero integer that has valuation less than `γ v` for a finite set of primes `v`. -/
theorem AdicCompletion.exists_nonZeroDivisor_finset_valued_lt
    (S : Set (HeightOneSpectrum R))
    (hS : Set.Finite S)
    (γ : (v : HeightOneSpectrum R) → ℤₘ₀ˣ) :
    ∃ (r : nonZeroDivisors R), ∀ v ∈ S, Valued.v (algebraMap _ (v.adicCompletion K) r.1) < γ v := by
  choose s hs using fun v => AdicCompletion.exists_nonZeroDivisor_valued_lt K v (γ v)
  refine ⟨hS.toFinset.prod s, fun v hv => ?_⟩
  simp only [Submonoid.coe_finset_prod, map_prod]
  rw [← hS.toFinset.prod_erase_mul _ (hS.mem_toFinset.2 hv)]
  refine mul_lt_of_le_one_of_lt (Finset.prod_le_one' (fun _ _ => ?_)) (hs v)
  rw [v.valuedAdicCompletion_eq_valuation]
  exact v.valuation_le_one _

variable {K v}

/-- If `x ∈ Kᵥ` has valuation at most that of `y ∈ Kᵥ`, then `x` is an integral
multiple of `y`. -/
theorem AdicCompletion.dvd_of_valued_le
    {x y : v.adicCompletion K} (h : Valued.v x ≤ Valued.v y) (hy : y ≠ 0):
    ∃ r : v.adicCompletionIntegers K, r * y = x := by
  have : Valued.v (x * y⁻¹) ≤ 1 := by
    rwa [Valued.v.map_mul, map_inv₀, mul_inv_le_iff₀ (Valued.v.pos_iff.2 hy), one_mul]
  exact ⟨⟨x * y⁻¹, this⟩, by rw [inv_mul_cancel_right₀ hy]⟩

end IsDedekindDomain.HeightOneSpectrum
