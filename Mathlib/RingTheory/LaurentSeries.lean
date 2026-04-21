/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.HahnSeries.PowerSeries
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.UniformSpace.DiscreteUniformity


/-!
# Laurent Series

In this file we define `LaurentSeries R`, the formal Laurent series over `R`, here an *arbitrary*
type with a zero. They are denoted `R⸨X⸩`.

## Main Definitions

* Defines `LaurentSeries` as an abbreviation for `HahnSeries ℤ`.
* Defines `hasseDeriv` of a Laurent series with coefficients in a module over a ring.
* Provides a coercion from power series `R⟦X⟧` into `R⸨X⸩` given by `HahnSeries.ofPowerSeries`.
* Defines `LaurentSeries.powerSeriesPart`
* Defines the localization map `LaurentSeries.of_powerSeries_localization` which evaluates to
  `HahnSeries.ofPowerSeries`.
* Embedding of rational functions into Laurent series, provided as a coercion, utilizing
  the underlying `RatFunc.coeAlgHom`.
* Study of the `X`-Adic valuation on the ring of Laurent series over a field
* In `LaurentSeries.uniformContinuous_coeff` we show that sending a Laurent series to its `d`th
  coefficient is uniformly continuous, ensuring that it sends a Cauchy filter `ℱ` in `K⸨X⸩`
  to a Cauchy filter in `K`: since this latter is given the discrete topology, this provides an
  element `LaurentSeries.Cauchy.coeff ℱ d` in `K` that serves as `d`th coefficient of the Laurent
  series to which the filter `ℱ` converges.

## Main Results

* Basic properties of Hasse derivatives
### About the `X`-Adic valuation:
* The (integral) valuation of a power series is the order of the first non-zero coefficient, see
  `LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero`.
* The valuation of a Laurent series is the order of the first non-zero coefficient, see
  `LaurentSeries.valuation_le_iff_coeff_lt_eq_zero`.
* Every Laurent series of valuation less than `(1 : ℤᵐ⁰)` comes from a power series, see
  `LaurentSeries.val_le_one_iff_eq_coe`.
* The uniform space of `LaurentSeries` over a field is complete, formalized in the instance
  `instLaurentSeriesComplete`.
* The field of rational functions is dense in `LaurentSeries`: this is the declaration
  `LaurentSeries.coe_range_dense` and relies principally upon `LaurentSeries.exists_ratFunc_val_lt`,
  stating that for every Laurent series `f` and every `γ : ℤᵐ⁰` one can find a rational function `Q`
  such that the `X`-adic valuation `v` satisfies `v (f - Q) < γ`.
* In `LaurentSeries.valuation_compare` we prove that the extension of the `X`-adic valuation from
  `K⟮X⟯` up to its abstract completion coincides, modulo the isomorphism with `K⸨X⸩`, with the
  `X`-adic valuation on `K⸨X⸩`.
* The two declarations `LaurentSeries.mem_integers_of_powerSeries` and
  `LaurentSeries.exists_powerSeries_of_memIntegers` show that an element in the completion of
  `K⟮X⟯` is in the unit ball if and only if it comes from a power series through the
  isomorphism `LaurentSeriesRingEquiv`.
* `LaurentSeries.powerSeriesAlgEquiv` is the `K`-algebra isomorphism between `K⟦X⟧`
  and the unit ball inside the `X`-adic completion of `K⟮X⟯`.

## Implementation details

* Since `LaurentSeries` is just an abbreviation of `HahnSeries ℤ`, the definition of the
  coefficients is given in terms of `HahnSeries.coeff` and this forces sometimes to go
  back-and-forth from `X : R⸨X⸩` to `single 1 1 : R⟦ℤ⟧`.
* To prove the isomorphism between the `X`-adic completion of `K⟮X⟯` and `K⸨X⸩` we construct
  two completions of `K⟮X⟯`: the first (`LaurentSeries.ratfuncAdicComplPkg`) is its abstract
  uniform completion; the second (`LaurentSeries.LaurentSeriesPkg`) is simply `K⸨X⸩`, once we prove
  that it is complete and contains `K⟮X⟯` as a dense subspace. The isomorphism is the
  comparison equivalence, expressing the mathematical idea that the completion "is unique". It is
  `LaurentSeries.comparePkg`.
* For applications to `K⟦X⟧` it is actually more handy to use the *inverse* of the above
  equivalence: `LaurentSeries.LaurentSeriesAlgEquiv` is the *topological, algebra equivalence*
  `K⸨X⸩ ≃ₐ[K] RatFuncAdicCompl K`.
* In order to compare `K⟦X⟧` with the valuation subring in the `X`-adic completion of
  `K⟮X⟯` we consider its alias `LaurentSeries.powerSeries_as_subring` as a subring of `K⸨X⸩`,
  that is itself clearly isomorphic (via the inverse of `LaurentSeries.powerSeriesEquivSubring`)
  to `K⟦X⟧`.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section
universe u

open scoped PowerSeries
open HahnSeries Polynomial

noncomputable section

/-- `LaurentSeries R` is the type of formal Laurent series with coefficients in `R`, denoted `R⸨X⸩`.

  It is implemented as a `HahnSeries` with value group `ℤ`.
-/
abbrev LaurentSeries (R : Type u) [Zero R] := R⟦ℤ⟧

variable {R : Type*}

namespace LaurentSeries

section

/-- `R⸨X⸩` is notation for `LaurentSeries R`. -/
scoped notation:9000 R "⸨X⸩" => LaurentSeries R

end

section HasseDeriv

/-- The Hasse derivative of Laurent series, as a linear map. -/
def hasseDeriv (R : Type*) {V : Type*} [AddCommGroup V] [Semiring R] [Module R V] (k : ℕ) :
    V⸨X⸩ →ₗ[R] V⸨X⸩ where
  toFun f := HahnSeries.ofSuppBddBelow (fun n ↦ Ring.choose (n + k) k • f.coeff (n + k)) <| by
    refine ⟨f.order - k, fun x h ↦ ?_⟩
    contrapose! h
    rw [Function.notMem_support, coeff_eq_zero_of_lt_order <| lt_sub_iff_add_lt.mp h, smul_zero]
  map_add' f g := by
    ext
    simp only [ofSuppBddBelow, coeff_add', Pi.add_apply, smul_add]
  map_smul' r f := by
    ext
    simp only [ofSuppBddBelow, HahnSeries.coeff_smul, RingHom.id_apply, smul_comm r]

variable [Semiring R] {V : Type*} [AddCommGroup V] [Module R V]

@[simp]
theorem hasseDeriv_coeff (k : ℕ) (f : LaurentSeries V) (n : ℤ) :
    (hasseDeriv R k f).coeff n = Ring.choose (n + k) k • f.coeff (n + k) :=
  rfl

@[simp]
theorem hasseDeriv_zero : hasseDeriv R 0 = LinearMap.id (M := LaurentSeries V) := by
  ext f n
  simp

theorem hasseDeriv_single_add (k : ℕ) (n : ℤ) (x : V) :
    hasseDeriv R k (single (n + k) x) = single n ((Ring.choose (n + k) k) • x) := by
  ext m
  dsimp only [hasseDeriv_coeff]
  by_cases h : m = n
  · simp [h]
  · simp [h, show m + k ≠ n + k by lia]

@[simp]
theorem hasseDeriv_single (k : ℕ) (n : ℤ) (x : V) :
    hasseDeriv R k (single n x) = single (n - k) ((Ring.choose n k) • x) := by
  rw [← Int.sub_add_cancel n k, hasseDeriv_single_add, Int.sub_add_cancel n k]

theorem hasseDeriv_comp_coeff (k l : ℕ) (f : LaurentSeries V) (n : ℤ) :
    (hasseDeriv R k (hasseDeriv R l f)).coeff n =
      ((Nat.choose (k + l) k) • hasseDeriv R (k + l) f).coeff n := by
  rw [coeff_nsmul]
  simp only [hasseDeriv_coeff, Pi.smul_apply, Nat.cast_add]
  rw [smul_smul, mul_comm, ← Ring.choose_add_smul_choose (n + k), add_assoc, Nat.choose_symm_add,
    smul_assoc]

@[simp]
theorem hasseDeriv_comp (k l : ℕ) (f : LaurentSeries V) :
    hasseDeriv R k (hasseDeriv R l f) = (k + l).choose k • hasseDeriv R (k + l) f := by
  ext n
  simp [hasseDeriv_comp_coeff k l f n]

/-- The derivative of a Laurent series. -/
def derivative (R : Type*) {V : Type*} [AddCommGroup V] [Semiring R] [Module R V] :
    LaurentSeries V →ₗ[R] LaurentSeries V :=
  hasseDeriv R 1

@[simp]
theorem derivative_apply (f : LaurentSeries V) : derivative R f = hasseDeriv R 1 f := by
  exact rfl

theorem derivative_iterate (k : ℕ) (f : LaurentSeries V) :
    (derivative R)^[k] f = k.factorial • (hasseDeriv R k f) := by
  ext n
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ, Function.comp_apply, ih, derivative_apply, hasseDeriv_comp,
      Nat.choose_symm_add, Nat.choose_one_right, Nat.factorial, mul_nsmul]

@[simp]
theorem derivative_iterate_coeff (k : ℕ) (f : LaurentSeries V) (n : ℤ) :
    ((derivative R)^[k] f).coeff n = (descPochhammer ℤ k).smeval (n + k) • f.coeff (n + k) := by
  rw [derivative_iterate, coeff_nsmul, Pi.smul_apply, hasseDeriv_coeff,
    Ring.descPochhammer_eq_factorial_smul_choose, smul_assoc]

end HasseDeriv

section Semiring

variable [Semiring R]

instance : Coe R⟦X⟧ R⸨X⸩ :=
  ⟨HahnSeries.ofPowerSeries ℤ R⟩

@[simp]
theorem coeff_coe_powerSeries (x : R⟦X⟧) (n : ℕ) :
    HahnSeries.coeff (x : R⸨X⸩) n = PowerSeries.coeff n x := by
  rw [ofPowerSeries_apply_coeff]

/-- This is a power series that can be multiplied by an integer power of `X` to give our
  Laurent series. If the Laurent series is nonzero, `powerSeriesPart` has a nonzero
  constant term. -/
def powerSeriesPart (x : R⸨X⸩) : R⟦X⟧ :=
  PowerSeries.mk fun n => x.coeff (x.order + n)

@[simp]
theorem powerSeriesPart_coeff (x : R⸨X⸩) (n : ℕ) :
    PowerSeries.coeff n x.powerSeriesPart = x.coeff (x.order + n) :=
  PowerSeries.coeff_mk _ _

@[simp]
theorem powerSeriesPart_zero : powerSeriesPart (0 : R⸨X⸩) = 0 := by
  ext
  simp

@[simp]
theorem powerSeriesPart_eq_zero (x : R⸨X⸩) : x.powerSeriesPart = 0 ↔ x = 0 := by
  constructor
  · contrapose!
    simp only [ne_eq]
    intro h
    rw [PowerSeries.ext_iff, not_forall]
    use 0
    simpa
  · rintro rfl
    simp

@[simp]
theorem single_order_mul_powerSeriesPart (x : R⸨X⸩) :
    (single x.order 1 : R⸨X⸩) * x.powerSeriesPart = x := by
  ext n
  rw [← sub_add_cancel n x.order, coeff_single_mul_add, sub_add_cancel, one_mul]
  by_cases h : x.order ≤ n
  · rw [Int.eq_natAbs_of_nonneg (sub_nonneg_of_le h), coeff_coe_powerSeries,
      powerSeriesPart_coeff, ← Int.eq_natAbs_of_nonneg (sub_nonneg_of_le h),
      add_sub_cancel]
  · rw [ofPowerSeries_apply, embDomain_notin_range]
    · contrapose! h
      exact order_le_of_coeff_ne_zero h.symm
    · contrapose h
      simp only [Set.mem_range, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at h
      lia

theorem ofPowerSeries_powerSeriesPart (x : R⸨X⸩) :
    ofPowerSeries ℤ R x.powerSeriesPart = single (-x.order) 1 * x := by
  refine Eq.trans ?_ (congr rfl x.single_order_mul_powerSeriesPart)
  rw [← mul_assoc, single_mul_single, neg_add_cancel, mul_one, ← C_apply, C_one, one_mul]

theorem X_order_mul_powerSeriesPart {n : ℕ} {f : R⸨X⸩} (hn : n = f.order) :
    (PowerSeries.X ^ n * f.powerSeriesPart : R⟦X⟧) = f := by
  simp only [map_mul, map_pow, ofPowerSeries_X, single_pow, nsmul_eq_mul, mul_one, one_pow, hn,
    single_order_mul_powerSeriesPart]

end Semiring

instance [CommSemiring R] : Algebra R⟦X⟧ R⸨X⸩ := (HahnSeries.ofPowerSeries ℤ R).toAlgebra

@[simp]
theorem coe_algebraMap [CommSemiring R] :
    ⇑(algebraMap R⟦X⟧ R⸨X⸩) = HahnSeries.ofPowerSeries ℤ R :=
  rfl

/-- The localization map from power series to Laurent series. -/
@[simps (rhsMd := .all) +simpRhs]
instance of_powerSeries_localization [CommRing R] :
    IsLocalization (Submonoid.powers (PowerSeries.X : R⟦X⟧)) R⸨X⸩ where
  map_units := by
    rintro ⟨_, n, rfl⟩
    refine ⟨⟨single (n : ℤ) 1, single (-n : ℤ) 1, ?_, ?_⟩, ?_⟩
    · simp
    · simp
    · dsimp; rw [ofPowerSeries_X_pow]
  surj z := by
    by_cases! h : 0 ≤ z.order
    · refine ⟨⟨PowerSeries.X ^ Int.natAbs z.order * powerSeriesPart z, 1⟩, ?_⟩
      simp only [map_one, mul_one, map_mul, coe_algebraMap, ofPowerSeries_X_pow,
        Submonoid.coe_one]
      rw [Int.natAbs_of_nonneg h, single_order_mul_powerSeriesPart]
    · refine ⟨⟨powerSeriesPart z, PowerSeries.X ^ Int.natAbs z.order, ⟨_, rfl⟩⟩, ?_⟩
      simp only [coe_algebraMap, ofPowerSeries_powerSeriesPart]
      rw [mul_comm _ z]
      refine congr rfl ?_
      rw [ofPowerSeries_X_pow, Int.ofNat_natAbs_of_nonpos]
      exact h.le
  exists_of_eq {x y} := by
    rw [coe_algebraMap, ofPowerSeries_injective.eq_iff]
    rintro rfl
    exact ⟨1, rfl⟩

instance {K : Type*} [Field K] : IsFractionRing K⟦X⟧ K⸨X⸩ :=
  IsLocalization.of_le (Submonoid.powers (PowerSeries.X : K⟦X⟧)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero) fun _ hf =>
    isUnit_of_mem_nonZeroDivisors <| map_mem_nonZeroDivisors _ HahnSeries.ofPowerSeries_injective hf

end LaurentSeries

namespace PowerSeries

open LaurentSeries

variable {R' : Type*} [Semiring R] [Ring R'] (f g : R⟦X⟧) (f' g' : R'⟦X⟧)

@[norm_cast]
theorem coe_zero : ((0 : R⟦X⟧) : R⸨X⸩) = 0 :=
  (ofPowerSeries ℤ R).map_zero

@[norm_cast]
theorem coe_one : ((1 : R⟦X⟧) : R⸨X⸩) = 1 :=
  (ofPowerSeries ℤ R).map_one

@[norm_cast]
theorem coe_add : ((f + g : R⟦X⟧) : R⸨X⸩) = f + g :=
  (ofPowerSeries ℤ R).map_add _ _

@[norm_cast]
theorem coe_sub : ((f' - g' : R'⟦X⟧) : R'⸨X⸩) = f' - g' :=
  (ofPowerSeries ℤ R').map_sub _ _

@[norm_cast]
theorem coe_neg : ((-f' : R'⟦X⟧) : R'⸨X⸩) = -f' :=
  (ofPowerSeries ℤ R').map_neg _

@[norm_cast]
theorem coe_mul : ((f * g : R⟦X⟧) : R⸨X⸩) = f * g :=
  (ofPowerSeries ℤ R).map_mul _ _

theorem coeff_coe (i : ℤ) :
    ((f : R⟦X⟧) : R⸨X⸩).coeff i =
      if i < 0 then 0 else PowerSeries.coeff i.natAbs f := by
  cases i
  · rw [Int.ofNat_eq_natCast, coeff_coe_powerSeries, if_neg (Int.natCast_nonneg _).not_gt,
      Int.natAbs_natCast]
  · rw [ofPowerSeries_apply, embDomain_notin_image_support, if_pos (Int.negSucc_lt_zero _)]
    simp only [not_exists, RelEmbedding.coe_mk, Set.mem_image, not_and, Function.Embedding.coeFn_mk,
      Ne, toPowerSeries_symm_apply_coeff, mem_support, imp_true_iff,
      not_false_iff, reduceCtorEq]

theorem coe_C (r : R) : ((C r : R⟦X⟧) : R⸨X⸩) = HahnSeries.C r :=
  ofPowerSeries_C _

theorem coe_X : ((X : R⟦X⟧) : R⸨X⸩) = single 1 1 :=
  ofPowerSeries_X

@[simp, norm_cast]
theorem coe_smul {S : Type*} [Semiring S] [Module R S] (r : R) (x : S⟦X⟧) :
    ((r • x : S⟦X⟧) : S⸨X⸩) = r • (ofPowerSeries ℤ S x) := by
  ext
  simp [coeff_coe, coeff_smul, smul_ite]

@[norm_cast]
theorem coe_pow (n : ℕ) : ((f ^ n : R⟦X⟧) : R⸨X⸩) = (ofPowerSeries ℤ R f) ^ n :=
  (ofPowerSeries ℤ R).map_pow _ _

end PowerSeries

namespace RatFunc

open scoped LaurentSeries

variable {F : Type u} [Field F] (p q : F[X]) (f g : RatFunc F)

instance : FaithfulSMul F[X] F⸨X⸩ := by
  refine (faithfulSMul_iff_algebraMap_injective F[X] F⸨X⸩).mpr ?_
  exact algebraMap_hahnSeries_injective ℤ

instance coeToLaurentSeries : Coe (RatFunc F) F⸨X⸩ :=
  ⟨algebraMap (RatFunc F) F⸨X⸩⟩

theorem coe_coe (P : Polynomial F) : ((P : F⟦X⟧) : F⸨X⸩) = (P : RatFunc F) := by
  simp [coePolynomial, coe_def, ← IsScalarTower.algebraMap_apply]

-- Porting note: removed `norm_cast` because "badly shaped lemma, rhs can't start with coe"
-- even though `single 1 1` is a bundled function application, not a "real" coercion
@[simp]
theorem coe_X : ((X : RatFunc F) : F⸨X⸩) = single 1 1 := by
  simp [← algebraMap_X, ← IsScalarTower.algebraMap_apply F[X] (RatFunc F) F⸨X⸩]

theorem single_one_eq_pow {R : Type*} [Semiring R] (n : ℕ) :
    single (n : ℤ) (1 : R) = single (1 : ℤ) 1 ^ n := by
  simp

@[deprecated HahnSeries.inv_single (since := "2025-11-07")]
theorem single_inv (d : ℤ) {α : F} (hα : α ≠ 0) :
    single (-d) (α⁻¹ : F) = (single (d : ℤ) (α : F))⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  simp [hα]

theorem single_zpow (n : ℤ) :
    single (n : ℤ) (1 : F) = single (1 : ℤ) 1 ^ n := by
  match n with
  | (n : ℕ) => apply single_one_eq_pow
  | -(n + 1 : ℕ) =>
    rw [← Nat.cast_one, ← inv_one, ← HahnSeries.inv_single, zpow_neg,
      ← Nat.cast_one, Nat.cast_one,
      inv_inj, zpow_natCast, single_one_eq_pow, inv_one]

theorem algebraMap_apply_div :
    algebraMap (RatFunc F) F⸨X⸩ (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap F[X] F⸨X⸩ p / algebraMap _ _ q := by
  simp only [map_div₀, IsScalarTower.algebraMap_apply F[X] (RatFunc F) F⸨X⸩]

end RatFunc

section AdicValuation

open scoped WithZero

variable (K : Type*) [Field K]
namespace PowerSeries

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The prime ideal `(X)` of `K⟦X⟧`, when `K` is a field, as a term of the `HeightOneSpectrum`. -/
def idealX : IsDedekindDomain.HeightOneSpectrum K⟦X⟧ where
  asIdeal := Ideal.span {X}
  isPrime := PowerSeries.span_X_isPrime
  ne_bot  := by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact X_ne_zero

open IsDedekindDomain.HeightOneSpectrum RatFunc WithZero

variable {K}

/- The `X`-adic valuation of a polynomial equals the `X`-adic valuation of
its coercion to `K⟦X⟧`. -/
theorem intValuation_eq_of_coe (P : K[X]) :
    (Polynomial.idealX K).intValuation P = (idealX K).intValuation (P : K⟦X⟧) := by
  by_cases hP : P = 0
  · rw [hP, Valuation.map_zero, Polynomial.coe_zero, Valuation.map_zero]
  rw [intValuation_if_neg _ hP, intValuation_if_neg _ <| (by simp [hP])]
  simp only [idealX_span, exp_neg, inv_inj, exp_inj, Nat.cast_inj]
  have span_ne_zero :
    (Ideal.span {P} : Ideal K[X]) ≠ 0 ∧ (Ideal.span {Polynomial.X} : Ideal K[X]) ≠ 0 := by
    simp only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot, hP, Polynomial.X_ne_zero,
      not_false_iff, and_self_iff]
  have span_ne_zero' :
    (Ideal.span {↑P} : Ideal K⟦X⟧) ≠ 0 ∧ ((idealX K).asIdeal : Ideal K⟦X⟧) ≠ 0 := by
    simp only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot, coe_eq_zero_iff, hP,
      not_false_eq_true, true_and, (idealX K).3]
  classical
  rw [Ideal.count_associates_factors_eq span_ne_zero.1
    (Ideal.span_singleton_prime Polynomial.X_ne_zero |>.mpr prime_X) span_ne_zero.2,
    Ideal.count_associates_factors_eq]
  on_goal 1 => convert (normalized_count_X_eq_of_coe hP).symm
  exacts [Ideal.count_span_normalizedFactors_eq_of_normUnit hP Polynomial.normUnit_X prime_X,
    Ideal.count_span_normalizedFactors_eq_of_normUnit (by simp [hP]) normUnit_X X_prime,
    span_ne_zero'.1, (idealX K).isPrime, span_ne_zero'.2]

/-- The integral valuation of the power series `X : K⟦X⟧` equals `(ofAdd -1) : ℤᵐ⁰`. -/
@[simp]
theorem intValuation_X : (idealX K).intValuation X = exp (-1 : ℤ) := by
  rw [← Polynomial.coe_X, ← intValuation_eq_of_coe]
  exact intValuation_singleton _ Polynomial.X_ne_zero (idealX_span _)

end PowerSeries

namespace RatFunc

open IsDedekindDomain.HeightOneSpectrum PowerSeries
open scoped LaurentSeries

/-- `polynomialValuationX` is an abbreviation for the `X`-adic valuation given by
`(Polynomial.idealX K).valuation K⟮X⟯`. -/
abbrev polynomialValuationX : Valuation K⟮X⟯ ℤᵐ⁰ :=
  (Polynomial.idealX K).valuation _

theorem valuation_eq_LaurentSeries_valuation (P : K⟮X⟯) :
    polynomialValuationX K P = (PowerSeries.idealX K).valuation K⸨X⸩ P := by
  refine RatFunc.induction_on' P ?_
  intro f g h
  rw [Polynomial.valuation_of_mk K f h, RatFunc.mk_eq_mk' f h, Eq.comm]
  convert @valuation_of_mk' K⟦X⟧ _ _ K⸨X⸩ _ _ _ (PowerSeries.idealX K) f
        ⟨g, mem_nonZeroDivisors_iff_ne_zero.2 <| (by simp [h])⟩
  · simp [← IsScalarTower.algebraMap_apply K[X] K⟮X⟯ K⸨X⸩]
  exacts [intValuation_eq_of_coe _, intValuation_eq_of_coe _]

end RatFunc

namespace LaurentSeries


open IsDedekindDomain.HeightOneSpectrum PowerSeries RatFunc WithZero

instance valued : Valued K⸨X⸩ ℤᵐ⁰ := Valued.mk' ((PowerSeries.idealX K).valuation _)

lemma valuation_def : (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰) = (PowerSeries.idealX K).valuation _ := rfl

lemma valuation_coe_ratFunc (f : K⟮X⟯) :
    Valued.v (f : K⸨X⸩) = Valued.v f := by
  simp [adicValued_apply, ← valuation_eq_LaurentSeries_valuation]

theorem valuation_X_pow (s : ℕ) :
    Valued.v (((X : K⟦X⟧) : K⸨X⸩) ^ s) = exp (-(s : ℤ)) := by
  rw [map_pow, valuation_def, ← LaurentSeries.coe_algebraMap,
    valuation_of_algebraMap, intValuation_X, ← exp_nsmul, smul_neg, nsmul_one]

theorem valuation_single_zpow (s : ℤ) :
    Valued.v (HahnSeries.single s (1 : K) : K⸨X⸩) = exp (-(s : ℤ)) := by
  obtain s | s := s
  · rw [Int.ofNat_eq_natCast, ← HahnSeries.ofPowerSeries_X_pow, PowerSeries.coe_pow,
      valuation_X_pow]
  · rw [Int.negSucc_eq, ← inv_inj, ← map_inv₀, inv_single, neg_neg, ← Int.natCast_succ, inv_one,
      ← HahnSeries.ofPowerSeries_X_pow, PowerSeries.coe_pow, valuation_X_pow, exp_neg]

/- The coefficients of a power series vanish in degree strictly less than its valuation. -/
theorem coeff_zero_of_lt_intValuation {n d : ℕ} {f : K⟦X⟧}
    (H : Valued.v (f : K⸨X⸩) ≤ exp (-d : ℤ)) :
    n < d → coeff n f = 0 := by
  intro hnd
  apply (PowerSeries.X_pow_dvd_iff).mp _ n hnd
  rwa [← LaurentSeries.coe_algebraMap, valuation_def, valuation_of_algebraMap,
    intValuation_le_pow_iff_dvd (PowerSeries.idealX K) f d, PowerSeries.idealX,
    Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd] at H

/- The valuation of a power series is the order of the first non-zero coefficient. -/
theorem intValuation_le_iff_coeff_lt_eq_zero {d : ℕ} (f : K⟦X⟧) :
    Valued.v (f : K⸨X⸩) ≤ exp (-d : ℤ) ↔
      ∀ n : ℕ, n < d → coeff n f = 0 := by
  have : PowerSeries.X ^ d ∣ f ↔ ∀ n : ℕ, n < d → (PowerSeries.coeff n) f = 0 :=
    ⟨PowerSeries.X_pow_dvd_iff.mp, PowerSeries.X_pow_dvd_iff.mpr⟩
  rw [← this, ← LaurentSeries.coe_algebraMap, valuation_def, valuation_of_algebraMap,
    ← Ideal.span_singleton_dvd_span_singleton_iff_dvd, ← Ideal.span_singleton_pow]
  apply intValuation_le_pow_iff_dvd

/- The coefficients of a Laurent series vanish in degree strictly less than its valuation. -/
theorem coeff_zero_of_lt_valuation {n D : ℤ} {f : K⸨X⸩}
    (H : Valued.v f ≤ exp (-D)) : n < D → f.coeff n = 0 := by
  intro hnd
  by_cases! h_n_ord : n < f.order
  · exact coeff_eq_zero_of_lt_order h_n_ord
  set F := powerSeriesPart f with hF
  by_cases! ord_nonpos : f.order ≤ 0
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat ord_nonpos
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_le_iff_add_nonneg.mp (hs ▸ h_n_ord))
    obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (a := D + s) (by lia)
    rw [eq_add_neg_of_add_eq hm, add_comm, ← hs, ← powerSeriesPart_coeff]
    apply (intValuation_le_iff_coeff_lt_eq_zero K F).mp _ m (by linarith)
    rw [hF, ofPowerSeries_powerSeriesPart f, hs, neg_neg, ← hd, neg_add_rev, exp_add, map_mul,
      ← ofPowerSeries_X_pow s, PowerSeries.coe_pow, valuation_X_pow K s]
    gcongr
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat (Int.neg_nonpos_of_nonneg (le_of_lt ord_nonpos))
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (a := n - s) (by grind)
    obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (a := D - s) (by lia)
    rw [sub_eq_iff_eq_add.mp hm, add_comm, ← neg_neg (s : ℤ), ← hs, neg_neg,
      ← powerSeriesPart_coeff]
    apply (intValuation_le_iff_coeff_lt_eq_zero K F).mp _ m (by linarith)
    rw [hF, ofPowerSeries_powerSeriesPart f, map_mul, ← hd, hs, neg_sub, sub_eq_add_neg,
      exp_add, valuation_single_zpow, neg_neg]
    gcongr

/- The valuation of a Laurent series is the order of the first non-zero coefficient. -/
theorem valuation_le_iff_coeff_lt_eq_zero {D : ℤ} {f : K⸨X⸩} :
    Valued.v f ≤ exp (-D : ℤ) ↔ ∀ n : ℤ, n < D → f.coeff n = 0 := by
  refine ⟨fun hnD n hn => coeff_zero_of_lt_valuation K hnD hn, fun h_val_f => ?_⟩
  let F := powerSeriesPart f
  by_cases! ord_nonpos : f.order ≤ 0
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat ord_nonpos
    rw [← f.single_order_mul_powerSeriesPart, hs, map_mul, valuation_single_zpow, neg_neg, mul_comm,
      ← le_mul_inv_iff₀, exp_neg, ← mul_inv, ← exp_add, ← exp_neg]
    · by_cases! hDs : D + s ≤ 0
      · apply le_trans ((PowerSeries.idealX K).valuation_le_one F)
        rwa [← log_le_iff_le_exp one_ne_zero, le_neg, log_one, neg_zero]
      · obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le hDs.le
        rw [hd]
        apply (intValuation_le_iff_coeff_lt_eq_zero K F).mpr
        intro n hn
        rw [powerSeriesPart_coeff f n, hs]
        apply h_val_f
        lia
    · simp [ne_eq, zero_lt_iff]
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat <| neg_nonpos_of_nonneg ord_nonpos.le
    rw [neg_inj] at hs
    rw [← f.single_order_mul_powerSeriesPart, hs, map_mul, valuation_single_zpow, mul_comm,
      ← le_mul_inv_iff₀, ← exp_neg, ← exp_add, neg_neg]
    · by_cases! hDs : D - s ≤ 0
      · apply le_trans ((PowerSeries.idealX K).valuation_le_one F)
        rw [← log_le_iff_le_exp one_ne_zero, log_one]
        lia
      · obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le hDs.le
        rw [← neg_neg (-D + ↑s), ← sub_eq_neg_add, neg_sub, hd]
        apply (intValuation_le_iff_coeff_lt_eq_zero K F).mpr
        intro n hn
        rw [powerSeriesPart_coeff f n, hs]
        apply h_val_f (s + n)
        lia
    · simp [ne_eq, zero_lt_iff]

theorem valuation_le_iff_coeff_lt_log_eq_zero {D : ℤᵐ⁰} (hD : D ≠ 0) {f : K⸨X⸩} :
    Valued.v f ≤ D ↔ ∀ n : ℤ, n < -log D → f.coeff n = 0 := by
  cases D
  · simp_all
  · rename_i D
    cases D
    rename_i D
    rw [← exp, ← neg_neg D, valuation_le_iff_coeff_lt_eq_zero, log_exp, neg_neg]

/- Two Laurent series whose difference has small valuation have the same coefficients for
small enough indices. -/
theorem eq_coeff_of_valuation_sub_lt {d n : ℤ} {f g : K⸨X⸩}
    (H : Valued.v (g - f) ≤ exp (-d)) : n < d → g.coeff n = f.coeff n := by
  by_cases triv : g = f
  · exact fun _ => by rw [triv]
  · intro hn
    apply eq_of_sub_eq_zero
    rw [← HahnSeries.coeff_sub]
    apply coeff_zero_of_lt_valuation K H hn

/- Every Laurent series of valuation less than `(1 : ℤᵐ⁰)` comes from a power series. -/
theorem val_le_one_iff_eq_coe (f : K⸨X⸩) : Valued.v f ≤ (1 : ℤᵐ⁰) ↔
    ∃ F : K⟦X⟧, F = f := by
  rw [valuation_le_iff_coeff_lt_log_eq_zero _ one_ne_zero, log_one, neg_zero]
  refine ⟨fun h => ⟨PowerSeries.mk fun n => f.coeff n, ?_⟩, ?_⟩
  on_goal 1 => ext (_ | n)
  · simp only [Int.ofNat_eq_natCast, coeff_coe_powerSeries, coeff_mk]
  on_goal 1 => simp only [h (Int.negSucc n) (Int.negSucc_lt_zero n)]
  on_goal 2 => rintro ⟨F, rfl⟩ _ _
  all_goals
    apply HahnSeries.embDomain_notin_range
    simp only [Nat.coe_castAddMonoidHom, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
      Set.mem_range, not_exists, reduceCtorEq]
    intro
  · simp only [not_false_eq_true]
  · lia

end LaurentSeries

end AdicValuation

namespace LaurentSeries

variable {K : Type*} [Field K]

section Complete

open Filter WithZero PowerSeries

variable (K) in
lemma valuation_surjective : Function.Surjective (Valued.v (R := K⸨X⸩)) := by
  intro n
  by_cases hn0 : n = 0
  · use 0; simp [hn0]
  · use ((HahnSeries.single (-WithZero.log n)) 1)
    simp [LaurentSeries.valuation_single_zpow, exp_log hn0]

/- Sending a Laurent series to its `d`-th coefficient is uniformly continuous (independently of the
uniformity with which `K` is endowed). -/
theorem uniformContinuous_coeff {uK : UniformSpace K} (d : ℤ) :
    UniformContinuous fun f : K⸨X⸩ ↦ f.coeff d := by
  refine uniformContinuous_iff_eventually.mpr fun S hS ↦ eventually_iff_exists_mem.mpr ?_
  let γ : (ℤᵐ⁰)ˣ := Units.mk0 (exp (-(d + 1))) coe_ne_zero
  use {P | Valued.v (P.snd - P.fst) < ↑γ}
  refine ⟨?_, fun _ hP ↦ ?_⟩
  · obtain ⟨x, hx⟩ := LaurentSeries.valuation_surjective K γ
    have : Valued.v.restrict x ≠ 0 := fun h ↦ NeZero.ne γ.1 <|
      hx ▸ MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff.1 h
    rw [← hx, ← MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
    simp_rw [← Valued.v.restrict_lt_iff_lt_embedding]
    exact (Valued.hasBasis_uniformity K⸨X⸩ ℤᵐ⁰).mem_of_mem
      (i := Units.mk0 (Valued.v.restrict x) this) (by tauto)
  · simpa [eq_coeff_of_valuation_sub_lt K hP.le (lt_add_one _)] using mem_uniformity_of_eq hS rfl

/-- Since extracting coefficients is uniformly continuous, every Cauchy filter in
`K⸨X⸩` gives rise to a Cauchy filter in `K` for every `d : ℤ`, and such Cauchy filter
in `K` converges to a principal filter -/
def Cauchy.coeff {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) : ℤ → K :=
  let _ : UniformSpace K := ⊥
  fun d ↦ DiscreteUniformity.cauchyConst <| hℱ.map (uniformContinuous_coeff d)

theorem Cauchy.coeff_tendsto {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) (D : ℤ) :
    Tendsto (fun f : K⸨X⸩ ↦ f.coeff D) ℱ (𝓟 {coeff hℱ D}) :=
  let _ : UniformSpace K := ⊥
  le_of_eq <| DiscreteUniformity.eq_pure_cauchyConst
    (hℱ.map (uniformContinuous_coeff D)) ▸ (principal_singleton _).symm

/- For every Cauchy filter of Laurent series, there is some `N` such that the `n`-th coefficient
vanishes for all `n ≤ N` and almost all series in the filter. This is an auxiliary lemma used
to construct the limit of the Cauchy filter as a Laurent series, ensuring that the support of the
limit is `PWO`.
The result is true also for more general Hahn Series indexed over a partially ordered group `Γ`
beyond the special case `Γ = ℤ`, that corresponds to Laurent Series: nevertheless the proof below
does not generalise, as it relies on the study of the `X`-adic valuation attached to the height-one
prime `X`, and this is peculiar to the one-variable setting. In the future we should prove this
result in full generality and deduce the case `Γ = ℤ` from that one. -/
lemma Cauchy.exists_lb_eventual_support {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) :
    ∃ N, ∀ᶠ f : K⸨X⸩ in ℱ, ∀ n < N, f.coeff n = (0 : K) := by
  let entourage : Set (K⸨X⸩ × K⸨X⸩) := {P : K⸨X⸩ × K⸨X⸩ | Valued.v.restrict (P.snd - P.fst) < 1}
  let ζ : (MonoidWithZeroHom.ValueGroup₀ (Valued.v (R := K⸨X⸩)))ˣ :=
    Units.mk0 1 (zero_ne_one.symm)
  obtain ⟨S, ⟨hS, ⟨T, ⟨hT, H⟩⟩⟩⟩ := mem_prod_iff.mp <| Filter.le_def.mp hℱ.2 entourage
    <| (Valued.hasBasis_uniformity K⸨X⸩ ℤᵐ⁰).mem_of_mem (i := ζ) (by tauto)
  obtain ⟨f, hf⟩ := forall_mem_nonempty_iff_neBot.mpr hℱ.1 (S ∩ T) (inter_mem_iff.mpr ⟨hS, hT⟩)
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ g : K⸨X⸩,
    Valued.v (g - f) ≤ 1 → ∀ n < N, g.coeff n = 0 := by
    by_cases hf : f = 0
    · refine ⟨0, fun x hg ↦ ?_⟩
      rw [hf, sub_zero] at hg
      exact (valuation_le_iff_coeff_lt_eq_zero K).mp hg
    · refine ⟨min (f.2.isWF.min (HahnSeries.support_nonempty_iff.mpr hf)) 0 - 1, fun _ hg n hn ↦ ?_⟩
      rw [eq_coeff_of_valuation_sub_lt K hg (d := 0)]
      · exact Function.notMem_support.mp fun h ↦
        f.2.isWF.not_lt_min (HahnSeries.support_nonempty_iff.mpr hf) h
        <| lt_trans hn <| Int.sub_one_lt_iff.mpr <| min_le_left _ _
      exact lt_of_lt_of_le hn <| le_of_lt (Int.sub_one_lt_of_le <| min_le_right _ _)
  use N
  apply mem_of_superset (inter_mem hS hT)
  intro g hg
  have h_prod : (f, g) ∈ S ×ˢ T := by simp [hf.1, hg.2]
  refine hN g (le_of_lt ?_)
  simpa [Valuation.restrict_def, ← Valuation.restrict_lt_one_iff] using H h_prod

/- The support of `Cauchy.coeff` has a lower bound. -/
theorem Cauchy.exists_lb_support {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) :
    ∃ N, ∀ n, n < N → coeff hℱ n = 0 := by
  let _ : UniformSpace K := ⊥
  obtain ⟨N, hN⟩ := exists_lb_eventual_support hℱ
  refine ⟨N, fun n hn ↦ Ultrafilter.eq_of_le_pure (hℱ.map (uniformContinuous_coeff n)).1
      ((principal_singleton _).symm ▸ coeff_tendsto _ _) ?_⟩
  simp only [pure_zero, nonpos_iff]
  apply Filter.mem_of_superset hN (fun _ ha ↦ ha _ hn)

/- The support of `Cauchy.coeff` is bounded below -/
theorem Cauchy.coeff_support_bddBelow {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) :
    BddBelow (coeff hℱ).support := by
  refine ⟨(exists_lb_support hℱ).choose, fun d hd ↦ ?_⟩
  by_contra hNd
  exact hd ((exists_lb_support hℱ).choose_spec d (not_le.mp hNd))

/-- To any Cauchy filter ℱ of `K⸨X⸩`, we can attach a laurent series that is the limit
of the filter. Its `d`-th coefficient is defined as the limit of `Cauchy.coeff hℱ d`, which is
again Cauchy but valued in the discrete space `K`. That sufficiently negative coefficients vanish
follows from `Cauchy.coeff_support_bddBelow` -/
def Cauchy.limit {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) : K⸨X⸩ :=
  HahnSeries.mk (coeff hℱ) <| Set.IsWF.isPWO (coeff_support_bddBelow _).wellFoundedOn_lt

/- The following lemma shows that for every `d` smaller than the minimum between the integers
produced in `Cauchy.exists_lb_eventual_support` and `Cauchy.exists_lb_support`, for almost all
series in `ℱ` the `d`th coefficient coincides with the `d`th coefficient of `Cauchy.coeff hℱ`. -/
theorem Cauchy.exists_lb_coeff_ne {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) :
    ∃ N, ∀ᶠ f : K⸨X⸩ in ℱ, ∀ d < N, coeff hℱ d = f.coeff d := by
  obtain ⟨⟨N₁, hN₁⟩, ⟨N₂, hN₂⟩⟩ := exists_lb_eventual_support hℱ, exists_lb_support hℱ
  refine ⟨min N₁ N₂, ℱ.3 hN₁ fun _ hf d hd ↦ ?_⟩
  rw [hf d (lt_of_lt_of_le hd (min_le_left _ _)), hN₂ d (lt_of_lt_of_le hd (min_le_right _ _))]

/- Given a Cauchy filter `ℱ` in the Laurent Series and a bound `D`, for almost all series in the
filter the coefficients below `D` coincide with `Cauchy.coeff hℱ`. -/
theorem Cauchy.coeff_eventually_equal {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) {D : ℤ} :
    ∀ᶠ f : K⸨X⸩ in ℱ, ∀ d, d < D → coeff hℱ d = f.coeff d := by
  -- `φ` sends `d` to the set of Laurent Series having `d`th coefficient equal to `ℱ.coeff`.
  let φ : ℤ → Set K⸨X⸩ := fun d ↦ {f | coeff hℱ d = f.coeff d}
  have intersec₁ :
    (⋂ n ∈ Set.Iio D, φ n) ⊆ {x : K⸨X⸩ | ∀ d : ℤ, d < D → coeff hℱ d = x.coeff d} := by
    intro _ hf
    simpa only [Set.mem_iInter] using hf
  -- The goal is now to show that the intersection of all `φ d` (for `d < D`) is in `ℱ`.
  let ℓ := (exists_lb_coeff_ne hℱ).choose
  let N := max ℓ D
  have intersec₂ : ⋂ n ∈ Set.Iio D, φ n ⊇ (⋂ n ∈ Set.Iio ℓ, φ n) ∩ (⋂ n ∈ Set.Icc ℓ N, φ n) := by
    simp only [Set.mem_Iio, Set.mem_Icc, Set.subset_iInter_iff]
    intro i hi x hx
    simp only [Set.mem_inter_iff, Set.mem_iInter, and_imp] at hx
    by_cases! H : i < ℓ
    exacts [hx.1 _ H, hx.2 _ H <| le_of_lt <| lt_max_of_lt_right hi]
  suffices (⋂ n ∈ Set.Iio ℓ, φ n) ∩ (⋂ n ∈ Set.Icc ℓ N, φ n) ∈ ℱ by
    exact ℱ.sets_of_superset this <| intersec₂.trans intersec₁
  /- To show that the intersection we have in sight is in `ℱ`, we use that it contains a double
  intersection (an infinite and a finite one): by general properties of filters, we are reduced
  to show that both terms are in `ℱ`, which is easy in light of their definition. -/
  · simp only [Set.mem_Iio, inter_mem_iff]
    constructor
    · have := (exists_lb_coeff_ne hℱ).choose_spec
      rw [Filter.eventually_iff] at this
      convert this
      ext
      simp only [Set.mem_iInter, Set.mem_setOf_eq]; rfl
    · rw [biInter_mem (Set.finite_Icc ℓ N)]
      intro i _
      apply (coeff_tendsto hℱ _).eventually
      simp

open scoped Topology
open MonoidWithZeroHom.ValueGroup₀

/- The main result showing that the Cauchy filter tends to the `Cauchy.limit` -/
theorem Cauchy.eventually_mem_nhds {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ)
    {U : Set K⸨X⸩} (hU : U ∈ 𝓝 (Cauchy.limit hℱ)) : ∀ᶠ f in ℱ, f ∈ U := by
  obtain ⟨γ, hU₁⟩ := Valued.mem_nhds.mp hU
  suffices ∀ᶠ f in ℱ, f ∈ {y : K⸨X⸩ | Valued.v (y - limit hℱ) < embedding γ.1} by
    simp_rw [← Valued.v.restrict_lt_iff_lt_embedding] at this
    apply this.mono fun _ hf ↦ hU₁ hf
  set D := -(log (embedding γ.1) - 1) with hD₀
  have hD : exp (-D) < embedding γ.1 := by
    rw [← lt_log_iff_exp_lt (by simp), hD₀]
    simp
  apply coeff_eventually_equal (D := D) hℱ |>.mono
  intro _ hf
  apply lt_of_le_of_lt (valuation_le_iff_coeff_lt_eq_zero K |>.mpr _) hD
  intro n hn
  rw [HahnSeries.coeff_sub, sub_eq_zero, eq_comm]
  exact hf _ hn

/- Laurent Series with coefficients in a field are complete w.r.t. the `X`-adic valuation -/
instance instLaurentSeriesComplete : CompleteSpace K⸨X⸩ :=
  ⟨fun hℱ ↦ ⟨Cauchy.limit hℱ, fun _ hS ↦ Cauchy.eventually_mem_nhds hℱ hS⟩⟩

end Complete

section Dense

open scoped Multiplicative

open LaurentSeries PowerSeries IsDedekindDomain.HeightOneSpectrum WithZero RatFunc

theorem exists_Polynomial_intValuation_lt (F : K⟦X⟧) (η : ℤᵐ⁰ˣ) :
    ∃ P : K[X], (PowerSeries.idealX K).intValuation (F - P) < η := by
  by_cases! h_neg : 1 < η
  · use 0
    simpa using (intValuation_le_one (PowerSeries.idealX K) F).trans_lt h_neg
  · rw [← Units.val_le_val, Units.val_one, ← WithZero.coe_one, ← coe_unzero η.ne_zero,
      coe_le_coe, ← Multiplicative.toAdd_le, toAdd_one] at h_neg
    obtain ⟨d, hd⟩ := Int.exists_eq_neg_ofNat h_neg
    use F.trunc (d + 1)
    have : Valued.v ((ofPowerSeries ℤ K) (F - (trunc (d + 1) F))) ≤
      (Multiplicative.ofAdd (-(d + 1 : ℤ))) := by
      apply (intValuation_le_iff_coeff_lt_eq_zero K _).mpr
      simpa only [map_sub, sub_eq_zero, Polynomial.coeff_coe, coeff_trunc] using
        fun _ h ↦ (if_pos h).symm
    rw [neg_add, ofAdd_add, ← hd, ofAdd_toAdd, WithZero.coe_mul, coe_unzero,
      ← coe_algebraMap] at this
    rw [← valuation_of_algebraMap (K := K⸨X⸩) (PowerSeries.idealX K) (F - F.trunc (d + 1))]
    apply lt_of_le_of_lt this
    rw [← mul_one (η : ℤᵐ⁰), mul_assoc, one_mul]
    gcongr
    · exact zero_lt_iff.2 η.ne_zero
    rw [← WithZero.coe_one, coe_lt_coe, ofAdd_neg, Right.inv_lt_one_iff, ← ofAdd_zero,
      Multiplicative.ofAdd_lt]
    exact Int.zero_lt_one

/-- For every Laurent series `f` and every `γ : ℤᵐ⁰` one can find a rational function `Q` such
that the `X`-adic valuation `v` satisfies `v (f - Q) < γ`. -/
theorem exists_ratFunc_val_lt (f : K⸨X⸩) (γ : ℤᵐ⁰ˣ) :
    ∃ Q : K⟮X⟯, Valued.v (f - Q) < γ := by
  set F := f.powerSeriesPart with hF
  by_cases! ord_nonpos : f.order < 0
  · set η : ℤᵐ⁰ˣ := Units.mk0 (exp f.order) coe_ne_zero
      with hη
    obtain ⟨P, hP⟩ := exists_Polynomial_intValuation_lt F (η * γ)
    use RatFunc.X ^ f.order * (P : K⟮X⟯)
    have F_mul := f.ofPowerSeries_powerSeriesPart
    obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat (le_of_lt ord_nonpos)
    rw [← hF, hs, neg_neg, ← ofPowerSeries_X_pow s, ← inv_mul_eq_iff_eq_mul₀] at F_mul
    · have : (algebraMap K⟮X⟯ K⸨X⸩) 1 = 1 := by exact algebraMap.coe_one
      rw [hs, ← F_mul, PowerSeries.coe_pow, PowerSeries.coe_X, map_mul, zpow_neg,
        zpow_natCast, inv_eq_one_div (RatFunc.X ^ s), map_div₀, map_pow,
        RatFunc.coe_X]
      simp only [map_one]
      rw [← inv_eq_one_div, ← mul_sub, map_mul, map_inv₀,
        ← PowerSeries.coe_X, valuation_X_pow, ← hs, ← RatFunc.coe_coe, ← PowerSeries.coe_sub,
        ← coe_algebraMap, adicValued_apply, valuation_of_algebraMap,
        ← Units.val_mk0 (a := exp f.order) exp_ne_zero, ← hη]
      apply inv_mul_lt_of_lt_mul₀
      rwa [← Units.val_mul]
    · simp
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat (Int.neg_nonpos_of_nonneg ord_nonpos)
    obtain ⟨P, hP⟩ := exists_Polynomial_intValuation_lt (PowerSeries.X ^ s * F) γ
    use P
    rw [← X_order_mul_powerSeriesPart (neg_inj.1 hs).symm, ← RatFunc.coe_coe,
      ← PowerSeries.coe_sub, ← coe_algebraMap, adicValued_apply, valuation_of_algebraMap]
    exact hP

open MonoidWithZeroHom.ValueGroup₀

theorem coe_range_dense : DenseRange ((↑) : K⟮X⟯ → K⸨X⸩) := by
  rw [denseRange_iff_closure_range]
  ext f
  simp only [UniformSpace.mem_closure_iff_symm_ball, Set.mem_univ, iff_true, Set.Nonempty,
    Set.mem_inter_iff, Set.mem_range, exists_exists_eq_and]
  intro V hV h_symm
  rw [uniformity_eq_comap_neg_add_nhds_zero_swapped] at hV
  obtain ⟨T, hT₀, hT₁⟩ := hV
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hT₀
  have := (embedding γ.1)
  obtain ⟨P, hP⟩ := exists_ratFunc_val_lt f
    (Units.map (embedding (f := (valued K).v)).toMonoidHom γ)
  use P
  apply hT₁
  apply hγ
  simpa only [Units.coe_map, MonoidHom.coe_mk, ZeroHom.toFun_eq_coe, OneHom.coe_mk, add_comm,
    MonoidWithZeroHom.toZeroHom_coe, ← sub_eq_add_neg, Set.mem_setOf_eq,
    Valuation.restrict_lt_iff_lt_embedding]

end Dense

section Comparison

open RatFunc AbstractCompletion IsDedekindDomain.HeightOneSpectrum WithZero

lemma exists_ratFunc_eq_v (x : K⸨X⸩) : ∃ f : K⟮X⟯, Valued.v f = Valued.v x := by
  by_cases hx : Valued.v x = 0
  · use 0
    simp [hx]
  use RatFunc.X ^ (-log (Valued.v x))
  rw [zpow_neg, map_inv₀, map_zpow₀, v_def, valuation_X_eq_neg_one, ← exp_zsmul, ← exp_neg]
  simp [exp_log, hx]

open MonoidWithZeroHom.ValueGroup₀

theorem inducing_coe : IsUniformInducing ((↑) : K⟮X⟯ → K⸨X⸩) := by
  rw [isUniformInducing_iff, Filter.comap]
  ext S
  simp only [Filter.mem_mk, Set.mem_setOf_eq, uniformity_eq_comap_nhds_zero,
    Filter.mem_comap]
  constructor
  · rintro ⟨T, ⟨⟨R, ⟨hR, pre_R⟩⟩, pre_T⟩⟩
    obtain ⟨d, hd⟩ := Valued.mem_nhds.mp hR
    use {P : K⟮X⟯ | Valued.v P < embedding d.1}
    simp only [Valued.mem_nhds, sub_zero]
    refine ⟨?_, subset_trans (fun _ _ ↦ pre_R ?_) pre_T⟩
    · obtain ⟨x, hx⟩ := RatFunc.valuation_surjective K (embedding d.1)
      use Units.mk0 (Valued.v.restrict x) (by
        rw [Valuation.restrict_def, ne_eq, restrict₀_eq_zero_iff]; simp [hx])
      simp [v_def, Valuation.restrict_lt_iff, ← hx]
    apply hd
    simp only [sub_zero, Set.mem_setOf_eq]
    rw [← map_sub, Valuation.restrict_lt_iff_lt_embedding]
    simp only [valuation_def]
    rwa [← valuation_eq_LaurentSeries_valuation]
  · rintro ⟨_, ⟨hT, pre_T⟩⟩
    obtain ⟨d, hd⟩ := Valued.mem_nhds.mp hT
    set X := {f : K⸨X⸩ | Valued.v f < embedding d.1} with X_def
    refine ⟨(fun x : K⸨X⸩ × K⸨X⸩ ↦ x.snd - x.fst) ⁻¹' X, ⟨X, ?_⟩, ?_⟩
    · refine ⟨?_, Set.Subset.refl _⟩
      · simp only [Valued.mem_nhds, sub_zero, Valuation.restrict_lt_iff_lt_embedding]
        obtain ⟨x, hx⟩ := restrict₀_surjective _ d.1
        use Units.mk0 (Valued.v.restrict (x : K⸨X⸩)) (by
          rw [Valuation.restrict_def, ne_eq, restrict₀_eq_zero_iff, valuation_def,
            ← valuation_eq_LaurentSeries_valuation, ← v_def, ← restrict₀_eq_zero_iff]
          simp [hx])
        simp only [Units.val_mk0, ← Valuation.restrict_lt_iff_lt_embedding,
          X_def, Set.setOf_subset_setOf, Valuation.restrict_lt_iff]
        rw [← hx, embedding_restrict₀]
        simp [v_def, valuation_coe_ratFunc]
    · refine subset_trans (fun _ _ ↦ ?_) pre_T
      apply hd
      rw [Set.mem_setOf_eq, sub_zero, Valuation.restrict_lt_iff_lt_embedding, v_def,
        valuation_eq_LaurentSeries_valuation, map_sub]
      assumption

theorem uniformContinuous_withVal_equiv :
    UniformContinuous (WithVal.equiv (polynomialValuationX K)) :=
  (Valuation.IsEquiv.refl).uniformContinuous_equiv rfl

theorem continuous_coe : Continuous ((↑) : K⟮X⟯ → K⸨X⸩) :=
  (isUniformInducing_iff'.1 (inducing_coe)).1.continuous

/-- The `X`-adic completion as an abstract completion of `K⟮X⟯` -/
abbrev ratfuncAdicComplPkg : AbstractCompletion (WithVal (polynomialValuationX K)) :=
  UniformSpace.Completion.cPkg

variable (K)
/-- Having established that the `K⸨X⸩` is complete and contains `K⟮X⟯` as a dense
subspace, it gives rise to an abstract completion of `K⟮X⟯`. -/
noncomputable def LaurentSeriesPkg :
    AbstractCompletion (WithVal (polynomialValuationX K)) where
  space := K⸨X⸩
  coe := (↑) ∘ WithVal.equiv _
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing :=
    inducing_coe.comp (WithVal.uniformEquiv rfl Valuation.IsEquiv.refl).isUniformInducing
  dense := .comp coe_range_dense (WithVal.equiv _).surjective.denseRange continuous_coe

theorem continuous_coe' :
    Continuous (((↑) : K⟮X⟯ → K⸨X⸩) ∘ WithVal.equiv (polynomialValuationX K)) :=
  continuous_coe.comp uniformContinuous_withVal_equiv.continuous

instance : TopologicalSpace (LaurentSeriesPkg K).space :=
  (LaurentSeriesPkg K).uniformStruct.toTopologicalSpace

@[simp]
theorem LaurentSeries_coe (x : K⟮X⟯) :
    (LaurentSeriesPkg K).coe (WithVal.toVal _ x) = (x : K⸨X⸩) := by
  rfl

/-- Reinterpret the extension of `coe : WithVal ((idealX K).valuation _) → K⸨X⸩` as a ring
homomorphism -/
abbrev extensionAsRingHom :=
  UniformSpace.Completion.extensionHom <|
    (algebraMap K⟮X⟯ K⸨X⸩).comp (WithVal.equiv (polynomialValuationX K)).toRingHom

/-- An abbreviation for the `X`-adic completion of `K⟮X⟯` -/
abbrev RatFuncAdicCompl := adicCompletion K⟮X⟯ (idealX K)

/- The two instances below make `comparePkg` and `comparePkg_eq_extension` slightly faster. -/
instance : UniformSpace (RatFuncAdicCompl K) := inferInstance
instance : UniformSpace K⸨X⸩ := inferInstance

/-- The uniform space isomorphism between two abstract completions of `ratfunc K` -/
abbrev comparePkg : RatFuncAdicCompl K ≃ᵤ K⸨X⸩ :=
  compareEquiv ratfuncAdicComplPkg (LaurentSeriesPkg K)

lemma comparePkg_eq_extension (x : RatFuncAdicCompl K) :
    (comparePkg K) x = (extensionAsRingHom K (continuous_coe' _)) x := rfl

/-- The uniform space equivalence between two abstract completions of `ratfunc K` as a ring
equivalence: this will be the *inverse* of the fundamental one. -/
abbrev ratfuncAdicComplRingEquiv : RatFuncAdicCompl K ≃+* K⸨X⸩ :=
  { comparePkg K with
    map_mul' := by
      intro x y
      rw [Equiv.toFun_as_coe, UniformEquiv.coe_toEquiv, comparePkg_eq_extension,
        (extensionAsRingHom K (continuous_coe' _)).map_mul]
      simp [← comparePkg_eq_extension]
    map_add' := by
      intro x y
      rw [Equiv.toFun_as_coe, UniformEquiv.coe_toEquiv, comparePkg_eq_extension,
        (extensionAsRingHom K (continuous_coe' _)).map_add]
      simp [← comparePkg_eq_extension] }

/-- The uniform space equivalence between two abstract completions of `ratfunc K` as a ring
equivalence: it goes from `K⸨X⸩` to `RatFuncAdicCompl K` -/
abbrev LaurentSeriesRingEquiv : K⸨X⸩ ≃+* RatFuncAdicCompl K :=
  (ratfuncAdicComplRingEquiv K).symm

@[simp]
lemma LaurentSeriesRingEquiv_def (f : K⟦X⟧) :
    (LaurentSeriesRingEquiv K) f = (LaurentSeriesPkg K).compare ratfuncAdicComplPkg (f : K⸨X⸩) :=
  rfl

@[simp]
theorem ratfuncAdicComplRingEquiv_apply (x : RatFuncAdicCompl K) :
    ratfuncAdicComplRingEquiv K x = ratfuncAdicComplPkg.compare (LaurentSeriesPkg K) x := rfl

theorem coe_X_compare :
    (ratfuncAdicComplRingEquiv K) ((RatFunc.X : K⟮X⟯) : RatFuncAdicCompl K) =
      ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) := by
  rw [PowerSeries.coe_X, ← RatFunc.coe_X, ← LaurentSeries_coe, ← compare_coe]
  rfl

theorem algebraMap_apply (a : K) : algebraMap K K⸨X⸩ a = HahnSeries.C a := by
  simp [RingHom.algebraMap_toAlgebra]

instance : Algebra K (RatFuncAdicCompl K) :=
  RingHom.toAlgebra ((LaurentSeriesRingEquiv K).toRingHom.comp HahnSeries.C)

/-- The algebra equivalence between `K⸨X⸩` and the `X`-adic completion of `RatFunc X` -/
def LaurentSeriesAlgEquiv : K⸨X⸩ ≃ₐ[K] RatFuncAdicCompl K :=
  AlgEquiv.ofRingEquiv (f := LaurentSeriesRingEquiv K)
    (fun a ↦ by simp [RingHom.algebraMap_toAlgebra])

open Filter WithZero

open scoped WithZeroTopology Topology Multiplicative

theorem valuation_LaurentSeries_equal_extension :
    (LaurentSeriesPkg K).isDenseInducing.extend Valued.v = (Valued.v : K⸨X⸩ → ℤᵐ⁰) := by
  apply IsDenseInducing.extend_unique
  · intro x
    rw [← WithVal.apply_ofVal, valuation_eq_LaurentSeries_valuation K]
    rfl
  · exact Valued.continuous_valuation_of_surjective (valuation_surjective K)

theorem tendsto_valuation (a : (idealX K).adicCompletion K⟮X⟯) :
    Tendsto (Valued.v : K⟮X⟯ → ℤᵐ⁰) (comap (↑) (𝓝 a)) (𝓝 (Valued.v a : ℤᵐ⁰)) := by
  have := Valued.is_topological_valuation (R := (idealX K).adicCompletion K⟮X⟯)
  by_cases ha : a = 0
  · rw [tendsto_def]
    intro S hS
    rw [ha, map_zero, WithZeroTopology.hasBasis_nhds_zero.1 S] at hS
    obtain ⟨γ, γ_ne_zero, γ_le⟩ := hS
    use {t | Valued.v t < γ}
    constructor
    · rw [ha, this]
      obtain ⟨x, hx⟩ := valuedAdicCompletion_surjective K⟮X⟯ (idealX K) γ
      use Units.mk0 (Valued.v.restrict x) (by
        rwa [Valuation.restrict_def, ne_eq, restrict₀_eq_zero_iff, hx])
      simp [Units.val_mk0, Valuation.restrict_lt_iff, hx]
    · refine Set.Subset.trans (fun a _ ↦ ?_) (Set.preimage_mono γ_le)
      rw [Set.mem_preimage, Set.mem_Iio, ← Valued.valuedCompletion_apply a]
      simp_all
  · rw [WithZeroTopology.tendsto_of_ne_zero ((Valuation.ne_zero_iff Valued.v).mpr ha),
      Filter.eventually_comap, Filter.Eventually, Valued.mem_nhds]
    use Units.mk0 (Valued.v.restrict a) (by simp [Valuation.restrict_def, ha])
    simp only [Units.val_mk0, v_def, Set.setOf_subset_setOf]
    rintro y val_y b rfl
    rw [← valuedAdicCompletion_eq_valuation']
    exact (Valuation.restrict_inj _).mp <| Valuation.map_eq_of_sub_lt Valued.v.restrict val_y

/- The extension of the `X`-adic valuation from `K⟮X⟯` up to its abstract completion coincides,
modulo the isomorphism with `K⸨X⸩`, with the `X`-adic valuation on `K⸨X⸩`. -/
theorem valuation_compare (f : K⸨X⸩) :
    (Valued.v : (RatFuncAdicCompl K) → ℤᵐ⁰)
        (AbstractCompletion.compare (LaurentSeriesPkg K) ratfuncAdicComplPkg f) =
      Valued.v f := by
  letI : UniformSpace (ratfuncAdicComplPkg (K := K).space) :=
      ratfuncAdicComplPkg.uniformStruct
  rw [← valuation_LaurentSeries_equal_extension, ← compare_comp_eq_compare ratfuncAdicComplPkg _]
  · exact congr_fun (ratfuncAdicComplPkg.isDenseInducing.extend_unique
      Valued.valuedCompletion_apply (Valued.continuous_valuation_of_surjective
        (valuedAdicCompletion_surjective _ _))).symm _
  · refine Valued.continuous_valuation_of_surjective (fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := RatFunc.valuation_surjective K x
    exact ⟨.toVal _ y, rfl⟩
  · intro x
    have h_cont := Valued.continuous_valuation_of_surjective
      (valuedAdicCompletion_surjective K⟮X⟯ (idealX K))
    rw [ratfuncAdicComplPkg.isDenseInducing.extend_unique
        Valued.valuedCompletion_apply h_cont]
    exact (h_cont.continuousAt.tendsto.comp tendsto_comap).congr
      Valued.valuedCompletion_apply

section PowerSeries

/-- In order to compare `K⟦X⟧` with the valuation subring in the `X`-adic completion of
`K⟮X⟯` we consider its alias as a subring of `K⸨X⸩`. -/
abbrev powerSeries_as_subring : Subring K⸨X⸩ :=
  Subring.map (HahnSeries.ofPowerSeries ℤ K) ⊤

/-- The ring `K⟦X⟧` is isomorphic to the subring `powerSeries_as_subring K` -/
abbrev powerSeriesEquivSubring : K⟦X⟧ ≃+* powerSeries_as_subring K :=
  ((Subring.topEquiv).symm).trans (Subring.equivMapOfInjective ⊤ (ofPowerSeries ℤ K)
    ofPowerSeries_injective)

lemma powerSeriesEquivSubring_apply (f : K⟦X⟧) :
    powerSeriesEquivSubring K f =
      ⟨HahnSeries.ofPowerSeries ℤ K f, Subring.mem_map.mpr ⟨f, trivial, rfl⟩⟩ :=
  rfl

lemma powerSeriesEquivSubring_coe_apply (f : K⟦X⟧) :
    (powerSeriesEquivSubring K f : K⸨X⸩) = ofPowerSeries ℤ K f :=
  rfl

/- Through the isomorphism `LaurentSeriesRingEquiv`, power series land in the unit ball inside the
completion of `K⟮X⟯`. -/
theorem mem_integers_of_powerSeries (F : K⟦X⟧) :
    (LaurentSeriesRingEquiv K) F ∈ (idealX K).adicCompletionIntegers K⟮X⟯ := by
  simp only [mem_adicCompletionIntegers, LaurentSeriesRingEquiv_def,
    valuation_compare, val_le_one_iff_eq_coe]
  exact ⟨F, rfl⟩

/- Conversely, all elements in the unit ball inside the completion of `K⟮X⟯` come from a power
series through the isomorphism `LaurentSeriesRingEquiv`. -/
theorem exists_powerSeries_of_memIntegers {x : RatFuncAdicCompl K}
    (hx : x ∈ (idealX K).adicCompletionIntegers K⟮X⟯) :
    ∃ F : K⟦X⟧, (LaurentSeriesRingEquiv K) F = x := by
  set f := (ratfuncAdicComplRingEquiv K) x with hf
  have H_x : (LaurentSeriesPkg K).compare ratfuncAdicComplPkg ((ratfuncAdicComplRingEquiv K) x) =
      x := congr_fun (inverse_compare (LaurentSeriesPkg K) ratfuncAdicComplPkg) x
  rw [mem_adicCompletionIntegers, ← H_x] at hx
  obtain ⟨F, hF⟩ := (val_le_one_iff_eq_coe K f).mp (valuation_compare _ f ▸ hx)
  exact ⟨F, by rw [hF, hf, RingEquiv.symm_apply_apply]⟩

theorem powerSeries_ext_subring :
    Subring.map (LaurentSeriesRingEquiv K).toRingHom (powerSeries_as_subring K) =
      ((idealX K).adicCompletionIntegers K⟮X⟯).toSubring := by
  ext x
  refine ⟨fun ⟨f, ⟨F, _, coe_F⟩, hF⟩ ↦ ?_, fun H ↦ ?_⟩
  · simp only [ValuationSubring.mem_toSubring, ← hF, ← coe_F]
    apply mem_integers_of_powerSeries
  · obtain ⟨F, hF⟩ := exists_powerSeries_of_memIntegers K H
    simp only [Subring.mem_map]
    exact ⟨F, ⟨F, trivial, rfl⟩, hF⟩

/-- The ring isomorphism between `K⟦X⟧` and the unit ball inside the `X`-adic completion of
`K⟮X⟯`. -/
abbrev powerSeriesRingEquiv : K⟦X⟧ ≃+* (idealX K).adicCompletionIntegers K⟮X⟯ :=
  ((powerSeriesEquivSubring K).trans (LaurentSeriesRingEquiv K).subringMap).trans
    <| RingEquiv.subringCongr (powerSeries_ext_subring K)

lemma powerSeriesRingEquiv_coe_apply (f : K⟦X⟧) :
    powerSeriesRingEquiv K f = LaurentSeriesRingEquiv K (f : K⸨X⸩) :=
  rfl

lemma LaurentSeriesRingEquiv_mem_valuationSubring (f : K⟦X⟧) :
    LaurentSeriesRingEquiv K f ∈ Valued.v.valuationSubring := by
  simp only [Valuation.mem_valuationSubring_iff]
  rw [LaurentSeriesRingEquiv_def, valuation_compare, val_le_one_iff_eq_coe]
  use f

lemma algebraMap_C_mem_adicCompletionIntegers (x : K) :
    ((LaurentSeriesRingEquiv K).toRingHom.comp HahnSeries.C) x ∈
      adicCompletionIntegers K⟮X⟯ (idealX K) := by
  have : HahnSeries.C x = ofPowerSeries ℤ K (PowerSeries.C x) := by
    simp [C_apply, ofPowerSeries_C]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this]
  apply LaurentSeriesRingEquiv_mem_valuationSubring

instance : Algebra K ((idealX K).adicCompletionIntegers K⟮X⟯) :=
  RingHom.toAlgebra <|
    ((LaurentSeriesRingEquiv K).toRingHom.comp HahnSeries.C).codRestrict _
      (algebraMap_C_mem_adicCompletionIntegers K)

/-- The algebra isomorphism between `K⟦X⟧` and the unit ball inside the `X`-adic completion of
`K⟮X⟯`. -/
def powerSeriesAlgEquiv : K⟦X⟧ ≃ₐ[K] (idealX K).adicCompletionIntegers K⟮X⟯ := by
  apply AlgEquiv.ofRingEquiv (f := powerSeriesRingEquiv K)
  intro a
  rw [PowerSeries.algebraMap_eq, RingHom.algebraMap_toAlgebra, ← Subtype.coe_inj,
    powerSeriesRingEquiv_coe_apply,
    RingHom.codRestrict_apply _ _ (algebraMap_C_mem_adicCompletionIntegers K)]
  simp

end PowerSeries

end Comparison

end LaurentSeries
