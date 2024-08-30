/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Laurent Series

## Main Definitions
* Defines `LaurentSeries` as an abbreviation for `HahnSeries ℤ`.
* Defines `hasseDeriv` of a Laurent series with coefficients in a module over a ring.
* Provides a coercion `PowerSeries R` into `LaurentSeries R` given by
  `HahnSeries.ofPowerSeries`.
* Defines `LaurentSeries.powerSeriesPart`
* Defines the localization map `LaurentSeries.of_powerSeries_localization` which evaluates to
  `HahnSeries.ofPowerSeries`.
* Embedding of rational functions into Laurent series, provided as a coercion, utilizing
the underlying `RatFunc.coeAlgHom`.
* Study of the `X`-Adic valuation on the ring of Laurent series over a field

## Main Results
* Basic properties of Hasse derivatives
### About the `X`-Adic valuation:
* The (integral) valuation of a power series is the order of the first non-zero coefficient, see
`intValuation_le_iff_coeff_lt_eq_zero`.
* The valuation of a Laurent series is the order of the first non-zero coefficient, see
`valuation_le_iff_coeff_lt_eq_zero`.
* Every Laurent series of valuation less than `(1 : ℤₘ₀)` comes from a power series, see
`val_le_one_iff_eq_coe`.

## Implementation details
* Since `LaurentSeries` is just an abbreviation of `HahnSeries ℤ _`, the definition of the
coefficients is given in terms of `HahnSeries.coeff` and this forces sometimes to go back-and-forth
from `X : LaurentSeries _` to `single 1 1 : HahnSeries ℤ _`.

-/
universe u

open scoped Classical
open HahnSeries Polynomial

noncomputable section

/-- A `LaurentSeries` is implemented as a `HahnSeries` with value group `ℤ`. -/
abbrev LaurentSeries (R : Type u) [Zero R] :=
  HahnSeries ℤ R

variable {R : Type*}

namespace LaurentSeries

section HasseDeriv

/-- The Hasse derivative of Laurent series, as a linear map. -/
@[simps]
def hasseDeriv (R : Type*) {V : Type*} [AddCommGroup V] [Semiring R] [Module R V] (k : ℕ) :
    LaurentSeries V →ₗ[R] LaurentSeries V where
  toFun f := HahnSeries.ofSuppBddBelow (fun (n : ℤ) => (Ring.choose (n + k) k) • f.coeff (n + k))
    (forallLTEqZero_supp_BddBelow _ (f.order - k : ℤ)
    (fun _ h_lt ↦ by rw [coeff_eq_zero_of_lt_order <| lt_sub_iff_add_lt.mp h_lt, smul_zero]))
  map_add' f g := by
    ext
    simp only [ofSuppBddBelow, add_coeff', Pi.add_apply, smul_add]
  map_smul' r f := by
    ext
    simp only [ofSuppBddBelow, smul_coeff, RingHom.id_apply, smul_comm r]

variable [Semiring R] {V : Type*} [AddCommGroup V] [Module R V]

theorem hasseDeriv_coeff (k : ℕ) (f : LaurentSeries V) (n : ℤ) :
    (hasseDeriv R k f).coeff n = Ring.choose (n + k) k • f.coeff (n + k) :=
  rfl

end HasseDeriv

section Semiring

variable [Semiring R]

instance : Coe (PowerSeries R) (LaurentSeries R) :=
  ⟨HahnSeries.ofPowerSeries ℤ R⟩

/- Porting note: now a syntactic tautology and not needed elsewhere
theorem coe_powerSeries (x : PowerSeries R) :
    (x : LaurentSeries R) = HahnSeries.ofPowerSeries ℤ R x :=
  rfl -/

@[simp]
theorem coeff_coe_powerSeries (x : PowerSeries R) (n : ℕ) :
    HahnSeries.coeff (x : LaurentSeries R) n = PowerSeries.coeff R n x := by
  rw [ofPowerSeries_apply_coeff]

/-- This is a power series that can be multiplied by an integer power of `X` to give our
  Laurent series. If the Laurent series is nonzero, `powerSeriesPart` has a nonzero
  constant term. -/
def powerSeriesPart (x : LaurentSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => x.coeff (x.order + n)

@[simp]
theorem powerSeriesPart_coeff (x : LaurentSeries R) (n : ℕ) :
    PowerSeries.coeff R n x.powerSeriesPart = x.coeff (x.order + n) :=
  PowerSeries.coeff_mk _ _

@[simp]
theorem powerSeriesPart_zero : powerSeriesPart (0 : LaurentSeries R) = 0 := by
  ext
  simp [(PowerSeries.coeff _ _).map_zero] -- Note: this doesn't get picked up any more

@[simp]
theorem powerSeriesPart_eq_zero (x : LaurentSeries R) : x.powerSeriesPart = 0 ↔ x = 0 := by
  constructor
  · contrapose!
    simp only [ne_eq]
    intro h
    rw [PowerSeries.ext_iff, not_forall]
    refine ⟨0, ?_⟩
    simp [coeff_order_ne_zero h]
  · rintro rfl
    simp

@[simp]
theorem single_order_mul_powerSeriesPart (x : LaurentSeries R) :
    (single x.order 1 : LaurentSeries R) * x.powerSeriesPart = x := by
  ext n
  rw [← sub_add_cancel n x.order, single_mul_coeff_add, sub_add_cancel, one_mul]
  by_cases h : x.order ≤ n
  · rw [Int.eq_natAbs_of_zero_le (sub_nonneg_of_le h), coeff_coe_powerSeries,
      powerSeriesPart_coeff, ← Int.eq_natAbs_of_zero_le (sub_nonneg_of_le h),
      add_sub_cancel]
  · rw [ofPowerSeries_apply, embDomain_notin_range]
    · contrapose! h
      exact order_le_of_coeff_ne_zero h.symm
    · contrapose! h
      simp only [Set.mem_range, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at h
      obtain ⟨m, hm⟩ := h
      rw [← sub_nonneg, ← hm]
      simp only [Nat.cast_nonneg]

theorem ofPowerSeries_powerSeriesPart (x : LaurentSeries R) :
    ofPowerSeries ℤ R x.powerSeriesPart = single (-x.order) 1 * x := by
  refine Eq.trans ?_ (congr rfl x.single_order_mul_powerSeriesPart)
  rw [← mul_assoc, single_mul_single, neg_add_cancel, mul_one, ← C_apply, C_one, one_mul]

end Semiring

instance [CommSemiring R] : Algebra (PowerSeries R) (LaurentSeries R) :=
  (HahnSeries.ofPowerSeries ℤ R).toAlgebra

@[simp]
theorem coe_algebraMap [CommSemiring R] :
    ⇑(algebraMap (PowerSeries R) (LaurentSeries R)) = HahnSeries.ofPowerSeries ℤ R :=
  rfl

/-- The localization map from power series to Laurent series. -/
@[simps (config := { rhsMd := .all, simpRhs := true })]
instance of_powerSeries_localization [CommRing R] :
    IsLocalization (Submonoid.powers (PowerSeries.X : PowerSeries R)) (LaurentSeries R) where
  map_units' := by
    rintro ⟨_, n, rfl⟩
    refine ⟨⟨single (n : ℤ) 1, single (-n : ℤ) 1, ?_, ?_⟩, ?_⟩
    · simp
    · simp
    · dsimp; rw [ofPowerSeries_X_pow]
  surj' z := by
    by_cases h : 0 ≤ z.order
    · refine ⟨⟨PowerSeries.X ^ Int.natAbs z.order * powerSeriesPart z, 1⟩, ?_⟩
      simp only [RingHom.map_one, mul_one, RingHom.map_mul, coe_algebraMap, ofPowerSeries_X_pow,
        Submonoid.coe_one]
      rw [Int.natAbs_of_nonneg h, single_order_mul_powerSeriesPart]
    · refine ⟨⟨powerSeriesPart z, PowerSeries.X ^ Int.natAbs z.order, ⟨_, rfl⟩⟩, ?_⟩
      simp only [coe_algebraMap, ofPowerSeries_powerSeriesPart]
      rw [mul_comm _ z]
      refine congr rfl ?_
      rw [ofPowerSeries_X_pow, Int.ofNat_natAbs_of_nonpos]
      exact le_of_not_ge h
  exists_of_eq {x y} := by
    rw [coe_algebraMap, ofPowerSeries_injective.eq_iff]
    rintro rfl
    exact ⟨1, rfl⟩

instance {K : Type*} [Field K] : IsFractionRing (PowerSeries K) (LaurentSeries K) :=
  IsLocalization.of_le (Submonoid.powers (PowerSeries.X : PowerSeries K)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero) fun _ hf =>
    isUnit_of_mem_nonZeroDivisors <| map_mem_nonZeroDivisors _ HahnSeries.ofPowerSeries_injective hf

end LaurentSeries

namespace PowerSeries

open LaurentSeries

variable {R' : Type*} [Semiring R] [Ring R'] (f g : PowerSeries R) (f' g' : PowerSeries R')

@[norm_cast] -- Porting note (#10618): simp can prove this
theorem coe_zero : ((0 : PowerSeries R) : LaurentSeries R) = 0 :=
  (ofPowerSeries ℤ R).map_zero

@[norm_cast] -- Porting note (#10618): simp can prove this
theorem coe_one : ((1 : PowerSeries R) : LaurentSeries R) = 1 :=
  (ofPowerSeries ℤ R).map_one

@[norm_cast] -- Porting note (#10618): simp can prove this
theorem coe_add : ((f + g : PowerSeries R) : LaurentSeries R) = f + g :=
  (ofPowerSeries ℤ R).map_add _ _

@[norm_cast]
theorem coe_sub : ((f' - g' : PowerSeries R') : LaurentSeries R') = f' - g' :=
  (ofPowerSeries ℤ R').map_sub _ _

@[norm_cast]
theorem coe_neg : ((-f' : PowerSeries R') : LaurentSeries R') = -f' :=
  (ofPowerSeries ℤ R').map_neg _

@[norm_cast] -- Porting note (#10618): simp can prove this
theorem coe_mul : ((f * g : PowerSeries R) : LaurentSeries R) = f * g :=
  (ofPowerSeries ℤ R).map_mul _ _

theorem coeff_coe (i : ℤ) :
    ((f : PowerSeries R) : LaurentSeries R).coeff i =
      if i < 0 then 0 else PowerSeries.coeff R i.natAbs f := by
  cases i
  · rw [Int.ofNat_eq_coe, coeff_coe_powerSeries, if_neg (Int.natCast_nonneg _).not_lt,
      Int.natAbs_ofNat]
  · rw [ofPowerSeries_apply, embDomain_notin_image_support, if_pos (Int.negSucc_lt_zero _)]
    simp only [not_exists, RelEmbedding.coe_mk, Set.mem_image, not_and, Function.Embedding.coeFn_mk,
      Ne, toPowerSeries_symm_apply_coeff, mem_support, imp_true_iff,
      not_false_iff]

-- Porting note (#10618): simp can prove this
-- Porting note: removed norm_cast attribute
theorem coe_C (r : R) : ((C R r : PowerSeries R) : LaurentSeries R) = HahnSeries.C r :=
  ofPowerSeries_C _

-- @[simp] -- Porting note (#10618): simp can prove this
theorem coe_X : ((X : PowerSeries R) : LaurentSeries R) = single 1 1 :=
  ofPowerSeries_X

@[simp, norm_cast]
theorem coe_smul {S : Type*} [Semiring S] [Module R S] (r : R) (x : PowerSeries S) :
    ((r • x : PowerSeries S) : LaurentSeries S) = r • (ofPowerSeries ℤ S x) := by
  ext
  simp [coeff_coe, coeff_smul, smul_ite]

-- Porting note: RingHom.map_bit0 and RingHom.map_bit1 no longer exist

@[norm_cast]
theorem coe_pow (n : ℕ) : ((f ^ n : PowerSeries R) : LaurentSeries R) = (ofPowerSeries ℤ R f) ^ n :=
  (ofPowerSeries ℤ R).map_pow _ _

end PowerSeries

namespace RatFunc

variable {F : Type u} [Field F] (p q : F[X]) (f g : RatFunc F)

/-- The coercion `RatFunc F → LaurentSeries F` as bundled alg hom. -/
def coeAlgHom (F : Type u) [Field F] : RatFunc F →ₐ[F[X]] LaurentSeries F :=
  liftAlgHom (Algebra.ofId _ _) <|
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ <|
      Polynomial.algebraMap_hahnSeries_injective _

/-- The coercion `RatFunc F → LaurentSeries F` as a function.

This is the implementation of `coeToLaurentSeries`.
-/
@[coe]
def coeToLaurentSeries_fun {F : Type u} [Field F] : RatFunc F → LaurentSeries F :=
  coeAlgHom F

instance coeToLaurentSeries : Coe (RatFunc F) (LaurentSeries F) :=
  ⟨coeToLaurentSeries_fun⟩

theorem coe_def : (f : LaurentSeries F) = coeAlgHom F f :=
  rfl

attribute [-instance] RatFunc.instCoePolynomial in
-- avoids a diamond, see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/compiling.20behaviour.20within.20one.20file
theorem coe_num_denom : (f : LaurentSeries F) = f.num / f.denom :=
  liftAlgHom_apply _ _ f

theorem coe_injective : Function.Injective ((↑) : RatFunc F → LaurentSeries F) :=
  liftAlgHom_injective _ (Polynomial.algebraMap_hahnSeries_injective _)

-- Porting note: removed the `norm_cast` tag:
-- `norm_cast: badly shaped lemma, rhs can't start with coe `↑(coeAlgHom F) f`
@[simp]
theorem coe_apply : coeAlgHom F f = f :=
  rfl

-- avoids a diamond, see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/compiling.20behaviour.20within.20one.20file
theorem coe_coe (P : Polynomial F) : ((P : PowerSeries F) : LaurentSeries F) = (P : RatFunc F) := by
  simp only [coePolynomial, coe_def, AlgHom.commutes, algebraMap_hahnSeries_apply]

@[simp, norm_cast]
theorem coe_zero : ((0 : RatFunc F) : LaurentSeries F) = 0 :=
  map_zero (coeAlgHom F)

theorem coe_ne_zero {f : Polynomial F} (hf : f ≠ 0) : (↑f : PowerSeries F) ≠ 0 := by
  simp only [ne_eq, Polynomial.coe_eq_zero_iff, hf, not_false_eq_true]

@[simp, norm_cast]
theorem coe_one : ((1 : RatFunc F) : LaurentSeries F) = 1 :=
  map_one (coeAlgHom F)

@[simp, norm_cast]
theorem coe_add : ((f + g : RatFunc F) : LaurentSeries F) = f + g :=
  map_add (coeAlgHom F) _ _

@[simp, norm_cast]
theorem coe_sub : ((f - g : RatFunc F) : LaurentSeries F) = f - g :=
  map_sub (coeAlgHom F) _ _

@[simp, norm_cast]
theorem coe_neg : ((-f : RatFunc F) : LaurentSeries F) = -f :=
  map_neg (coeAlgHom F) _

@[simp, norm_cast]
theorem coe_mul : ((f * g : RatFunc F) : LaurentSeries F) = f * g :=
  map_mul (coeAlgHom F) _ _

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((f ^ n : RatFunc F) : LaurentSeries F) = (f : LaurentSeries F) ^ n :=
  map_pow (coeAlgHom F) _ _

@[simp, norm_cast]
theorem coe_div :
    ((f / g : RatFunc F) : LaurentSeries F) = (f : LaurentSeries F) / (g : LaurentSeries F) :=
  map_div₀ (coeAlgHom F) _ _

@[simp, norm_cast]
theorem coe_C (r : F) : ((RatFunc.C r : RatFunc F) : LaurentSeries F) = HahnSeries.C r := by
  rw [coe_num_denom, num_C, denom_C, Polynomial.coe_C, -- Porting note: removed `coe_C`
    Polynomial.coe_one,
    PowerSeries.coe_one, div_one]
  simp only [algebraMap_eq_C, ofPowerSeries_C, C_apply]  -- Porting note: added

-- TODO: generalize over other modules
@[simp, norm_cast]
theorem coe_smul (r : F) : ((r • f : RatFunc F) : LaurentSeries F) = r • (f : LaurentSeries F) := by
  rw [RatFunc.smul_eq_C_mul, ← C_mul_eq_smul, coe_mul, coe_C]

-- Porting note: removed `norm_cast` because "badly shaped lemma, rhs can't start with coe"
-- even though `single 1 1` is a bundled function application, not a "real" coercion
@[simp]
theorem coe_X : ((X : RatFunc F) : LaurentSeries F) = single 1 1 := by
  rw [coe_num_denom, num_X, denom_X, Polynomial.coe_X, -- Porting note: removed `coe_C`
     Polynomial.coe_one,
     PowerSeries.coe_one, div_one]
  simp only [ofPowerSeries_X]  -- Porting note: added

theorem single_one_eq_pow {R : Type _} [Ring R] (n : ℕ) :
    single (n : ℤ) (1 : R) = single (1 : ℤ) 1 ^ n := by
  induction' n with n h_ind
  · simp
  · rw [← Int.ofNat_add_one_out, pow_succ', ← h_ind, HahnSeries.single_mul_single, one_mul,
      add_comm]

theorem single_inv (d : ℤ) {α : F} (hα : α ≠ 0) :
    single (-d) (α⁻¹ : F) = (single (d : ℤ) (α : F))⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  simp [hα]

theorem single_zpow (n : ℤ) :
    single (n : ℤ) (1 : F) = single (1 : ℤ) 1 ^ n := by
  induction' n with n_pos n_neg
  · apply single_one_eq_pow
  · rw [Int.negSucc_coe, Int.ofNat_add, Nat.cast_one, ← inv_one,
      single_inv (n_neg + 1 : ℤ) one_ne_zero, zpow_neg, ← Nat.cast_one, ← Int.ofNat_add,
      Nat.cast_one, inv_inj, zpow_natCast, single_one_eq_pow, inv_one]

instance : Algebra (RatFunc F) (LaurentSeries F) :=
  RingHom.toAlgebra (coeAlgHom F).toRingHom

theorem algebraMap_apply_div :
    algebraMap (RatFunc F) (LaurentSeries F) (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap F[X] (LaurentSeries F) p / algebraMap _ _ q := by
  -- Porting note: had to supply implicit arguments to `convert`
  convert coe_div (algebraMap F[X] (RatFunc F) p) (algebraMap F[X] (RatFunc F) q) <;>
    rw [← mk_one, coe_def, coeAlgHom, mk_eq_div, liftAlgHom_apply_div, map_one, div_one,
      Algebra.ofId_apply]

instance : IsScalarTower F[X] (RatFunc F) (LaurentSeries F) :=
  ⟨fun x y z => by
    ext
    simp⟩

end RatFunc
section AdicValuation

open scoped DiscreteValuation

variable (K : Type*) [Field K]
namespace PowerSeries

/-- The prime ideal `(X)` of `PowerSeries K`, when `K` is a field, as a term of the
`HeightOneSpectrum`. -/
def idealX : IsDedekindDomain.HeightOneSpectrum K⟦X⟧ where
  asIdeal := Ideal.span {X}
  isPrime := PowerSeries.span_X_isPrime
  ne_bot  := by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact X_ne_zero

open RatFunc IsDedekindDomain.HeightOneSpectrum

variable {K}

/- The `X`-adic valuation of a polynomial equals the `X`-adic valuation of its coercion to `K⟦X⟧`-/
theorem intValuation_eq_of_coe (P : K[X]) :
    (Polynomial.idealX K).intValuation P = (idealX K).intValuation (P : K⟦X⟧) := by
  by_cases hP : P = 0
  · rw [hP, Valuation.map_zero, Polynomial.coe_zero, Valuation.map_zero]
  simp only [intValuation_apply]
  rw [intValuationDef_if_neg _ hP, intValuationDef_if_neg _ <| coe_ne_zero hP]
  simp only [idealX_span, ofAdd_neg, inv_inj, WithZero.coe_inj, EmbeddingLike.apply_eq_iff_eq,
    Nat.cast_inj]
  have span_ne_zero :
    (Ideal.span {P} : Ideal K[X]) ≠ 0 ∧ (Ideal.span {Polynomial.X} : Ideal K[X]) ≠ 0 := by
    simp only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot, hP, Polynomial.X_ne_zero,
      not_false_iff, and_self_iff]
  have span_ne_zero' :
    (Ideal.span {↑P} : Ideal K⟦X⟧) ≠ 0 ∧ ((idealX K).asIdeal : Ideal K⟦X⟧) ≠ 0 := by
    simp only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot, coe_eq_zero_iff, hP,
      not_false_eq_true, true_and, (idealX K).3]
  rw [count_associates_factors_eq (Ideal.span {P}) (Ideal.span {Polynomial.X}) (span_ne_zero).1
    (Ideal.span_singleton_prime Polynomial.X_ne_zero|>.mpr prime_X) (span_ne_zero).2,
    count_associates_factors_eq (Ideal.span {↑(P : K⟦X⟧)}) (idealX K).asIdeal]
  on_goal 1 => convert (normalized_count_X_eq_of_coe hP).symm
  exacts [count_span_normalizedFactors_eq_of_normUnit hP Polynomial.normUnit_X prime_X,
    count_span_normalizedFactors_eq_of_normUnit (coe_ne_zero hP) normUnit_X X_prime,
    span_ne_zero'.1, (idealX K).isPrime, span_ne_zero'.2]

/-- The integral valuation of the power series `X : K⟦X⟧` equals `(ofAdd -1) : ℤₘ₀`-/
@[simp]
theorem intValuation_X : (idealX K).intValuationDef X = ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
  rw [← Polynomial.coe_X, ← intValuation_apply, ← intValuation_eq_of_coe]
  apply intValuation_singleton _ Polynomial.X_ne_zero (by rfl)

end PowerSeries

namespace RatFunc

open IsDedekindDomain.HeightOneSpectrum PowerSeries

theorem valuation_eq_LaurentSeries_valuation (P : RatFunc K) :
    (Polynomial.idealX K).valuation P = (PowerSeries.idealX K).valuation (P : LaurentSeries K) := by
  refine RatFunc.induction_on' P ?_
  intro f g h
  rw [Polynomial.valuation_of_mk K f h, RatFunc.mk_eq_mk' f h, Eq.comm]
  convert @valuation_of_mk' (PowerSeries K) _ _ (LaurentSeries K) _ _ _ (PowerSeries.idealX K) f
        ⟨g, mem_nonZeroDivisors_iff_ne_zero.2 <| coe_ne_zero h⟩
  · simp only [IsFractionRing.mk'_eq_div, coe_div, LaurentSeries.coe_algebraMap, coe_coe]
    rfl
  exacts [intValuation_eq_of_coe _, intValuation_eq_of_coe _]

end RatFunc

namespace LaurentSeries

open IsDedekindDomain.HeightOneSpectrum PowerSeries RatFunc

instance : Valued (LaurentSeries K) ℤₘ₀ := Valued.mk' (PowerSeries.idealX K).valuation

theorem valuation_X_pow (s : ℕ) :
    Valued.v (((X : K⟦X⟧) : LaurentSeries K) ^ s) = Multiplicative.ofAdd (-(s : ℤ)) := by
  erw [map_pow, ← one_mul (s : ℤ), ← neg_mul (1 : ℤ) s, Int.ofAdd_mul,
    WithZero.coe_zpow, ofAdd_neg, WithZero.coe_inv, zpow_natCast, valuation_of_algebraMap,
    intValuation_toFun, intValuation_X, ofAdd_neg, WithZero.coe_inv, inv_pow]

theorem valuation_single_zpow (s : ℤ) :
    Valued.v (HahnSeries.single s (1 : K) : LaurentSeries K) =
      Multiplicative.ofAdd (-(s : ℤ)) := by
  have : Valued.v (1 : LaurentSeries K) = (1 : ℤₘ₀) := Valued.v.map_one
  rw [← single_zero_one, ← add_neg_cancel s, ← mul_one 1, ← single_mul_single, map_mul,
    mul_eq_one_iff_eq_inv₀] at this
  · rw [this]
    induction' s with s s
    · rw [Int.ofNat_eq_coe, ← HahnSeries.ofPowerSeries_X_pow] at this
      rw [Int.ofNat_eq_coe, ← this, PowerSeries.coe_pow, valuation_X_pow]
    · simp only [Int.negSucc_coe, neg_neg, ← HahnSeries.ofPowerSeries_X_pow, PowerSeries.coe_pow,
        valuation_X_pow, ofAdd_neg, WithZero.coe_inv, inv_inv]
  · simp only [Valuation.ne_zero_iff, ne_eq, one_ne_zero, not_false_iff, HahnSeries.single_ne_zero]

/- The coefficients of a power series vanish in degree strictly less than its valuation. -/
theorem coeff_zero_of_lt_intValuation {n d : ℕ} {f : K⟦X⟧}
    (H : Valued.v (f : LaurentSeries K) ≤ Multiplicative.ofAdd (-d : ℤ)) :
    n < d → coeff K n f = 0 := by
  intro hnd
  apply (PowerSeries.X_pow_dvd_iff).mp _ n hnd
  erw [← span_singleton_dvd_span_singleton_iff_dvd, ← Ideal.span_singleton_pow,
    ← (intValuation_le_pow_iff_dvd (PowerSeries.idealX K) f d), ← intValuation_apply,
    ← valuation_of_algebraMap (R := K⟦X⟧) (K := (LaurentSeries K))]
  exact H

/- The valuation of a power series is the order of the first non-zero coefficient. -/
theorem intValuation_le_iff_coeff_lt_eq_zero {d : ℕ} (f : K⟦X⟧) :
    Valued.v (f : LaurentSeries K) ≤ Multiplicative.ofAdd (-d : ℤ) ↔
      ∀ n : ℕ, n < d → coeff K n f = 0 := by
  have : PowerSeries.X ^ d ∣ f ↔ ∀ n : ℕ, n < d → (PowerSeries.coeff K n) f = 0 :=
    ⟨PowerSeries.X_pow_dvd_iff.mp, PowerSeries.X_pow_dvd_iff.mpr⟩
  erw [← this, valuation_of_algebraMap (PowerSeries.idealX K) f, ←
    span_singleton_dvd_span_singleton_iff_dvd, ← Ideal.span_singleton_pow]
  apply intValuation_le_pow_iff_dvd

/- The coefficients of a Laurent series vanish in degree strictly less than its valuation. -/
theorem coeff_zero_of_lt_valuation {n D : ℤ} {f : LaurentSeries K}
    (H : Valued.v f ≤ Multiplicative.ofAdd (-D)) : n < D → f.coeff n = 0 := by
  intro hnd
  by_cases h_n_ord : n < f.order
  · exact coeff_eq_zero_of_lt_order h_n_ord
  rw [not_lt] at h_n_ord
  set F := powerSeriesPart f with hF
  by_cases ord_nonpos : f.order ≤ 0
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat ord_nonpos
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_le_iff_add_nonneg.mp (hs ▸ h_n_ord))
    obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (a := D + s) (by linarith)
    rw [eq_add_neg_of_add_eq hm, add_comm, ← hs, ← powerSeriesPart_coeff]
    apply (intValuation_le_iff_coeff_lt_eq_zero K F).mp _ m (by linarith)
    rwa [hF, ofPowerSeries_powerSeriesPart f, hs, neg_neg, ← hd, neg_add_rev, ofAdd_add, map_mul,
      ← ofPowerSeries_X_pow s, PowerSeries.coe_pow,  WithZero.coe_mul, valuation_X_pow K s,
      mul_le_mul_left (by simp only [ne_eq, WithZero.coe_ne_zero, not_false_iff, zero_lt_iff])]
  · rw [not_le] at ord_nonpos
    obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat (Int.neg_nonpos_of_nonneg (le_of_lt ord_nonpos))
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (a := n - s) (by linarith)
    obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (a := D - s) (by linarith)
    rw [(sub_eq_iff_eq_add).mp hm, add_comm, ← neg_neg (s : ℤ), ← hs, neg_neg,
      ← powerSeriesPart_coeff]
    apply (intValuation_le_iff_coeff_lt_eq_zero K F).mp _ m (by linarith)
    rwa [hF, ofPowerSeries_powerSeriesPart f, map_mul, ← hd, hs, neg_sub, sub_eq_add_neg,
      ofAdd_add, valuation_single_zpow, neg_neg, WithZero.coe_mul,
      mul_le_mul_left (by simp only [ne_eq, WithZero.coe_ne_zero, not_false_iff, zero_lt_iff])]

/- The valuation of a Laurent series is the order of the first non-zero coefficient. -/
theorem valuation_le_iff_coeff_lt_eq_zero {D : ℤ} {f : LaurentSeries K} :
    Valued.v f ≤ ↑(Multiplicative.ofAdd (-D : ℤ)) ↔ ∀ n : ℤ, n < D → f.coeff n = 0 := by
  refine ⟨fun hnD n hn => coeff_zero_of_lt_valuation K hnD hn, fun h_val_f => ?_⟩
  let F := powerSeriesPart f
  by_cases ord_nonpos : f.order ≤ 0
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat ord_nonpos
    rw [← f.single_order_mul_powerSeriesPart, hs, map_mul, valuation_single_zpow, neg_neg, mul_comm,
      ← le_mul_inv_iff₀, ofAdd_neg, WithZero.coe_inv, ← mul_inv, ← WithZero.coe_mul, ← ofAdd_add,
      ← WithZero.coe_inv, ← ofAdd_neg]
    · by_cases hDs : D + s ≤ 0
      · apply le_trans ((PowerSeries.idealX K).valuation_le_one F)
        rwa [← WithZero.coe_one, ← ofAdd_zero, WithZero.coe_le_coe, Multiplicative.ofAdd_le,
          Left.nonneg_neg_iff]
      · obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (le_of_lt <| not_le.mp hDs)
        rw [hd]
        apply (intValuation_le_iff_coeff_lt_eq_zero K F).mpr
        intro n hn
        rw [powerSeriesPart_coeff f n, hs]
        apply h_val_f
        linarith
    · simp only [ne_eq, WithZero.coe_ne_zero, not_false_iff, zero_lt_iff]
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat
      <| neg_nonpos_of_nonneg <| le_of_lt <| not_le.mp ord_nonpos
    rw [neg_inj] at hs
    rw [← f.single_order_mul_powerSeriesPart, hs, map_mul, valuation_single_zpow, mul_comm,
      ← le_mul_inv_iff₀, ofAdd_neg, WithZero.coe_inv, ← mul_inv, ← WithZero.coe_mul, ← ofAdd_add,
      ← WithZero.coe_inv, ← ofAdd_neg, neg_add, neg_neg]
    · by_cases hDs : D - s ≤ 0
      · apply le_trans ((PowerSeries.idealX K).valuation_le_one F)
        rw [← WithZero.coe_one, ← ofAdd_zero, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
        linarith
      · obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (le_of_lt <| not_le.mp hDs)
        rw [← neg_neg (-D + ↑s), ← sub_eq_neg_add, neg_sub, hd]
        apply (intValuation_le_iff_coeff_lt_eq_zero K F).mpr
        intro n hn
        rw [powerSeriesPart_coeff f n, hs]
        apply h_val_f (s + n)
        linarith
    · simp only [ne_eq, WithZero.coe_ne_zero, not_false_iff, zero_lt_iff]

/- Two Laurent series whose difference has small valuation have the same coefficients for
small enough indices. -/
theorem eq_coeff_of_valuation_sub_lt {d n : ℤ} {f g : LaurentSeries K}
    (H : Valued.v (g - f) ≤ ↑(Multiplicative.ofAdd (-d))) : n < d → g.coeff n = f.coeff n := by
  by_cases triv : g = f
  · exact fun _ => by rw [triv]
  · intro hn
    apply eq_of_sub_eq_zero
    erw [← HahnSeries.sub_coeff]
    apply coeff_zero_of_lt_valuation K H hn

/- Every Laurent series of valuation less than `(1 : ℤₘ₀)` comes from a power series. -/
theorem val_le_one_iff_eq_coe (f : LaurentSeries K) : Valued.v f ≤ (1 : ℤₘ₀) ↔
    ∃ F : PowerSeries K, F = f := by
  rw [← WithZero.coe_one, ← ofAdd_zero, ← neg_zero, valuation_le_iff_coeff_lt_eq_zero]
  refine ⟨fun h => ⟨PowerSeries.mk fun n => f.coeff n, ?_⟩, ?_⟩
  on_goal 1 => ext (_ | n)
  · simp only [Int.ofNat_eq_coe, coeff_coe_powerSeries, coeff_mk]
  on_goal 1 => simp only [h (Int.negSucc n) (Int.negSucc_lt_zero n)]
  on_goal 2 => rintro ⟨F, rfl⟩ _ _
  all_goals
    apply HahnSeries.embDomain_notin_range
    simp only [Nat.coe_castAddMonoidHom, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
      Set.mem_range, not_exists, Int.negSucc_lt_zero,]
    intro
  · simp only [not_false_eq_true]
  · linarith

end LaurentSeries

end AdicValuation
