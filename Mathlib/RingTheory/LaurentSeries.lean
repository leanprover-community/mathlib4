/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Localization.FractionRing

#align_import ring_theory.laurent_series from "leanprover-community/mathlib"@"831c494092374cfe9f50591ed0ac81a25efc5b86"

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

## Main Results
* Basic properties of Hasse derivatives

-/
universe u

open scoped Classical
open HahnSeries Polynomial

noncomputable section

/-- A `LaurentSeries` is implemented as a `HahnSeries` with value group `ℤ`. -/
abbrev LaurentSeries (R : Type u) [Zero R] :=
  HahnSeries ℤ R
#align laurent_series LaurentSeries

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
#noalign laurent_series.coe_power_series

@[simp]
theorem coeff_coe_powerSeries (x : PowerSeries R) (n : ℕ) :
    HahnSeries.coeff (x : LaurentSeries R) n = PowerSeries.coeff R n x := by
  rw [ofPowerSeries_apply_coeff]
#align laurent_series.coeff_coe_power_series LaurentSeries.coeff_coe_powerSeries

/-- This is a power series that can be multiplied by an integer power of `X` to give our
  Laurent series. If the Laurent series is nonzero, `powerSeriesPart` has a nonzero
  constant term.  -/
def powerSeriesPart (x : LaurentSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => x.coeff (x.order + n)
#align laurent_series.power_series_part LaurentSeries.powerSeriesPart

@[simp]
theorem powerSeriesPart_coeff (x : LaurentSeries R) (n : ℕ) :
    PowerSeries.coeff R n x.powerSeriesPart = x.coeff (x.order + n) :=
  PowerSeries.coeff_mk _ _
#align laurent_series.power_series_part_coeff LaurentSeries.powerSeriesPart_coeff

@[simp]
theorem powerSeriesPart_zero : powerSeriesPart (0 : LaurentSeries R) = 0 := by
  ext
  simp [(PowerSeries.coeff _ _).map_zero] -- Note: this doesn't get picked up any more
#align laurent_series.power_series_part_zero LaurentSeries.powerSeriesPart_zero

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
#align laurent_series.power_series_part_eq_zero LaurentSeries.powerSeriesPart_eq_zero

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
#align laurent_series.single_order_mul_power_series_part LaurentSeries.single_order_mul_powerSeriesPart

theorem ofPowerSeries_powerSeriesPart (x : LaurentSeries R) :
    ofPowerSeries ℤ R x.powerSeriesPart = single (-x.order) 1 * x := by
  refine Eq.trans ?_ (congr rfl x.single_order_mul_powerSeriesPart)
  rw [← mul_assoc, single_mul_single, neg_add_self, mul_one, ← C_apply, C_one, one_mul]
#align laurent_series.of_power_series_power_series_part LaurentSeries.ofPowerSeries_powerSeriesPart

end Semiring

instance [CommSemiring R] : Algebra (PowerSeries R) (LaurentSeries R) :=
  (HahnSeries.ofPowerSeries ℤ R).toAlgebra

@[simp]
theorem coe_algebraMap [CommSemiring R] :
    ⇑(algebraMap (PowerSeries R) (LaurentSeries R)) = HahnSeries.ofPowerSeries ℤ R :=
  rfl
#align laurent_series.coe_algebra_map LaurentSeries.coe_algebraMap

/-- The localization map from power series to Laurent series. -/
@[simps (config := { rhsMd := .all, simpRhs := true })]
instance of_powerSeries_localization [CommRing R] :
    IsLocalization (Submonoid.powers (PowerSeries.X : PowerSeries R)) (LaurentSeries R) where
  map_units' := by
    rintro ⟨_, n, rfl⟩
    refine ⟨⟨single (n : ℤ) 1, single (-n : ℤ) 1, ?_, ?_⟩, ?_⟩
    · simp only [single_mul_single, mul_one, add_right_neg]
      rfl
    · simp only [single_mul_single, mul_one, add_left_neg]
      rfl
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
#align laurent_series.of_power_series_localization LaurentSeries.of_powerSeries_localization

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
#align power_series.coe_zero PowerSeries.coe_zero

@[norm_cast] -- Porting note (#10618): simp can prove this
theorem coe_one : ((1 : PowerSeries R) : LaurentSeries R) = 1 :=
  (ofPowerSeries ℤ R).map_one
#align power_series.coe_one PowerSeries.coe_one

@[norm_cast] -- Porting note (#10618): simp can prove this
theorem coe_add : ((f + g : PowerSeries R) : LaurentSeries R) = f + g :=
  (ofPowerSeries ℤ R).map_add _ _
#align power_series.coe_add PowerSeries.coe_add

@[norm_cast]
theorem coe_sub : ((f' - g' : PowerSeries R') : LaurentSeries R') = f' - g' :=
  (ofPowerSeries ℤ R').map_sub _ _
#align power_series.coe_sub PowerSeries.coe_sub

@[norm_cast]
theorem coe_neg : ((-f' : PowerSeries R') : LaurentSeries R') = -f' :=
  (ofPowerSeries ℤ R').map_neg _
#align power_series.coe_neg PowerSeries.coe_neg

@[norm_cast] -- Porting note (#10618): simp can prove this
theorem coe_mul : ((f * g : PowerSeries R) : LaurentSeries R) = f * g :=
  (ofPowerSeries ℤ R).map_mul _ _
#align power_series.coe_mul PowerSeries.coe_mul

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
#align power_series.coeff_coe PowerSeries.coeff_coe

-- Porting note (#10618): simp can prove this
-- Porting note: removed norm_cast attribute
theorem coe_C (r : R) : ((C R r : PowerSeries R) : LaurentSeries R) = HahnSeries.C r :=
  ofPowerSeries_C _
set_option linter.uppercaseLean3 false in
#align power_series.coe_C PowerSeries.coe_C

-- @[simp] -- Porting note (#10618): simp can prove this
theorem coe_X : ((X : PowerSeries R) : LaurentSeries R) = single 1 1 :=
  ofPowerSeries_X
set_option linter.uppercaseLean3 false in
#align power_series.coe_X PowerSeries.coe_X

@[simp, norm_cast]
theorem coe_smul {S : Type*} [Semiring S] [Module R S] (r : R) (x : PowerSeries S) :
    ((r • x : PowerSeries S) : LaurentSeries S) = r • (ofPowerSeries ℤ S x) := by
  ext
  simp [coeff_coe, coeff_smul, smul_ite]
#align power_series.coe_smul PowerSeries.coe_smul

-- Porting note: RingHom.map_bit0 and RingHom.map_bit1 no longer exist
#noalign power_series.coe_bit0
#noalign power_series.coe_bit1

@[norm_cast]
theorem coe_pow (n : ℕ) : ((f ^ n : PowerSeries R) : LaurentSeries R) = (ofPowerSeries ℤ R f) ^ n :=
  (ofPowerSeries ℤ R).map_pow _ _
#align power_series.coe_pow PowerSeries.coe_pow

end PowerSeries

namespace RatFunc
section RatFunc

open RatFunc

variable {F : Type u} [Field F] (p q : F[X]) (f g : RatFunc F)

/-- The coercion `RatFunc F → LaurentSeries F` as bundled alg hom. -/
def coeAlgHom (F : Type u) [Field F] : RatFunc F →ₐ[F[X]] LaurentSeries F :=
  liftAlgHom (Algebra.ofId _ _) <|
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ <|
      Polynomial.algebraMap_hahnSeries_injective _
#align ratfunc.coe_alg_hom RatFunc.coeAlgHom

/-- The coercion `RatFunc F → LaurentSeries F` as a function.

This is the implementation of `coeToLaurentSeries`.
-/
@[coe]
def coeToLaurentSeries_fun {F : Type u} [Field F] : RatFunc F → LaurentSeries F :=
  coeAlgHom F

instance coeToLaurentSeries : Coe (RatFunc F) (LaurentSeries F) :=
  ⟨coeToLaurentSeries_fun⟩
#align ratfunc.coe_to_laurent_series RatFunc.coeToLaurentSeries

theorem coe_def : (f : LaurentSeries F) = coeAlgHom F f :=
  rfl
#align ratfunc.coe_def RatFunc.coe_def

theorem coe_num_denom : (f : LaurentSeries F) = f.num / f.denom :=
  liftAlgHom_apply _ _ f
#align ratfunc.coe_num_denom RatFunc.coe_num_denom

theorem coe_injective : Function.Injective ((↑) : RatFunc F → LaurentSeries F) :=
  liftAlgHom_injective _ (Polynomial.algebraMap_hahnSeries_injective _)
#align ratfunc.coe_injective RatFunc.coe_injective

-- Porting note: removed the `norm_cast` tag:
-- `norm_cast: badly shaped lemma, rhs can't start with coe `↑(coeAlgHom F) f`
@[simp]
theorem coe_apply : coeAlgHom F f = f :=
  rfl
#align ratfunc.coe_apply RatFunc.coe_apply

theorem coe_coe (P : Polynomial F) : (P : LaurentSeries F) = (P : RatFunc F) := by
  simp only [coePolynomial, coe_def, AlgHom.commutes, algebraMap_hahnSeries_apply]

@[simp, norm_cast]
theorem coe_zero : ((0 : RatFunc F) : LaurentSeries F) = 0 :=
  (coeAlgHom F).map_zero
#align ratfunc.coe_zero RatFunc.coe_zero

theorem coe_ne_zero {f : Polynomial F} (hf : f ≠ 0) : (↑f : PowerSeries F) ≠ 0 := by
  simp only [ne_eq, Polynomial.coe_eq_zero_iff, hf, not_false_eq_true]

@[simp, norm_cast]
theorem coe_one : ((1 : RatFunc F) : LaurentSeries F) = 1 :=
  (coeAlgHom F).map_one
#align ratfunc.coe_one RatFunc.coe_one

@[simp, norm_cast]
theorem coe_add : ((f + g : RatFunc F) : LaurentSeries F) = f + g :=
  (coeAlgHom F).map_add _ _
#align ratfunc.coe_add RatFunc.coe_add

@[simp, norm_cast]
theorem coe_sub : ((f - g : RatFunc F) : LaurentSeries F) = f - g :=
  (coeAlgHom F).map_sub _ _
#align ratfunc.coe_sub RatFunc.coe_sub

@[simp, norm_cast]
theorem coe_neg : ((-f : RatFunc F) : LaurentSeries F) = -f :=
  (coeAlgHom F).map_neg _
#align ratfunc.coe_neg RatFunc.coe_neg

@[simp, norm_cast]
theorem coe_mul : ((f * g : RatFunc F) : LaurentSeries F) = f * g :=
  (coeAlgHom F).map_mul _ _
#align ratfunc.coe_mul RatFunc.coe_mul

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((f ^ n : RatFunc F) : LaurentSeries F) = (f : LaurentSeries F) ^ n :=
  (coeAlgHom F).map_pow _ _
#align ratfunc.coe_pow RatFunc.coe_pow

@[simp, norm_cast]
theorem coe_div :
    ((f / g : RatFunc F) : LaurentSeries F) = (f : LaurentSeries F) / (g : LaurentSeries F) :=
  map_div₀ (coeAlgHom F) _ _
#align ratfunc.coe_div RatFunc.coe_div

@[simp, norm_cast]
theorem coe_C (r : F) : ((RatFunc.C r : RatFunc F) : LaurentSeries F) = HahnSeries.C r := by
  rw [coe_num_denom, num_C, denom_C, Polynomial.coe_C, -- Porting note: removed `coe_C`
    Polynomial.coe_one,
    PowerSeries.coe_one, div_one]
  simp only [algebraMap_eq_C, ofPowerSeries_C, C_apply]  -- Porting note: added
set_option linter.uppercaseLean3 false in
#align ratfunc.coe_C RatFunc.coe_C

-- TODO: generalize over other modules
@[simp, norm_cast]
theorem coe_smul (r : F) : ((r • f : RatFunc F) : LaurentSeries F) = r • (f : LaurentSeries F) := by
  rw [RatFunc.smul_eq_C_mul, ← C_mul_eq_smul, coe_mul, coe_C]
#align ratfunc.coe_smul RatFunc.coe_smul

-- Porting note: removed `norm_cast` because "badly shaped lemma, rhs can't start with coe"
-- even though `single 1 1` is a bundled function application, not a "real" coercion
@[simp]
theorem coe_X : ((X : RatFunc F) : LaurentSeries F) = single 1 1 := by
  rw [coe_num_denom, num_X, denom_X, Polynomial.coe_X, -- Porting note: removed `coe_C`
     Polynomial.coe_one,
     PowerSeries.coe_one, div_one]
  simp only [ofPowerSeries_X]  -- Porting note: added
set_option linter.uppercaseLean3 false in
#align ratfunc.coe_X RatFunc.coe_X

theorem single_one_eq_pow {R : Type _} [Ring R] (n : ℕ) :
    single (n : ℤ) (1 : R) = single (1 : ℤ) 1 ^ n := by
  induction' n with n h_ind
  · simp only [Nat.cast_zero, pow_zero]
    rfl
  · rw [← Int.ofNat_add_one_out, pow_succ', ← h_ind, HahnSeries.single_mul_single, one_mul,
      add_comm]

theorem single_inv (d : ℤ) {α : F} (hα : α ≠ 0) :
    single (-d) (α⁻¹ : F) = (single (d : ℤ) (α : F))⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [HahnSeries.single_mul_single, add_right_neg, mul_comm,
    inv_mul_cancel hα]
  rfl

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
#align ratfunc.algebra_map_apply_div RatFunc.algebraMap_apply_div

instance : IsScalarTower F[X] (RatFunc F) (LaurentSeries F) :=
  ⟨fun x y z => by
    ext
    simp⟩

end RatFunc

end RatFunc
