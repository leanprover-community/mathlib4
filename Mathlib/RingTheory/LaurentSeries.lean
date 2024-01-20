/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.LeastGreatest
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.HahnSeries
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

## Main Results
* Basic properties of Hasse derivatives

-/


open HahnSeries BigOperators Classical

noncomputable section

/-- A `LaurentSeries` is implemented as a `HahnSeries` with value group `ℤ`. -/
abbrev LaurentSeries (R : Type*) [Zero R] :=
  HahnSeries ℤ R
#align laurent_series LaurentSeries

variable {R : Type*}

namespace LaurentSeries

section Zero

variable [Zero R]

theorem supp_bdd_below_supp_PWO (f : ℤ → R) (n : ℤ) (hn : ∀(m : ℤ), m < n → f m = 0) :
    (Function.support f).IsPWO := by
  rw [← Set.isWF_iff_isPWO, Set.isWF_iff_no_descending_seq]
  rintro g hg hsupp
  refine Set.infinite_range_of_injective (StrictAnti.injective hg) ?_
  refine (Set.finite_Icc n <| g 0).subset <| Set.range_subset_iff.2 ?_
  simp_all only [Function.mem_support, ne_eq, Set.mem_Icc]
  intro k
  constructor
  exact Int.not_lt.mp (mt (hn (g k)) (hsupp k))
  exact (StrictAnti.le_iff_le hg).mpr (Nat.zero_le k)

/-- Construct a Laurent series from any function with support that is bounded below. -/
def LaurentFromSuppBddBelow (f : ℤ → R) (n : ℤ) (hn : ∀(m : ℤ), m < n → f m = 0) :
    LaurentSeries R where
  coeff := f
  isPWO_support' := supp_bdd_below_supp_PWO f n hn

@[simp]
theorem coeff_LaurentFromSuppBddBelow (f : ℤ → R) (m n : ℤ) (hn : ∀(m : ℤ), m < n → f m = 0) :
    coeff (LaurentFromSuppBddBelow f n hn) m = f m := by exact rfl

end Zero

section HasseDeriv

variable {V : Type*} [AddCommGroup V] [CommRing R] [Module R V]

theorem hasseDeriv_bdd_below (k : ℕ) (f : LaurentSeries V) (m : ℤ) (h : m < f.order - k) :
    (fun (n : ℤ) ↦ Ring.choose (n + k) k • HahnSeries.coeff f (n + k)) m = 0 := by
  simp only
  rw [@lt_sub_iff_add_lt] at h
  rw [coeff_eq_zero_of_lt_order h, smul_zero]

/-- The Laurent series given by Hasse derivative. -/
def hasseDeriv (k : ℕ) (f : LaurentSeries V) : LaurentSeries V :=
  LaurentFromSuppBddBelow (fun n => (Ring.choose (n + k) k) • f.coeff (n + k)) (f.order - k)
    (hasseDeriv_bdd_below k f)

theorem hasseDeriv_coeff (k : ℕ) (f : LaurentSeries V) (n : ℤ) : (hasseDeriv k f).coeff n =
    Ring.choose (n + k) k • HahnSeries.coeff f (n + k) := rfl

theorem hasseDeriv_coeff_add (k : ℕ) (f g : LaurentSeries V) (n : ℤ) :
    HahnSeries.coeff (hasseDeriv k (f + g)) n = HahnSeries.coeff (hasseDeriv k f) n +
    HahnSeries.coeff (hasseDeriv k g) n := by
  simp only [hasseDeriv_coeff, add_coeff', Pi.add_apply, smul_add]

theorem hasseDeriv_coeff_smul {S : Type*} [Monoid S] [DistribMulAction S V] (k : ℕ) (s : S)
    (f : LaurentSeries V) (n : ℤ) : HahnSeries.coeff (hasseDeriv k (s • f)) n =
    s • HahnSeries.coeff (hasseDeriv k f) n := by
  rw [hasseDeriv_coeff, hasseDeriv_coeff, smul_coeff, smul_comm]

theorem hasseDeriv_add (k : ℕ) (f g : LaurentSeries V) : hasseDeriv k (f + g) =
    hasseDeriv k f + hasseDeriv k g := by
  ext
  exact hasseDeriv_coeff_add k f g _

theorem hasseDeriv_smul (k : ℕ) (r : R) (f : LaurentSeries V) : hasseDeriv k (r • f) =
    r • (hasseDeriv k f) := by
  ext
  exact hasseDeriv_coeff_smul k r f _

@[simp]
theorem hasseDeriv_zero' (f : LaurentSeries V) : hasseDeriv 0 f = f := by
  simp only [HahnSeries.ext_iff, hasseDeriv, hasseDeriv, Ring.choose_zero_right]
  ext
  simp_rw [Nat.cast_zero, add_zero, one_smul, sub_zero]
  exact rfl

/-- The Hasse derivative as a linear map. -/
def hasseDeriv.linearMap (k : ℕ) : LaurentSeries V →ₗ[R] LaurentSeries V where
  toFun := fun f => hasseDeriv k f
  map_add' := by
    intros
    ext
    simp only [add_coeff', Pi.add_apply, hasseDeriv_coeff_add]
  map_smul' := by
    intros
    ext
    simp only [RingHom.id_apply, smul_coeff, hasseDeriv_coeff_smul]

@[simp]
theorem hasseDeriv_apply (k : ℕ) (f : LaurentSeries V) :
    @hasseDeriv.linearMap R V _ _ _ k f = hasseDeriv k f := by
  exact rfl

@[simp]
theorem hasseDeriv_zero : @hasseDeriv.linearMap R V _ _ _ 0 = LinearMap.id :=
  LinearMap.ext <| hasseDeriv_zero'

theorem hasseDeriv_single' (k : ℕ) (n : ℤ) (x : V) :
    hasseDeriv k (single (n + k) x) = single n ((Ring.choose (n + k) k) • x) := by
  simp_rw [hasseDeriv, single_coeff, single]
  ext m
  simp only [add_left_inj, smul_ite_zero, ne_eq, coeff_LaurentFromSuppBddBelow, ZeroHom.coe_mk]
  unfold Pi.single Function.update
  simp_all only [eq_rec_constant, Pi.zero_apply, dite_eq_ite]

theorem hasseDeriv_single (k : ℕ) (n : ℤ) (x : V) :
    hasseDeriv k (single n x) = single (n - k) ((Ring.choose n k) • x) := by
  rw [← Int.sub_add_cancel n k, hasseDeriv_single', Int.sub_add_cancel n k]

theorem hasseDeriv_comp_coeff (k l : ℕ) (f : LaurentSeries V) (n : ℤ) :
    HahnSeries.coeff (hasseDeriv k (hasseDeriv l f)) n =
    HahnSeries.coeff ((Nat.choose (k + l) k) • hasseDeriv (k + l) f) n := by
  rw [nsmul_eq_smul_cast R, smul_coeff]
  simp only [hasseDeriv_coeff]
  rw [smul_smul, mul_comm, ← Ring.choose_mul' (n + k), add_assoc, Nat.choose_symm_add, Nat.cast_add,
    smul_assoc, ← nsmul_eq_smul_cast]

theorem hasseDeriv_comp' (k l : ℕ) (f : LaurentSeries V) :
    hasseDeriv k (hasseDeriv l f) = (k + l).choose k • hasseDeriv (k + l) f := by
  ext n
  rw [@hasseDeriv_comp_coeff R]

theorem hasseDeriv_comp (k l : ℕ) :
    (@hasseDeriv.linearMap R V _ _ _ k).comp (@hasseDeriv.linearMap R V _ _ _ l) =
    (k + l).choose k • (@hasseDeriv.linearMap R V _ _ _ (k + l)) := by
  ext f n
  simp only [LinearMap.coe_comp, Function.comp_apply, hasseDeriv_apply, LinearMap.smul_apply]
  rw [nsmul_eq_smul_cast R, LinearMap.smul_apply, hasseDeriv_apply, @hasseDeriv_comp_coeff R,
    nsmul_eq_smul_cast R]

/-- The derivative of a Laurent series. -/
def derivative : LaurentSeries V →ₗ[R] LaurentSeries V := hasseDeriv.linearMap 1

theorem derivative_apply (f : LaurentSeries V) : @derivative R V _ _ _ f = hasseDeriv 1 f := by
  exact rfl

theorem factorial_smul_hasseDeriv_coeff (k : ℕ) (f : LaurentSeries V) (n : ℤ) :
    HahnSeries.coeff (k.factorial • hasseDeriv k f) n =
    HahnSeries.coeff ((@derivative R V _ _ _)^[k] f) n := by
  induction k generalizing f with
  | zero =>
    rw [Nat.zero_eq, Nat.factorial_zero, hasseDeriv_zero', one_smul, Function.iterate_zero, id_eq]
  | succ k ih =>
    rw [Function.iterate_succ, Function.comp_apply, ← ih, derivative_apply, @hasseDeriv_comp' R,
      Nat.choose_symm_add, Nat.choose_one_right, Nat.factorial, mul_nsmul]

theorem factorial_smul_hasseDeriv (k : ℕ) :
    (k.factorial • @hasseDeriv.linearMap R V _ _ _ k) = (@derivative R V _ _ _)^[k] := by
  ext f n
  exact factorial_smul_hasseDeriv_coeff k f n

-- `hasseDeriv_mul`: the "Leibniz rule" `D k (f * g) = ∑ ij in antidiagonal k, D ij.1 f * D ij.2 g`

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
  simp
#align laurent_series.power_series_part_zero LaurentSeries.powerSeriesPart_zero

@[simp]
theorem powerSeriesPart_eq_zero (x : LaurentSeries R) : x.powerSeriesPart = 0 ↔ x = 0 := by
  constructor
  · contrapose!
    simp only [ne_eq]
    intro h
    rw [PowerSeries.ext_iff, not_forall]
    refine' ⟨0, _⟩
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
      add_sub_cancel'_right]
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
  refine' Eq.trans _ (congr rfl x.single_order_mul_powerSeriesPart)
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
    refine' ⟨⟨single (n : ℤ) 1, single (-n : ℤ) 1, _, _⟩, _⟩
    · simp only [single_mul_single, mul_one, add_right_neg]
      rfl
    · simp only [single_mul_single, mul_one, add_left_neg]
      rfl
    · dsimp; rw [ofPowerSeries_X_pow]
  surj' z := by
    by_cases h : 0 ≤ z.order
    · refine' ⟨⟨PowerSeries.X ^ Int.natAbs z.order * powerSeriesPart z, 1⟩, _⟩
      simp only [RingHom.map_one, mul_one, RingHom.map_mul, coe_algebraMap, ofPowerSeries_X_pow,
        Submonoid.coe_one]
      rw [Int.natAbs_of_nonneg h, single_order_mul_powerSeriesPart]
    · refine' ⟨⟨powerSeriesPart z, PowerSeries.X ^ Int.natAbs z.order, ⟨_, rfl⟩⟩, _⟩
      simp only [coe_algebraMap, ofPowerSeries_powerSeriesPart]
      rw [mul_comm _ z]
      refine' congr rfl _
      rw [ofPowerSeries_X_pow, Int.ofNat_natAbs_of_nonpos]
      exact le_of_not_ge h
  exists_of_eq {x y} := by
    rw [coe_algebraMap, ofPowerSeries_injective.eq_iff]
    rintro rfl
    exact ⟨1, rfl⟩
#align laurent_series.of_power_series_localization LaurentSeries.of_powerSeries_localization

-- Porting note: this instance is needed
local instance {K : Type*} [Field K] : MonoidWithZero (HahnSeries ℤ K) := inferInstance in
instance {K : Type*} [Field K] : IsFractionRing (PowerSeries K) (LaurentSeries K) :=
  IsLocalization.of_le (Submonoid.powers (PowerSeries.X : PowerSeries K)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero) fun _ hf =>
    isUnit_of_mem_nonZeroDivisors <| map_mem_nonZeroDivisors _ HahnSeries.ofPowerSeries_injective hf

end LaurentSeries

namespace PowerSeries

open LaurentSeries

variable {R' : Type*} [Semiring R] [Ring R'] (f g : PowerSeries R) (f' g' : PowerSeries R')

@[norm_cast] -- Porting note: simp can prove this
theorem coe_zero : ((0 : PowerSeries R) : LaurentSeries R) = 0 :=
  (ofPowerSeries ℤ R).map_zero
#align power_series.coe_zero PowerSeries.coe_zero

@[norm_cast] -- Porting note: simp can prove this
theorem coe_one : ((1 : PowerSeries R) : LaurentSeries R) = 1 :=
  (ofPowerSeries ℤ R).map_one
#align power_series.coe_one PowerSeries.coe_one

@[norm_cast] -- Porting note: simp can prove this
theorem coe_add : ((f + g : PowerSeries R) : LaurentSeries R) = f + g :=
  (ofPowerSeries ℤ R).map_add _ _
#align power_series.coe_add PowerSeries.coe_add

@[simp, norm_cast]
theorem coe_sub : ((f' - g' : PowerSeries R') : LaurentSeries R') = f' - g' :=
  (ofPowerSeries ℤ R').map_sub _ _
#align power_series.coe_sub PowerSeries.coe_sub

@[simp, norm_cast]
theorem coe_neg : ((-f' : PowerSeries R') : LaurentSeries R') = -f' :=
  (ofPowerSeries ℤ R').map_neg _
#align power_series.coe_neg PowerSeries.coe_neg

@[norm_cast] -- Porting note: simp can prove this
theorem coe_mul : ((f * g : PowerSeries R) : LaurentSeries R) = f * g :=
  (ofPowerSeries ℤ R).map_mul _ _
#align power_series.coe_mul PowerSeries.coe_mul

theorem coeff_coe (i : ℤ) :
    ((f : PowerSeries R) : LaurentSeries R).coeff i =
      if i < 0 then 0 else PowerSeries.coeff R i.natAbs f := by
  cases i
  · rw [Int.ofNat_eq_coe, coeff_coe_powerSeries, if_neg (Int.coe_nat_nonneg _).not_lt,
      Int.natAbs_ofNat]
  · rw [ofPowerSeries_apply, embDomain_notin_image_support, if_pos (Int.negSucc_lt_zero _)]
    simp only [not_exists, RelEmbedding.coe_mk, Set.mem_image, not_and, Function.Embedding.coeFn_mk,
      Ne.def, toPowerSeries_symm_apply_coeff, mem_support, imp_true_iff,
      not_false_iff]
#align power_series.coeff_coe PowerSeries.coeff_coe

-- Porting note: simp can prove this, and removed norm_cast attribute
theorem coe_C (r : R) : ((C R r : PowerSeries R) : LaurentSeries R) = HahnSeries.C r :=
  ofPowerSeries_C _
set_option linter.uppercaseLean3 false in
#align power_series.coe_C PowerSeries.coe_C

-- @[simp] -- Porting note: simp can prove this
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

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((f ^ n : PowerSeries R) : LaurentSeries R) = (ofPowerSeries ℤ R f) ^ n :=
  (ofPowerSeries ℤ R).map_pow _ _
#align power_series.coe_pow PowerSeries.coe_pow

end PowerSeries
