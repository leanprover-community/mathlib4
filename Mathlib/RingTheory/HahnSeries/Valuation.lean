/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.Valuation.Basic

#align_import ring_theory.hahn_series from "leanprover-community/mathlib"@"a484a7d0eade4e1268f4fb402859b6686037f965"

/-!
# Hahn Series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `HahnSeries Γ R`.  We introduce valuations and binomial
expansions.

## Main Definitions
  * `HahnSeries.addVal Γ R` defines an `AddValuation` on `HahnSeries Γ R` when `Γ` is linearly
    ordered.

## Main results

  *

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

set_option linter.uppercaseLean3 false

open Finset Function

open scoped Classical
open BigOperators Pointwise

noncomputable section

variable {Γ : Type*} {R : Type*}

namespace HahnSeries

section Seminorm

section Valuation

variable (Γ R) [LinearOrderedCancelAddCommMonoid Γ] [Ring R] [IsDomain R]

/-- The additive valuation on `HahnSeries Γ R`, returning the smallest index at which
  a Hahn Series has a nonzero coefficient, or `⊤` for the 0 series.  -/
def addVal : AddValuation (HahnSeries Γ R) (WithTop Γ) :=
  AddValuation.of orderTop orderTop_zero (orderTop_one) (fun x y => min_orderTop_le_orderTop_add)
  fun x y => by
    by_cases hx : x = 0; · simp [hx]
    by_cases hy : y = 0; · simp [hy]
    rw [← order_eq_orderTop_of_ne hx, ← order_eq_orderTop_of_ne hy,
      ← order_eq_orderTop_of_ne (mul_ne_zero hx hy), ← WithTop.coe_add, WithTop.coe_eq_coe,
      order_mul hx hy]
#align hahn_series.add_val HahnSeries.addVal

variable {Γ} {R}

theorem addVal_apply {x : HahnSeries Γ R} : addVal Γ R x = x.orderTop :=
  AddValuation.of_apply _
#align hahn_series.add_val_apply HahnSeries.addVal_apply

@[simp]
theorem addVal_apply_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) : addVal Γ R x = x.order :=
  addVal_apply.trans (order_eq_orderTop_of_ne hx).symm
#align hahn_series.add_val_apply_of_ne HahnSeries.addVal_apply_of_ne

theorem addVal_le_of_coeff_ne_zero {x : HahnSeries Γ R} {g : Γ} (h : x.coeff g ≠ 0) :
    addVal Γ R x ≤ g :=
  orderTop_le_of_coeff_ne_zero h
#align hahn_series.add_val_le_of_coeff_ne_zero HahnSeries.addVal_le_of_coeff_ne_zero

end Valuation


section Binomial
/-! We consider integral powers of binomials with invertible leading term.  Also, we consider more
binomial ring powers of binomials with leading term 1, when the coefficient ring is an algebra over
the binomial ring in question.  Question: how to approach switching to consider locality in vertex
algebras?  -/

variable [LinearOrderedAddCommGroup Γ] [CommRing R]

theorem isUnit_one_sub_single {g : Γ} (hg : 0 < g) (r : R) : IsUnit (1 - single g r) := by
  refine isUnit_of_mul_eq_one _ _ (SummableFamily.one_sub_self_mul_hsum_powers ?_)
  by_cases hr : r = 0;
  · simp_all only [map_zero, orderTop_zero, WithTop.zero_lt_top]
  · simp_all only [orderTop_single hr, WithTop.coe_pos]

--Maybe do coeff_smul_binomial first?
theorem coeff_mul_binomial {x : HahnSeries Γ R} {g g' : Γ} {r : R} :
    (x * (1 - single g r)).coeff g' = x.coeff g' - r * x.coeff (g' - g) := by
  rw [mul_one_sub, sub_coeff, sub_right_inj, ← sub_add_cancel g' g,  mul_single_coeff_add,
    sub_add_cancel, mul_comm]

/-!
theorem support_one_sub_single_pow {g : Γ} (hg : 0 < g) {r : R} {n : ℤ} :
    ((IsUnit.unit (isUnit_one_sub_single hg r)) ^ n).val.coeff.support ⊆
      AddSubmonoid.closure {g} := by
  sorry -- use support_pow_subset_closure

theorem coeff_one_sub_single_pow_of_neg {g g' : Γ} (hg : 0 < g) (hg' : g' < 0) {r : R} {n : ℤ} :
    ((IsUnit.unit (isUnit_one_sub_single hg r)) ^ n).val.coeff g' = 0 := by
  cases n with
  | ofNat n =>
    erw [zpow_natCast _ n]
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    sorry
  | negSucc _ => sorry

theorem coeff_one_sub_single_pow {g : Γ} (hg : 0 < g) {r : R} {n : ℤ} : ∀(k : ℕ),
    ((IsUnit.unit (isUnit_one_sub_single hg r)) ^ n).val.coeff (k • g) =
      (-r) ^ k • Ring.choose n k := by
  refine Int.induction_on n ?_ ?_ ?_
  · exact fun k => by
      by_cases hk : k = 0
      · rw [hk, Ring.choose_zero_right, zero_smul, zpow_zero, pow_zero]
        norm_cast
        simp
      · rw [Ring.choose_zero_pos ℤ k (Nat.pos_iff_ne_zero.mpr hk), zpow_zero]
        norm_cast
        rw [smul_zero]
        have hkg : 0 < k • g := (nsmul_pos_iff hk).mpr hg
        have hkg' : ¬ k • g = 0 := fun h => by simp_all
        rw [one_coeff, if_neg hkg']
  · intro n h k
    rw [zpow_add_one, Units.val_mul, IsUnit.unit_spec]
    by_cases hk : k = 0
    · rw [coeff_mul_binomial, h, hk, coeff_one_sub_single_pow_of_neg hg
        (show 0 • g - g < 0 by simp [hg])]
      simp
    · sorry
  · sorry
-/
theorem single_add_single_coeff {g g' : Γ} (hgg' : g < g') {a b : R} :
    (single g a + single g' b).coeff g = a := by
  simp_all [ne_of_lt hgg']

theorem single_add_single_coeff_ne {g g' : Γ} (hgg' : g < g') {a b : R} (ha : a ≠ 0) :
    single g a + single g' b ≠ 0 :=
  ne_zero_of_coeff_ne_zero (ne_of_eq_of_ne (single_add_single_coeff hgg') ha)

theorem single_add_single_support {g g' : Γ} {a b : R} :
    (single g a + single g' b).support ⊆ {g} ∪ {g'} := by
  refine support_add_subset.trans ?_
  simp_all only [Set.union_singleton, Set.union_subset_iff]
  refine { left := fun _ hk => Set.mem_insert_of_mem g' (support_single_subset hk), right := ?_ }
  rw [Set.pair_comm]
  exact fun k hk => Equiv.Set.union.proof_1 k <| Set.mem_insert_of_mem g (support_single_subset hk)

theorem orderTop_binomial {g g' : Γ} (hgg' : g < g') {a b : R} (ha : a ≠ 0) :
    (single g a + single g' b).orderTop = g := by
  rw [← orderTop_single ha]
  exact orderTop_add_eq (lt_of_eq_of_lt (orderTop_single ha)
    (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hgg') orderTop_single_le))

theorem leadingCoeff_binomial {g g' : Γ} (hgg' : g < g') {a b : R} (ha : a ≠ 0) :
    (single g a + single g' b).leadingCoeff = a := by
  rw [leadingCoeff, orderTop_binomial hgg' ha, coeffTop_eq, single_add_single_coeff hgg']

theorem isUnit_binomial {g g' : Γ} (hgg' : g < g') (a : Units R) (b : R) :
    IsUnit (single g a.val + single g' b) := by
  refine isUnit_of_isUnit_leadingCoeff ?_
  by_cases ha : a.val = 0
  · have aa: a.val * a.inv = 1 := Units.val_inv a
    rw [ha, zero_mul] at aa
    rw [← one_mul (leadingCoeff ((single g) a.val + (single g') b)), ← aa, zero_mul, aa,
      isUnit_iff_dvd_one]
  · rw [leadingCoeff, orderTop_binomial hgg' ha, coeffTop_eq, single_add_single_coeff hgg']
    exact Units.isUnit a

end Binomial
