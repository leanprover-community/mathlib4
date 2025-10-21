/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
--import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Binomial

/-!
# Binomial Power Series
We introduce formal power series of the form `(1 + X) ^ r`, where `r` is an element of a
commutative binomial ring `R`.

-- also, substitute `f(X)` for `X`.
--This formal exponentiation operation makes the group `1 + XR⟦X⟧` into an `R`-module.

## Main Definitions
* `PowerSeries.binomialSeries`: A power series expansion of `(1 + X) ^ r`, where `r` is an element
  of a commutative binomial ring `R`.

## Main Results
 * `PowerSeries.binomial_add`: Adding exponents yields multiplication of series.
 * `PowerSeries.binomialSeries_nat`: when `r` is a natural number, we get `(1 + X) ^ r`.
 * `PowerSeries.rescale_neg_one_invOneSubPow`: The image of `(1 - X) ^ (-d)` under the map
   `X ↦ (-X)` is `(1 + X) ^ (-d)`

## TODO

 * `PowerSeries.binomial_mul`: expand `(1 + (X 1)) ^ r * (1 + (X 2)) ^ r`
 * `PowerSeries.binomial_pow`: show `((1 + X) ^ r) ^ s = (1 + X) ^ (r * s)`

-/

open Finset Function
open BigOperators Pointwise

suppress_compilation

variable {Γ R A : Type*}

namespace PowerSeries

variable [CommRing R] [BinomialRing R]

/-- The power series for `(1 + X) ^ r`. -/
def binomialSeries (A) [One A] [SMul R A] (r : R) : PowerSeries A :=
  mk fun n => Ring.choose r n • 1

@[simp]
lemma binomialSeries_coeff [Semiring A] [SMul R A] (r : R) (n : ℕ) :
    coeff n (binomialSeries A r) = Ring.choose r n • 1 :=
  coeff_mk n fun n ↦ Ring.choose r n • 1

@[simp]
lemma binomialSeries_constantCoeff [Ring A] [Algebra R A] (r : R) :
    constantCoeff (binomialSeries A r) = 1 := by
  simp [← coeff_zero_eq_constantCoeff_apply]

@[simp]
lemma binomialSeries_add [Ring A] [Algebra R A] (r s : R) :
    binomialSeries A (r + s) = binomialSeries A r * binomialSeries A s := by
  ext n
  simp only [binomialSeries_coeff, Ring.add_choose_eq n (Commute.all r s), coeff_mul,
    Algebra.mul_smul_comm, mul_one, sum_smul]
  refine sum_congr rfl fun ab hab => ?_
  rw [mul_comm, mul_smul]

@[simp]
lemma binomialSeries_nat [Ring A] [Algebra R A] (d : ℕ) :
    binomialSeries A (d : R) = (1 + X) ^ d := by
  ext n
  have hright : (1 + X) ^ d = (((1 : Polynomial A) + (Polynomial.X)) ^ d).toPowerSeries := by
    simp
  rw [hright, Polynomial.coeff_coe, binomialSeries_coeff, Polynomial.coeff_one_add_X_pow]
  simp [Ring.choose_natCast, Nat.cast_smul_eq_nsmul]

@[simp]
lemma binomialSeries_zero [Ring A] [Algebra R A] :
    binomialSeries A (0 : R) = (1 : A⟦X⟧) := by
  simpa using binomialSeries_nat 0

lemma rescale_neg_one_invOneSubPow [CommRing A] (d : ℕ) :
    rescale (-1 : A) (invOneSubPow A d) = binomialSeries A (-d : ℤ) := by
  ext n
  rw [coeff_rescale, binomialSeries_coeff, ← Int.cast_negOnePow_natCast, ← zsmul_eq_mul]
  cases d with
  | zero =>
    by_cases hn : n = 0 <;> simp [invOneSubPow, Ring.choose_zero_ite, hn]
  | succ d =>
    simp only [invOneSubPow, coeff_mk, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg,
      zsmul_eq_mul, mul_one]
    rw [show (-1 : ℤ) + -d = -(d + 1) by abel, Ring.choose_neg, Nat.choose_symm_add, Units.smul_def,
      show (d : ℤ) + 1 + n - 1 = d + n by cutsat, ← Nat.cast_add, Ring.choose_natCast]
    norm_cast

/-!
lemma binomialSeries_mul (r : R) : -- need mvPowerSeries
    (1 + (X 1)) ^ r * (1 + (X 2)) ^ r = (1 + (X 1) + (X 2) + (X 1) * (X 2)) ^ r := by


variable [UniformSpace R] [T2Space R] [CompleteSpace R] [IsTopologicalRing R]
[UniformAddGroup R] [IsLinearTopology R R] --[DiscreteTopology R]

open WithPiTopology

lemma X_mul_topologically_nilpotent (f : PowerSeries R) :
    IsTopologicallyNilpotent (X * f) := by
  intro U hU
  refine Filter.mem_map'.mpr ?_
  rw [Filter.mem_atTop_sets, Set.setOf_set]
  rw [mem_nhds_iff] at hU
  obtain ⟨t, ht1, ht2, ht3⟩ := hU
  rw [isOpen_iff_isOpen_ball_subset] at ht2
  specialize ht2 0 ht3
  obtain ⟨V, hV1, hV2, hV3⟩ := ht2
  rw [Set.subset_def] at hV3

  sorry

/-- The power series given by `(1 + X * f X) ^ r`. -/
def BinomialEval (f : PowerSeries R) (r : R) : PowerSeries R :=
  aeval (X_mul_topologically_nilpotent f) (binomialSeries R r)


/-- `(1 + X) ^ (r * s) = ((1 + X) ^ r) ^ s` -/
lemma binomial_mul (r s : R) :
    BinomialSeries (r * s) = BinomialEval (mk fun n => Ring.choose r (n + 1)) s := by

  simp only [binomial_coeff, BinomialEval, eval_coeff, smul_eq_mul]
  rw [some_theorem_about_(r*s).choose]
-/
end PowerSeries
