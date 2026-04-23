/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Ralf Stephan
-/
module

public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.NumberTheory.Height.Basic

import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Heights over number fields

We provide an instance of `Height.AdmissibleAbsValues` for algebraic number fields
and set up some API.

## TODO

When this file gets long, split the material on heights over `ℚ` off into a file `Rat.lean`.
-/

@[expose] public section

/-!
### Instance for number fields
-/

namespace NumberField

open Height

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- The infinite places of a number field `K` as a `Multiset` of absolute values on `K`,
with multiplicity given by `InfinitePlace.mult`. -/
noncomputable def multisetInfinitePlace : Multiset (AbsoluteValue K ℝ) :=
  .bind (.univ : Finset (InfinitePlace K)).val fun v ↦ .replicate v.mult v.val

@[simp]
lemma mem_multisetInfinitePlace {v : AbsoluteValue K ℝ} :
    v ∈ multisetInfinitePlace K ↔ IsInfinitePlace v := by
  simp [multisetInfinitePlace, Multiset.mem_replicate, isInfinitePlace_iff, eq_comm (a := v)]

set_option backward.isDefEq.respectTransparency false in
lemma count_multisetInfinitePlace_eq_mult [DecidableEq (AbsoluteValue K ℝ)] (v : InfinitePlace K) :
    (multisetInfinitePlace K).count v.val = v.mult := by
  have : DecidableEq (InfinitePlace K) := Subtype.instDecidableEq
  simpa only [multisetInfinitePlace, Multiset.count_bind, Finset.sum_map_val,
    Multiset.count_replicate, ← Subtype.ext_iff] using Fintype.sum_ite_eq' v ..

-- For the user-facing version, see `prod_archAbsVal_eq` below.
private lemma prod_multisetInfinitePlace_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K ℝ → M) :
    ((multisetInfinitePlace K).map f).prod = ∏ v : InfinitePlace K, f v.val ^ v.mult := by
  classical
  rw [Finset.prod_multiset_map_count]
  exact Finset.prod_bij' (fun w hw ↦ ⟨w, mem_multisetInfinitePlace.mp <| Multiset.mem_dedup.mp hw⟩)
    (fun v _ ↦ v.val) (fun _ _ ↦ Finset.mem_univ _) (fun v _ ↦ by simp [v.isInfinitePlace])
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun w hw ↦ by rw [count_multisetInfinitePlace_eq_mult ⟨w, _⟩]

noncomputable
instance instAdmissibleAbsValues : AdmissibleAbsValues K where
  archAbsVal := multisetInfinitePlace K
  nonarchAbsVal := {v | IsFinitePlace v}
  isNonarchimedean v hv := FinitePlace.add_le ⟨v, by simpa using hv⟩
  hasFiniteMulSupport := FinitePlace.hasFiniteMulSupport
  product_formula {x} hx := private prod_multisetInfinitePlace_eq (· x) ▸ prod_abs_eq_one hx

open AdmissibleAbsValues

lemma prod_archAbsVal_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (archAbsVal.map f).prod = ∏ v : InfinitePlace K, f v.val ^ v.mult :=
  prod_multisetInfinitePlace_eq f

lemma prod_nonarchAbsVal_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (∏ᶠ v : nonarchAbsVal, f v.val) = ∏ᶠ v : FinitePlace K, f v.val :=
  rfl

open Finset Multiset in
lemma sum_archAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (archAbsVal.map f).sum = ∑ v : InfinitePlace K, v.mult • f v.val := by
  classical
  rw [sum_multiset_map_count]
  exact sum_bij' (⟨·, mem_multisetInfinitePlace.mp <| mem_dedup.mp ·⟩)
    _ (by simp) (by simp [InfinitePlace.isInfinitePlace, archAbsVal]) (by simp) (fun _ _ ↦ rfl)
    fun w hw ↦ by
      simp only [archAbsVal, mem_toFinset, mem_multisetInfinitePlace] at hw ⊢
      simp [count_multisetInfinitePlace_eq_mult ⟨w, hw⟩]

lemma sum_nonarchAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (∑ᶠ v : nonarchAbsVal, f v.val) = ∑ᶠ v : FinitePlace K, f v.val :=
  rfl


/-- This is the familiar definition of the multiplicative height on a number field. -/
lemma mulHeight₁_eq (x : K) :
    mulHeight₁ x =
      (∏ v : InfinitePlace K, max (v x) 1 ^ v.mult) * ∏ᶠ v : FinitePlace K, max (v x) 1 := by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.mulHeight₁_eq,
    prod_archAbsVal_eq, prod_nonarchAbsVal_eq fun v ↦ max (v x) 1]

open Real in
/-- This is the familiar definition of the logarithmic height on a number field. -/
lemma logHeight₁_eq (x : K) :
    logHeight₁ x =
      (∑ v : InfinitePlace K, v.mult * log⁺ (v x)) + ∑ᶠ v : FinitePlace K, log⁺ (v x) := by
  simp only [← nsmul_eq_mul, FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.logHeight₁_eq,
    sum_archAbsVal_eq, sum_nonarchAbsVal_eq fun v ↦ log⁺ (v x)]

/-- This is the familiar definition of the multiplicative height on (nonzero) tuples
of number field elements. -/
lemma mulHeight_eq {ι : Type*} {x : ι → K} (hx : x ≠ 0) :
    mulHeight x =
      (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.mulHeight_eq hx,
    prod_archAbsVal_eq, prod_nonarchAbsVal_eq fun v ↦ ⨆ i, v (x i)]

variable (K) in
lemma totalWeight_eq_sum_mult : totalWeight K = ∑ v : InfinitePlace K, v.mult := by
  simp only [totalWeight]
  convert sum_archAbsVal_eq (fun _ ↦ (1 : ℕ))
  · rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem, ← Multiset.length_toList,
      Fin.sum_const, Multiset.length_toList, smul_eq_mul, mul_one]
  · simp

variable (K) in
lemma totalWeight_eq_finrank : totalWeight K = Module.finrank ℚ K := by
  rw [totalWeight_eq_sum_mult, InfinitePlace.sum_mult_eq]

variable (K) in
@[grind! .]
lemma totalWeight_pos : 0 < totalWeight K := by
  have : Inhabited (InfinitePlace K) := Classical.inhabited_of_nonempty'
  simpa [totalWeight, archAbsVal, multisetInfinitePlace]
    using Fintype.sum_pos
      (Function.ne_iff.mpr ⟨default, (default : InfinitePlace K).mult_ne_zero⟩).pos

end NumberField

/-!
### Heights over the rational numbers

We show that the `Height.mulHeight` of a tuple of coprime integers (considered as rational numbers)
equals the maximum of their absolute values and that the `Height.mulHeight₁` of a rational
number is the maximum of the absolute value of the numerator and the denominator.
We add the corresponding results for logarithmic heights.
-/

namespace Rat

open NumberField Height

section tuples

variable {ι : Type*} [Fintype ι] [Nonempty ι] {x : ι → ℤ}

/-- The term corresponding to a finite place in the definition of the multiplicative height
of a tuple of rational numbers equals `1` if the tuple consists of coprime integers. -/
lemma iSup_finitePlace_apply_eq_one_of_gcd_eq_one (v : FinitePlace ℚ) (hx : Finset.univ.gcd x = 1) :
    ⨆ i, v (x i) = 1 := by
  have hv : IsNonarchimedean (v ·) := FinitePlace.add_le v
  have H (n : ℤ) : v n ≤ 1 := IsNonarchimedean.apply_intCast_le_one_of_isNonarchimedean hv
  obtain ⟨f, hf⟩ := by classical exact Finset.gcd_eq_sum_mul .univ x
  rw [hx] at hf
  obtain ⟨j, hj⟩ : ∃ j, v (x j) = 1 := by
    have h' : v (∑ i, x i * f i) ≤ ⨆ i, v (x i * f i) := by
      convert IsNonarchimedean.apply_sum_le hv
      rw [← cbiSup_eq_of_forall (by grind)]
      simp [Finset.mem_univ, ciSup_unique]
    by_contra! h
    replace h i : v (x i) < 1 := lt_of_le_of_ne (H <| x i) (h i)
    rw [← map_one v, show (1 : ℚ) = (1 : ℤ) from rfl, hf] at h
    push_cast at h
    replace h i : v (x i * f i) < ⨆ i, v (x i * f i) := by
      rw [map_mul, ← mul_one (iSup _)]
      exact mul_lt_mul_of_nonneg_of_pos ((h i).trans_le h') (H _) (by positivity) zero_lt_one
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ v (x i * f i))
    exact (h i).ne hi
  exact le_antisymm (ciSup_le fun i ↦ H (x i)) <| Finite.le_ciSup_of_le j hj.symm.le

open AdmissibleAbsValues in
/-- The multiplicative height of a tuple of rational numbers that consists of coprime integers
is the maximum of the absolute values of the entries. -/
lemma mulHeight_eq_max_abs_of_gcd_eq_one (hx : Finset.univ.gcd x = 1) :
    mulHeight (((↑) : ℤ →  ℚ) ∘ x) = ⨆ i, |x i| := by
  have hx₀ : Int.cast ∘ x ≠ (0 : ι → ℚ) := by
    contrapose! hx
    rw [Function.comp_eq_zero_iff x intCast_injective Rat.intCast_zero] at hx
    rw [hx, Finset.gcd_eq_zero_iff.mpr (by simp)]
    exact zero_ne_one
  have : ⨆ i, (↑|x i| : ℝ) = ↑(⨆ i, |x i|) :=
    (Monotone.map_ciSup_of_continuousAt continuous_of_discreteTopology.continuousAt
      (Int.cast_mono (R := ℝ)) (Finite.bddAbove_range _)).symm
  simp_rw [NumberField.mulHeight_eq hx₀, Function.comp_apply, infinitePlace_apply, ← Int.cast_abs]
  simp [-Int.cast_abs,
    finprod_eq_one_of_forall_eq_one (iSup_finitePlace_apply_eq_one_of_gcd_eq_one · hx), this]

open Real in
/-- The logarithmic height of a tuple of rational numbers that consists of coprime integers
is the logarithm of the maximum of the absolute values of the entries. -/
lemma logHeight_eq_max_abs_of_gcd_eq_one (hx : Finset.univ.gcd x = 1) :
    logHeight (((↑) : ℤ →  ℚ) ∘ x) = log ↑(⨆ i, |x i|) := by
  rw [logHeight_eq_log_mulHeight, mulHeight_eq_max_abs_of_gcd_eq_one hx]

end tuples

section mulHeight₁

lemma mulHeight_self_one_eq_mulHeight_num_den (q : ℚ) :
    mulHeight ![q, 1] = mulHeight ![(q.num : ℚ), q.den] := by
  have hq₀ : (q.den : ℚ) ≠ 0 := mod_cast q.den_nz
  rw [← mulHeight_smul_eq_mulHeight _ hq₀]
  simp

/-- The multiplicative height of a rational number is the maximum of the absolute value of
its numerator and its denominator. -/
lemma mulHeight₁_eq_max (q : ℚ) : mulHeight₁ q = max q.num.natAbs q.den := by
  rw [mulHeight₁_eq_mulHeight, mulHeight_self_one_eq_mulHeight_num_den, ← intCast_natCast q.den]
  have : (.univ : Finset (Fin 2)).gcd ![q.num, q.den] = 1 := by
    simpa [Finset.univ_fin2, Int.normalize_coe_nat, ← Int.coe_gcd q.num q.den] using
      Int.isCoprime_iff_gcd_eq_one.mp <| isCoprime_num_den q
  convert mulHeight_eq_max_abs_of_gcd_eq_one this
  · ext i; fin_cases i <;> simp
  · rw [show (↑(max q.num.natAbs q.den) : ℝ) = (max q.num.natAbs q.den : ℤ) by norm_cast]
    norm_cast
    push_cast
    refine le_antisymm (max_le ?_ ?_) <| ciSup_le fun i ↦ ?_
    · exact Finite.le_ciSup_of_le 0 <| by simp
    · exact Finite.le_ciSup_of_le 1 <| by simp
    · fin_cases i <;> simp

open Real in
/-- The logarithmic height of a rational number is the logarithm of the maximum of the absolute
value of its numerator and its denominator. -/
lemma logHeight₁_eq_log_max (q : ℚ) : logHeight₁ q = log ↑(max q.num.natAbs q.den) := by
  rw [logHeight₁_eq_log_mulHeight₁, mulHeight₁_eq_max]

/-- The multiplicative height of a positive natural number `n` cast to `ℚ` equals `n`. -/
theorem mulHeight₁_natCast (n : ℕ) [NeZero n] :
    mulHeight₁ (n : ℚ) = n := by
  simp [mulHeight₁_eq_max, show 1 ≤ n by grind [NeZero.ne n]]

/-- The logarithmic height of a positive natural number `n` cast to `ℚ` equals `log n`. -/
theorem logHeight₁_natCast (n : ℕ) [NeZero n] :
    logHeight₁ (n : ℚ) = Real.log n := by
  simp [logHeight₁_eq_log_mulHeight₁, mulHeight₁_natCast n]

end mulHeight₁

end Rat

/-!
### Positivity extension for totalWeight on number fields
-/

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `Height.totalWeight` is positive for number fields. -/
@[positivity Height.totalWeight _]
meta def evalHeightTotalWeight : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(@Height.totalWeight $K $KF $KA) =>
    -- Check whether there is a `NumberField` instance for `$K` around.
    match ← trySynthInstanceQ q(NumberField $K) with
    | .some _instFinite =>
      assertInstancesCommute
      return .positive q(NumberField.totalWeight_pos $K)
    | _ => throwError "field in Height.totalWeight not known to be a number field"
  | _, _, _ => throwError "not Height.totalWeight"

end Mathlib.Meta.Positivity

end
