/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.CstarAlgebra.ContinuousFunctionalCalculus.Unique

/-!
# Real powers defined via the continuous functional calculus

This file defines real powers via the continuous functional calculus (CFC) and builds its API.
This allows one to take real powers of matrices, operators, elements of a C⋆-algebra, etc. The
square root is also defined via the non-unital CFC.

## Main declarations

+ `CFC.nnrpow`: the `ℝ≥0` power function based on the non-unital CFC, i.e. `cfcₙ NNReal.rpow`
  composed with `(↑) : ℝ≥0 → ℝ`.
+ `CFC.sqrt`: the square root function based on the non-unital CFC, i.e. `cfcₙ NNReal.sqrt`
+ `CFC.rpow`: the real power function based on the unital CFC, i.e. `cfc NNReal.rpow`

## Implementation notes

We define two separate versions `CFC.nnrpow` and `CFC.rpow` due to what happens at 0. Since
`NNReal.rpow 0 0 = 1`, this means that this function does not map zero to zero when the exponent
is zero, and hence `CFC.nnrpow a 0 = 0` whereas `CFC.rpow a 0 = 1`. Note that the non-unital version
only makes sense for nonnegative exponents, and hence we define it such that the exponent is in
`ℝ≥0`.

## Notation

+ We define a `Pow A ℝ` instance for `CFC.rpow`, i.e `a ^ y` with `A` an operator and `y : ℝ` works
  as expected. Likewise, we define a `Pow A ℝ≥0` instance for `CFC.nnrpow`.

## TODO

+ Relate these to the log and exp functions
+ Lemmas about how these functions interact with commuting `a` and `b`.
+ Prove the order properties (operator monotonicity and concavity/convexity)
-/

open scoped NNReal

namespace NNReal

/-- Taking a nonnegative power of a nonnegative number. This is defined as a standalone definition
in order to speed up automation such as `cfc_cont_tac`. -/
noncomputable abbrev nnrpow (a : ℝ≥0) (b : ℝ≥0) : ℝ≥0 := a ^ (b : ℝ)

@[simp] lemma nnrpow_def (a b : ℝ≥0) : nnrpow a b = a ^ (b : ℝ) := rfl

@[fun_prop]
lemma continuous_nnrpow_const (y : ℝ≥0) : Continuous (nnrpow · y) :=
  continuous_rpow_const zero_le_coe

end NNReal

namespace CFC

section NonUnital

variable {A : Type*} [PartialOrder A] [NonUnitalNormedRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalRing A] [Module ℝ≥0 A] [SMulCommClass ℝ≥0 A A] [IsScalarTower ℝ≥0 A A]
  [CompleteSpace A] [NonUnitalContinuousFunctionalCalculus ℝ≥0 (fun (a : A) => 0 ≤ a)]

/- ## `nnrpow` -/

/-- Real powers of operators, based on the non-unital continuous functional calculus. -/
noncomputable def nnrpow (a : A) (y : ℝ≥0) : A := cfcₙ (NNReal.nnrpow · y) a

/-- Enable `a ^ y` notation for `CFC.nnrpow`. This is a low-priority instance to make sure it does
not take priority over other instances when they are available. -/
noncomputable instance (priority := 100) : Pow A ℝ≥0 where
  pow a y := nnrpow a y

@[simp]
lemma nnrpow_eq_pow {a : A} {y : ℝ≥0} : nnrpow a y = a ^ y := rfl

@[simp]
lemma nnrpow_nonneg {a : A} {x : ℝ≥0} : 0 ≤ a ^ x := cfcₙ_predicate _ a

lemma nnrpow_def {a : A} {y : ℝ≥0} : a ^ y = cfcₙ (NNReal.nnrpow · y) a := rfl

lemma nnrpow_add {a : A} {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) :
    a ^ (x + y) = a ^ x * a ^ y := by
  simp only [nnrpow_def]
  rw [← cfcₙ_mul _ _ a]
  congr! 2 with z
  exact_mod_cast NNReal.rpow_add' z <| ne_of_gt (add_pos hx hy)

@[simp]
lemma nnrpow_zero {a : A} : a ^ (0 : ℝ≥0) = 0 := by
  simp [nnrpow_def, cfcₙ_apply_of_not_map_zero]

lemma nnrpow_one {a : A} (ha : 0 ≤ a := by cfc_tac) : a ^ (1 : ℝ≥0) = a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_one, NNReal.rpow_one]
  change cfcₙ (id : ℝ≥0 → ℝ≥0) a = a
  rw [cfcₙ_id ℝ≥0 a]

lemma nnrpow_two {a : A} (ha : 0 ≤ a := by cfc_tac) : a ^ (2 : ℝ≥0) = a * a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_ofNat, NNReal.rpow_ofNat, pow_two]
  change cfcₙ (fun z : ℝ≥0 => id z * id z) a = a * a
  rw [cfcₙ_mul id id a, cfcₙ_id ℝ≥0 a]

lemma nnrpow_three {a : A} (ha : 0 ≤ a := by cfc_tac) : a ^ (3 : ℝ≥0) = a * a * a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_ofNat, NNReal.rpow_ofNat, pow_three]
  change cfcₙ (fun z : ℝ≥0 => id z * (id z * id z)) a = a * a * a
  rw [cfcₙ_mul id _ a, cfcₙ_mul id _ a, ← mul_assoc, cfcₙ_id ℝ≥0 a]

@[simp]
lemma zero_nnrpow {x : ℝ≥0} : (0 : A) ^ x = 0 := by simp [nnrpow_def]

@[simp]
lemma nnrpow_nnrpow [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]
    {a : A} {x y : ℝ≥0} : (a ^ x) ^ y = a ^ (x * y) := by
  by_cases ha : 0 ≤ a
  case pos =>
    obtain (rfl | hx) := eq_zero_or_pos x <;> obtain (rfl | hy) := eq_zero_or_pos y
    all_goals try simp
    simp only [nnrpow_def, NNReal.coe_mul]
    rw [← cfcₙ_comp _ _ a]
    congr! 2 with u
    ext
    simp [Real.rpow_mul]
  case neg =>
    simp [nnrpow_def, cfcₙ_apply_of_not_predicate a ha]

/- ## `sqrt` -/

section sqrt

/-- Square roots of operators, based on the non-unital continuous functional calculus. -/
noncomputable def sqrt (a : A) : A := cfcₙ NNReal.sqrt a

@[simp]
lemma sqrt_nonneg {a : A} : 0 ≤ sqrt a := cfcₙ_predicate _ a

lemma sqrt_eq_nnrpow {a : A} : sqrt a = a ^ (1 / 2 : ℝ≥0) := by
  simp only [sqrt, nnrpow, NNReal.coe_inv, NNReal.coe_ofNat, NNReal.rpow_eq_pow]
  congr
  ext
  exact_mod_cast NNReal.sqrt_eq_rpow _

@[simp]
lemma sqrt_zero : sqrt (0 : A) = 0 := by simp [sqrt]

variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]

@[simp]
lemma nnrpow_sqrt {a : A} {x : ℝ≥0} : (sqrt a) ^ x = a ^ (x / 2) := by
  rw [sqrt_eq_nnrpow, nnrpow_nnrpow, one_div_mul_eq_div 2 x]

lemma nnrpow_sqrt_two {a : A} (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ (2 : ℝ≥0) = a := by
  simp only [nnrpow_sqrt, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [nnrpow_one]

lemma sqrt_mul_sqrt_self {a : A} (ha : 0 ≤ a := by cfc_tac) : sqrt a * sqrt a = a := by
  rw [← nnrpow_two, nnrpow_sqrt_two]

@[simp]
lemma sqrt_nnrpow {a : A} {x : ℝ≥0} : sqrt (a ^ x) = a ^ (x / 2) := by
  simp [sqrt_eq_nnrpow, div_eq_mul_inv]

lemma sqrt_nnrpow_two {a : A} (ha : 0 ≤ a := by cfc_tac) : sqrt (a ^ (2 : ℝ≥0)) = a := by
  simp only [sqrt_nnrpow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [nnrpow_one]

lemma sqrt_mul_self {a : A} (ha : 0 ≤ a := by cfc_tac) : sqrt (a * a) = a := by
  rw [← nnrpow_two, sqrt_nnrpow_two]

end sqrt

end NonUnital

section Unital

variable {A : Type*} [PartialOrder A] [NormedRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [ContinuousFunctionalCalculus ℝ≥0 (fun (a : A) => 0 ≤ a)]

/- ## `rpow` -/

/-- Real powers of operators, based on the unital continuous functional calculus. -/
noncomputable def rpow (a : A) (y : ℝ) : A := cfc (fun x : ℝ≥0 => x ^ y) a

/-- Enable `a ^ y` notation for `CFC.rpow`. This is a low-priority instance to make sure it does
not take priority over other instances when they are available. -/
noncomputable instance (priority := 100) : Pow A ℝ where
  pow a y := rpow a y

@[simp]
lemma rpow_eq_pow {a : A} {y : ℝ} : rpow a y = a ^ y := rfl

@[simp]
lemma rpow_nonneg {a : A} {y : ℝ} : 0 ≤ a ^ y := cfc_predicate _ a

lemma rpow_def {a : A} {y : ℝ} : a ^ y = cfc (fun x : ℝ≥0 => x ^ y) a := rfl

lemma rpow_natCast {a : A} {n : ℕ} (ha : 0 ≤ a := by cfc_tac) : a ^ (n : ℝ) = a ^ n := by
  have h₁ : (fun x : ℝ≥0 => x ^ (n : ℝ)) = fun (x : ℝ≥0) => x ^ n := by ext; simp
  simp_rw [rpow_def, h₁]
  change cfc (fun x : ℝ≥0 => (id x) ^ n) a = a ^ n
  rw [cfc_pow (id : ℝ≥0 → ℝ≥0) n a, cfc_id ℝ≥0 a]

@[simp]
lemma rpow_algebraMap {x : ℝ≥0} {y : ℝ} :
    (algebraMap ℝ≥0 A x) ^ y = algebraMap ℝ≥0 A (x ^ y) := by
  simp only [rpow_def]
  rw [cfc_algebraMap x (fun z : ℝ≥0 => z ^ y)]

lemma rpow_add_of_zero_not_mem_spectrum {a : A} {x y : ℝ} (ha : 0 ∉ spectrum ℝ≥0 a) :
    a ^ (x + y) = a ^ x * a ^ y := by
  simp only [rpow_def, NNReal.rpow_eq_pow]
  have h : ∀ r, ContinuousOn (fun z : ℝ≥0 => z ^ (r : ℝ)) (spectrum ℝ≥0 a) := by
    intro r z hz
    exact ContinuousAt.continuousWithinAt <| NNReal.continuousAt_rpow_const <| Or.inl <| by aesop
  rw [← cfc_mul _ _ a (h x) (h y)]
  refine cfc_congr ?_
  intro z hz
  have : z ≠ 0 := by aesop
  simp [NNReal.rpow_add this _ _]

-- TODO: relate to a strict positivity condition
lemma rpow_rpow_of_zero_not_mem_spectrum [UniqueContinuousFunctionalCalculus ℝ≥0 A]
    {a : A} {x y : ℝ} (ha₁ : 0 ∉ spectrum ℝ≥0 a) (hx : x ≠ 0) (ha₂ : 0 ≤ a := by cfc_tac) :
    (a ^ x) ^ y = a ^ (x * y) := by
  simp only [rpow_def]
  have h₁ : ContinuousOn (fun z : ℝ≥0 => z ^ (y : ℝ))
      ((fun z : ℝ≥0 => z ^ (x : ℝ)) '' spectrum ℝ≥0 a) := by
    intro z hz
    exact ContinuousAt.continuousWithinAt <| NNReal.continuousAt_rpow_const <| Or.inl <| by aesop
  have h₂ : ContinuousOn (fun z : ℝ≥0 => z ^ (x : ℝ)) (spectrum ℝ≥0 a) := by
    intro z hz
    exact ContinuousAt.continuousWithinAt <| NNReal.continuousAt_rpow_const <| Or.inl <| by aesop
  rw [← cfc_comp _ _ a ha₂ h₁ h₂]
  refine cfc_congr fun _ _ => ?_
  simp [NNReal.rpow_mul]

lemma rpow_rpow_of_exponent_nonneg {a : A} {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha₂ : 0 ≤ a := by cfc_tac) : (a ^ x) ^ y = a ^ (x * y) := by
  simp only [rpow_def]
  have h₁ : ContinuousOn (fun z : ℝ≥0 => z ^ (y : ℝ))
      ((fun z : ℝ≥0 => z ^ (x : ℝ)) '' spectrum ℝ≥0 a) :=
    fun _ _ => ContinuousAt.continuousWithinAt <| NNReal.continuousAt_rpow_const (Or.inr hy)
  have h₂ : ContinuousOn (fun z : ℝ≥0 => z ^ (x : ℝ)) (spectrum ℝ≥0 a) :=
    fun _ _ => ContinuousAt.continuousWithinAt <| NNReal.continuousAt_rpow_const (Or.inr hx)
  rw [← cfc_comp _ _ a ha₂ h₁ h₂]
  refine cfc_congr fun _ _ => ?_
  simp [NNReal.rpow_mul]

lemma rpow_one {a : A} (ha : 0 ≤ a := by cfc_tac) : a ^ (1 : ℝ) = a := by
  simp only [rpow_def, NNReal.coe_one, NNReal.rpow_eq_pow, NNReal.rpow_one]
  change cfc (id : ℝ≥0 → ℝ≥0) a = a
  rw [cfc_id ℝ≥0 a]

@[simp]
lemma one_rpow {x : ℝ} : (1 : A) ^ x = (1 : A) := by simp [rpow_def]

lemma rpow_zero {a : A} (ha : 0 ≤ a := by cfc_tac) : a ^ (0 : ℝ) = 1 := by
  simp [rpow_def, cfc_const_one ℝ≥0 a]

lemma zero_rpow {x : ℝ} (hx : x ≠ 0) : rpow (0 : A) x = 0 := by simp [rpow, NNReal.zero_rpow hx]

section unital_vs_nonunital

lemma nnrpow_eq_rpow {a : A} {x : ℝ≥0} (hx : 0 < x) : a ^ x = a ^ (x : ℝ) := by
  rw [nnrpow_def (A := A), rpow_def, cfcₙ_eq_cfc]

lemma sqrt_eq_rpow {a : A} : sqrt a = a ^ (1 / 2 : ℝ) := by
  have : a ^ (1 / 2 : ℝ) = a ^ ((1 / 2 : ℝ≥0) : ℝ) := rfl
  rw [this, ← nnrpow_eq_rpow (by norm_num), sqrt_eq_nnrpow (A := A)]

lemma sqrt_eq_cfc {a : A} : sqrt a = cfc NNReal.sqrt a := by
  unfold sqrt
  rw [cfcₙ_eq_cfc]

lemma sqrt_sq {a : A} (ha : 0 ≤ a := by cfc_tac) : sqrt (a ^ 2) = a := by
  rw [pow_two, sqrt_mul_self (A := A)]

lemma sq_sqrt {a : A} (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ 2 = a := by
  rw [pow_two, sqrt_mul_sqrt_self (A := A)]

@[simp]
lemma sqrt_algebraMap {r : ℝ≥0} : sqrt (algebraMap ℝ≥0 A r) = algebraMap ℝ≥0 A (NNReal.sqrt r) := by
  rw [sqrt_eq_cfc, cfc_algebraMap]

@[simp]
lemma sqrt_one : sqrt (1 : A) = 1 := by simp [sqrt_eq_cfc]

-- TODO: relate to a strict positivity condition
lemma sqrt_rpow_of_zero_not_mem_spectrum {a : A} {x : ℝ} (h : 0 ∉ spectrum ℝ≥0 a)
    (hx : x ≠ 0) : sqrt (a ^ x) = a ^ (x / 2) := by
  by_cases hnonneg : 0 ≤ a
  case pos =>
    simp only [sqrt_eq_rpow, div_eq_mul_inv, one_mul, rpow_rpow_of_zero_not_mem_spectrum h hx]
  case neg =>
    simp [sqrt_eq_cfc, rpow_def, cfc_apply_of_not_predicate a hnonneg]

-- TODO: relate to a strict positivity condition
lemma rpow_sqrt_of_zero_not_mem_spectrum {a : A} {x : ℝ} (h : 0 ∉ spectrum ℝ≥0 a)
    (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ x = a ^ (x / 2) := by
  rw [sqrt_eq_rpow, div_eq_mul_inv, one_mul, rpow_rpow_of_zero_not_mem_spectrum h (by norm_num),
      inv_mul_eq_div]

lemma sqrt_rpow_nnreal {a : A} {x : ℝ≥0} : sqrt (a ^ (x : ℝ)) = a ^ (x / 2 : ℝ) := by
  by_cases htriv : 0 ≤ a
  case neg => simp [sqrt_eq_cfc, rpow_def, cfc_apply_of_not_predicate a htriv]
  case pos =>
    by_cases hx : x = 0
    case pos => simp [hx, rpow_zero htriv]
    case neg =>
      have h₁ : 0 < x := lt_of_le_of_ne (by aesop) (Ne.symm hx)
      have h₂ : (x : ℝ) / 2 = NNReal.toReal (x / 2) := rfl
      have h₃ : 0 < x / 2 := by positivity
      rw [← nnrpow_eq_rpow h₁, h₂, ← nnrpow_eq_rpow h₃, sqrt_nnrpow (A := A)]

lemma rpow_sqrt_nnreal {a : A} {x : ℝ≥0} (ha : 0 ≤ a := by cfc_tac) :
    (sqrt a) ^ (x : ℝ) = a ^ (x / 2 : ℝ) := by
  by_cases hx : x = 0
  case pos =>
    have ha' : 0 ≤ sqrt a := by exact sqrt_nonneg
    simp [hx, rpow_zero ha', rpow_zero ha]
  case neg =>
    have h₁ : 0 ≤ (x : ℝ) := by exact NNReal.zero_le_coe
    rw [sqrt_eq_rpow, rpow_rpow_of_exponent_nonneg (by norm_num) h₁, one_div_mul_eq_div]

end unital_vs_nonunital

end Unital

end CFC
