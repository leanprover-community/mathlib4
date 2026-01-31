/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Data.Fintype.Order
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Basic theory of heights

This is an attempt at formalizing some basic properties of height functions.

We aim at a level of generality that allows to apply the theory to algebraic number fields
and to function fields (and possibly beyond).

The general set-up for heights is the following. Let `K` be a field.
* We have a `Multiset` of archimedean absolute values on `K` (with values in `ℝ`).
* We also have a `Set` of non-archimedean (i.e., `|x+y| ≤ max |x| |y|`) absolute values.
* For a given `x ≠ 0` in `K`, `|x|ᵥ = 1` for all but finitely many (non-archimedean) `v`.
* We have the *product formula* `∏ v : arch, |x|ᵥ * ∏ v : nonarch, |x|ᵥ = 1`
  for all `x ≠ 0` in `K`, where the first product is over the multiset of archimedean
  absolute values.

We realize this implementation via the class `Height.AdmissibleAbsValues K`.

## Main definitions

We define *multiplicative heights* and *logarithmic heights* (which are just defined to
be the (real) logarithm of the corresponding multiplicative height). This leads to some
duplication (in the definitions and statements; the proofs are reduced to those for the
multiplicative height), which is justified, as both versions are frequently used.

We define the following variants.
* `Height.mulHeight₁ x` and `Height.logHeight₁ x` for `x : K`.
  This is the height of an element of `K`.
* `Height.mulHeight x` and `Height.logHeight x` for `x : ι → K` with `ι` finite. This is the height
  of a tuple of elements of `K` representing a point in projective space. When `x = 0`, we
  define the multiplicative height to be `1` (so the loarithmic height is `0`).
  It is invariant under scaling by nonzero elements of `K`.
* `Finsupp.mulHeight x` and `Finsupp.logHeight x` for `x : α →₀ K`. This is the same
  as the height of `x` restricted to the support of `x`.
* (TODO)
  `Projectivization.mulHeight` and `Projectivization.logHeight` on
  `Projectivization K (ι → K)` (with a `Fintype ι`). This is the height of a point
  on projective space (with fixed basis).

## Tags

Height, absolute value

-/

@[expose] public noncomputable section

namespace Height

/-!
### Families of admissible absolute values

We define the class `AdmissibleAbsValues K` for a field `K`, which captures the notion of a
family of absolute values on `K` satisfying a product formula.
-/

/-- A type class capturing an admissible family of absolute values. -/
class AdmissibleAbsValues (K : Type*) [Field K] where
  /-- The archimedean absolute values as a multiset of `ℝ`-valued absolute values on `K`. -/
  archAbsVal : Multiset (AbsoluteValue K ℝ)
  /-- The nonarchimedean absolute values as a set of `ℝ`-valued absolute values on `K`. -/
  nonarchAbsVal : Set (AbsoluteValue K ℝ)
  /-- The nonarchimedean absolute values are indeed nonarchimedean. -/
  isNonarchimedean : ∀ v ∈ nonarchAbsVal, IsNonarchimedean v
  /-- Only finitely many (nonarchimedean) absolute values are `≠ 1` for any nonzero `x : K`. -/
  mulSupport_finite {x : K} (_ : x ≠ 0) : (fun v : nonarchAbsVal ↦ v.val x).mulSupport.Finite
  /-- The product formula. The archimedean absolute values are taken with their multiplicity. -/
  product_formula {x : K} (_ : x ≠ 0) :
      (archAbsVal.map (· x)).prod * ∏ᶠ v : nonarchAbsVal, v.val x = 1

open AdmissibleAbsValues Real

variable (K : Type*) [Field K] [AdmissibleAbsValues K]

/-- The `totalWeight` of a field with `AdmissibleAbsValues` is the sum of the multiplicities of
the archimedean places. -/
def totalWeight : ℕ := archAbsVal (K := K) |>.card

variable {K}

/-!
### Heights of field elements

We use the subscipt `₁` to denote multiplicative and logarithmic heights of field elements
(this is because we are in the one-dimensional case of (affine) heights).
-/

/-- The multiplicative height of an element of `K`. -/
def mulHeight₁ (x : K) : ℝ :=
  (archAbsVal.map fun v ↦ max (v x) 1).prod * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1

lemma mulHeight₁_eq (x : K) :
    mulHeight₁ x =
      (archAbsVal.map fun v ↦ max (v x) 1).prod * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1 :=
  rfl

@[simp]
lemma mulHeight₁_zero : mulHeight₁ (0 : K) = 1 := by
  simp [mulHeight₁_eq]

@[simp]
lemma mulHeight₁_one : mulHeight₁ (1 : K) = 1 := by
  simp [mulHeight₁_eq]

/-- The mutliplicative height of a field element is always at least `1`. -/
lemma one_le_mulHeight₁ (x : K) : 1 ≤ mulHeight₁ x := by
  refine one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod fun _ h ↦ ?_) ?_
  · obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp h
    exact le_max_right ..
  · exact one_le_finprod fun _ ↦ le_max_right ..

-- This is needed as a side condition in proofs about logarithmic heights
lemma mulHeight₁_pos (x : K) : 0 < mulHeight₁ x :=
  zero_lt_one.trans_le <| one_le_mulHeight₁ x

-- This is needed as a side condition in proofs about logarithmic heights
lemma mulHeight₁_ne_zero (x : K) : mulHeight₁ x ≠ 0 :=
  (mulHeight₁_pos x).ne'

lemma zero_le_mulHeight₁ (x : K) : 0 ≤ mulHeight₁ x :=
  (mulHeight₁_pos x).le

/-- The logarithmic height of an element of `K`. -/
def logHeight₁ (x : K) : ℝ := log (mulHeight₁ x)

lemma logHeight₁_eq_log_mulHeight₁ (x : K) : logHeight₁ x = log (mulHeight₁ x) := rfl

@[simp]
lemma logHeight₁_zero : logHeight₁ (0 : K) = 0 := by
  simp [logHeight₁_eq_log_mulHeight₁]

@[simp]
lemma logHeight₁_one : logHeight₁ (1 : K) = 0 := by
  simp [logHeight₁_eq_log_mulHeight₁]

lemma zero_le_logHeight₁ (x : K) : 0 ≤ logHeight₁ x :=
  Real.log_nonneg <| one_le_mulHeight₁ x

end Height

/-!
### Positivity extension for mulHeight₁, logHeight₁
-/

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq Height

/-- Extension for the `positivity` tactic: `Height.mulHeight₁` is always positive. -/
@[positivity Height.mulHeight₁ _]
meta def evalMulHeight₁ : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@mulHeight₁ $K $KF $KA $a) =>
    assertInstancesCommute
    pure (.positive q(mulHeight₁_pos $a))
  | _, _, _ => throwError "not Height.mulHeight₁"

/-- Extension for the `positivity` tactic: `Height.logHeight₁` is always nonnegative. -/
@[positivity Height.logHeight₁ _]
meta def evalLogHeight₁ : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@logHeight₁ $K $KF $KA $a) =>
    assertInstancesCommute
    pure (.nonnegative q(zero_le_logHeight₁ $a))
  | _, _, _ => throwError "not Height.logHeight₁"

end Mathlib.Meta.Positivity

/-!
### Heights of tuples and finitely supported maps

We define the multiplicative height of a nonzero tuple `x : ι → K` as the product of the maxima
of `v` on `x`, as `v` runs through the relevant absolute values of `K`. As usual, the
logarithmic height is the logarithm of the multiplicative height.
When `x = 0`, we define the multiplicative height to be `1`; this is a convenient "junk value",
which allows to avoid the condition `x ≠ 0` in most of the results.

For a finitely supported function `x : ι →₀ K`, we define the height as the height of `x`
restricted to its support.
-/


namespace Height

open AdmissibleAbsValues Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*}

/-- The multiplicative height of a tuple of elements of `K`.
For the zero tuple we take the junk value `1`. -/
def mulHeight (x : ι → K) : ℝ :=
  have : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then 1 else
    (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i)

lemma mulHeight_eq {x : ι → K} (hx : x ≠ 0) :
    mulHeight x =
      (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i) := by
  simp [mulHeight, hx]

@[simp]
lemma mulHeight_zero : mulHeight (0 : ι → K) = 1 := by
  simp [mulHeight]

@[simp]
lemma mulHeight_one : mulHeight (1 : ι → K) = 1 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [show (1 : ι → K) = 0 from Subsingleton.elim ..]
    exact mulHeight_zero
  · have hx : (1 : ι → K) ≠ 0 := by simp
    simp [mulHeight_eq hx]

/-- The multiplicative height does not change under re-indexing. -/
lemma mulHeight_comp_equiv {ι' : Type*} (e : ι ≃ ι') (x : ι' → K) :
    mulHeight (x ∘ e) = mulHeight x := by
  have H (v : AbsoluteValue K ℝ) : ⨆ i, v (x (e i)) = ⨆ i, v (x i) := e.iSup_congr (congrFun rfl)
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : x ∘ e ≠ 0 := by
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
      exact Function.ne_iff.mpr ⟨e.symm i, by simp [hi]⟩
    simp [mulHeight_eq hx, mulHeight_eq hx', Function.comp_apply, H]

lemma mulHeight_swap (x y : K) : mulHeight ![x, y] = mulHeight ![y, x] := by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  rw [show ![x, y] = ![y, x] ∘ e from List.ofFn_inj.mp rfl]
  exact mulHeight_comp_equiv e ![y, x]

/-- The logarithmic height of a tuple of elements of `K`. -/
def logHeight (x : ι → K) : ℝ := log (mulHeight x)

lemma logHeight_eq_log_mulHeight (x : ι → K) : logHeight x = log (mulHeight x) := rfl

variable {α : Type*}

/-- The multiplicative height of a finitely supported function. -/
def _root_.Finsupp.mulHeight (x : α →₀ K) : ℝ :=
  Height.mulHeight fun i : x.support ↦ x i

/-- The logarithmic height of a finitely supported function. -/
def _root_.Finsupp.logHeight (x : α →₀ K) : ℝ := log (mulHeight x)

lemma _root_.Finsupp.logHeight_eq_log_mulHeight (x : α →₀ K) :
    logHeight x = log (mulHeight x) := rfl

/-!
### First properties of heights
-/

private lemma max_eq_iSup {α : Type*} [ConditionallyCompleteLattice α] (a b : α) :
    max a b = iSup ![a, b] :=
  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two]

variable [Finite ι]

private lemma mulSupport_iSup_nonarchAbsVal_finite {x : ι → K} (hx : x ≠ 0) :
    (Function.mulSupport fun v : nonarchAbsVal ↦ ⨆ i, v.val (x i)).Finite := by
  have : Nonempty {j // x j ≠ 0} := nonempty_subtype.mpr <| Function.ne_iff.mp hx
  suffices (Function.mulSupport fun v : nonarchAbsVal ↦ ⨆ i : {j // x j ≠ 0}, v.val (x i)).Finite by
    convert this with v
    have ⟨i, hi⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx
    have : Nonempty ι := .intro i
    refine le_antisymm (ciSup_le fun j ↦ ?_) <|
      ciSup_le fun ⟨j, hj⟩ ↦ le_ciSup_of_le (Finite.bddAbove_range _) j le_rfl
    rcases eq_or_ne (x j) 0 with h | h
    · rw [h, v.val.map_zero]
      exact Real.iSup_nonneg' ⟨⟨i, hi⟩, v.val.nonneg ..⟩
    · exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨j, h⟩ le_rfl
  exact (Set.finite_iUnion fun i : {j | x j ≠ 0} ↦ mulSupport_finite i.prop).subset <|
    Function.mulSupport_iSup _

private lemma mulSupport_max_nonarchAbsVal_finite (x : K) :
    (Function.mulSupport fun v : nonarchAbsVal ↦ v.val x ⊔ 1).Finite := by
  convert mulSupport_iSup_nonarchAbsVal_finite (x := ![x, 1]) <| by simp with v
  rw [max_eq_iSup]
  congr 1
  ext1 i
  fin_cases i <;> simp

/-- The multiplicative height of a tuple does not change under scaling. -/
lemma mulHeight_smul_eq_mulHeight (x : ι → K) {c : K} (hc : c ≠ 0) :
    mulHeight (c • x) = mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  have : Nonempty ι := (Function.ne_iff.mp hx).nonempty
  have hcx : c • x ≠ 0 := by simp [hc, hx]
  simp only [mulHeight_eq hx, mulHeight_eq hcx, Pi.smul_apply, smul_eq_mul, map_mul,
    ← mul_iSup_of_nonneg <| AbsoluteValue.nonneg .., Multiset.prod_map_mul]
  rw [finprod_mul_distrib (mulSupport_finite hc) (mulSupport_iSup_nonarchAbsVal_finite hx),
    mul_mul_mul_comm, product_formula hc, one_mul]

lemma one_le_mulHeight (x : ι → K) : 1 ≤ mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  have hx' : (x i)⁻¹ • x ≠ 0 := by simp [hi, hx]
  rw [← mulHeight_smul_eq_mulHeight _ <| inv_ne_zero hi, mulHeight_eq hx']
  refine one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod fun vx h ↦ ?_) ?_
  · simp only [Pi.smul_apply, smul_eq_mul, AbsoluteValue.map_mul, map_inv₀, Multiset.mem_map] at h
    obtain ⟨v, -, rfl⟩ := h
    refine le_ciSup_of_le (Finite.bddAbove_range _) i <| le_of_eq ?_
    exact (inv_mul_cancel₀ <| v.ne_zero_iff.mpr hi).symm
  · refine one_le_finprod fun v ↦ le_ciSup_of_le (Finite.bddAbove_range _) i ?_
    simp [inv_mul_cancel₀ <| v.val.ne_zero_iff.mpr hi]

lemma mulHeight_pos (x : ι → K) : 0 < mulHeight x :=
  zero_lt_one.trans_le <| one_le_mulHeight x

lemma mulHeight.ne_zero (x : ι → K) : mulHeight x ≠ 0 :=
  (mulHeight_pos x).ne'

lemma zero_le_logHeight (x : ι → K) : 0 ≤ logHeight x :=
  log_nonneg <| one_le_mulHeight x

end Height

/-!
### Positivity extension for mulHeight, logHeight
-/

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq Height

/-- Extension for the `positivity` tactic: `Height.mulHeight` is always positive. -/
@[positivity Height.mulHeight _]
meta def evalMulHeight : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@mulHeight $K $KF $KA $ι $a) =>
    -- Check whether there is a `Finite` instance for `$ι` around.
    match ← trySynthInstanceQ q(Finite $ι) with
    | .some _instFinite =>
      assertInstancesCommute
      return .positive q(mulHeight_pos $a)
    | _ => throwError "index type in Height.mulHeight not known to be finite"
  | _, _, _ => throwError "not Height.mulHeight"

/-- Extension for the `positivity` tactic: `Height.logHeight` is always nonnegative. -/
@[positivity Height.logHeight _]
meta def evalLogHeight : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@logHeight $K $KF $KA $ι $a) =>
    -- Check whether there is a `Finite` instance for `$ι` around.
    match ← trySynthInstanceQ q(Finite $ι) with
    | .some _instFinite =>
      assertInstancesCommute
      return .nonnegative q(zero_le_logHeight $a)
    | _ => throwError "index type in Height.logHeight not known to be finite"
  | _, _, _ => throwError "not Height.logHeight"

end Mathlib.Meta.Positivity

/-!
### Further properties of heights
-/

namespace Height

open AdmissibleAbsValues Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} {α : Type*} [Finite ι]
/-- The logarithmic height of a tuple does not change under scaling. -/
lemma logHeight_smul_eq_logHeight (x : ι → K) {c : K} (hc : c ≠ 0) :
    logHeight (c • x) = logHeight x := by
  simp only [logHeight_eq_log_mulHeight, mulHeight_smul_eq_mulHeight x hc]

lemma mulHeight₁_eq_mulHeight (x : K) : mulHeight₁ x = mulHeight ![x, 1] := by
  have H (v : AbsoluteValue K ℝ) (x : K) : v x ⊔ 1 = ⨆ i, v (![x, 1] i) := by
    have (i : Fin 2) : v (![x, 1] i) = ![v x, 1] i := by fin_cases i <;> simp
    simpa [this] using max_eq_iSup (v x) 1
  have hx : ![x, 1] ≠ 0 := by simp
  simp only [mulHeight₁_eq, mulHeight_eq hx, H]

lemma logHeight₁_eq_logHeight (x : K) : logHeight₁ x = logHeight ![x, 1] := by
  simp only [logHeight₁_eq_log_mulHeight₁, logHeight_eq_log_mulHeight, mulHeight₁_eq_mulHeight x]

lemma mulHeight₁_div_eq_mulHeight (x y : K) :
    mulHeight₁ (x / y) = mulHeight ![x, y] := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [div_zero, mulHeight₁_zero]
    rcases eq_or_ne x 0 with rfl | hx
    · rw [show (![0, 0] : Fin 2 → K) = 0 by simp]
      simp
    · have := mulHeight_smul_eq_mulHeight ![1, 0] hx
      simp only [Matrix.smul_cons, smul_eq_mul, mul_one, mul_zero, Matrix.smul_empty] at this
      rw [this, mulHeight_swap, ← mulHeight₁_eq_mulHeight, mulHeight₁_zero]
  · rw [mulHeight₁_eq_mulHeight, ← mulHeight_smul_eq_mulHeight _ hy]
    simp [mul_div_cancel₀ x hy]

lemma logHeight₁_div_eq_logHeight (x y : K) :
    logHeight₁ (x / y) = logHeight ![x, y] := by
  rw [logHeight₁_eq_log_mulHeight₁, logHeight_eq_log_mulHeight, mulHeight₁_div_eq_mulHeight x y]

/-- The multiplicative height of the coordinate-wise `n`th power of a tuple
is the `n`th power of its multiplicative height. -/
lemma mulHeight_pow (x : ι → K) (n : ℕ) :
    mulHeight (x ^ n) = mulHeight x ^ n := by
  rcases eq_or_ne x 0 with rfl | hx
  · cases n <;> simp
  have : Nonempty ι := (Function.ne_iff.mp hx).nonempty
  have H (v : AbsoluteValue K ℝ) : ⨆ i : ι, v ((x ^ n) i) = (⨆ i, v (x i)) ^ n := by
    simp only [Pi.pow_apply, map_pow]
    simp +singlePass only [← coe_toNNReal _ (v.nonneg _)]
    norm_cast
    exact (pow_left_mono n).map_ciSup_of_continuousAt (continuous_pow n).continuousAt
      (Finite.bddAbove_range _) |>.symm
  have hxn : x ^ n ≠ 0 := by simp [hx]
  simp only [mulHeight_eq hx, mulHeight_eq hxn, H, mul_pow,
    finprod_pow <| mulSupport_iSup_nonarchAbsVal_finite hx, ← Multiset.prod_map_pow]

/-- The logarithmic height of the coordinate-wise `n`th power of a tuple
is `n` times its logarithmic height. -/
lemma logHeight_pow (x : ι → K) (n : ℕ) : logHeight (x ^ n) = n * logHeight x := by
  simp [logHeight_eq_log_mulHeight, mulHeight_pow x n]

/-- The multiplicative height of the inverse of a field element `x`
is the same as the multiplicative height of `x`. -/
lemma mulHeight₁_inv (x : K) : mulHeight₁ (x⁻¹) = mulHeight₁ x := by
  simp_rw [mulHeight₁_eq_mulHeight]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [inv_zero]
  · have H : x • ![x⁻¹, 1] = ![1, x] := by ext1 i; fin_cases i <;> simp [hx]
    rw [← mulHeight_smul_eq_mulHeight _ hx, H, mulHeight_swap]

/-- The logarithmic height of the inverse of a field element `x`
is the same as the logarithmic height of `x`. -/
lemma logHeight₁_inv (x : K) : logHeight₁ (x⁻¹) = logHeight₁ x := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_inv]

/-- The multiplicative height of the `n`th power of a field element `x` (with `n : ℕ`)
is the `n`th power of the multiplicative height of `x`. -/
lemma mulHeight₁_pow (x : K) (n : ℕ) : mulHeight₁ (x ^ n) = mulHeight₁ x ^ n := by
  simp only [mulHeight₁_eq_mulHeight, ← mulHeight_pow _ n]
  congr 1
  ext1 i
  fin_cases i <;> simp

/-- The logarithmic height of the `n`th power of a field element `x` (with `n : ℕ`)
is `n` times the logaritmic height of `x`. -/
lemma logHeight₁_pow (x : K) (n : ℕ) : logHeight₁ (x ^ n) = n * logHeight₁ x := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_pow, log_pow]

/-- The multiplicative height of the `n`th power of a field element `x` (with `n : ℤ`)
is the `|n|`th power of the multiplicative height of `x`. -/
lemma mulHeight₁_zpow (x : K) (n : ℤ) : mulHeight₁ (x ^ n) = mulHeight₁ x ^ n.natAbs := by
  rcases le_or_gt 0 n with h | h
  · lift n to ℕ using h
    rw [zpow_natCast, mulHeight₁_pow, Int.natAbs_natCast]
  · nth_rewrite 1 [show n = -n.natAbs by grind]
    rw [zpow_neg, mulHeight₁_inv, zpow_natCast, mulHeight₁_pow]

/-- The logarithmic height of the `n`th power of a field element `x` (with `n : ℤ`)
is `|n|` times the logarithmic height of `x`. -/
lemma logHeight₁_zpow (x : K) (n : ℤ) : logHeight₁ (x ^ n) = n.natAbs * logHeight₁ x := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_zpow, log_pow]

end Height
