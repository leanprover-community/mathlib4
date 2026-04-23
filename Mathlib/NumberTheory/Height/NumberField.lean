/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Ralf Stephan
-/
module

public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Heights over number fields

We provide an instance of `Height.AdmissibleAbsValues` for algebraic number fields
and set up some API.

## TODO

Prove that the height of `(x₀ : x₁ : ··· : xₙ) ∈ ℙⁿ(ℚ)` equals the
maximum of the absolute values of the `xᵢ` when they are chosen to be coprime integers. This
should then be split off into a separate `Mathlib.NumberTheory.Height.Rat` file.
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
### Heights of rational numbers

Since `ℚ` has a unique infinite place (the usual absolute value)
and every finite place satisfies `v n ≤ 1` for `n : ℕ`, the height simplifies to
`mulHeight₁ (n : ℚ) = n` and `logHeight₁ (n : ℚ) = Real.log n` for `1 ≤ n`.
-/

namespace Rat

open NumberField Height

/-- The multiplicative height of a positive natural number cast to `ℚ` equals `n`. -/
theorem mulHeight₁_natCast (n : ℕ) [NeZero n] :
    mulHeight₁ (n : ℚ) = n := by
  have hfin (v : FinitePlace ℚ) : max (v n) 1 = 1 :=
    max_eq_right (IsNonarchimedean.apply_natCast_le_one_of_isNonarchimedean
      (NonarchimedeanHomClass.map_add_le_max v))
  rw [NumberField.mulHeight₁_eq, finprod_eq_one_of_forall_eq_one hfin, Fintype.prod_unique,
    show (default : InfinitePlace ℚ) = infinitePlace from Subsingleton.elim _ _]
  have hn : 1 ≤ n := by grind [NeZero.ne n]
  simp [hn, InfinitePlace.mult, isReal_infinitePlace]

/-- The logarithmic height of a positive natural number cast to `ℚ` equals `log n`. -/
theorem logHeight₁_natCast (n : ℕ) [NeZero n] :
    logHeight₁ (n : ℚ) = Real.log n := by
  simp [logHeight₁_eq_log_mulHeight₁, mulHeight₁_natCast n]

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
