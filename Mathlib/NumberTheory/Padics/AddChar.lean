/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Monoid.AddChar

/-!
# Additive characters of `ℤ_[p]`

We show that for any complete, ultrametric normed `ℤ_[p]`-algebra `R`, there is a bijection between
continuous additive characters `ℤ_[p] → R` and topologically nilpotent elements of `R`, given by
sending `κ` to the element `κ 1 - 1`. This is used to define the Mahler transform for `p`-adic
measures.

Note that if the norm on `R` is not strictly multiplicative, then the condition that `κ 1 - 1` be
topologically nilpotent is strictly weaker than assuming `‖κ 1 - 1‖ < 1`, although they are
equivalent if `NormMulClass R` holds.

## Main definitions and theorems:

* `addChar_of_value_at_one`: given a topologically nilpotent `r : R`, construct a continuous
  additive character of `ℤ_[p]` mapping `1` to `1 + r`.
* `continuousAddCharEquiv`: for any complete, ultrametric normed `ℤ_[p]`-algebra `R`, the map
  `addChar_of_value_at_one` defines a bijection between continuous additive characters `ℤ_[p] → R`
  and topologically nilpotent elements of `R`.
* `continuousAddCharEquiv_of_norm_mul`: if the norm on `R` is strictly multiplicative (not just
  sub-multiplicative), then `addChar_of_value_at_one` is a bijection between continuous additive
  characters `ℤ_[p] → R` and elements of `R` with `‖r‖ < 1`.

## TODO:

* Show that the above equivalences are homeomorphisms, for appropriate choices of the topology.
-/

@[expose] public section

open scoped fwdDiff
open Filter Topology

variable {p : ℕ} [Fact p.Prime]

variable {R : Type*} [NormedRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
  [IsUltrametricDist R]

lemma AddChar.tendsto_eval_one_sub_pow {κ : AddChar ℤ_[p] R} (hκ : Continuous κ) :
    Tendsto (fun n ↦ (κ 1 - 1) ^ n) atTop (𝓝 0) := by
  refine (PadicInt.fwdDiff_tendsto_zero ⟨κ, hκ⟩).congr fun n ↦ ?_
  simpa only [AddChar.map_zero_eq_one, mul_one] using fwdDiff_addChar_eq κ 0 1 n

namespace PadicInt
variable [CompleteSpace R]

/-- The unique continuous additive character of `ℤ_[p]` mapping `1` to `1 + r`. -/
noncomputable def addChar_of_value_at_one (r : R) (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    AddChar ℤ_[p] R where
  toFun := mahlerSeries (r ^ ·)
  map_zero_eq_one' := by
    rw [← Nat.cast_zero, mahlerSeries_apply_nat hr le_rfl, zero_add, Finset.sum_range_one,
      Nat.choose_self, pow_zero, one_smul]
  map_add_eq_mul' a b := by
    let F : C(ℤ_[p], R) := mahlerSeries (r ^ ·)
    change F (a + b) = F a * F b
    -- It is fiddly to show directly that `F (a + b) = F a * F b` for general `a, b`,
    -- so we prove it for `a, b ∈ ℕ` directly, and then deduce it for all `a, b` by continuity.
    have hF (n : ℕ) : F n = (r + 1) ^ n := by
      rw [mahlerSeries_apply_nat hr le_rfl, (Commute.one_right _).add_pow]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [one_pow, mul_one, nsmul_eq_mul, Nat.cast_comm]
    refine congr_fun ((denseRange_natCast.prodMap denseRange_natCast).equalizer
      ((map_continuous F).comp continuous_add)
      (continuous_mul.comp (map_continuous <| F.prodMap F)) (funext fun ⟨m, n⟩ ↦ ?_)) (a, b)
    simp [← Nat.cast_add, hF, ContinuousMap.prodMap_apply, pow_add]

@[fun_prop]
lemma continuous_addChar_of_value_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    Continuous (addChar_of_value_at_one r hr : ℤ_[p] → R) :=
  map_continuous (mahlerSeries (r ^ ·))

lemma coe_addChar_of_value_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    (addChar_of_value_at_one r hr : ℤ_[p] → R) = mahlerSeries (r ^ ·) :=
  rfl

@[simp]
lemma addChar_of_value_at_one_def {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    addChar_of_value_at_one r hr (1 : ℤ_[p]) = 1 + r := by
  change mahlerSeries (r ^ ·) ↑(1 : ℕ) = _
  rw [mahlerSeries_apply_nat hr le_rfl, Finset.sum_range_succ, Finset.sum_range_one,
    Nat.choose_zero_right, Nat.choose_self, one_smul, one_smul, pow_zero, pow_one]

lemma eq_addChar_of_value_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0))
    {κ : AddChar ℤ_[p] R} (hκ : Continuous κ) (hκ' : κ 1 = 1 + r) :
    κ = addChar_of_value_at_one r hr :=
  denseRange_natCast.addChar_eq_of_eval_one_eq hκ (by fun_prop) (by simp [hκ'])

variable (p R) in
/-- Equivalence between continuous additive characters `ℤ_[p] → R`, and `r ∈ R` with `r ^ n → 0`. -/
noncomputable def continuousAddCharEquiv :
    {κ : AddChar ℤ_[p] R // Continuous κ} ≃ {r : R // Tendsto (r ^ ·) atTop (𝓝 0)} where
  toFun := fun ⟨κ, hκ⟩ ↦ ⟨κ 1 - 1, κ.tendsto_eval_one_sub_pow hκ⟩
  invFun := fun ⟨r, hr⟩ ↦ ⟨_, continuous_addChar_of_value_at_one hr⟩
  left_inv := fun ⟨κ, hκ⟩ ↦ by simpa using (eq_addChar_of_value_at_one _ hκ (by abel)).symm
  right_inv := fun ⟨r, hr⟩ ↦ by simp [addChar_of_value_at_one_def hr]

@[simp] lemma continuousAddCharEquiv_apply {κ : AddChar ℤ_[p] R} (hκ : Continuous κ) :
    continuousAddCharEquiv p R ⟨κ, hκ⟩ = κ 1 - 1 :=
  rfl

@[simp] lemma continuousAddCharEquiv_symm_apply {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    (continuousAddCharEquiv p R).symm ⟨r, hr⟩ =
    (addChar_of_value_at_one r hr : AddChar ℤ_[p] R) :=
  rfl

section NormMulClass
variable [NormMulClass R]

variable (p R) in
/-- Equivalence between continuous additive characters `ℤ_[p] → R`, and `r ∈ R` with `‖r‖ < 1`,
for rings with strictly multiplicative norm. -/
noncomputable def continuousAddCharEquiv_of_norm_mul :
    {κ : AddChar ℤ_[p] R // Continuous κ} ≃ {r : R // ‖r‖ < 1} :=
  (continuousAddCharEquiv p R).trans <|
    .subtypeEquivProp (by simp only [tendsto_pow_atTop_nhds_zero_iff_norm_lt_one])

@[simp] lemma continuousAddCharEquiv_of_norm_mul_apply {κ : AddChar ℤ_[p] R} (hκ : Continuous κ) :
    continuousAddCharEquiv_of_norm_mul p R ⟨κ, hκ⟩ = κ 1 - 1 :=
  rfl

@[simp] lemma continuousAddCharEquiv_of_norm_mul_symm_apply {r : R} (hr : ‖r‖ < 1) :
    (continuousAddCharEquiv_of_norm_mul p R).symm ⟨r, hr⟩ = (addChar_of_value_at_one r
    (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hr) : AddChar ℤ_[p] R) :=
  rfl

end NormMulClass

end PadicInt
