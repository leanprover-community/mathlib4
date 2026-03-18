/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Analysis.Normed.Order.Antidiag

/-!
# Multivariate restricted power series

`IsRestricted` : We say a multivariate power series over a normed ring `R` is restricted for a
tuple `c` if `‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i → 0` under the cofinite filter.

-/

@[expose] public section

namespace MvPowerSeries

open Filter
open scoped Topology Pointwise

variable {R : Type*} [NormedRing R] {σ : Type*}

/-- A multivariate powe0r series over a normed ring `R` is restricted for a
  tuple `c` if `‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i → 0` under the cofinite filter. -/
def IsRestricted (c : σ → ℝ) (f : MvPowerSeries σ R) :=
  Tendsto (fun (t : σ →₀ ℕ) ↦ ‖coeff t f‖ * t.prod (c · ^ ·)) cofinite (𝓝 0)

@[simp]
lemma isRestricted_abs_iff (c : σ → ℝ) (f : MvPowerSeries σ R) :
    IsRestricted |c| f ↔ IsRestricted c f := by
  simp [IsRestricted, NormedAddGroup.tendsto_nhds_zero, Finsupp.prod]

lemma isRestricted_zero (c : σ → ℝ) : IsRestricted c (0 : MvPowerSeries σ R) := by
  simpa [IsRestricted] using tendsto_const_nhds

lemma isRestricted_monomial (c : σ → ℝ) (n : σ →₀ ℕ) (a : R) :
    IsRestricted c (monomial n a) := by
  classical
  refine tendsto_nhds_of_eventually_eq (Set.Subsingleton.finite ?_)
  aesop (add simp [Set.Subsingleton, coeff_monomial])

lemma isRestricted_one (c : σ → ℝ) : IsRestricted c (1 : MvPowerSeries σ R) :=
  isRestricted_monomial c 0 1

lemma isRestricted_C (c : σ → ℝ) (a : R) : IsRestricted c (C a) := by
  simpa [monomial_zero_eq_C_apply] using isRestricted_monomial c 0 a

lemma isRestricted.add (c : σ → ℝ) {f g : MvPowerSeries σ R} (hf : IsRestricted c f)
    (hg : IsRestricted c g) : IsRestricted c (f + g) := by
  rw [← isRestricted_abs_iff, IsRestricted] at *
  refine tendsto_const_nhds.squeeze (add_zero (0 : ℝ) ▸ hf.add hg) (fun n ↦ ?_) fun n ↦ ?_
  · dsimp [Finsupp.prod]; positivity -- TODO: add positivity extension for Finsupp.prod
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le ..) (by dsimp [Finsupp.prod]; positivity)

lemma isRestricted.neg (c : σ → ℝ) {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    IsRestricted c (-f) := by
  rw [← isRestricted_abs_iff, IsRestricted] at *
  simpa [IsRestricted] using hf

open IsUltrametricDist

lemma isRestricted.mul [IsUltrametricDist R] (c : σ → ℝ) {f g : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f * g) := by
  classical
  rw [← isRestricted_abs_iff, IsRestricted] at *
  exact tendsto_antidiagonal (by simp [Finsupp.prod_add_index', pow_add]) hf hg

/-- Additive subgroup structure on `MvPowerSeries σ R`. -/
instance isAddSubgroup (c : σ → ℝ) : AddSubgroup (MvPowerSeries σ R) where
  carrier := IsRestricted c
  zero_mem' := isRestricted_zero c
  add_mem' := isRestricted.add c
  neg_mem' := isRestricted.neg c

/-- Ring structure on `MvPowerSeries σ R`. -/
instance isSubring [IsUltrametricDist R] (c : σ → ℝ) : Subring (MvPowerSeries σ R) where
  __ := isAddSubgroup c
  one_mem' := isRestricted_one c
  mul_mem' := isRestricted.mul c

variable (R) in
/-- The type of restricted `MvPowerSeries σ R`. -/
def Restricted [IsUltrametricDist R] (c : σ → ℝ) : Type _ := isSubring (R := R) c

/-- Ring structure on `Restricted R c`. -/
noncomputable
instance [IsUltrametricDist R] (c : σ → ℝ) : Ring (Restricted R c) :=
  Subring.toRing (isSubring c)

end MvPowerSeries
