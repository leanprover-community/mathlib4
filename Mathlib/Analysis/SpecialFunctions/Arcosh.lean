/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Inverse of the cosh function

In this file we define an inverse of cosh as a function from [0, ∞) to [1, ∞).

## Main definitions

- `Real.arcosh`: An inverse function of `Real.cosh` as a function from [0, ∞) to [1, ∞).

- `Real.cosh'`, `Real.arcosh'`: Versions of `Real.cosh` and `Real.arcosh` restricted
  to the domains [0, ∞) and [1, ∞), respectively.

- `Real.cosh'Equiv`, `Real.cosh'OrderIso`, `Real.cosh'Homeomorph`: `Real.cosh'` as an `Equiv`,
  `OrderIso`, and `Homeomorph`, respectively.

## Main Results

- `Real.cosh_arcosh`, `Real.arcosh_cosh`: cosh and arcosh are inverse in the appropriate domains.

## Tags

arcosh, arccosh, argcosh, acosh
-/

@[expose] public section


noncomputable section

open Function Filter Set NNReal

open scoped Topology

namespace Real

variable {x y : ℝ}

/-- `arcosh` is defined using a logarithm, `arcosh x = log (x + √(x ^ 2 - 1))`. -/
@[pp_nodot]
def arcosh (x : ℝ) :=
  log (x + √(x ^ 2 - 1))

theorem exp_arcosh (x : ℝ) (hx : 1 ≤ x) : exp (arcosh x) = x + √(x ^ 2 - 1) := by
  apply exp_log
  positivity

@[simp]
theorem arcosh_zero : arcosh 1 = 0 := by simp [arcosh]

lemma add_sqrt_self_sq_sub_one_inv (x : ℝ) (hx : 1 ≤ x) :
    (x + √(x ^ 2 - 1))⁻¹ = x - √(x ^ 2 - 1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_two_sub_pow_two, sq_sqrt (sub_nonneg_of_le (one_le_pow₀ hx)), sub_sub_cancel]

/-- `arcosh` is the right inverse of `cosh` over [1, ∞). -/
@[simp]
theorem cosh_arcosh {x : ℝ} (hx : 1 ≤ x) : cosh (arcosh x) = x := by
  rw [arcosh, cosh_eq, exp_neg, exp_log (by positivity), x_add_sqrt_x_sq_sub_one_inv x hx]
  ring

@[simp]
theorem arcosh_eq_zero_iff {x : ℝ} (hx : 1 ≤ x) : arcosh x = 0 ↔ x = 1 := by
  rw [← exp_injective.eq_iff, exp_arcosh x hx, exp_zero]
  grind

@[simp]
theorem sinh_arcosh {x : ℝ} (hx : 1 ≤ x) : sinh (arcosh x) = √(x ^ 2 - 1) := by
  rw [arcosh, sinh_eq, exp_neg, exp_log (by positivity), x_add_sqrt_x_sq_sub_one_inv x hx]
  ring

/-- `arcosh` is the left inverse of `cosh` over [0, ∞). -/
@[simp]
theorem arcosh_cosh {x : ℝ} (hx : 0 ≤ x) : arcosh (cosh x) = x := by
  rw [arcosh, ← exp_eq_exp, exp_log (by positivity), ← eq_sub_iff_add_eq', exp_sub_cosh,
    ← sq_eq_sq₀ (sqrt_nonneg _) (sinh_nonneg_iff.mpr hx), ← sinh_sq, sq_sqrt (pow_two_nonneg _)]

@[simp]
theorem arcosh_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ arcosh x := by
  apply log_nonneg
  calc
    1 ≤ x := hx
    _ ≤ x + √(x ^ 2 - 1) := by
      apply (le_add_iff_nonneg_right _).mpr
      apply sqrt_nonneg

@[simp]
theorem arcosh_pos {x : ℝ} (hx : 1 < x) : 0 < arcosh x := by
  have hx' := le_of_lt hx
  apply Std.lt_of_le_of_ne (arcosh_nonneg hx')
  contrapose! hx
  exact ge_of_eq ((arcosh_eq_zero_iff hx').mp hx.symm).symm

@[simp]
theorem arcosh_le_arcosh {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : arcosh x ≤ arcosh y ↔ x ≤ y := by
  rw (occs := .pos [2]) [← cosh_arcosh hx, ← cosh_arcosh hy]
  rw (occs := .pos [1]) [← abs_of_nonneg (arcosh_nonneg hx), ← abs_of_nonneg (arcosh_nonneg hy)]
  exact cosh_le_cosh.symm

@[simp]
theorem arcosh_lt_arcosh {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : arcosh x < arcosh y ↔ x < y := by
  rw (occs := .pos [2]) [← cosh_arcosh hx, ← cosh_arcosh hy]
  rw (occs := .pos [1]) [← abs_of_nonneg (arcosh_nonneg hx), ← abs_of_nonneg (arcosh_nonneg hy)]
  exact cosh_lt_cosh.symm

end Real

/-- Real numbers which are at least 1. -/
def AOReal := { r : ℝ // 1 ≤ r } deriving
  Preorder, PartialOrder, SemilatticeInf, SemilatticeSup, DistribLattice,
  TopologicalSpace, UniformSpace, PseudoMetricSpace,
  Nontrivial, Inhabited

namespace AOReal

@[inherit_doc] scoped notation "ℝ≥1" => AOReal

instance : OrderTopology ℝ≥1 :=
  orderTopology_of_ordConnected (t := Ici 1)

/-- Coercion `ℝ≥1 → ℝ`. -/
@[coe] def toReal : ℝ≥1 → ℝ := Subtype.val

instance : Coe ℝ≥1 ℝ := ⟨toReal⟩

-- Simp lemma to put back `n.val` into the normal form given by the coercion.
@[simp]
theorem val_eq_coe (n : ℝ≥1) : n.val = n :=
  rfl

@[simp, norm_cast] theorem coe_mk (a : ℝ) (ha) : toReal ⟨a, ha⟩ = a := rfl

end AOReal

open AOReal

namespace Real

/-- `cosh` as a function from [0, ∞) to [1, ∞) -/
@[pp_nodot]
def cosh' (x : ℝ≥0) : ℝ≥1 :=
  {
    val := cosh x
    property := one_le_cosh _
  }

/-- `arcosh` as a function from [1, ∞) to [0, ∞). -/
@[pp_nodot]
def arcosh' (x : ℝ≥1) : ℝ≥0 :=
  {
    val := arcosh x
    property := arcosh_nonneg x.property
  }

@[simp]
theorem cosh'_arcosh' (x : ℝ≥1) : cosh' (arcosh' x) = x := by
  rw [cosh', arcosh']
  congr
  rw [NNReal.coe_mk, cosh_arcosh, AOReal.val_eq_coe]
  exact x.property

@[simp]
theorem arcosh'_cosh' (x : ℝ≥0) : arcosh' (cosh' x) = x := by
  rw [cosh', arcosh']
  congr
  rw [AOReal.coe_mk, arcosh_cosh, NNReal.val_eq_coe]
  exact x.property

/-- `cosh'` is injective. -/
theorem cosh'_injective : Injective cosh' :=
  RightInverse.injective arcosh'_cosh'

/-- `cosh'` is surjective. -/
theorem cosh'_surjective : Surjective cosh' :=
  LeftInverse.surjective cosh'_arcosh'

/-- `cosh'` is bijective, both injective and surjective. -/
theorem cosh'_bijective : Bijective cosh' :=
  ⟨cosh'_injective, cosh'_surjective⟩

/-- `Real.cosh'` as an `Equiv`. -/
@[simps]
def cosh'Equiv : ℝ≥0 ≃ ℝ≥1 where
  toFun := cosh'
  invFun := arcosh'
  left_inv := arcosh'_cosh'
  right_inv := cosh'_arcosh'

@[simp]
theorem cosh'_le_cosh' (x y : ℝ≥0) : cosh' x ≤ cosh' y ↔ x ≤ y := by
  constructor
  · intro h
    have : cosh x ≤ cosh y := by
      rw [cosh', cosh'] at h
      exact h
    have := cosh_le_cosh.mp this
    rw [NNReal.abs_eq, NNReal.abs_eq, coe_le_coe] at this
    exact this
  · intro h
    rw [cosh', cosh']
    gcongr
    apply cosh_le_cosh.mpr
    rw [NNReal.abs_eq, NNReal.abs_eq, coe_le_coe]
    exact h

/-- `Real.cosh'` as an `OrderIso`. -/
def cosh'OrderIso : ℝ≥0 ≃o ℝ≥1 where
  toEquiv := cosh'Equiv
  map_rel_iff' := @cosh'_le_cosh'

/-- `Real.cosh'` as a `Homeomorph`. -/
def cosh'Homeomorph : ℝ≥0 ≃ₜ ℝ≥1 :=
  cosh'OrderIso.toHomeomorph

theorem arcosh'_bijective : Bijective arcosh' :=
  cosh'Equiv.symm.bijective

theorem arcosh'_injective : Injective arcosh' :=
  cosh'Equiv.symm.injective

theorem arcosh'_surjective : Surjective arcosh' :=
  cosh'Equiv.symm.surjective

theorem arcosh'_strictMono : StrictMono arcosh' :=
  cosh'OrderIso.symm.strictMono

@[simp]
theorem arcosh'_inj (x y) : arcosh' x = arcosh' y ↔ x = y :=
  arcosh'_injective.eq_iff

@[simp]
theorem arcosh'_le_arcosh' (x y) : arcosh' x ≤ arcosh' y ↔ x ≤ y :=
  cosh'OrderIso.symm.le_iff_le

@[gcongr] protected alias ⟨_, GCongr.arcosh'_le_arcosh'⟩ := arcosh'_le_arcosh'

@[simp]
theorem arcosh'_lt_arcosh' (x y) : arcosh' x < arcosh' y ↔ x < y :=
  cosh'OrderIso.symm.lt_iff_lt


end Real
