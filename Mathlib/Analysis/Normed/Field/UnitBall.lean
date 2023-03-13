/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth

! This file was ported from Lean 3 source module analysis.normed.field.unit_ball
! leanprover-community/mathlib commit 3339976e2bcae9f1c81e620836d1eb736e3c4700
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Field.Basic
import Mathbin.Analysis.Normed.Group.BallSphere

/-!
# Algebraic structures on unit balls and spheres

In this file we define algebraic structures (`semigroup`, `comm_semigroup`, `monoid`, `comm_monoid`,
`group`, `comm_group`) on `metric.ball (0 : 𝕜) 1`, `metric.closed_ball (0 : 𝕜) 1`, and
`metric.sphere (0 : 𝕜) 1`. In each case we use the weakest possible typeclass assumption on `𝕜`,
from `non_unital_semi_normed_ring` to `normed_field`.
-/


open Set Metric

variable {𝕜 : Type _}

/-- Unit ball in a non unital semi normed ring as a bundled `subsemigroup`. -/
def Subsemigroup.unitBall (𝕜 : Type _) [NonUnitalSeminormedRing 𝕜] : Subsemigroup 𝕜
    where
  carrier := ball (0 : 𝕜) 1
  mul_mem' x y hx hy := by
    rw [mem_ball_zero_iff] at *
    exact (norm_mul_le x y).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy.le)
#align subsemigroup.unit_ball Subsemigroup.unitBall

instance [NonUnitalSeminormedRing 𝕜] : Semigroup (ball (0 : 𝕜) 1) :=
  MulMemClass.toSemigroup (Subsemigroup.unitBall 𝕜)

instance [NonUnitalSeminormedRing 𝕜] : ContinuousMul (ball (0 : 𝕜) 1) :=
  (Subsemigroup.unitBall 𝕜).ContinuousMul

instance [SeminormedCommRing 𝕜] : CommSemigroup (ball (0 : 𝕜) 1) :=
  MulMemClass.toCommSemigroup (Subsemigroup.unitBall 𝕜)

instance [NonUnitalSeminormedRing 𝕜] : HasDistribNeg (ball (0 : 𝕜) 1) :=
  Subtype.coe_injective.HasDistribNeg (coe : ball (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

@[simp, norm_cast]
theorem coe_mul_unit_ball [NonUnitalSeminormedRing 𝕜] (x y : ball (0 : 𝕜) 1) :
    ↑(x * y) = (x * y : 𝕜) :=
  rfl
#align coe_mul_unit_ball coe_mul_unit_ball

/-- Closed unit ball in a non unital semi normed ring as a bundled `subsemigroup`. -/
def Subsemigroup.unitClosedBall (𝕜 : Type _) [NonUnitalSeminormedRing 𝕜] : Subsemigroup 𝕜
    where
  carrier := closedBall 0 1
  mul_mem' x y hx hy := by
    rw [mem_closedBall_zero_iff] at *
    exact (norm_mul_le x y).trans (mul_le_one hx (norm_nonneg _) hy)
#align subsemigroup.unit_closed_ball Subsemigroup.unitClosedBall

instance [NonUnitalSeminormedRing 𝕜] : Semigroup (closedBall (0 : 𝕜) 1) :=
  MulMemClass.toSemigroup (Subsemigroup.unitClosedBall 𝕜)

instance [NonUnitalSeminormedRing 𝕜] : HasDistribNeg (closedBall (0 : 𝕜) 1) :=
  Subtype.coe_injective.HasDistribNeg (coe : closedBall (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

instance [NonUnitalSeminormedRing 𝕜] : ContinuousMul (closedBall (0 : 𝕜) 1) :=
  (Subsemigroup.unitClosedBall 𝕜).ContinuousMul

@[simp, norm_cast]
theorem coe_mul_unit_closedBall [NonUnitalSeminormedRing 𝕜] (x y : closedBall (0 : 𝕜) 1) :
    ↑(x * y) = (x * y : 𝕜) :=
  rfl
#align coe_mul_unit_closed_ball coe_mul_unit_closedBall

/-- Closed unit ball in a semi normed ring as a bundled `submonoid`. -/
def Submonoid.unitClosedBall (𝕜 : Type _) [SeminormedRing 𝕜] [NormOneClass 𝕜] : Submonoid 𝕜 :=
  { Subsemigroup.unitClosedBall 𝕜 with
    carrier := closedBall 0 1
    one_mem' := mem_closedBall_zero_iff.2 norm_one.le }
#align submonoid.unit_closed_ball Submonoid.unitClosedBall

instance [SeminormedRing 𝕜] [NormOneClass 𝕜] : Monoid (closedBall (0 : 𝕜) 1) :=
  SubmonoidClass.toMonoid (Submonoid.unitClosedBall 𝕜)

instance [SeminormedCommRing 𝕜] [NormOneClass 𝕜] : CommMonoid (closedBall (0 : 𝕜) 1) :=
  SubmonoidClass.toCommMonoid (Submonoid.unitClosedBall 𝕜)

@[simp, norm_cast]
theorem coe_one_unit_closedBall [SeminormedRing 𝕜] [NormOneClass 𝕜] :
    ((1 : closedBall (0 : 𝕜) 1) : 𝕜) = 1 :=
  rfl
#align coe_one_unit_closed_ball coe_one_unit_closedBall

@[simp, norm_cast]
theorem coe_pow_unit_closedBall [SeminormedRing 𝕜] [NormOneClass 𝕜] (x : closedBall (0 : 𝕜) 1)
    (n : ℕ) : ↑(x ^ n) = (x ^ n : 𝕜) :=
  rfl
#align coe_pow_unit_closed_ball coe_pow_unit_closedBall

/-- Unit sphere in a normed division ring as a bundled `submonoid`. -/
def Submonoid.unitSphere (𝕜 : Type _) [NormedDivisionRing 𝕜] : Submonoid 𝕜
    where
  carrier := sphere (0 : 𝕜) 1
  mul_mem' x y hx hy := by
    rw [mem_sphere_zero_iff_norm] at *
    simp [*]
  one_mem' := mem_sphere_zero_iff_norm.2 norm_one
#align submonoid.unit_sphere Submonoid.unitSphere

instance [NormedDivisionRing 𝕜] : Inv (sphere (0 : 𝕜) 1) :=
  ⟨fun x =>
    ⟨x⁻¹,
      mem_sphere_zero_iff_norm.2 <| by
        rw [norm_inv, mem_sphere_zero_iff_norm.1 x.coe_prop, inv_one]⟩⟩

@[simp, norm_cast]
theorem coe_inv_unit_sphere [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) : ↑x⁻¹ = (x⁻¹ : 𝕜) :=
  rfl
#align coe_inv_unit_sphere coe_inv_unit_sphere

instance [NormedDivisionRing 𝕜] : Div (sphere (0 : 𝕜) 1) :=
  ⟨fun x y =>
    ⟨x / y,
      mem_sphere_zero_iff_norm.2 <| by
        rw [norm_div, mem_sphere_zero_iff_norm.1 x.coe_prop, mem_sphere_zero_iff_norm.1 y.coe_prop,
          div_one]⟩⟩

@[simp, norm_cast]
theorem coe_div_unit_sphere [NormedDivisionRing 𝕜] (x y : sphere (0 : 𝕜) 1) :
    ↑(x / y) = (x / y : 𝕜) :=
  rfl
#align coe_div_unit_sphere coe_div_unit_sphere

instance [NormedDivisionRing 𝕜] : Pow (sphere (0 : 𝕜) 1) ℤ :=
  ⟨fun x n =>
    ⟨x ^ n, by
      rw [mem_sphere_zero_iff_norm, norm_zpow, mem_sphere_zero_iff_norm.1 x.coe_prop, one_zpow]⟩⟩

@[simp, norm_cast]
theorem coe_zpow_unit_sphere [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) (n : ℤ) :
    ↑(x ^ n) = (x ^ n : 𝕜) :=
  rfl
#align coe_zpow_unit_sphere coe_zpow_unit_sphere

instance [NormedDivisionRing 𝕜] : Monoid (sphere (0 : 𝕜) 1) :=
  SubmonoidClass.toMonoid (Submonoid.unitSphere 𝕜)

@[simp, norm_cast]
theorem coe_one_unit_sphere [NormedDivisionRing 𝕜] : ((1 : sphere (0 : 𝕜) 1) : 𝕜) = 1 :=
  rfl
#align coe_one_unit_sphere coe_one_unit_sphere

@[simp, norm_cast]
theorem coe_mul_unit_sphere [NormedDivisionRing 𝕜] (x y : sphere (0 : 𝕜) 1) :
    ↑(x * y) = (x * y : 𝕜) :=
  rfl
#align coe_mul_unit_sphere coe_mul_unit_sphere

@[simp, norm_cast]
theorem coe_pow_unit_sphere [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) (n : ℕ) :
    ↑(x ^ n) = (x ^ n : 𝕜) :=
  rfl
#align coe_pow_unit_sphere coe_pow_unit_sphere

/-- Monoid homomorphism from the unit sphere to the group of units. -/
def unitSphereToUnits (𝕜 : Type _) [NormedDivisionRing 𝕜] : sphere (0 : 𝕜) 1 →* Units 𝕜 :=
  Units.liftRight (Submonoid.unitSphere 𝕜).Subtype
    (fun x => Units.mk0 x <| ne_zero_of_mem_unit_sphere _) fun x => rfl
#align unit_sphere_to_units unitSphereToUnits

@[simp]
theorem unitSphereToUnits_apply_coe [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) :
    (unitSphereToUnits 𝕜 x : 𝕜) = x :=
  rfl
#align unit_sphere_to_units_apply_coe unitSphereToUnits_apply_coe

theorem unitSphereToUnits_injective [NormedDivisionRing 𝕜] :
    Function.Injective (unitSphereToUnits 𝕜) := fun x y h =>
  Subtype.eq <| by convert congr_arg Units.val h
#align unit_sphere_to_units_injective unitSphereToUnits_injective

instance [NormedDivisionRing 𝕜] : Group (sphere (0 : 𝕜) 1) :=
  unitSphereToUnits_injective.Group (unitSphereToUnits 𝕜) (Units.ext rfl) (fun x y => Units.ext rfl)
    (fun x => Units.ext rfl) (fun x y => Units.ext <| div_eq_mul_inv _ _)
    (fun x n => Units.ext (Units.val_pow_eq_pow_val (unitSphereToUnits 𝕜 x) n).symm) fun x n =>
    Units.ext (Units.val_zpow_eq_zpow_val (unitSphereToUnits 𝕜 x) n).symm

instance [NormedDivisionRing 𝕜] : HasDistribNeg (sphere (0 : 𝕜) 1) :=
  Subtype.coe_injective.HasDistribNeg (coe : sphere (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

instance [NormedDivisionRing 𝕜] : TopologicalGroup (sphere (0 : 𝕜) 1)
    where
  to_continuousMul := (Submonoid.unitSphere 𝕜).ContinuousMul
  continuous_inv := (continuous_subtype_val.inv₀ ne_zero_of_mem_unit_sphere).subtype_mk _

instance [NormedField 𝕜] : CommGroup (sphere (0 : 𝕜) 1) :=
  { Metric.sphere.group, SubmonoidClass.toCommMonoid (Submonoid.unitSphere 𝕜) with }

