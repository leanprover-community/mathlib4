/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.BallSphere

#align_import analysis.normed.field.unit_ball from "leanprover-community/mathlib"@"3339976e2bcae9f1c81e620836d1eb736e3c4700"

/-!
# Algebraic structures on unit balls and spheres

In this file we define algebraic structures (`Semigroup`, `CommSemigroup`, `Monoid`, `CommMonoid`,
`Group`, `CommGroup`) on `Metric.ball (0 : 𝕜) 1`, `Metric.closedBall (0 : 𝕜) 1`, and
`Metric.sphere (0 : 𝕜) 1`. In each case we use the weakest possible typeclass assumption on `𝕜`,
from `NonUnitalSeminormedRing` to `NormedField`.
-/


open Set Metric

variable {𝕜 : Type*}

/-- Unit ball in a non unital semi normed ring as a bundled `Subsemigroup`. -/
def Subsemigroup.unitBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] : Subsemigroup 𝕜
    where
  carrier := ball (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_ball_zero_iff] at *
    -- ⊢ ‖a✝ * b✝‖ < 1
    exact (norm_mul_le _ _).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy.le)
    -- 🎉 no goals
#align subsemigroup.unit_ball Subsemigroup.unitBall

instance Metric.unitBall.semigroup [NonUnitalSeminormedRing 𝕜] : Semigroup (ball (0 : 𝕜) 1) :=
  MulMemClass.toSemigroup (Subsemigroup.unitBall 𝕜)

instance Metric.unitBall.continuousMul [NonUnitalSeminormedRing 𝕜] :
    ContinuousMul (ball (0 : 𝕜) 1) :=
  (Subsemigroup.unitBall 𝕜).continuousMul

instance Metric.unitBall.commSemigroup [SeminormedCommRing 𝕜] : CommSemigroup (ball (0 : 𝕜) 1) :=
  MulMemClass.toCommSemigroup (Subsemigroup.unitBall 𝕜)

instance Metric.unitBall.hasDistribNeg [NonUnitalSeminormedRing 𝕜] :
    HasDistribNeg (ball (0 : 𝕜) 1) :=
  Subtype.coe_injective.hasDistribNeg ((↑) : ball (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

@[simp, norm_cast]
theorem coe_mul_unitBall [NonUnitalSeminormedRing 𝕜] (x y : ball (0 : 𝕜) 1) :
    ↑(x * y) = (x * y : 𝕜) :=
  rfl
#align coe_mul_unit_ball coe_mul_unitBall

/-- Closed unit ball in a non unital semi normed ring as a bundled `Subsemigroup`. -/
def Subsemigroup.unitClosedBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] : Subsemigroup 𝕜
    where
  carrier := closedBall 0 1
  mul_mem' hx hy := by
    rw [mem_closedBall_zero_iff] at *
    -- ⊢ ‖a✝ * b✝‖ ≤ 1
    exact (norm_mul_le _ _).trans (mul_le_one hx (norm_nonneg _) hy)
    -- 🎉 no goals
#align subsemigroup.unit_closed_ball Subsemigroup.unitClosedBall

instance Metric.unitClosedBall.semigroup [NonUnitalSeminormedRing 𝕜] :
    Semigroup (closedBall (0 : 𝕜) 1) :=
  MulMemClass.toSemigroup (Subsemigroup.unitClosedBall 𝕜)

instance Metric.unitClosedBall.hasDistribNeg [NonUnitalSeminormedRing 𝕜] :
    HasDistribNeg (closedBall (0 : 𝕜) 1) :=
  Subtype.coe_injective.hasDistribNeg ((↑) : closedBall (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

instance Metric.unitClosedBall.continuousMul [NonUnitalSeminormedRing 𝕜] :
    ContinuousMul (closedBall (0 : 𝕜) 1) :=
  (Subsemigroup.unitClosedBall 𝕜).continuousMul

@[simp, norm_cast]
theorem coe_mul_unitClosedBall [NonUnitalSeminormedRing 𝕜] (x y : closedBall (0 : 𝕜) 1) :
    ↑(x * y) = (x * y : 𝕜) :=
  rfl
#align coe_mul_unit_closed_ball coe_mul_unitClosedBall

/-- Closed unit ball in a semi normed ring as a bundled `Submonoid`. -/
def Submonoid.unitClosedBall (𝕜 : Type*) [SeminormedRing 𝕜] [NormOneClass 𝕜] : Submonoid 𝕜 :=
  { Subsemigroup.unitClosedBall 𝕜 with
    carrier := closedBall 0 1
    one_mem' := mem_closedBall_zero_iff.2 norm_one.le }
#align submonoid.unit_closed_ball Submonoid.unitClosedBall

instance Metric.unitClosedBall.monoid [SeminormedRing 𝕜] [NormOneClass 𝕜] :
    Monoid (closedBall (0 : 𝕜) 1) :=
  SubmonoidClass.toMonoid (Submonoid.unitClosedBall 𝕜)

instance Metric.unitClosedBall.commMonoid [SeminormedCommRing 𝕜] [NormOneClass 𝕜] :
    CommMonoid (closedBall (0 : 𝕜) 1) :=
  SubmonoidClass.toCommMonoid (Submonoid.unitClosedBall 𝕜)

@[simp, norm_cast]
theorem coe_one_unitClosedBall [SeminormedRing 𝕜] [NormOneClass 𝕜] :
    ((1 : closedBall (0 : 𝕜) 1) : 𝕜) = 1 :=
  rfl
#align coe_one_unit_closed_ball coe_one_unitClosedBall

@[simp, norm_cast]
theorem coe_pow_unitClosedBall [SeminormedRing 𝕜] [NormOneClass 𝕜] (x : closedBall (0 : 𝕜) 1)
    (n : ℕ) : ↑(x ^ n) = (x : 𝕜) ^ n :=
  rfl
#align coe_pow_unit_closed_ball coe_pow_unitClosedBall

/-- Unit sphere in a normed division ring as a bundled `Submonoid`. -/
def Submonoid.unitSphere (𝕜 : Type*) [NormedDivisionRing 𝕜] : Submonoid 𝕜
    where
  carrier := sphere (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_sphere_zero_iff_norm] at *
    -- ⊢ ‖a✝ * b✝‖ = 1
    simp [*]
    -- 🎉 no goals
  one_mem' := mem_sphere_zero_iff_norm.2 norm_one
#align submonoid.unit_sphere Submonoid.unitSphere

instance Metric.unitSphere.inv [NormedDivisionRing 𝕜] : Inv (sphere (0 : 𝕜) 1) :=
  ⟨fun x =>
    ⟨x⁻¹,
      mem_sphere_zero_iff_norm.2 <| by
        rw [norm_inv, mem_sphere_zero_iff_norm.1 x.coe_prop, inv_one]⟩⟩
        -- 🎉 no goals

@[simp, norm_cast]
theorem coe_inv_unitSphere [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) : ↑x⁻¹ = (x⁻¹ : 𝕜) :=
  rfl
#align coe_inv_unit_sphere coe_inv_unitSphere

instance Metric.unitSphere.div [NormedDivisionRing 𝕜] : Div (sphere (0 : 𝕜) 1) :=
  ⟨fun x y =>
    ⟨x / y,
      mem_sphere_zero_iff_norm.2 <| by
        rw [norm_div, mem_sphere_zero_iff_norm.1 x.coe_prop, mem_sphere_zero_iff_norm.1 y.coe_prop,
          div_one]⟩⟩

@[simp, norm_cast]
theorem coe_div_unitSphere [NormedDivisionRing 𝕜] (x y : sphere (0 : 𝕜) 1) :
    ↑(x / y) = (x / y : 𝕜) :=
  rfl
#align coe_div_unit_sphere coe_div_unitSphere

instance Metric.unitSphere.pow [NormedDivisionRing 𝕜] : Pow (sphere (0 : 𝕜) 1) ℤ :=
  ⟨fun x n =>
    ⟨(x : 𝕜) ^ n, by
      rw [mem_sphere_zero_iff_norm, norm_zpow, mem_sphere_zero_iff_norm.1 x.coe_prop, one_zpow]⟩⟩
      -- 🎉 no goals

@[simp, norm_cast]
theorem coe_zpow_unitSphere [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) (n : ℤ) :
    ↑(x ^ n) = (x : 𝕜) ^ n :=
  rfl
#align coe_zpow_unit_sphere coe_zpow_unitSphere

instance Metric.unitSphere.monoid [NormedDivisionRing 𝕜] : Monoid (sphere (0 : 𝕜) 1) :=
  SubmonoidClass.toMonoid (Submonoid.unitSphere 𝕜)

@[simp, norm_cast]
theorem coe_one_unitSphere [NormedDivisionRing 𝕜] : ((1 : sphere (0 : 𝕜) 1) : 𝕜) = 1 :=
  rfl
#align coe_one_unit_sphere coe_one_unitSphere

@[simp, norm_cast]
theorem coe_mul_unitSphere [NormedDivisionRing 𝕜] (x y : sphere (0 : 𝕜) 1) :
    ↑(x * y) = (x * y : 𝕜) :=
  rfl
#align coe_mul_unit_sphere coe_mul_unitSphere

@[simp, norm_cast]
theorem coe_pow_unitSphere [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) (n : ℕ) :
    ↑(x ^ n) = (x : 𝕜) ^ n :=
  rfl
#align coe_pow_unit_sphere coe_pow_unitSphere

/-- Monoid homomorphism from the unit sphere to the group of units. -/
def unitSphereToUnits (𝕜 : Type*) [NormedDivisionRing 𝕜] : sphere (0 : 𝕜) 1 →* Units 𝕜 :=
  Units.liftRight (Submonoid.unitSphere 𝕜).subtype
    (fun x => Units.mk0 x <| ne_zero_of_mem_unit_sphere _) fun _x => rfl
#align unit_sphere_to_units unitSphereToUnits

@[simp]
theorem unitSphereToUnits_apply_coe [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) :
    (unitSphereToUnits 𝕜 x : 𝕜) = x :=
  rfl
#align unit_sphere_to_units_apply_coe unitSphereToUnits_apply_coe

theorem unitSphereToUnits_injective [NormedDivisionRing 𝕜] :
    Function.Injective (unitSphereToUnits 𝕜) := fun x y h =>
  Subtype.eq <| by convert congr_arg Units.val h
                   -- 🎉 no goals
#align unit_sphere_to_units_injective unitSphereToUnits_injective

instance Metric.sphere.group [NormedDivisionRing 𝕜] : Group (sphere (0 : 𝕜) 1) :=
  unitSphereToUnits_injective.group (unitSphereToUnits 𝕜) (Units.ext rfl)
    (fun _x _y => Units.ext rfl)
    (fun _x => Units.ext rfl) (fun _x _y => Units.ext <| div_eq_mul_inv _ _)
    (fun x n => Units.ext (Units.val_pow_eq_pow_val (unitSphereToUnits 𝕜 x) n).symm) fun x n =>
    Units.ext (Units.val_zpow_eq_zpow_val (unitSphereToUnits 𝕜 x) n).symm

instance Metric.sphere.hasDistribNeg [NormedDivisionRing 𝕜] : HasDistribNeg (sphere (0 : 𝕜) 1) :=
  Subtype.coe_injective.hasDistribNeg ((↑) : sphere (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

instance Metric.sphere.topologicalGroup [NormedDivisionRing 𝕜] : TopologicalGroup (sphere (0 : 𝕜) 1)
    where
  toContinuousMul := (Submonoid.unitSphere 𝕜).continuousMul
  continuous_inv := (continuous_subtype_val.inv₀ ne_zero_of_mem_unit_sphere).subtype_mk _

instance Metric.sphere.commGroup [NormedField 𝕜] : CommGroup (sphere (0 : 𝕜) 1) :=
  { Metric.sphere.group,
    Subtype.coe_injective.commMonoid (↑) rfl (fun _ _ => rfl) (fun _ _ => rfl) with }
  -- porting note: Lean couldn't see past the type synonym into the subtype.
