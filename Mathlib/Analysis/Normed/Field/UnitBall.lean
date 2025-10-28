/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.BallSphere

/-!
# Algebraic structures on unit balls and spheres

In this file we define algebraic structures (`Semigroup`, `CommSemigroup`, `Monoid`, `CommMonoid`,
`Group`, `CommGroup`) on `Metric.ball (0 : 𝕜) 1`, `Metric.closedBall (0 : 𝕜) 1`, and
`Metric.sphere (0 : 𝕜) 1`. In each case we use the weakest possible typeclass assumption on `𝕜`,
from `NonUnitalSeminormedRing` to `NormedField`.
-/


open Set Metric

variable {𝕜 : Type*}

/-!
### Algebraic structures on `Metric.ball 0 1`
-/

/-- Unit ball in a non-unital seminormed ring as a bundled `Subsemigroup`. -/
def Subsemigroup.unitBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] : Subsemigroup 𝕜 where
  carrier := ball (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_ball_zero_iff] at *
    exact (norm_mul_le _ _).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy.le)

instance Metric.unitBall.instSemigroup [NonUnitalSeminormedRing 𝕜] : Semigroup (ball (0 : 𝕜) 1) :=
  MulMemClass.toSemigroup (Subsemigroup.unitBall 𝕜)

instance Metric.unitBall.instContinuousMul [NonUnitalSeminormedRing 𝕜] :
    ContinuousMul (ball (0 : 𝕜) 1) :=
  (Subsemigroup.unitBall 𝕜).continuousMul

instance Metric.unitBall.instCommSemigroup [SeminormedCommRing 𝕜] :
    CommSemigroup (ball (0 : 𝕜) 1) :=
  MulMemClass.toCommSemigroup (Subsemigroup.unitBall 𝕜)

instance Metric.unitBall.instHasDistribNeg [NonUnitalSeminormedRing 𝕜] :
    HasDistribNeg (ball (0 : 𝕜) 1) :=
  Subtype.coe_injective.hasDistribNeg ((↑) : ball (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

@[simp, norm_cast]
protected theorem Metric.unitBall.coe_mul [NonUnitalSeminormedRing 𝕜] (x y : ball (0 : 𝕜) 1) :
    ↑(x * y) = (x * y : 𝕜) :=
  rfl

@[deprecated (since := "2025-04-18")]
alias coe_mul_unitBall := Metric.unitBall.coe_mul

instance Metric.unitBall.instZero [Zero 𝕜] [PseudoMetricSpace 𝕜] : Zero (ball (0 : 𝕜) 1) :=
  ⟨⟨0, by simp⟩⟩

@[simp, norm_cast]
protected theorem Metric.unitBall.coe_zero [Zero 𝕜] [PseudoMetricSpace 𝕜] :
    ((0 : ball (0 : 𝕜) 1) : 𝕜) = 0 :=
  rfl

@[simp, norm_cast]
protected theorem Metric.unitBall.coe_eq_zero [Zero 𝕜] [PseudoMetricSpace 𝕜] {a : ball (0 : 𝕜) 1} :
    (a : 𝕜) = 0 ↔ a = 0 :=
  Subtype.val_injective.eq_iff' unitBall.coe_zero

instance Metric.unitBall.instSemigroupWithZero [NonUnitalSeminormedRing 𝕜] :
    SemigroupWithZero (ball (0 : 𝕜) 1) where
  zero_mul _ := Subtype.eq <| zero_mul _
  mul_zero _ := Subtype.eq <| mul_zero _

instance Metric.unitBall.instIsLeftCancelMulZero [NonUnitalSeminormedRing 𝕜]
    [IsLeftCancelMulZero 𝕜] : IsLeftCancelMulZero (ball (0 : 𝕜) 1) :=
  Subtype.val_injective.isLeftCancelMulZero _ rfl fun _ _ ↦ rfl

instance Metric.unitBall.instIsRightCancelMulZero [NonUnitalSeminormedRing 𝕜]
    [IsRightCancelMulZero 𝕜] : IsRightCancelMulZero (ball (0 : 𝕜) 1) :=
  Subtype.val_injective.isRightCancelMulZero _ rfl fun _ _ ↦ rfl

instance Metric.unitBall.instIsCancelMulZero [NonUnitalSeminormedRing 𝕜]
    [IsCancelMulZero 𝕜] : IsCancelMulZero (ball (0 : 𝕜) 1) where

/-!
### Algebraic instances for `Metric.closedBall 0 1`
-/

/-- Closed unit ball in a non-unital seminormed ring as a bundled `Subsemigroup`. -/
def Subsemigroup.unitClosedBall (𝕜 : Type*) [NonUnitalSeminormedRing 𝕜] : Subsemigroup 𝕜 where
  carrier := closedBall 0 1
  mul_mem' hx hy := by
    rw [mem_closedBall_zero_iff] at *
    exact (norm_mul_le _ _).trans (mul_le_one₀ hx (norm_nonneg _) hy)

instance Metric.unitClosedBall.instSemigroup [NonUnitalSeminormedRing 𝕜] :
    Semigroup (closedBall (0 : 𝕜) 1) :=
  MulMemClass.toSemigroup (Subsemigroup.unitClosedBall 𝕜)

instance Metric.unitClosedBall.instHasDistribNeg [NonUnitalSeminormedRing 𝕜] :
    HasDistribNeg (closedBall (0 : 𝕜) 1) :=
  Subtype.coe_injective.hasDistribNeg ((↑) : closedBall (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

instance Metric.unitClosedBall.instContinuousMul [NonUnitalSeminormedRing 𝕜] :
    ContinuousMul (closedBall (0 : 𝕜) 1) :=
  (Subsemigroup.unitClosedBall 𝕜).continuousMul

@[simp, norm_cast]
protected theorem Metric.unitClosedBall.coe_mul [NonUnitalSeminormedRing 𝕜]
    (x y : closedBall (0 : 𝕜) 1) : ↑(x * y) = (x * y : 𝕜) :=
  rfl

@[deprecated (since := "2025-04-18")]
alias coe_mul_unitClosedBall := Metric.unitClosedBall.coe_mul

instance Metric.unitClosedBall.instZero [Zero 𝕜] [PseudoMetricSpace 𝕜] :
    Zero (closedBall (0 : 𝕜) 1) where
  zero := ⟨0, by simp⟩

@[simp, norm_cast]
protected lemma Metric.unitClosedBall.coe_zero [Zero 𝕜] [PseudoMetricSpace 𝕜] :
    ((0 : closedBall (0 : 𝕜) 1) : 𝕜) = 0 :=
  rfl

@[simp, norm_cast]
protected lemma Metric.unitClosedBall.coe_eq_zero [Zero 𝕜] [PseudoMetricSpace 𝕜]
    {a : closedBall (0 : 𝕜) 1} : (a : 𝕜) = 0 ↔ a = 0 :=
  Subtype.val_injective.eq_iff' unitClosedBall.coe_zero

instance Metric.unitClosedBall.instSemigroupWithZero [NonUnitalSeminormedRing 𝕜] :
    SemigroupWithZero (closedBall (0 : 𝕜) 1) where
  zero_mul _ := Subtype.eq <| zero_mul _
  mul_zero _ := Subtype.eq <| mul_zero _

/-- Closed unit ball in a seminormed ring as a bundled `Submonoid`. -/
def Submonoid.unitClosedBall (𝕜 : Type*) [SeminormedRing 𝕜] [NormOneClass 𝕜] : Submonoid 𝕜 :=
  { Subsemigroup.unitClosedBall 𝕜 with
    carrier := closedBall 0 1
    one_mem' := mem_closedBall_zero_iff.2 norm_one.le }

instance Metric.unitClosedBall.instMonoid [SeminormedRing 𝕜] [NormOneClass 𝕜] :
    Monoid (closedBall (0 : 𝕜) 1) :=
  SubmonoidClass.toMonoid (Submonoid.unitClosedBall 𝕜)

instance Metric.unitClosedBall.instCommMonoid [SeminormedCommRing 𝕜] [NormOneClass 𝕜] :
    CommMonoid (closedBall (0 : 𝕜) 1) :=
  SubmonoidClass.toCommMonoid (Submonoid.unitClosedBall 𝕜)

@[simp, norm_cast]
protected theorem Metric.unitClosedBall.coe_one [SeminormedRing 𝕜] [NormOneClass 𝕜] :
    ((1 : closedBall (0 : 𝕜) 1) : 𝕜) = 1 :=
  rfl

@[deprecated (since := "2025-04-18")]
alias coe_one_unitClosedBall := Metric.unitClosedBall.coe_one

@[simp, norm_cast]
protected theorem Metric.unitClosedBall.coe_eq_one [SeminormedRing 𝕜] [NormOneClass 𝕜]
    {a : closedBall (0 : 𝕜) 1} : (a : 𝕜) = 1 ↔ a = 1 :=
  Subtype.val_injective.eq_iff' unitClosedBall.coe_one

@[simp, norm_cast]
protected theorem Metric.unitClosedBall.coe_pow [SeminormedRing 𝕜] [NormOneClass 𝕜]
    (x : closedBall (0 : 𝕜) 1) (n : ℕ) : ↑(x ^ n) = (x : 𝕜) ^ n :=
  rfl

@[deprecated (since := "2025-04-18")]
alias coe_pow_unitClosedBall := Metric.unitClosedBall.coe_pow

instance Metric.unitClosedBall.instMonoidWithZero [SeminormedRing 𝕜] [NormOneClass 𝕜] :
    MonoidWithZero (closedBall (0 : 𝕜) 1) where

instance Metric.unitClosedBall.instCancelMonoidWithZero [SeminormedRing 𝕜] [IsCancelMulZero 𝕜]
    [NormOneClass 𝕜] : CancelMonoidWithZero (closedBall (0 : 𝕜) 1) where
  toIsCancelMulZero := Subtype.val_injective.isCancelMulZero _ rfl fun _ _ ↦ rfl

/-!
### Algebraic instances on the unit sphere
-/

/-- Unit sphere in a seminormed ring (with strictly multiplicative norm) as a bundled
`Submonoid`. -/
@[simps]
def Submonoid.unitSphere (𝕜 : Type*) [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    Submonoid 𝕜 where
  carrier := sphere (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_sphere_zero_iff_norm] at *
    simp [*]
  one_mem' := mem_sphere_zero_iff_norm.2 norm_one

instance Metric.unitSphere.instInv [NormedDivisionRing 𝕜] : Inv (sphere (0 : 𝕜) 1) where
  inv x := ⟨x⁻¹, mem_sphere_zero_iff_norm.2 <| by
    rw [norm_inv, mem_sphere_zero_iff_norm.1 x.coe_prop, inv_one]⟩

@[simp, norm_cast]
theorem Metric.unitSphere.coe_inv [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) :
    ↑x⁻¹ = (x⁻¹ : 𝕜) :=
  rfl

@[deprecated (since := "2025-04-18")]
alias coe_inv_unitSphere := Metric.unitSphere.coe_inv

instance Metric.unitSphere.instDiv [NormedDivisionRing 𝕜] : Div (sphere (0 : 𝕜) 1) where
  div x y := .mk (x / y) <| mem_sphere_zero_iff_norm.2 <| by
    rw [norm_div, mem_sphere_zero_iff_norm.1 x.2, mem_sphere_zero_iff_norm.1 y.coe_prop, div_one]

@[simp, norm_cast]
protected theorem Metric.unitSphere.coe_div [NormedDivisionRing 𝕜] (x y : sphere (0 : 𝕜) 1) :
    ↑(x / y) = (x / y : 𝕜) :=
  rfl

@[deprecated (since := "2025-04-18")]
alias coe_div_unitSphere := Metric.unitSphere.coe_div

instance Metric.unitSphere.instZPow [NormedDivisionRing 𝕜] : Pow (sphere (0 : 𝕜) 1) ℤ where
  pow x n := .mk ((x : 𝕜) ^ n) <| by
    rw [mem_sphere_zero_iff_norm, norm_zpow, mem_sphere_zero_iff_norm.1 x.coe_prop, one_zpow]

@[simp, norm_cast]
theorem Metric.unitSphere.coe_zpow [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) (n : ℤ) :
    ↑(x ^ n) = (x : 𝕜) ^ n :=
  rfl

@[deprecated (since := "2025-04-18")]
alias coe_zpow_unitSphere := Metric.unitSphere.coe_zpow

instance Metric.unitSphere.instMonoid [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    Monoid (sphere (0 : 𝕜) 1) :=
  SubmonoidClass.toMonoid (Submonoid.unitSphere 𝕜)

instance Metric.unitSphere.instCommMonoid [SeminormedCommRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    CommMonoid (sphere (0 : 𝕜) 1) :=
  SubmonoidClass.toCommMonoid (Submonoid.unitSphere 𝕜)

@[simp, norm_cast]
protected theorem Metric.unitSphere.coe_one [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    ((1 : sphere (0 : 𝕜) 1) : 𝕜) = 1 :=
  rfl

@[deprecated (since := "2025-04-18")]
alias coe_one_unitSphere := Metric.unitSphere.coe_one

@[simp, norm_cast]
theorem Metric.unitSphere.coe_mul [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
    (x y : sphere (0 : 𝕜) 1) : ↑(x * y) = (x * y : 𝕜) :=
  rfl

@[deprecated (since := "2025-04-18")]
alias coe_mul_unitSphere := Metric.unitSphere.coe_mul

@[simp, norm_cast]
theorem Metric.unitSphere.coe_pow [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜]
    (x : sphere (0 : 𝕜) 1) (n : ℕ) : ↑(x ^ n) = (x : 𝕜) ^ n :=
  rfl

@[deprecated (since := "2025-04-18")]
alias coe_pow_unitSphere := Metric.unitSphere.coe_pow

/-- Monoid homomorphism from the unit sphere in a normed division ring to the group of units. -/
def unitSphereToUnits (𝕜 : Type*) [NormedDivisionRing 𝕜] : sphere (0 : 𝕜) 1 →* Units 𝕜 :=
  Units.liftRight (Submonoid.unitSphere 𝕜).subtype
    (fun x => Units.mk0 x <| ne_zero_of_mem_unit_sphere _) fun _x => rfl

@[simp]
theorem unitSphereToUnits_apply_coe [NormedDivisionRing 𝕜] (x : sphere (0 : 𝕜) 1) :
    (unitSphereToUnits 𝕜 x : 𝕜) = x :=
  rfl

theorem unitSphereToUnits_injective [NormedDivisionRing 𝕜] :
    Function.Injective (unitSphereToUnits 𝕜) := fun x y h =>
  Subtype.eq <| by convert congr_arg Units.val h

instance Metric.unitSphere.instGroup [NormedDivisionRing 𝕜] : Group (sphere (0 : 𝕜) 1) :=
  unitSphereToUnits_injective.group (unitSphereToUnits 𝕜) (Units.ext rfl)
    (fun _x _y => Units.ext rfl)
    (fun _x => Units.ext rfl) (fun _x _y => Units.ext <| div_eq_mul_inv _ _)
    (fun x n => Units.ext (Units.val_pow_eq_pow_val (unitSphereToUnits 𝕜 x) n).symm) fun x n =>
    Units.ext (Units.val_zpow_eq_zpow_val (unitSphereToUnits 𝕜 x) n).symm

instance Metric.sphere.instHasDistribNeg [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    HasDistribNeg (sphere (0 : 𝕜) 1) :=
  Subtype.coe_injective.hasDistribNeg ((↑) : sphere (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

instance Metric.sphere.instContinuousMul [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    ContinuousMul (sphere (0 : 𝕜) 1) :=
  (Submonoid.unitSphere 𝕜).continuousMul

instance Metric.sphere.instIsTopologicalGroup [NormedDivisionRing 𝕜] :
    IsTopologicalGroup (sphere (0 : 𝕜) 1) where
  continuous_inv := (continuous_subtype_val.inv₀ ne_zero_of_mem_unit_sphere).subtype_mk _

instance Metric.sphere.instCommGroup [NormedField 𝕜] : CommGroup (sphere (0 : 𝕜) 1) where
