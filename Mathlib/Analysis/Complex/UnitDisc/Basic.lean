/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import Mathlib.Algebra.Group.PNatPowAssoc

/-!
# Poincaré disc

In this file we define `Complex.UnitDisc` to be the unit disc in the complex plane. We also
introduce some basic operations on this disc.
-/

@[expose] public section

open Set Function Metric Filter
open scoped Topology

noncomputable section

local notation "conj'" => starRingEnd ℂ

namespace Complex

/-- The complex unit disc, denoted as `𝔻` withinin the Complex namespace -/
def UnitDisc : Type :=
  ball (0 : ℂ) 1 deriving TopologicalSpace

@[inherit_doc] scoped[UnitDisc] notation "𝔻" => Complex.UnitDisc
open UnitDisc

namespace UnitDisc

/-- Coercion to `ℂ`. -/
@[coe] protected def coe : 𝔻 → ℂ := Subtype.val

instance instCommSemigroup : CommSemigroup UnitDisc := by unfold UnitDisc; infer_instance
instance instSemigroupWithZero : SemigroupWithZero UnitDisc := by unfold UnitDisc; infer_instance
instance instIsCancelMulZero : IsCancelMulZero UnitDisc := by unfold UnitDisc; infer_instance
instance instHasDistribNeg : HasDistribNeg UnitDisc := by unfold UnitDisc; infer_instance
instance instCoe : Coe UnitDisc ℂ := ⟨UnitDisc.coe⟩

theorem coe_injective : Injective ((↑) : 𝔻 → ℂ) :=
  Subtype.coe_injective

@[simp, norm_cast]
theorem coe_inj {z w : 𝔻} : (z : ℂ) = w ↔ z = w := Subtype.val_inj

@[fun_prop]
theorem isEmbedding_coe : Topology.IsEmbedding ((↑) : 𝔻 → ℂ) := .subtypeVal

@[fun_prop]
theorem continuous_coe : Continuous ((↑) : 𝔻 → ℂ) := isEmbedding_coe.continuous

theorem norm_lt_one (z : 𝔻) : ‖(z : ℂ)‖ < 1 :=
  mem_ball_zero_iff.1 z.2

theorem norm_ne_one (z : 𝔻) : ‖(z : ℂ)‖ ≠ 1 :=
  z.norm_lt_one.ne

theorem normSq_lt_one (z : 𝔻) : normSq z < 1 := by
  convert (Real.sqrt_lt' one_pos).1 z.norm_lt_one
  exact (one_pow 2).symm

theorem coe_ne_one (z : 𝔻) : (z : ℂ) ≠ 1 :=
  ne_of_apply_ne (‖·‖) <| by simp [z.norm_ne_one]

theorem coe_ne_neg_one (z : 𝔻) : (z : ℂ) ≠ -1 :=
  ne_of_apply_ne (‖·‖) <| by simpa [norm_neg] using z.norm_ne_one

theorem one_add_coe_ne_zero (z : 𝔻) : (1 + z : ℂ) ≠ 0 :=
  mt neg_eq_iff_add_eq_zero.2 z.coe_ne_neg_one.symm

@[simp, norm_cast]
theorem coe_mul (z w : 𝔻) : ↑(z * w) = (z * w : ℂ) :=
  rfl

/-- A constructor that assumes `‖z‖ < 1` instead of `dist z 0 < 1` and returns an element
of `𝔻` instead of `↥Metric.ball (0 : ℂ) 1`. -/
def mk (z : ℂ) (hz : ‖z‖ < 1) : 𝔻 :=
  ⟨z, mem_ball_zero_iff.2 hz⟩

@[simp]
theorem coe_mk (z : ℂ) (hz : ‖z‖ < 1) : (mk z hz : ℂ) = z :=
  rfl

@[simp]
theorem mk_coe (z : 𝔻) (hz : ‖(z : ℂ)‖ < 1 := z.norm_lt_one) : mk z hz = z :=
  Subtype.eta _ _

@[simp]
theorem mk_neg (z : ℂ) (hz : ‖-z‖ < 1) : mk (-z) hz = -mk z (norm_neg z ▸ hz) :=
  rfl

@[simp]
theorem coe_zero : ((0 : 𝔻) : ℂ) = 0 :=
  rfl

@[simp]
theorem coe_eq_zero {z : 𝔻} : (z : ℂ) = 0 ↔ z = 0 :=
  coe_injective.eq_iff' coe_zero

@[simp] theorem mk_zero : mk 0 (by simp) = 0 := rfl
@[simp] theorem mk_eq_zero {z : ℂ} (hz : ‖z‖ < 1) : mk z hz = 0 ↔ z = 0 := by simp [← coe_inj]

instance : Inhabited 𝔻 :=
  ⟨0⟩

instance circleAction : MulAction Circle 𝔻 :=
  mulActionSphereBall

instance isScalarTower_circle_circle : IsScalarTower Circle Circle 𝔻 :=
  isScalarTower_sphere_sphere_ball

instance isScalarTower_circle : IsScalarTower Circle 𝔻 𝔻 :=
  isScalarTower_sphere_ball_ball

instance instSMulCommClass_circle : SMulCommClass Circle 𝔻 𝔻 :=
  instSMulCommClass_sphere_ball_ball

instance instSMulCommClass_circle' : SMulCommClass 𝔻 Circle 𝔻 :=
  SMulCommClass.symm _ _ _

@[simp, norm_cast]
theorem coe_smul_circle (z : Circle) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

instance closedBallAction : MulAction (closedBall (0 : ℂ) 1) 𝔻 :=
  mulActionClosedBallBall

instance isScalarTower_closedBall_closedBall :
    IsScalarTower (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) 𝔻 :=
  isScalarTower_closedBall_closedBall_ball

instance isScalarTower_closedBall : IsScalarTower (closedBall (0 : ℂ) 1) 𝔻 𝔻 :=
  isScalarTower_closedBall_ball_ball

instance instSMulCommClass_closedBall : SMulCommClass (closedBall (0 : ℂ) 1) 𝔻 𝔻 :=
  ⟨fun _ _ _ => Subtype.ext <| mul_left_comm _ _ _⟩

instance instSMulCommClass_closedBall' : SMulCommClass 𝔻 (closedBall (0 : ℂ) 1) 𝔻 :=
  SMulCommClass.symm _ _ _

instance instSMulCommClass_circle_closedBall : SMulCommClass Circle (closedBall (0 : ℂ) 1) 𝔻 :=
  instSMulCommClass_sphere_closedBall_ball

instance instSMulCommClass_closedBall_circle : SMulCommClass (closedBall (0 : ℂ) 1) Circle 𝔻 :=
  SMulCommClass.symm _ _ _

@[simp, norm_cast]
theorem coe_smul_closedBall (z : closedBall (0 : ℂ) 1) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

instance : Pow UnitDisc ℕ+ where
  pow z n := ⟨z ^ (n : ℕ), by simp [pow_lt_one_iff_of_nonneg, z.norm_lt_one]⟩

@[simp, norm_cast]
theorem coe_pow (z : 𝔻) (n : ℕ+) : ((z ^ n : 𝔻) : ℂ) = z ^ (n : ℕ) := rfl

@[fun_prop]
theorem continuous_pow (n : ℕ+) : Continuous (· ^ n : 𝔻 → 𝔻) := by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_pow]
  fun_prop

@[simp]
theorem pow_eq_zero {z : 𝔻} {n : ℕ+} : z ^ n = 0 ↔ z = 0 := by
  rw [← coe_inj, coe_pow]
  simp

instance : PNatPowAssoc 𝔻 where
  ppow_add m n z := mod_cast pow_add (z : ℂ) m n
  ppow_one z := by simp [← coe_inj]

theorem tendsto_pow_atTop_nhds_zero (z : 𝔻) :
    Tendsto (fun n : ℕ+ ↦ z ^ n) atTop (𝓝 0) := by
  simp only [isEmbedding_coe.tendsto_nhds_iff, comp_def, coe_pow]
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr z.norm_lt_one
    |>.comp tendsto_PNat_val_atTop_atTop

/-- Real part of a point of the unit disc. -/
def re (z : 𝔻) : ℝ :=
  Complex.re z

/-- Imaginary part of a point of the unit disc. -/
def im (z : 𝔻) : ℝ :=
  Complex.im z

@[simp, norm_cast]
theorem re_coe (z : 𝔻) : (z : ℂ).re = z.re :=
  rfl

@[simp, norm_cast]
theorem im_coe (z : 𝔻) : (z : ℂ).im = z.im :=
  rfl

@[simp]
theorem re_neg (z : 𝔻) : (-z).re = -z.re :=
  rfl

@[simp]
theorem im_neg (z : 𝔻) : (-z).im = -z.im :=
  rfl

/-- Conjugate point of the unit disc. -/
def conj (z : 𝔻) : 𝔻 :=
  mk (conj' ↑z) <| (norm_conj z).symm ▸ z.norm_lt_one

@[simp]
theorem coe_conj (z : 𝔻) : (z.conj : ℂ) = conj' ↑z :=
  rfl

@[simp]
theorem conj_zero : conj 0 = 0 :=
  coe_injective (map_zero conj')

@[simp]
theorem conj_conj (z : 𝔻) : conj (conj z) = z :=
  coe_injective <| Complex.conj_conj (z : ℂ)

@[simp]
theorem conj_neg (z : 𝔻) : (-z).conj = -z.conj :=
  rfl

@[simp]
theorem re_conj (z : 𝔻) : z.conj.re = z.re :=
  rfl

@[simp]
theorem im_conj (z : 𝔻) : z.conj.im = -z.im :=
  rfl

@[simp]
theorem conj_mul (z w : 𝔻) : (z * w).conj = z.conj * w.conj :=
  Subtype.ext <| map_mul _ _ _

end UnitDisc

end Complex
