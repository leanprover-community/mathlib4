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
open scoped ComplexConjugate Topology

noncomputable section

namespace Complex

/-- The complex unit disc, denoted as `𝔻` withinin the Complex namespace -/
def UnitDisc : Type :=
  ball (0 : ℂ) 1 deriving TopologicalSpace

@[inherit_doc] scoped[Complex.UnitDisc] notation "𝔻" => Complex.UnitDisc
open UnitDisc

namespace UnitDisc

/-- Coercion to `ℂ`. -/
@[coe] protected def coe : 𝔻 → ℂ := Subtype.val

instance instCommSemigroup : CommSemigroup UnitDisc := by unfold UnitDisc; infer_instance
instance instSemigroupWithZero : SemigroupWithZero UnitDisc := by unfold UnitDisc; infer_instance
instance instIsCancelMulZero : IsCancelMulZero UnitDisc := by unfold UnitDisc; infer_instance
instance instHasDistribNeg : HasDistribNeg UnitDisc := by unfold UnitDisc; infer_instance
instance instCoe : Coe UnitDisc ℂ := ⟨UnitDisc.coe⟩

@[ext]
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

theorem sq_norm_lt_one (z : 𝔻) : ‖(z : ℂ)‖ ^ 2 < 1 := by
  rw [sq_lt_one_iff_abs_lt_one, abs_norm]
  exact z.norm_lt_one

theorem normSq_lt_one (z : 𝔻) : normSq z < 1 := by
  rw [← Complex.norm_mul_self_eq_normSq, ← sq]
  exact z.sq_norm_lt_one

theorem coe_ne_one (z : 𝔻) : (z : ℂ) ≠ 1 :=
  ne_of_apply_ne (‖·‖) <| by simp [z.norm_ne_one]

theorem coe_ne_neg_one (z : 𝔻) : (z : ℂ) ≠ -1 :=
  ne_of_apply_ne (‖·‖) <| by simpa [norm_neg] using z.norm_ne_one

theorem one_add_coe_ne_zero (z : 𝔻) : (1 + z : ℂ) ≠ 0 :=
  mt neg_eq_iff_add_eq_zero.2 z.coe_ne_neg_one.symm

@[simp, norm_cast]
theorem coe_mul (z w : 𝔻) : ↑(z * w) = (z * w : ℂ) :=
  rfl

@[simp, norm_cast]
theorem coe_neg (z : 𝔻) : ↑(-z) = (-z : ℂ) := rfl

/-- A constructor that assumes `‖z‖ < 1` instead of `dist z 0 < 1` and returns an element
of `𝔻` instead of `↥Metric.ball (0 : ℂ) 1`. -/
def mk (z : ℂ) (hz : ‖z‖ < 1) : 𝔻 :=
  ⟨z, mem_ball_zero_iff.2 hz⟩

instance : CanLift ℂ 𝔻 (↑) (‖·‖ < 1) where
  prf z hz := ⟨mk z hz, rfl⟩

/-- A cases eliminator that makes `cases z` use `UnitDisc.mk` instead of `Subtype.mk`. -/
@[elab_as_elim, cases_eliminator]
protected def casesOn {motive : 𝔻 → Sort*} (mk : ∀ z hz, motive (.mk z hz)) (z : 𝔻) :
    motive z :=
  mk z z.norm_lt_one

@[simp]
theorem casesOn_mk {motive : 𝔻 → Sort*} (mk' : ∀ z hz, motive (.mk z hz)) {z : ℂ} (hz : ‖z‖ < 1) :
    (mk z hz).casesOn mk' = mk' z hz :=
  rfl

@[simp]
theorem coe_mk (z : ℂ) (hz : ‖z‖ < 1) : (mk z hz : ℂ) = z :=
  rfl

@[simp]
theorem mk_coe (z : 𝔻) (hz : ‖(z : ℂ)‖ < 1 := z.norm_lt_one) : mk z hz = z :=
  Subtype.eta _ _

@[simp]
theorem mk_inj {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) : mk z hz = mk w hw ↔ z = w :=
  Subtype.mk_eq_mk

protected theorem «forall» {p : 𝔻 → Prop} : (∀ z, p z) ↔ ∀ z hz, p (mk z hz) :=
  ⟨fun h z hz ↦ h (mk z hz), fun h z ↦ h z z.norm_lt_one⟩

protected theorem «exists» {p : 𝔻 → Prop} : (∃ z, p z) ↔ ∃ z hz, p (mk z hz) :=
  ⟨fun ⟨z, hz⟩ ↦ ⟨z, z.norm_lt_one, hz⟩, fun ⟨z, hz, h⟩ ↦ ⟨mk z hz, h⟩⟩

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

instance instMulActionCircle : MulAction Circle 𝔻 :=
  mulActionSphereBall

instance instIsScalarTower_circle_circle : IsScalarTower Circle Circle 𝔻 :=
  isScalarTower_sphere_sphere_ball

instance instIsScalarTower_circle : IsScalarTower Circle 𝔻 𝔻 :=
  isScalarTower_sphere_ball_ball

instance instSMulCommClass_circle_left : SMulCommClass Circle 𝔻 𝔻 :=
  instSMulCommClass_sphere_ball_ball

instance instSMulCommClass_circle_right : SMulCommClass 𝔻 Circle 𝔻 :=
  SMulCommClass.symm _ _ _

@[simp, norm_cast]
theorem coe_circle_smul (z : Circle) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

@[deprecated (since := "2026-01-06")]
alias coe_smul_circle := coe_circle_smul

instance instMulActionClosedBall : MulAction (closedBall (0 : ℂ) 1) 𝔻 :=
  mulActionClosedBallBall

instance instIsScalarTower_closedBall_closedBall :
    IsScalarTower (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) 𝔻 :=
  isScalarTower_closedBall_closedBall_ball

instance instIsScalarTower_closedBall : IsScalarTower (closedBall (0 : ℂ) 1) 𝔻 𝔻 :=
  isScalarTower_closedBall_ball_ball

instance instSMulCommClass_closedBall_left : SMulCommClass (closedBall (0 : ℂ) 1) 𝔻 𝔻 :=
  ⟨fun _ _ _ => Subtype.ext <| mul_left_comm _ _ _⟩

instance instSMulCommClass_closedBall_right : SMulCommClass 𝔻 (closedBall (0 : ℂ) 1) 𝔻 :=
  SMulCommClass.symm _ _ _

instance instSMulCommClass_circle_closedBall : SMulCommClass Circle (closedBall (0 : ℂ) 1) 𝔻 :=
  instSMulCommClass_sphere_closedBall_ball

instance instSMulCommClass_closedBall_circle : SMulCommClass (closedBall (0 : ℂ) 1) Circle 𝔻 :=
  SMulCommClass.symm _ _ _

@[simp, norm_cast]
theorem coe_closedBall_smul (z : closedBall (0 : ℂ) 1) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

@[deprecated (since := "2026-01-06")]
alias coe_smul_closedBall := coe_closedBall_smul

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
instance : Star 𝔻 where
  star z := mk (conj z) <| (norm_conj z).symm ▸ z.norm_lt_one

/-- Conjugate point of the unit disc. Deprecated, use `star` instead. -/
@[deprecated star (since := "2026-01-06")]
protected def «conj» (z : 𝔻) := star z

@[simp] theorem coe_star (z : 𝔻) : (↑(star z) : ℂ) = conj ↑z := rfl

@[deprecated (since := "2026-01-06")]
alias coe_conj := coe_star

@[simp]
protected theorem star_eq_zero {z : 𝔻} : star z = 0 ↔ z = 0 := by
  simp [← coe_eq_zero]

@[simp]
protected theorem star_zero : star (0 : 𝔻) = 0 := by simp

instance : InvolutiveStar 𝔻 where
  star_involutive z := by ext; simp

@[deprecated star_star (since := "2026-01-06")]
theorem conj_conj (z : 𝔻) : star (star z) = z := star_star z

@[simp] protected theorem star_neg (z : 𝔻) : star (-z) = -(star z) := rfl

@[deprecated (since := "2026-01-06")]
alias conj_neg := UnitDisc.star_neg

@[simp] protected theorem re_star (z : 𝔻) : (star z).re = z.re := rfl

@[deprecated (since := "2026-01-06")]
alias re_conj := UnitDisc.re_star

@[simp] protected theorem im_star (z : 𝔻) : (star z).im = -z.im := rfl

@[deprecated (since := "2026-01-06")] alias im_conj := UnitDisc.im_star

instance : StarMul 𝔻 where
  star_mul z w := coe_injective <| by simp [mul_comm]

@[deprecated star_mul' (since := "2026-01-06")]
theorem conj_mul (z w : 𝔻) : star (z * w) = star z * star w :=
  star_mul' z w

end UnitDisc

end Complex
