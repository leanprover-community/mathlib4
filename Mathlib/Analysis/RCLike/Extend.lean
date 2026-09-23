/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Extending an `ℝ`-linear functional to a `𝕜`-linear functional

In this file we provide a way to extend a (optionally, continuous) `ℝ`-linear map to a (continuous)
`𝕜`-linear map in a way that bounds the norm by the norm of the original map, when `𝕜` is either
`ℝ` (the extension is trivial) or `ℂ`. We formulate the extension uniformly, by assuming `RCLike 𝕜`.

We motivate the form of the extension as follows. Note that `fc : F →ₗ[𝕜] 𝕜` is determined fully by
`re fc`: for all `x : F`, `fc (I • x) = I * fc x`, so `im (fc x) = -re (fc (I • x))`. Therefore,
given an `fr : F →ₗ[ℝ] ℝ`, we define `fc x = fr x - fr (I • x) * I`.

In `Mathlib/Analysis/Normed/Module/RCLike/Extend.lean` we show that this extension is isometric.
This is separate to avoid importing material about the operator norm into files about more
elementary properties, like locally convex spaces.

## Main definitions

* `LinearMap.extendRCLike`
* `ContinuousLinearMap.extendRCLike`

-/

@[expose] public section

open RCLike

open ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] {F : Type*}
namespace Module.Dual

variable [AddCommGroup F] [Module ℝ F] [Module 𝕜 F] [IsScalarTower ℝ 𝕜 F]

/-- Extend `fr : Dual ℝ F` to `Dual 𝕜 F` in a way that will also be continuous and have its norm
(as a continuous linear map) equal to `‖fr‖` when `fr` is itself continuous on a normed space. -/
noncomputable def extendRCLike (fr : Dual ℝ F) : Dual 𝕜 F :=
  letI fc : F → 𝕜 := fun x => (fr x : 𝕜) - (I : 𝕜) * fr ((I : 𝕜) • x)
  have add (x y) : fc (x + y) = fc x + fc y := by
    simp only [fc, smul_add, map_add, mul_add]
    abel
  have A (c : ℝ) (x : F) : (fr ((c : 𝕜) • x) : 𝕜) = (c : 𝕜) * (fr x : 𝕜) := by simp
  have smul_ℝ (c : ℝ) (x : F) : fc ((c : 𝕜) • x) = (c : 𝕜) * fc x := by
    simp only [fc, A, smul_comm I, mul_comm I, mul_sub, mul_assoc]
  have smul_I (x : F) : fc ((I : 𝕜) • x) = (I : 𝕜) * fc x := by
    obtain (h | h) := @I_mul_I_ax 𝕜 _
    · simp [fc, h]
    · simp [fc, mul_sub, ← mul_assoc, smul_smul, h, add_comm]
  have smul_𝕜 (c : 𝕜) (x : F) : fc (c • x) = c • fc x := by
    rw [← re_add_im c]
    simp only [add_smul, ← smul_smul, add, smul_ℝ, smul_I, ← mul_assoc, smul_eq_mul, add_mul]
  { toFun := fc
    map_add' := add
    map_smul' := smul_𝕜 }

theorem extendRCLike_apply (fr : Dual ℝ F) (x : F) :
    fr.extendRCLike x = (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) := rfl

@[simp]
theorem re_extendRCLike_apply (fr : Dual ℝ F) (x : F) : re (fr.extendRCLike x : 𝕜) = fr x := by
  simp only [extendRCLike_apply, map_sub, zero_mul, mul_zero, sub_zero, rclike_simps]

@[simp]
lemma im_extendRCLike_apply (g : Dual ℝ F) (x : F) :
    im ((extendRCLike g) x : 𝕜) = - g ((I : 𝕜) • x) := by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  all_goals simp [h, extendRCLike_apply]

theorem norm_extendRCLike_apply_sq (fr : Dual ℝ F) (x : F) :
    ‖(fr.extendRCLike x : 𝕜)‖ ^ 2 = fr (conj (fr.extendRCLike x : 𝕜) • x) := calc
  ‖(fr.extendRCLike x : 𝕜)‖ ^ 2 = re (conj (fr.extendRCLike x) * fr.extendRCLike x : 𝕜) := by
    rw [RCLike.conj_mul, ← ofReal_pow, ofReal_re]
  _ = fr (conj (fr.extendRCLike x : 𝕜) • x) := by
    rw [← smul_eq_mul, ← map_smul, re_extendRCLike_apply]

/-- The extension `Module.Dual.extendRCLike` as a linear equivalence between the algebraic duals. -/
@[simps -isSimp apply symm_apply]
noncomputable def extendRCLikeₗ : Dual ℝ F ≃ₗ[ℝ] Dual 𝕜 F where
  toFun := extendRCLike (𝕜 := 𝕜)
  invFun f := RCLike.reLm.comp (f.restrictScalars ℝ)
  left_inv f := by ext; simp
  right_inv f := by ext; apply RCLike.ext <;> simp
  map_add' := by intros; ext; simp [extendRCLike_apply]; ring
  map_smul' := by intros; ext; simp [extendRCLike_apply, real_smul_eq_coe_mul]; ring

end Module.Dual

namespace StrongDual

variable [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [ContinuousConstSMul 𝕜 F]
variable [Module ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- Extend `fr : StrongDual ℝ F` to `StrongDual 𝕜 F`.

It would be possible to use `LinearMap.mkContinuous` here, but we would need to know that the
continuity of `fr` implies it has bounded norm and we want to avoid that dependency here.

Norm properties of this extension can be found in
`Mathlib/Analysis/Normed/Module/RCLike/Extend.lean`. -/
noncomputable def extendRCLike (fr : StrongDual ℝ F) : StrongDual 𝕜 F where
  __ := Module.Dual.extendRCLike fr.toLinearMap
  cont := show Continuous fun x ↦ (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) by fun_prop

theorem extendRCLike_apply (fr : StrongDual ℝ F) (x : F) :
    fr.extendRCLike x = (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) := rfl

@[simp]
lemma re_extendRCLike_apply (g : StrongDual ℝ F) (x : F) :
    re ((extendRCLike g) x : 𝕜) = g x := by
  simp [extendRCLike_apply]

@[deprecated (since := "2026-02-24")] alias _root_.RCLike.re_extendTo𝕜ₗ := re_extendRCLike_apply

@[simp]
lemma im_extendRCLike_apply (g : StrongDual ℝ F) (x : F) :
    im ((extendRCLike g) x : 𝕜) = - g ((I : 𝕜) • x) := by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  all_goals simp [h, extendRCLike_apply]

/-- The extension `StrongDual.extendRCLike` as a linear equivalence between the algebraic duals.

When `F` is a normed space, this can be upgraded to an *isometric* linear equivalence, see
`StrongDual.extendRCLikeₗᵢ`. -/
@[simps -isSimp apply symm_apply]
noncomputable def extendRCLikeₗ : StrongDual ℝ F ≃ₗ[ℝ] StrongDual 𝕜 F where
  toFun := StrongDual.extendRCLike (𝕜 := 𝕜)
  invFun f := RCLike.reCLM.comp (f.restrictScalars ℝ)
  left_inv f := by ext; simp
  right_inv f := by ext; apply RCLike.ext <;> simp [extendRCLike_apply]
  map_add' := by intros; ext; simp [extendRCLike_apply]; ring
  map_smul' := by intros; ext; simp [extendRCLike_apply, real_smul_eq_coe_mul]; ring

@[deprecated (since := "2026-02-24")] alias _root_.RCLike.extendTo𝕜ₗ := extendRCLikeₗ

end StrongDual

namespace LinearMap

open Module.Dual

@[deprecated (since := "2026-02-24")] alias extendTo𝕜' := extendRCLike
@[deprecated (since := "2026-02-24")] alias extendTo𝕜'_apply := extendRCLike_apply
@[deprecated (since := "2026-02-24")] alias extendTo𝕜'_apply_re := re_extendRCLike_apply
@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜'_apply_sq := norm_extendRCLike_apply_sq
@[deprecated (since := "2026-02-24")] alias extendTo𝕜 := extendRCLike
@[deprecated (since := "2026-02-24")] alias extendTo𝕜_apply := extendRCLike_apply

end LinearMap

namespace ContinuousLinearMap

open StrongDual

@[deprecated (since := "2026-02-24")] alias extendTo𝕜' := extendRCLike
@[deprecated (since := "2026-02-24")] alias extendTo𝕜'_apply := extendRCLike_apply
@[deprecated (since := "2026-02-24")] alias extendTo𝕜 := extendRCLike
@[deprecated (since := "2026-02-24")] alias extendTo𝕜_apply := extendRCLike_apply

end ContinuousLinearMap
