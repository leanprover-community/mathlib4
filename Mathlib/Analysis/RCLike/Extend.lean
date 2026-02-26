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

* `LinearMap.extendTo𝕜`
* `ContinuousLinearMap.extendTo𝕜`

## Implementation details

For convenience, the main definitions above operate in terms of `RestrictScalars ℝ 𝕜 F`.
Alternate forms which operate on `[IsScalarTower ℝ 𝕜 F]` instead are provided with a primed name.

-/

@[expose] public section


open RCLike

open ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] {F : Type*}
namespace LinearMap

open Module

section ScalarTower

variable [AddCommGroup F] [Module ℝ F] [Module 𝕜 F] [IsScalarTower ℝ 𝕜 F]

/-- Extend `fr : Dual ℝ F` to `Dual 𝕜 F` in a way that will also be continuous and have its norm
(as a continuous linear map) equal to `‖fr‖` when `fr` is itself continuous on a normed space. -/
noncomputable def extendTo𝕜' (fr : Dual ℝ F) : Dual 𝕜 F :=
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

theorem extendTo𝕜'_apply (fr : Dual ℝ F) (x : F) :
    fr.extendTo𝕜' x = (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) := rfl

@[simp]
theorem extendTo𝕜'_apply_re (fr : Dual ℝ F) (x : F) : re (fr.extendTo𝕜' x : 𝕜) = fr x := by
  simp only [extendTo𝕜'_apply, map_sub, zero_mul, mul_zero, sub_zero, rclike_simps]

theorem norm_extendTo𝕜'_apply_sq (fr : Dual ℝ F) (x : F) :
    ‖(fr.extendTo𝕜' x : 𝕜)‖ ^ 2 = fr (conj (fr.extendTo𝕜' x : 𝕜) • x) := calc
  ‖(fr.extendTo𝕜' x : 𝕜)‖ ^ 2 = re (conj (fr.extendTo𝕜' x) * fr.extendTo𝕜' x : 𝕜) := by
    rw [RCLike.conj_mul, ← ofReal_pow, ofReal_re]
  _ = fr (conj (fr.extendTo𝕜' x : 𝕜) • x) := by
    rw [← smul_eq_mul, ← map_smul, extendTo𝕜'_apply_re]

end ScalarTower

section RestrictScalars

variable [AddCommGroup F] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

instance : NormedSpace 𝕜 (RestrictScalars ℝ 𝕜 F) :=
  inferInstanceAs (NormedSpace 𝕜 F)

/-- Extend `fr : Dual ℝ (RestrictScalars ℝ 𝕜 F)` to `Dual 𝕜 F`. -/
noncomputable def extendTo𝕜 (fr : Dual ℝ (RestrictScalars ℝ 𝕜 F)) : Dual 𝕜 F :=
  fr.extendTo𝕜'

theorem extendTo𝕜_apply (fr : RestrictScalars ℝ 𝕜 F →ₗ[ℝ] ℝ) (x : F) :
    fr.extendTo𝕜 x = (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) := rfl

end RestrictScalars

end LinearMap

namespace ContinuousLinearMap

variable [AddCommGroup F] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

section ScalarTower

variable [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- Extend `fr : StrongDual ℝ F` to `StrongDual 𝕜 F`.

It would be possible to use `LinearMap.mkContinuous` here, but we would need to know that the
continuity of `fr` implies it has bounded norm and we want to avoid that dependency here.

Norm properties of this extension can be found in
`Mathlib/Analysis/Normed/Module/RCLike/Extend.lean`. -/
noncomputable def extendTo𝕜' (fr : StrongDual ℝ F) : StrongDual 𝕜 F where
  __ := fr.toLinearMap.extendTo𝕜'
  cont := show Continuous fun x ↦ (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) by fun_prop

theorem extendTo𝕜'_apply (fr : StrongDual ℝ F) (x : F) :
    fr.extendTo𝕜' x = (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) := rfl

end ScalarTower

/-- Extend `fr : StrongDual ℝ (RestrictScalars ℝ 𝕜 F)` to `StrongDual 𝕜 F`. -/
noncomputable def extendTo𝕜 (fr : StrongDual ℝ (RestrictScalars ℝ 𝕜 F)) :
    StrongDual 𝕜 F := fr.extendTo𝕜'

theorem extendTo𝕜_apply (fr : StrongDual ℝ (RestrictScalars ℝ 𝕜 F)) (x : F) :
    fr.extendTo𝕜 x = (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) := rfl

end ContinuousLinearMap
