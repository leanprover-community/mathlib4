/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Additive characters valued in the unit circle

This file defines additive characters, valued in the unit circle, from either
* the ring `ZMod N` for any non-zero natural `N`,
* the additive circle `ℝ / T ⬝ ℤ`, for any real `T`.

These results are separate from `Analysis.SpecialFunctions.Complex.Circle` in order to reduce
the imports of that file.
-/

open Complex Function

open scoped Real

/-- The canonical map from the additive to the multiplicative circle, as an `AddChar`. -/
noncomputable def AddCircle.toCircle_addChar {T : ℝ} : AddChar (AddCircle T) Circle where
  toFun := toCircle
  map_zero_eq_one' := toCircle_zero
  map_add_eq_mul' := toCircle_add

open AddCircle

namespace ZMod

/-!
### Additive characters valued in the complex circle
-/

open scoped Real

variable {N : ℕ} [NeZero N]

/-- The additive character from `ZMod N` to the unit circle in `ℂ`, sending `j mod N` to
`exp (2 * π * I * j / N)`. -/
noncomputable def toCircle : AddChar (ZMod N) Circle :=
  toCircle_addChar.compAddMonoidHom toAddCircle

lemma toCircle_intCast (j : ℤ) :
    toCircle (j : ZMod N) = exp (2 * π * I * j / N) := by
  rw [toCircle, AddChar.compAddMonoidHom_apply, toCircle_addChar, AddChar.coe_mk,
    AddCircle.toCircle, toAddCircle_intCast, Function.Periodic.lift_coe, Circle.coe_exp]
  push_cast
  ring_nf

lemma toCircle_natCast (j : ℕ) :
    toCircle (j : ZMod N) = exp (2 * π * I * j / N) := by
  simpa using toCircle_intCast (N := N) j

/--
Explicit formula for `toCircle j`. Note that this is "evil" because it uses `ZMod.val`. Where
possible, it is recommended to lift `j` to `ℤ` and use `toCircle_intCast` instead.
-/
lemma toCircle_apply (j : ZMod N) :
    toCircle j = exp (2 * π * I * j.val / N) := by
  rw [← toCircle_natCast, natCast_zmod_val]

lemma toCircle_eq_circleExp (j : ZMod N) :
    toCircle j = Circle.exp (2 * π * (j.val / N)) := by
  ext
  rw [toCircle_apply, Circle.coe_exp]
  push_cast
  ring_nf

lemma injective_toCircle : Injective (toCircle : ZMod N → Circle) :=
  (AddCircle.injective_toCircle one_ne_zero).comp (toAddCircle_injective N)

/-- The additive character from `ZMod N` to `ℂ`, sending `j mod N` to `exp (2 * π * I * j / N)`. -/
noncomputable def stdAddChar : AddChar (ZMod N) ℂ := Circle.coeHom.compAddChar toCircle

lemma stdAddChar_coe (j : ℤ) :
    stdAddChar (j : ZMod N) = exp (2 * π * I * j / N) := by simp [stdAddChar, toCircle_intCast]

lemma stdAddChar_apply (j : ZMod N) : stdAddChar j = ↑(toCircle j) := rfl

lemma injective_stdAddChar : Injective (stdAddChar : AddChar (ZMod N) ℂ) :=
  Subtype.coe_injective.comp injective_toCircle

/-- The standard additive character `ZMod N → ℂ` is primitive. -/
lemma isPrimitive_stdAddChar (N : ℕ) [NeZero N] :
    (stdAddChar (N := N)).IsPrimitive := by
  refine AddChar.zmod_char_primitive_of_eq_one_only_at_zero _ _ (fun t ht ↦ ?_)
  rwa [← (stdAddChar (N := N)).map_zero_eq_one, injective_stdAddChar.eq_iff] at ht

/-- `ZMod.toCircle` as an `AddChar` into `rootsOfUnity n Circle`. -/
noncomputable def expHom (n : ℕ) [NeZero n] : AddChar (ZMod n) (rootsOfUnity n Circle) where
  toFun x := ⟨toUnits (ZMod.toCircle x), by
    have e1 : ↑n * (2 * π * (↑x.val / ↑n)) = ↑x.val * (2 * π) := by
      rw [mul_comm, mul_assoc, natCast_val, div_mul_cancel_of_invertible, mul_comm]
    simp_rw [_root_.mem_rootsOfUnity, toCircle_eq_circleExp, ← map_pow,
      ← Circle.exp_nat_mul, e1, Circle.exp_nat_mul_two_pi]
    simp only [natCast_val, map_one]⟩
  map_zero_eq_one' := by
    simp only [AddChar.map_zero_eq_one, map_one, Subgroup.mk_eq_one]
  map_add_eq_mul' _ _:= by
    simp_rw [AddChar.map_add_eq_mul]
    simp_all only [map_mul, MulMemClass.mk_mul_mk]

end ZMod
