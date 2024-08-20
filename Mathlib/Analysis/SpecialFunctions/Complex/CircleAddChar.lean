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

open AddChar Complex Function Real

namespace Circle
variable {r s : ℝ}

/-- The standard character sending `r : ℝ` to $$e^{2πir}$$. -/
noncomputable def e : AddChar ℝ Circle where
  toFun r := exp (2 * π * r)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by simp [mul_add, Complex.exp_add]

lemma e_apply (r : ℝ) : e r = exp (2 * π * r) := rfl

@[simp, norm_cast] lemma coe_e (r : ℝ) : ↑(e r) = Complex.exp ((2 * π * r : ℝ) * Complex.I) := rfl

@[simp] lemma e_int (z : ℤ) : e z = 1 := exp_two_pi_mul_int _
@[simp] lemma e_one : e 1 = 1 := by simpa using e_int 1
@[simp] lemma e_add_int {z : ℤ} : e (r + z) = e r := by rw [map_add_eq_mul, e_int, mul_one]
@[simp] lemma e_sub_int {z : ℤ} : e (r - z) = e r := by rw [map_sub_eq_div, e_int, div_one]
@[simp] lemma e_fract (r : ℝ) : e (Int.fract r) = e r := by rw [Int.fract, e_sub_int]

@[simp] lemma e_mod_div {m : ℤ} {n : ℕ} : e ((m % n : ℤ) / n) = e (m / n) := by
  obtain hn | hn := eq_or_ne (n : ℝ) 0
  · rw [hn, div_zero, div_zero]
  · rw [Int.emod_def, Int.cast_sub, sub_div, Int.cast_mul, Int.cast_natCast,
      mul_div_cancel_left₀ _ hn, e_sub_int]

lemma e_eq_one : e r = 1 ↔ ∃ n : ℤ, r = n := by
  simp [e_apply, exp_eq_one, mul_comm (2 * π), pi_ne_zero]

lemma e_inj : e r = e s ↔ r ≡ s [PMOD 1] := by
  simp [AddCommGroup.ModEq, ← e_eq_one, div_eq_one, map_sub_eq_div, eq_comm (b := 1),
    eq_comm (a := e r)]

end Circle

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

end ZMod
