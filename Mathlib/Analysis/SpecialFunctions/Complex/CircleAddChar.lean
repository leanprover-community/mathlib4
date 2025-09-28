/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Topology.Instances.AddCircle.Real

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
  congr; ring

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
noncomputable def rootsOfUnityAddChar (n : ℕ) [NeZero n] :
    AddChar (ZMod n) (rootsOfUnity n Circle) where
  toFun x := ⟨toUnits (ZMod.toCircle x), by ext; simp [← AddChar.map_nsmul_eq_pow]⟩
  map_zero_eq_one' := by simp
  map_add_eq_mul' _ _:= by ext; simp [AddChar.map_add_eq_mul]

@[simp] lemma rootsOfUnityAddChar_val (n : ℕ) [NeZero n] (x : ZMod n) :
    (rootsOfUnityAddChar n x).val = toCircle x := by
  rfl

end ZMod

variable (n : ℕ) [NeZero n]

/-- Interpret `n`-th roots of unity in `ℂ` as elements of the circle -/
noncomputable def rootsOfUnitytoCircle : (rootsOfUnity n ℂ) →* Circle where
  toFun := fun z => ⟨z.val.val,
    mem_sphere_zero_iff_norm.2 (Complex.norm_eq_one_of_mem_rootsOfUnity z.prop)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Equivalence of the nth roots of unity of the Circle with nth roots of unity of the complex
numbers -/
noncomputable def rootsOfUnityCircleEquiv : rootsOfUnity n Circle ≃* rootsOfUnity n ℂ where
  __ := (rootsOfUnityUnitsMulEquiv ℂ n).toMonoidHom.comp (restrictRootsOfUnity Circle.toUnits n)
  invFun z := ⟨(rootsOfUnitytoCircle n).toHomUnits z, by
    rw [mem_rootsOfUnity', MonoidHom.coe_toHomUnits, ← MonoidHom.map_pow,
      ← (rootsOfUnitytoCircle n).map_one]
    congr
    aesop⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

instance : HasEnoughRootsOfUnity Circle n := (rootsOfUnityCircleEquiv n).symm.hasEnoughRootsOfUnity

@[simp] lemma rootsOfUnityCircleEquiv_apply (w : rootsOfUnity n Circle) :
    ((rootsOfUnityCircleEquiv n w).val : ℂ) = ((w.val : Circle) : ℂ) :=
  rfl

open Real in
lemma rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val (j : ZMod n) :
    (rootsOfUnityCircleEquiv n (ZMod.rootsOfUnityAddChar n j)).val
      = Complex.exp (2 * π * I * j.val / n) := by
  simp [← ZMod.toCircle_natCast, -ZMod.natCast_val, ZMod.natCast_zmod_val]

theorem surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar (n : ℕ) [NeZero n] :
    Surjective (rootsOfUnityCircleEquiv n ∘ ZMod.rootsOfUnityAddChar n) := fun ⟨w, hw⟩ ↦ by
  obtain ⟨j, hj1, hj2⟩ := (Complex.mem_rootsOfUnity n w).mp hw
  exact ⟨j, by simp [Units.ext_iff, Subtype.ext_iff, ← hj2, ZMod.toCircle_natCast, mul_div_assoc]⟩

lemma bijective_rootsOfUnityAddChar :
    Bijective (ZMod.rootsOfUnityAddChar n) where
  left _ _ := by simp [ZMod.rootsOfUnityAddChar, ZMod.injective_toCircle.eq_iff]
  right := (surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar n).of_comp_left
    (rootsOfUnityCircleEquiv n).injective
