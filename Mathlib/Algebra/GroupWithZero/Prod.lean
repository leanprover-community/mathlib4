/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.GroupWithZero.Equiv
import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

/-!
# Products of monoids with zero, groups with zero

In this file we define `MonoidWithZero`, `GroupWithZero`, etc... instances for `M₀ × N₀`.

## Main declarations

* `mulMonoidWithZeroHom`: Multiplication bundled as a monoid with zero homomorphism.
* `divMonoidWithZeroHom`: Division bundled as a monoid with zero homomorphism.
-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

variable {M₀ N₀ : Type*}

namespace Prod

instance instMulZeroClass [MulZeroClass M₀] [MulZeroClass N₀] : MulZeroClass (M₀ × N₀) where
  zero_mul := by simp [Prod.mul_def]
  mul_zero := by simp [Prod.mul_def]

instance instSemigroupWithZero [SemigroupWithZero M₀] [SemigroupWithZero N₀] :
    SemigroupWithZero (M₀ × N₀) where
  zero_mul := by simp
  mul_zero := by simp

instance instMulZeroOneClass [MulZeroOneClass M₀] [MulZeroOneClass N₀] :
    MulZeroOneClass (M₀ × N₀) where
  zero_mul := by simp
  mul_zero := by simp

instance instMonoidWithZero [MonoidWithZero M₀] [MonoidWithZero N₀] : MonoidWithZero (M₀ × N₀) where
  zero_mul := by simp
  mul_zero := by simp

instance instCommMonoidWithZero [CommMonoidWithZero M₀] [CommMonoidWithZero N₀] :
    CommMonoidWithZero (M₀ × N₀) where
  zero_mul := by simp
  mul_zero := by simp

end Prod

variable (M₀) in
@[simp]
lemma WithZero.toMonoidWithZeroHom_withZeroUnitsEquiv [GroupWithZero M₀]
    [DecidablePred fun x : M₀ ↦ x = 0] :
    MonoidWithZeroHomClass.toMonoidWithZeroHom WithZero.withZeroUnitsEquiv =
      WithZero.lift' (Units.coeHom M₀) :=
  rfl

/-! ### Multiplication and division as homomorphisms -/

section BundledMulDiv

/-- Multiplication as a multiplicative homomorphism with zero. -/
@[simps]
def mulMonoidWithZeroHom [CommMonoidWithZero M₀] : M₀ × M₀ →*₀ M₀ where
  __ := mulMonoidHom
  map_zero' := mul_zero _

/-- Division as a multiplicative homomorphism with zero. -/
@[simps]
def divMonoidWithZeroHom [CommGroupWithZero M₀] : M₀ × M₀ →*₀ M₀ where
  __ := divMonoidHom
  map_zero' := zero_div _

end BundledMulDiv
