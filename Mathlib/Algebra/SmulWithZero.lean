/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module algebra.smul_with_zero
! leanprover-community/mathlib commit 550b58538991c8977703fdeb7c9d51a5aa27df11
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Ring.Opposite
import Mathlib.GroupTheory.GroupAction.Opposite
import Mathlib.GroupTheory.GroupAction.Prod

/-!
# Introduce `smul_with_zero`

In analogy with the usual monoid action on a Type `M`, we introduce an action of a
`MonoidWithZero` on a Type with `0`.

In particular, for Types `R` and `M`, both containing `0`, we define `SmulWithZero R M` to
be the typeclass where the products `r • 0` and `0 • m` vanish for all `r : R` and all `m : M`.

Moreover, in the case in which `R` is a `MonoidWithZero`, we introduce the typeclass
`MulActionWithZero R M`, mimicking group actions and having an absorbing `0` in `R`.
Thus, the action is required to be compatible with

* the unit of the monoid, acting as the identity;
* the zero of the monoid_with_zero, acting as zero;
* associativity of the monoid.

We also add an `instance`:

* any `MonoidWithZero` has a `MulActionWithZero R R` acting on itself.

## Main declarations

* `smulMonoidWithZeroHom`: Scalar multiplication bundled as a morphism of monoids with zero.
-/


variable {R R' M M' : Type _}

section Zero

variable (R M)

/-- `smulWithZero` is a class consisting of a Type `R` with `0 ∈ R` and a scalar multiplication
of `R` on a Type `M` with `0`, such that the equality `r • m = 0` holds if at least one among `r`
or `m` equals `0`. -/
class SmulWithZero [Zero R] [Zero M] extends SMulZeroClass R M where
  /-- Scalar multiplication by the scalar `0` is `0`. -/
  zero_smul : ∀ m : M, (0 : R) • m = 0
#align smul_with_zero SmulWithZero

instance MulZeroClass.toSmulWithZero [MulZeroClass R] :
    SmulWithZero R R where
  smul := (· * ·)
  smul_zero := mul_zero
  zero_smul := zero_mul
#align mul_zero_class.to_smul_with_zero MulZeroClass.toSmulWithZero

/-- Like `MulZeroClass.toSmulWithZero`, but multiplies on the right. -/
instance MulZeroClass.toOppositeSmulWithZero [MulZeroClass R] :
    SmulWithZero Rᵐᵒᵖ R where
  smul := (· • ·)
  smul_zero _ := zero_mul _
  zero_smul := mul_zero
#align mul_zero_class.to_opposite_smul_with_zero MulZeroClass.toOppositeSmulWithZero

variable {M} [Zero R] [Zero M] [SmulWithZero R M]

@[simp]
theorem zero_smul (m : M) : (0 : R) • m = 0 :=
  SmulWithZero.zero_smul m
#align zero_smul zero_smul

variable {R} [Zero R'] [Zero M'] [SMul R M']

/-- Pullback a `SmulWithZero` structure along an injective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.smulWithZero (f : ZeroHom M' M) (hf : Function.Injective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) :
    SmulWithZero R M' where
  smul := (· • ·)
  zero_smul a := hf <| by simp [smul]
  smul_zero a := hf <| by simp [smul]
#align function.injective.smul_with_zero Function.Injective.smulWithZero

/-- Pushforward a `SmulWithZero` structure along a surjective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.smulWithZero (f : ZeroHom M M') (hf : Function.Surjective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) :
    SmulWithZero R M' where
  smul := (· • ·)
  zero_smul m := by
    rcases hf m with ⟨x, rfl⟩
    simp [← smul]
  smul_zero c := by rw [←f.map_zero, ←smul, smul_zero]

#align function.surjective.smul_with_zero Function.Surjective.smulWithZero

variable (M)

/-- Compose a `SmulWithZero` with a `ZeroHom`, with action `f r' • m` -/
def SmulWithZero.compHom (f : ZeroHom R' R) :
    SmulWithZero R' M where
  smul := (· • ·) ∘ f
  smul_zero m := smul_zero (f m)
  zero_smul m := by show (f 0) • m = 0 ; rw [map_zero, zero_smul]

#align smul_with_zero.comp_hom SmulWithZero.compHom

end Zero

instance AddMonoid.natSmulWithZero [AddMonoid M] :
    SmulWithZero ℕ M where
  smul_zero := _root_.nsmul_zero
  zero_smul := zero_nsmul
#align add_monoid.nat_smul_with_zero AddMonoid.natSmulWithZero

instance AddGroup.intSmulWithZero [AddGroup M] :
    SmulWithZero ℤ M where
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul
#align add_group.int_smul_with_zero AddGroup.intSmulWithZero

section MonoidWithZero

variable [MonoidWithZero R] [MonoidWithZero R'] [Zero M]

variable (R M)

/-- An action of a monoid with zero `R` on a Type `M`, also with `0`, extends `MulAction` and
is compatible with `0` (both in `R` and in `M`), with `1 ∈ R`, and with associativity of
multiplication on the monoid `M`. -/
class MulActionWithZero extends MulAction R M where
  -- these fields are copied from `SmulWithZero`, as `extends` behaves poorly
  /-- Scalar multiplication by any element send `0` to `0`. -/
  smul_zero : ∀ r : R, r • (0 : M) = 0
  /-- Scalar multiplication by the scalar `0` is `0`. -/
  zero_smul : ∀ m : M, (0 : R) • m = 0
#align mul_action_with_zero MulActionWithZero

-- see Note [lower instance priority]
instance (priority := 100) MulActionWithZero.toSmulWithZero [m : MulActionWithZero R M] :
    SmulWithZero R M :=
  { m with }
#align mul_action_with_zero.to_smul_with_zero MulActionWithZero.toSmulWithZero

/-- See also `Semiring.toModule` -/
instance MonoidWithZero.toMulActionWithZero : MulActionWithZero R R :=
  { MulZeroClass.toSmulWithZero R, Monoid.toMulAction R with }
#align monoid_with_zero.to_mul_action_with_zero MonoidWithZero.toMulActionWithZero

/-- Like `MonoidWithZero.toMulActionWithZero`, but multiplies on the right. See also
`semiring.toOppositeModule` -/
instance MonoidWithZero.toOppositeMulActionWithZero : MulActionWithZero Rᵐᵒᵖ R :=
  { MulZeroClass.toOppositeSmulWithZero R, Monoid.toOppositeMulAction R with }
#align monoid_with_zero.to_opposite_mul_action_with_zero MonoidWithZero.toOppositeMulActionWithZero

variable {R M}
variable [MulActionWithZero R M] [Zero M'] [SMul R M']

/-- Pullback a `MulActionWithZero` structure along an injective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulActionWithZero (f : ZeroHom M' M) (hf : Function.Injective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) : MulActionWithZero R M' :=
  { hf.mulAction f smul, hf.smulWithZero f smul with }
#align function.injective.mul_action_with_zero Function.Injective.mulActionWithZero

/-- Pushforward a `MulActionWithZero` structure along a surjective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulActionWithZero (f : ZeroHom M M') (hf : Function.Surjective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) : MulActionWithZero R M' :=
  { hf.mulAction f smul, hf.smulWithZero f smul with }
#align function.surjective.mul_action_with_zero Function.Surjective.mulActionWithZero

variable (M)

/-- Compose a `MulActionWithZero` with a `MonoidWithZeroHom`, with action `f r' • m` -/
def MulActionWithZero.compHom (f : R' →*₀ R) : MulActionWithZero R' M :=
  { SmulWithZero.compHom M f.toZeroHom with
    smul := (· • ·) ∘ f
    mul_smul := fun r s m => by show f (r * s) • m = (f r) • (f s) • m; simp [mul_smul]
    one_smul := fun m => by show (f 1) • m = m; simp }
#align mul_action_with_zero.comp_hom MulActionWithZero.compHom

end MonoidWithZero

section GroupWithZero

variable {α β : Type _} [GroupWithZero α] [GroupWithZero β] [MulActionWithZero α β]

theorem smul_inv₀ [SMulCommClass α β β] [IsScalarTower α β β] (c : α) (x : β) :
    (c • x)⁻¹ = c⁻¹ • x⁻¹ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp only [inv_zero, zero_smul]
  obtain rfl | hx := eq_or_ne x 0
  · simp only [inv_zero, smul_zero]
  · refine' inv_eq_of_mul_eq_one_left _
    rw [smul_mul_smul, inv_mul_cancel hc, inv_mul_cancel hx, one_smul]
#align smul_inv₀ smul_inv₀

end GroupWithZero

/-- Scalar multiplication as a monoid homomorphism with zero. -/
@[simps]
def smulMonoidWithZeroHom {α β : Type _} [MonoidWithZero α] [MulZeroOneClass β]
    [MulActionWithZero α β] [IsScalarTower α β β] [SMulCommClass α β β] : α × β →*₀ β :=
  { smulMonoidHom with map_zero' := smul_zero _ }
#align smul_monoid_with_zero_hom smulMonoidWithZeroHom
