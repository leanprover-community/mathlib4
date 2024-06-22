/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.GroupWithZero.Prod
import Mathlib.Algebra.Ring.Opposite
import Mathlib.GroupTheory.GroupAction.Opposite
import Mathlib.GroupTheory.GroupAction.Prod

#align_import algebra.smul_with_zero from "leanprover-community/mathlib"@"966e0cf0685c9cedf8a3283ac69eef4d5f2eaca2"

/-!
# Introduce `SMulWithZero`

In analogy with the usual monoid action on a Type `M`, we introduce an action of a
`MonoidWithZero` on a Type with `0`.

In particular, for Types `R` and `M`, both containing `0`, we define `SMulWithZero R M` to
be the typeclass where the products `r • 0` and `0 • m` vanish for all `r : R` and all `m : M`.

Moreover, in the case in which `R` is a `MonoidWithZero`, we introduce the typeclass
`MulActionWithZero R M`, mimicking group actions and having an absorbing `0` in `R`.
Thus, the action is required to be compatible with

* the unit of the monoid, acting as the identity;
* the zero of the `MonoidWithZero`, acting as zero;
* associativity of the monoid.

We also add an `instance`:

* any `MonoidWithZero` has a `MulActionWithZero R R` acting on itself.

## Main declarations

* `smulMonoidWithZeroHom`: Scalar multiplication bundled as a morphism of monoids with zero.
-/


variable {R R' M M' : Type*}

section Zero

variable (R M)

/-- `SMulWithZero` is a class consisting of a Type `R` with `0 ∈ R` and a scalar multiplication
of `R` on a Type `M` with `0`, such that the equality `r • m = 0` holds if at least one among `r`
or `m` equals `0`. -/
class SMulWithZero [Zero R] [Zero M] extends SMulZeroClass R M where
  /-- Scalar multiplication by the scalar `0` is `0`. -/
  zero_smul : ∀ m : M, (0 : R) • m = 0
#align smul_with_zero SMulWithZero

instance MulZeroClass.toSMulWithZero [MulZeroClass R] : SMulWithZero R R where
  smul := (· * ·)
  smul_zero := mul_zero
  zero_smul := zero_mul
#align mul_zero_class.to_smul_with_zero MulZeroClass.toSMulWithZero

/-- Like `MulZeroClass.toSMulWithZero`, but multiplies on the right. -/
instance MulZeroClass.toOppositeSMulWithZero [MulZeroClass R] : SMulWithZero Rᵐᵒᵖ R where
  smul := (· • ·)
  smul_zero _ := zero_mul _
  zero_smul := mul_zero
#align mul_zero_class.to_opposite_smul_with_zero MulZeroClass.toOppositeSMulWithZero

variable {M} [Zero R] [Zero M] [SMulWithZero R M]

@[simp]
theorem zero_smul (m : M) : (0 : R) • m = 0 :=
  SMulWithZero.zero_smul m
#align zero_smul zero_smul

variable {R} {a : R} {b : M}

lemma smul_eq_zero_of_left (h : a = 0) (b : M) : a • b = 0 := h.symm ▸ zero_smul _ b
#align smul_eq_zero_of_left smul_eq_zero_of_left
lemma left_ne_zero_of_smul : a • b ≠ 0 → a ≠ 0 := mt fun h ↦ smul_eq_zero_of_left h b
#align left_ne_zero_of_smul left_ne_zero_of_smul

variable [Zero R'] [Zero M'] [SMul R M']

/-- Pullback a `SMulWithZero` structure along an injective zero-preserving homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.smulWithZero (f : ZeroHom M' M) (hf : Function.Injective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) :
    SMulWithZero R M' where
  smul := (· • ·)
  zero_smul a := hf <| by simp [smul]
  smul_zero a := hf <| by simp [smul]
#align function.injective.smul_with_zero Function.Injective.smulWithZero

/-- Pushforward a `SMulWithZero` structure along a surjective zero-preserving homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Surjective.smulWithZero (f : ZeroHom M M') (hf : Function.Surjective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) :
    SMulWithZero R M' where
  smul := (· • ·)
  zero_smul m := by
    rcases hf m with ⟨x, rfl⟩
    simp [← smul]
  smul_zero c := by rw [← f.map_zero, ← smul, smul_zero]
#align function.surjective.smul_with_zero Function.Surjective.smulWithZero

variable (M)

/-- Compose a `SMulWithZero` with a `ZeroHom`, with action `f r' • m` -/
def SMulWithZero.compHom (f : ZeroHom R' R) : SMulWithZero R' M where
  smul := (f · • ·)
  smul_zero m := smul_zero (f m)
  zero_smul m := by show (f 0) • m = 0; rw [map_zero, zero_smul]
#align smul_with_zero.comp_hom SMulWithZero.compHom

end Zero

instance AddMonoid.natSMulWithZero [AddMonoid M] : SMulWithZero ℕ M where
  smul_zero := _root_.nsmul_zero
  zero_smul := zero_nsmul
#align add_monoid.nat_smul_with_zero AddMonoid.natSMulWithZero

instance AddGroup.intSMulWithZero [AddGroup M] : SMulWithZero ℤ M where
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul
#align add_group.int_smul_with_zero AddGroup.intSMulWithZero

section MonoidWithZero

variable [MonoidWithZero R] [MonoidWithZero R'] [Zero M]
variable (R M)

/-- An action of a monoid with zero `R` on a Type `M`, also with `0`, extends `MulAction` and
is compatible with `0` (both in `R` and in `M`), with `1 ∈ R`, and with associativity of
multiplication on the monoid `M`. -/
class MulActionWithZero extends MulAction R M where
  -- these fields are copied from `SMulWithZero`, as `extends` behaves poorly
  /-- Scalar multiplication by any element send `0` to `0`. -/
  smul_zero : ∀ r : R, r • (0 : M) = 0
  /-- Scalar multiplication by the scalar `0` is `0`. -/
  zero_smul : ∀ m : M, (0 : R) • m = 0
#align mul_action_with_zero MulActionWithZero

-- see Note [lower instance priority]
instance (priority := 100) MulActionWithZero.toSMulWithZero [m : MulActionWithZero R M] :
    SMulWithZero R M :=
  { m with }
#align mul_action_with_zero.to_smul_with_zero MulActionWithZero.toSMulWithZero

/-- See also `Semiring.toModule` -/
instance MonoidWithZero.toMulActionWithZero : MulActionWithZero R R :=
  { MulZeroClass.toSMulWithZero R, Monoid.toMulAction R with }
#align monoid_with_zero.to_mul_action_with_zero MonoidWithZero.toMulActionWithZero

/-- Like `MonoidWithZero.toMulActionWithZero`, but multiplies on the right. See also
`Semiring.toOppositeModule` -/
instance MonoidWithZero.toOppositeMulActionWithZero : MulActionWithZero Rᵐᵒᵖ R :=
  { MulZeroClass.toOppositeSMulWithZero R, Monoid.toOppositeMulAction with }
#align monoid_with_zero.to_opposite_mul_action_with_zero MonoidWithZero.toOppositeMulActionWithZero

protected lemma MulActionWithZero.subsingleton
    [MulActionWithZero R M] [Subsingleton R] : Subsingleton M :=
  ⟨fun x y => by
    rw [← one_smul R x, ← one_smul R y, Subsingleton.elim (1 : R) 0, zero_smul, zero_smul]⟩
#align mul_action_with_zero.subsingleton MulActionWithZero.subsingleton

protected lemma MulActionWithZero.nontrivial
    [MulActionWithZero R M] [Nontrivial M] : Nontrivial R :=
  (subsingleton_or_nontrivial R).resolve_left fun _ =>
    not_subsingleton M <| MulActionWithZero.subsingleton R M
#align mul_action_with_zero.nontrivial MulActionWithZero.nontrivial

variable {R M}
variable [MulActionWithZero R M] [Zero M'] [SMul R M'] (p : Prop) [Decidable p]

lemma ite_zero_smul (a : R) (b : M) : (if p then a else 0 : R) • b = if p then a • b else 0 := by
  rw [ite_smul, zero_smul]

lemma boole_smul (a : M) : (if p then 1 else 0 : R) • a = if p then a else 0 := by simp

/-- Pullback a `MulActionWithZero` structure along an injective zero-preserving homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.mulActionWithZero (f : ZeroHom M' M) (hf : Function.Injective f)
    (smul : ∀ (a : R) (b), f (a • b) = a • f b) : MulActionWithZero R M' :=
  { hf.mulAction f smul, hf.smulWithZero f smul with }
#align function.injective.mul_action_with_zero Function.Injective.mulActionWithZero

/-- Pushforward a `MulActionWithZero` structure along a surjective zero-preserving homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Surjective.mulActionWithZero (f : ZeroHom M M')
    (hf : Function.Surjective f) (smul : ∀ (a : R) (b), f (a • b) = a • f b) :
    MulActionWithZero R M' :=
  { hf.mulAction f smul, hf.smulWithZero f smul with }
#align function.surjective.mul_action_with_zero Function.Surjective.mulActionWithZero

variable (M)

/-- Compose a `MulActionWithZero` with a `MonoidWithZeroHom`, with action `f r' • m` -/
def MulActionWithZero.compHom (f : R' →*₀ R) : MulActionWithZero R' M :=
  { SMulWithZero.compHom M f.toZeroHom with
    mul_smul := fun r s m => by show f (r * s) • m = (f r) • (f s) • m; simp [mul_smul]
    one_smul := fun m => by show (f 1) • m = m; simp }
#align mul_action_with_zero.comp_hom MulActionWithZero.compHom

end MonoidWithZero

section GroupWithZero

variable {α β : Type*} [GroupWithZero α] [GroupWithZero β] [MulActionWithZero α β]

theorem smul_inv₀ [SMulCommClass α β β] [IsScalarTower α β β] (c : α) (x : β) :
    (c • x)⁻¹ = c⁻¹ • x⁻¹ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp only [inv_zero, zero_smul]
  obtain rfl | hx := eq_or_ne x 0
  · simp only [inv_zero, smul_zero]
  · refine inv_eq_of_mul_eq_one_left ?_
    rw [smul_mul_smul, inv_mul_cancel hc, inv_mul_cancel hx, one_smul]
#align smul_inv₀ smul_inv₀

end GroupWithZero

/-- Scalar multiplication as a monoid homomorphism with zero. -/
@[simps]
def smulMonoidWithZeroHom {α β : Type*} [MonoidWithZero α] [MulZeroOneClass β]
    [MulActionWithZero α β] [IsScalarTower α β β] [SMulCommClass α β β] : α × β →*₀ β :=
  { smulMonoidHom with map_zero' := smul_zero _ }
#align smul_monoid_with_zero_hom smulMonoidWithZeroHom
#align smul_monoid_with_zero_hom_apply smulMonoidWithZeroHom_apply

-- This instance seems a bit incongruous in this file, but `#find_home!` told me to put it here.
instance NonUnitalNonAssocSemiring.toDistribSMul [NonUnitalNonAssocSemiring R] :
    DistribSMul R R where
  smul_add := mul_add
