/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Hom

/-!
# Definitions of group actions

This file defines a hierarchy of group action type-classes on top of the previously defined
notation classes `SMul` and its additive version `VAdd`:

* `SMulZeroClass` is a typeclass for an action that preserves zero
* `DistribSMul M A` is a typeclass for an action on an additive monoid (`AddZeroClass`) that
  preserves addition and zero
* `DistribMulAction M A` is a typeclass for an action of a multiplicative monoid on
  an additive monoid such that `a • (b + c) = a • b + a • c` and `a • 0 = 0`.

The hierarchy is extended further by `Module`, defined elsewhere.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

assert_not_exists Equiv.Perm.equivUnitsEnd Prod.fst_mul Ring

open Function

variable {M M₀ M₀' N A A' B α β : Type*}

section smul_zero

variable [Zero A] [SMulZeroClass M A]

/-- Pullback a zero-preserving scalar multiplication along an injective zero-preserving map.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.smulZeroClass [Zero B] [SMul M B] (f : ZeroHom B A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) :
    SMulZeroClass M B where
  smul := (· • ·)
  smul_zero c := hf <| by simp only [smul, map_zero, smul_zero]

/-- Pushforward a zero-preserving scalar multiplication along a zero-preserving map.
See note [reducible non-instances]. -/
protected abbrev ZeroHom.smulZeroClass [Zero B] [SMul M B] (f : ZeroHom A B)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) :
    SMulZeroClass M B where
  -- Porting note: `simp` no longer works here.
  smul_zero c := by rw [← map_zero f, ← smul, smul_zero]

variable (A)

/-- Each element of the scalars defines a zero-preserving map. -/
@[simps]
def SMulZeroClass.toZeroHom (x : M) :
    ZeroHom A A where
  toFun := (x • ·)
  map_zero' := smul_zero x

end smul_zero

section Zero
variable [Zero M₀] [Zero A] [SMulWithZero M₀ A] {a : M₀} {b : A}
variable [Zero M₀'] [Zero A'] [SMul M₀ A']

/-- Pullback a `SMulWithZero` structure along an injective zero-preserving homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.smulWithZero (f : ZeroHom A' A) (hf : Function.Injective f)
    (smul : ∀ (a : M₀) (b), f (a • b) = a • f b) :
    SMulWithZero M₀ A' where
  smul := (· • ·)
  zero_smul a := hf <| by simp [smul]
  smul_zero a := hf <| by simp [smul]

/-- Pushforward a `SMulWithZero` structure along a surjective zero-preserving homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Surjective.smulWithZero (f : ZeroHom A A') (hf : Function.Surjective f)
    (smul : ∀ (a : M₀) (b), f (a • b) = a • f b) :
    SMulWithZero M₀ A' where
  smul := (· • ·)
  zero_smul m := by
    rcases hf m with ⟨x, rfl⟩
    simp [← smul]
  smul_zero c := by rw [← f.map_zero, ← smul, smul_zero]

variable (A)

/-- Compose a `SMulWithZero` with a `ZeroHom`, with action `f r' • m` -/
def SMulWithZero.compHom (f : ZeroHom M₀' M₀) : SMulWithZero M₀' A where
  smul := (f · • ·)
  smul_zero m := smul_zero (f m)
  zero_smul m := by show (f 0) • m = 0; rw [map_zero, zero_smul]

end Zero

section MonoidWithZero

variable [MonoidWithZero M₀] [MonoidWithZero M₀'] [Zero A]
variable [MulActionWithZero M₀ A] [Zero A'] [SMul M₀ A'] (p : Prop) [Decidable p]

lemma Pi.single_apply_smul {ι : Type*} [DecidableEq ι] (x : A) (i j : ι) :
    (Pi.single i 1 : ι → M₀) j • x = (Pi.single i x : ι → A) j := by
  rw [single_apply, ite_smul, one_smul, zero_smul, single_apply]

/-- Pullback a `MulActionWithZero` structure along an injective zero-preserving homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.mulActionWithZero (f : ZeroHom A' A) (hf : Function.Injective f)
    (smul : ∀ (a : M₀) (b), f (a • b) = a • f b) : MulActionWithZero M₀ A' :=
  { hf.mulAction f smul, hf.smulWithZero f smul with }

/-- Pushforward a `MulActionWithZero` structure along a surjective zero-preserving homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Surjective.mulActionWithZero (f : ZeroHom A A')
    (hf : Function.Surjective f) (smul : ∀ (a : M₀) (b), f (a • b) = a • f b) :
    MulActionWithZero M₀ A' :=
  { hf.mulAction f smul, hf.smulWithZero f smul with }

variable (A)

/-- Compose a `MulActionWithZero` with a `MonoidWithZeroHom`, with action `f r' • m` -/
def MulActionWithZero.compHom (f : M₀' →*₀ M₀) : MulActionWithZero M₀' A :=
  { SMulWithZero.compHom A f.toZeroHom with
    mul_smul := fun r s m => by show f (r * s) • m = (f r) • (f s) • m; simp [mul_smul]
    one_smul := fun m => by show (f 1) • m = m; simp }

end MonoidWithZero

section DistribSMul

variable [AddZeroClass A] [DistribSMul M A]

instance AddMonoidHom.smulZeroClass [AddZeroClass B] : SMulZeroClass M (B →+ A) where
  smul r f :=
    { toFun := fun a => r • (f a)
      map_zero' := by simp only [map_zero, smul_zero]
      map_add' := fun x y => by simp only [map_add, smul_add] }
  smul_zero _ := ext fun _ => smul_zero _

/-- Pullback a distributive scalar multiplication along an injective additive monoid
homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.distribSMul [AddZeroClass B] [SMul M B] (f : B →+ A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribSMul M B :=
  { hf.smulZeroClass f.toZeroHom smul with
    smul_add := fun c x y => hf <| by simp only [smul, map_add, smul_add] }

/-- Pushforward a distributive scalar multiplication along a surjective additive monoid
homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Surjective.distribSMul [AddZeroClass B] [SMul M B] (f : A →+ B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribSMul M B :=
  { f.toZeroHom.smulZeroClass smul with
    smul_add := fun c x y => by
      rcases hf x with ⟨x, rfl⟩
      rcases hf y with ⟨y, rfl⟩
      simp only [smul_add, ← smul, ← map_add] }

variable (A)

/-- Each element of the scalars defines an additive monoid homomorphism. -/
@[simps]
def DistribSMul.toAddMonoidHom (x : M) : A →+ A :=
  { SMulZeroClass.toZeroHom A x with toFun := (x • ·), map_add' := smul_add x }

end DistribSMul

section

variable [Monoid M] [AddMonoid A] [DistribMulAction M A]

/-- Pullback a distributive multiplicative action along an injective additive monoid
homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.distribMulAction [AddMonoid B] [SMul M B] (f : B →+ A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribMulAction M B :=
  { hf.distribSMul f smul, hf.mulAction f smul with }

/-- Pushforward a distributive multiplicative action along a surjective additive monoid
homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Surjective.distribMulAction [AddMonoid B] [SMul M B] (f : A →+ B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribMulAction M B :=
  { hf.distribSMul f smul, hf.mulAction f smul with }

variable (A)

/-- Each element of the monoid defines an additive monoid homomorphism. -/
@[simps!]
def DistribMulAction.toAddMonoidHom (x : M) : A →+ A :=
  DistribSMul.toAddMonoidHom A x

variable (M)

/-- Each element of the monoid defines an additive monoid homomorphism. -/
@[simps]
def DistribMulAction.toAddMonoidEnd :
    M →* AddMonoid.End A where
  toFun := DistribMulAction.toAddMonoidHom A
  map_one' := AddMonoidHom.ext <| one_smul M
  map_mul' x y := AddMonoidHom.ext <| mul_smul x y

instance AddMonoid.nat_smulCommClass :
    SMulCommClass ℕ M
      A where smul_comm n x y := ((DistribMulAction.toAddMonoidHom A x).map_nsmul y n).symm

-- `SMulCommClass.symm` is not registered as an instance, as it would cause a loop
instance AddMonoid.nat_smulCommClass' : SMulCommClass M ℕ A :=
  SMulCommClass.symm _ _ _

end

section

variable [Monoid M] [AddGroup A] [DistribMulAction M A]

instance AddGroup.int_smulCommClass : SMulCommClass ℤ M A where
  smul_comm n x y := ((DistribMulAction.toAddMonoidHom A x).map_zsmul y n).symm

-- `SMulCommClass.symm` is not registered as an instance, as it would cause a loop
instance AddGroup.int_smulCommClass' : SMulCommClass M ℤ A :=
  SMulCommClass.symm _ _ _

end

section

variable [Monoid M] [Monoid A] [MulDistribMulAction M A]

/-- Pullback a multiplicative distributive multiplicative action along an injective monoid
homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.mulDistribMulAction [Monoid B] [SMul M B] (f : B →* A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B :=
  { hf.mulAction f smul with
    smul_mul := fun c x y => hf <| by simp only [smul, f.map_mul, smul_mul'],
    smul_one := fun c => hf <| by simp only [smul, f.map_one, smul_one] }

/-- Pushforward a multiplicative distributive multiplicative action along a surjective monoid
homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Surjective.mulDistribMulAction [Monoid B] [SMul M B] (f : A →* B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B :=
  { hf.mulAction f smul with
    smul_mul := fun c x y => by
      rcases hf x with ⟨x, rfl⟩
      rcases hf y with ⟨y, rfl⟩
      simp only [smul_mul', ← smul, ← f.map_mul],
    smul_one := fun c => by rw [← f.map_one, ← smul, smul_one] }

variable (A)

/-- Scalar multiplication by `r` as a `MonoidHom`. -/
def MulDistribMulAction.toMonoidHom (r : M) :
    A →* A where
  toFun := (r • ·)
  map_one' := smul_one r
  map_mul' := smul_mul' r

variable {A}

@[simp]
theorem MulDistribMulAction.toMonoidHom_apply (r : M) (x : A) :
    MulDistribMulAction.toMonoidHom A r x = r • x :=
  rfl

@[simp] lemma smul_pow' (r : M) (x : A) (n : ℕ) : r • x ^ n = (r • x) ^ n :=
  (MulDistribMulAction.toMonoidHom _ _).map_pow _ _

end

section

variable [Monoid M] [Group A] [MulDistribMulAction M A]

@[simp]
theorem smul_inv' (r : M) (x : A) : r • x⁻¹ = (r • x)⁻¹ :=
  (MulDistribMulAction.toMonoidHom A r).map_inv x

theorem smul_div' (r : M) (x y : A) : r • (x / y) = r • x / r • y :=
  map_div (MulDistribMulAction.toMonoidHom A r) x y

end
