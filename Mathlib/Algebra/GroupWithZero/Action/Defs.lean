/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Action.Units
import Mathlib.Algebra.Group.Int
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Opposite
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Definitions of group actions

This file defines a hierarchy of group action type-classes on top of the previously defined
notation classes `SMul` and its additive version `VAdd`:

* `MulAction M α` and its additive version `AddAction G P` are typeclasses used for
  actions of multiplicative and additive monoids and groups; they extend notation classes
  `SMul` and `VAdd` that are defined in `Algebra.Group.Defs`;
* `DistribMulAction M A` is a typeclass for an action of a multiplicative monoid on
  an additive monoid such that `a • (b + c) = a • b + a • c` and `a • 0 = 0`.

The hierarchy is extended further by `Module`, defined elsewhere.

Also provided are typeclasses for faithful and transitive actions, and typeclasses regarding the
interaction of different group actions,

* `SMulCommClass M N α` and its additive version `VAddCommClass M N α`;
* `IsScalarTower M N α` and its additive version `VAddAssocClass M N α`;
* `IsCentralScalar M α` and its additive version `IsCentralVAdd M N α`.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.
- `a +ᵥ b` is used as notation for `VAdd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

assert_not_exists Equiv.Perm.equivUnitsEnd
assert_not_exists Prod.fst_mul
assert_not_exists Ring

open Function

variable {M M₀ M₀' N A A' B α β : Type*}

/-- `Monoid.toMulAction` is faithful on nontrivial cancellative monoids with zero. -/
instance CancelMonoidWithZero.faithfulSMul [CancelMonoidWithZero α] [Nontrivial α] :
    FaithfulSMul α α where eq_of_smul_eq_smul  h := mul_left_injective₀ one_ne_zero (h 1)

section GroupWithZero
variable [GroupWithZero α] [MulAction α β] {a : α}

@[simp] lemma inv_smul_smul₀ (ha : a ≠ 0) (x : β) : a⁻¹ • a • x = x :=
  inv_smul_smul (Units.mk0 a ha) x

@[simp]
lemma smul_inv_smul₀ (ha : a ≠ 0) (x : β) : a • a⁻¹ • x = x := smul_inv_smul (Units.mk0 a ha) x

lemma inv_smul_eq_iff₀ (ha : a ≠ 0) {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
  inv_smul_eq_iff (g := Units.mk0 a ha)

lemma eq_inv_smul_iff₀ (ha : a ≠ 0) {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
  eq_inv_smul_iff (g := Units.mk0 a ha)

@[simp]
lemma Commute.smul_right_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y : β}
    (ha : a ≠ 0) : Commute x (a • y) ↔ Commute x y := Commute.smul_right_iff (g := Units.mk0 a ha)

@[simp]
lemma Commute.smul_left_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y : β}
    (ha : a ≠ 0) : Commute (a • x) y ↔ Commute x y := Commute.smul_left_iff (g := Units.mk0 a ha)

/-- Right scalar multiplication as an order isomorphism. -/
@[simps] def Equiv.smulRight (ha : a ≠ 0) : β ≃ β where
  toFun b := a • b
  invFun b := a⁻¹ • b
  left_inv := inv_smul_smul₀ ha
  right_inv := smul_inv_smul₀ ha

end GroupWithZero

/-- Typeclass for scalar multiplication that preserves `0` on the right. -/
class SMulZeroClass (M A : Type*) [Zero A] extends SMul M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : ∀ a : M, a • (0 : A) = 0

section smul_zero

variable [Zero A] [SMulZeroClass M A]

@[simp]
theorem smul_zero (a : M) : a • (0 : A) = 0 :=
  SMulZeroClass.smul_zero _

lemma smul_ite_zero (p : Prop) [Decidable p] (a : M) (b : A) :
    (a • if p then b else 0) = if p then a • b else 0 := by split_ifs <;> simp

lemma smul_eq_zero_of_right (a : M) {b : A} (h : b = 0) : a • b = 0 := h.symm ▸ smul_zero a
lemma right_ne_zero_of_smul {a : M} {b : A} : a • b ≠ 0 → b ≠ 0 := mt <| smul_eq_zero_of_right a

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

/-- Push forward the multiplication of `R` on `M` along a compatible surjective map `f : R → S`.

See also `Function.Surjective.distribMulActionLeft`.
-/
abbrev Function.Surjective.smulZeroClassLeft {R S M : Type*} [Zero M] [SMulZeroClass R M]
    [SMul S M] (f : R → S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) :
    SMulZeroClass S M where
  smul := (· • ·)
  smul_zero := hf.forall.mpr fun c => by rw [hsmul, smul_zero]

variable (A)

/-- Compose a `SMulZeroClass` with a function, with scalar multiplication `f r' • m`.
See note [reducible non-instances]. -/
abbrev SMulZeroClass.compFun (f : N → M) :
    SMulZeroClass N A where
  smul := SMul.comp.smul f
  smul_zero x := smul_zero (f x)

/-- Each element of the scalars defines a zero-preserving map. -/
@[simps]
def SMulZeroClass.toZeroHom (x : M) :
    ZeroHom A A where
  toFun := (x • ·)
  map_zero' := smul_zero x

end smul_zero

section Zero

variable (M₀ A)

/-- `SMulWithZero` is a class consisting of a Type `M₀` with `0 ∈ M₀` and a scalar multiplication
of `M₀` on a Type `A` with `0`, such that the equality `r • m = 0` holds if at least one among `r`
or `m` equals `0`. -/
class SMulWithZero [Zero M₀] [Zero A] extends SMulZeroClass M₀ A where
  /-- Scalar multiplication by the scalar `0` is `0`. -/
  zero_smul : ∀ m : A, (0 : M₀) • m = 0

instance MulZeroClass.toSMulWithZero [MulZeroClass M₀] : SMulWithZero M₀ M₀ where
  smul := (· * ·)
  smul_zero := mul_zero
  zero_smul := zero_mul

/-- Like `MulZeroClass.toSMulWithZero`, but multiplies on the right. -/
instance MulZeroClass.toOppositeSMulWithZero [MulZeroClass M₀] : SMulWithZero M₀ᵐᵒᵖ M₀ where
  smul := (· • ·)
  smul_zero _ := zero_mul _
  zero_smul := mul_zero

variable {A} [Zero M₀] [Zero A] [SMulWithZero M₀ A]

@[simp]
theorem zero_smul (m : A) : (0 : M₀) • m = 0 :=
  SMulWithZero.zero_smul m

variable {M₀} {a : M₀} {b : A}

lemma smul_eq_zero_of_left (h : a = 0) (b : A) : a • b = 0 := h.symm ▸ zero_smul _ b
lemma left_ne_zero_of_smul : a • b ≠ 0 → a ≠ 0 := mt fun h ↦ smul_eq_zero_of_left h b

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

instance AddMonoid.natSMulWithZero [AddMonoid A] : SMulWithZero ℕ A where
  smul_zero := _root_.nsmul_zero
  zero_smul := zero_nsmul

instance AddGroup.intSMulWithZero [AddGroup A] : SMulWithZero ℤ A where
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul

section MonoidWithZero

variable [MonoidWithZero M₀] [MonoidWithZero M₀'] [Zero A]
variable (M₀ A)

/-- An action of a monoid with zero `M₀` on a Type `A`, also with `0`, extends `MulAction` and
is compatible with `0` (both in `M₀` and in `A`), with `1 ∈ M₀`, and with associativity of
multiplication on the monoid `A`. -/
class MulActionWithZero extends MulAction M₀ A where
  -- these fields are copied from `SMulWithZero`, as `extends` behaves poorly
  /-- Scalar multiplication by any element send `0` to `0`. -/
  smul_zero : ∀ r : M₀, r • (0 : A) = 0
  /-- Scalar multiplication by the scalar `0` is `0`. -/
  zero_smul : ∀ m : A, (0 : M₀) • m = 0

-- see Note [lower instance priority]
instance (priority := 100) MulActionWithZero.toSMulWithZero (M₀ A) {_ : MonoidWithZero M₀}
    {_ : Zero A} [m : MulActionWithZero M₀ A] : SMulWithZero M₀ A :=
  { m with }

/-- See also `Semiring.toModule` -/
instance MonoidWithZero.toMulActionWithZero : MulActionWithZero M₀ M₀ :=
  { MulZeroClass.toSMulWithZero M₀, Monoid.toMulAction M₀ with }

/-- Like `MonoidWithZero.toMulActionWithZero`, but multiplies on the right. See also
`Semiring.toOppositeModule` -/
instance MonoidWithZero.toOppositeMulActionWithZero : MulActionWithZero M₀ᵐᵒᵖ M₀ :=
  { MulZeroClass.toOppositeSMulWithZero M₀, Monoid.toOppositeMulAction with }

protected lemma MulActionWithZero.subsingleton
    [MulActionWithZero M₀ A] [Subsingleton M₀] : Subsingleton A :=
  ⟨fun x y => by
    rw [← one_smul M₀ x, ← one_smul M₀ y, Subsingleton.elim (1 : M₀) 0, zero_smul, zero_smul]⟩

protected lemma MulActionWithZero.nontrivial
    [MulActionWithZero M₀ A] [Nontrivial A] : Nontrivial M₀ :=
  (subsingleton_or_nontrivial M₀).resolve_left fun _ =>
    not_subsingleton A <| MulActionWithZero.subsingleton M₀ A

variable {M₀ A}
variable [MulActionWithZero M₀ A] [Zero A'] [SMul M₀ A'] (p : Prop) [Decidable p]

lemma ite_zero_smul (a : M₀) (b : A) : (if p then a else 0 : M₀) • b = if p then a • b else 0 := by
  rw [ite_smul, zero_smul]

lemma boole_smul (a : A) : (if p then 1 else 0 : M₀) • a = if p then a else 0 := by simp

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

section GroupWithZero

variable {α β : Type*} [GroupWithZero α] [GroupWithZero β] [MulActionWithZero α β]

theorem smul_inv₀ [SMulCommClass α β β] [IsScalarTower α β β] (c : α) (x : β) :
    (c • x)⁻¹ = c⁻¹ • x⁻¹ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp only [inv_zero, zero_smul]
  obtain rfl | hx := eq_or_ne x 0
  · simp only [inv_zero, smul_zero]
  · refine inv_eq_of_mul_eq_one_left ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, inv_mul_cancel₀ hx, one_smul]

end GroupWithZero

/-- Typeclass for scalar multiplication that preserves `0` and `+` on the right.

This is exactly `DistribMulAction` without the `MulAction` part.
-/
@[ext]
class DistribSMul (M A : Type*) [AddZeroClass A] extends SMulZeroClass M A where
  /-- Scalar multiplication distributes across addition -/
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y

section DistribSMul

variable [AddZeroClass A] [DistribSMul M A]

theorem smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
  DistribSMul.smul_add _ _ _

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

/-- Push forward the multiplication of `R` on `M` along a compatible surjective map `f : R → S`.

See also `Function.Surjective.distribMulActionLeft`.
-/
abbrev Function.Surjective.distribSMulLeft {R S M : Type*} [AddZeroClass M] [DistribSMul R M]
    [SMul S M] (f : R → S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : DistribSMul S M :=
  { hf.smulZeroClassLeft f hsmul with
    smul_add := hf.forall.mpr fun c x y => by simp only [hsmul, smul_add] }

variable (A)

/-- Compose a `DistribSMul` with a function, with scalar multiplication `f r' • m`.
See note [reducible non-instances]. -/
abbrev DistribSMul.compFun (f : N → M) : DistribSMul N A :=
  { SMulZeroClass.compFun A f with
    smul_add := fun x => smul_add (f x) }

/-- Each element of the scalars defines an additive monoid homomorphism. -/
@[simps]
def DistribSMul.toAddMonoidHom (x : M) : A →+ A :=
  { SMulZeroClass.toZeroHom A x with toFun := (· • ·) x, map_add' := smul_add x }

end DistribSMul

/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
@[ext]
class DistribMulAction (M A : Type*) [Monoid M] [AddMonoid A] extends MulAction M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : ∀ a : M, a • (0 : A) = 0
  /-- Scalar multiplication distributes across addition -/
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y

section

variable [Monoid M] [AddMonoid A] [DistribMulAction M A]

-- See note [lower instance priority]
instance (priority := 100) DistribMulAction.toDistribSMul : DistribSMul M A :=
  { ‹DistribMulAction M A› with }

-- Porting note: this probably is no longer relevant.
/-! Since Lean 3 does not have definitional eta for structures, we have to make sure
that the definition of `DistribMulAction.toDistribSMul` was done correctly,
and the two paths from `DistribMulAction` to `SMul` are indeed definitionally equal. -/
example :
    (DistribMulAction.toMulAction.toSMul : SMul M A) =
      DistribMulAction.toDistribSMul.toSMul :=
  rfl

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

/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →* S`.

See also `Function.Surjective.mulActionLeft` and `Function.Surjective.moduleLeft`.
-/
abbrev Function.Surjective.distribMulActionLeft {R S M : Type*} [Monoid R] [AddMonoid M]
    [DistribMulAction R M] [Monoid S] [SMul S M] (f : R →* S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : DistribMulAction S M :=
  { hf.distribSMulLeft f hsmul, hf.mulActionLeft f hsmul with }

variable (A)

/-- Compose a `DistribMulAction` with a `MonoidHom`, with action `f r' • m`.
See note [reducible non-instances]. -/
abbrev DistribMulAction.compHom [Monoid N] (f : N →* M) : DistribMulAction N A :=
  { DistribSMul.compFun A f, MulAction.compHom A f with }

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

@[simp]
theorem smul_neg (r : M) (x : A) : r • -x = -(r • x) :=
  eq_neg_of_add_eq_zero_left <| by rw [← smul_add, neg_add_cancel, smul_zero]

theorem smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, smul_add, smul_neg]

end

/-- Typeclass for multiplicative actions on multiplicative structures. This generalizes
conjugation actions. -/
@[ext]
class MulDistribMulAction (M : Type*) (A : Type*) [Monoid M] [Monoid A] extends
  MulAction M A where
  /-- Distributivity of `•` across `*` -/
  smul_mul : ∀ (r : M) (x y : A), r • (x * y) = r • x * r • y
  /-- Multiplying `1` by a scalar gives `1` -/
  smul_one : ∀ r : M, r • (1 : A) = 1

export MulDistribMulAction (smul_one)

section

variable [Monoid M] [Monoid A] [MulDistribMulAction M A]

theorem smul_mul' (a : M) (b₁ b₂ : A) : a • (b₁ * b₂) = a • b₁ * a • b₂ :=
  MulDistribMulAction.smul_mul _ _ _

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

/-- Compose a `MulDistribMulAction` with a `MonoidHom`, with action `f r' • m`.
See note [reducible non-instances]. -/
abbrev MulDistribMulAction.compHom [Monoid N] (f : N →* M) : MulDistribMulAction N A :=
  { MulAction.compHom A f with
    smul_one := fun x => smul_one (f x),
    smul_mul := fun x => smul_mul' (f x) }

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

variable (M A)

/-- Each element of the monoid defines a monoid homomorphism. -/
@[simps]
def MulDistribMulAction.toMonoidEnd :
    M →* Monoid.End A where
  toFun := MulDistribMulAction.toMonoidHom A
  map_one' := MonoidHom.ext <| one_smul M
  map_mul' x y := MonoidHom.ext <| mul_smul x y

end

section

variable [Monoid M] [Group A] [MulDistribMulAction M A]

@[simp]
theorem smul_inv' (r : M) (x : A) : r • x⁻¹ = (r • x)⁻¹ :=
  (MulDistribMulAction.toMonoidHom A r).map_inv x

theorem smul_div' (r : M) (x y : A) : r • (x / y) = r • x / r • y :=
  map_div (MulDistribMulAction.toMonoidHom A r) x y

end

/-- The tautological action by `AddMonoid.End α` on `α`.

This generalizes `Function.End.applyMulAction`. -/
instance AddMonoid.End.applyDistribMulAction [AddMonoid α] :
    DistribMulAction (AddMonoid.End α) α where
  smul := (· <| ·)
  smul_zero := AddMonoidHom.map_zero
  smul_add := AddMonoidHom.map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
theorem AddMonoid.End.smul_def [AddMonoid α] (f : AddMonoid.End α) (a : α) : f • a = f a :=
  rfl

/-- `AddMonoid.End.applyDistribMulAction` is faithful. -/
instance AddMonoid.End.applyFaithfulSMul [AddMonoid α] :
    FaithfulSMul (AddMonoid.End α) α :=
  ⟨fun {_ _ h} => AddMonoidHom.ext h⟩

/-- Each non-zero element of a `GroupWithZero` defines an additive monoid isomorphism of an
`AddMonoid` on which it acts distributively.
This is a stronger version of `DistribMulAction.toAddMonoidHom`. -/
def DistribMulAction.toAddEquiv₀ {α : Type*} (β : Type*) [GroupWithZero α] [AddMonoid β]
    [DistribMulAction α β] (x : α) (hx : x ≠ 0) : β ≃+ β :=
  { DistribMulAction.toAddMonoidHom β x with
    invFun := fun b ↦ x⁻¹ • b
    left_inv := fun b ↦ inv_smul_smul₀ hx b
    right_inv := fun b ↦ smul_inv_smul₀ hx b }

section Group
variable [Group α] [AddMonoid β] [DistribMulAction α β]

lemma smul_eq_zero_iff_eq (a : α) {x : β} : a • x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← inv_smul_smul a x, h, smul_zero], fun h => h.symm ▸ smul_zero _⟩

lemma smul_ne_zero_iff_ne (a : α) {x : β} : a • x ≠ 0 ↔ x ≠ 0 :=
  not_congr <| smul_eq_zero_iff_eq a

end Group
