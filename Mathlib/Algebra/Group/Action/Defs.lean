/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Tactic.Spread

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

Also provided are typeclasses regarding the interaction of different group actions,

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

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {M N G H α β γ δ : Type*}

attribute [to_additive Add.toVAdd /-- See also `AddMonoid.toAddAction` -/] instSMulOfMul

-- see Note [lower instance priority]
/-- See also `Monoid.toMulAction` and `MulZeroClass.toSMulWithZero`. -/
@[deprecated instSMulOfMul (since := "2025-10-18")]
def Mul.toSMul (α : Type*) [Mul α] : SMul α α := ⟨(· * ·)⟩

/-- Like `Mul.toSMul`, but multiplies on the right.

See also `Monoid.toOppositeMulAction` and `MonoidWithZero.toOppositeMulActionWithZero`. -/
@[to_additive /-- Like `Add.toVAdd`, but adds on the right.

  See also `AddMonoid.toOppositeAddAction`. -/]
instance (priority := 910) Mul.toSMulMulOpposite (α : Type*) [Mul α] : SMul αᵐᵒᵖ α where
  smul a b := b * a.unop

@[to_additive (attr := simp)]
lemma smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b := rfl

@[to_additive]
lemma op_smul_eq_mul {α : Type*} [Mul α] (a b : α) : MulOpposite.op a • b = b * a := rfl

@[to_additive (attr := simp)]
lemma MulOpposite.smul_eq_mul_unop [Mul α] (a : αᵐᵒᵖ) (b : α) : a • b = b * a.unop := rfl

/--
Type class for additive monoid actions on types, with notation `g +ᵥ p`.

The `AddAction G P` typeclass says that the additive monoid `G` acts additively on a type `P`.
More precisely this means that the action satisfies the two axioms `0 +ᵥ p = p` and
`(g₁ + g₂) +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)`. A mathematician might simply say that the additive monoid `G`
acts on `P`.

For example, if `A` is an additive group and `X` is a type, if a mathematician says
say "let `A` act on the set `X`" they will usually mean `[AddAction A X]`.
-/
class AddAction (G : Type*) (P : Type*) [AddMonoid G] extends VAdd G P where
  /-- Zero is a neutral element for `+ᵥ` -/
  protected zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p
  /-- Associativity of `+` and `+ᵥ` -/
  add_vadd : ∀ (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ g₂ +ᵥ p

/--
Type class for monoid actions on types, with notation `g • p`.

The `MulAction G P` typeclass says that the monoid `G` acts multiplicatively on a type `P`.
More precisely this means that the action satisfies the two axioms `1 • p = p` and
`(g₁ * g₂) • p = g₁ • (g₂ • p)`. A mathematician might simply say that the monoid `G`
acts on `P`.

For example, if `G` is a group and `X` is a type, if a mathematician says
say "let `G` act on the set `X`" they will probably mean  `[AddAction G X]`.
-/
@[to_additive (attr := ext)]
class MulAction (α : Type*) (β : Type*) [Monoid α] extends SMul α β where
  /-- One is the neutral element for `•` -/
  protected one_smul : ∀ b : β, (1 : α) • b = b
  /-- Associativity of `•` and `*` -/
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b

/-! ### Scalar tower and commuting actions -/

/-- A typeclass mixin saying that two additive actions on the same space commute. -/
class VAddCommClass (M N α : Type*) [VAdd M α] [VAdd N α] : Prop where
  /-- `+ᵥ` is left commutative -/
  vadd_comm : ∀ (m : M) (n : N) (a : α), m +ᵥ (n +ᵥ a) = n +ᵥ (m +ᵥ a)

/-- A typeclass mixin saying that two multiplicative actions on the same space commute. -/
@[to_additive]
class SMulCommClass (M N α : Type*) [SMul M α] [SMul N α] : Prop where
  /-- `•` is left commutative -/
  smul_comm : ∀ (m : M) (n : N) (a : α), m • n • a = n • m • a

export MulAction (mul_smul)
export AddAction (add_vadd)
export SMulCommClass (smul_comm)
export VAddCommClass (vadd_comm)

library_note2 «bundled maps over different rings» /--
Frequently, we find ourselves wanting to express a bilinear map `M →ₗ[R] N →ₗ[R] P` or an
equivalence between maps `(M →ₗ[R] N) ≃ₗ[R] (M' →ₗ[R] N')` where the maps have an associated ring
`R`. Unfortunately, using definitions like these requires that `R` satisfy `CommSemiring R`, and
not just `Semiring R`. Using `M →ₗ[R] N →+ P` and `(M →ₗ[R] N) ≃+ (M' →ₗ[R] N')` avoids this
problem, but throws away structure that is useful for when we _do_ have a commutative (semi)ring.

To avoid making this compromise, we instead state these definitions as `M →ₗ[R] N →ₗ[S] P` or
`(M →ₗ[R] N) ≃ₗ[S] (M' →ₗ[R] N')` and require `SMulCommClass S R` on the appropriate modules. When
the caller has `CommSemiring R`, they can set `S = R` and `smulCommClass_self` will populate the
instance. If the caller only has `Semiring R` they can still set either `R = ℕ` or `S = ℕ`, and
`AddCommMonoid.nat_smulCommClass` or `AddCommMonoid.nat_smulCommClass'` will populate
the typeclass, which is still sufficient to recover a `≃+` or `→+` structure.

An example of where this is used is `LinearMap.prod_equiv`.
-/

/-- Commutativity of actions is a symmetric relation. This lemma can't be an instance because this
would cause a loop in the instance search graph. -/
@[to_additive]
lemma SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass N M α where smul_comm a' a b := (smul_comm a a' b).symm

/-- Commutativity of additive actions is a symmetric relation. This lemma can't be an instance
because this would cause a loop in the instance search graph. -/
add_decl_doc VAddCommClass.symm

@[to_additive]
lemma Function.Injective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N β]
    [SMulCommClass M N β] {f : α → β} (hf : Injective f) (h₁ : ∀ (c : M) x, f (c • x) = c • f x)
    (h₂ : ∀ (c : N) x, f (c • x) = c • f x) : SMulCommClass M N α where
  smul_comm c₁ c₂ x := hf <| by simp only [h₁, h₂, smul_comm c₁ c₂ (f x)]

@[to_additive]
lemma Function.Surjective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N β]
    [SMulCommClass M N α] {f : α → β} (hf : Surjective f) (h₁ : ∀ (c : M) x, f (c • x) = c • f x)
    (h₂ : ∀ (c : N) x, f (c • x) = c • f x) : SMulCommClass M N β where
  smul_comm c₁ c₂ := hf.forall.2 fun x ↦ by simp only [← h₁, ← h₂, smul_comm c₁ c₂ x]

@[to_additive]
instance smulCommClass_self (M α : Type*) [CommMonoid M] [MulAction M α] : SMulCommClass M M α where
  smul_comm a a' b := by rw [← mul_smul, mul_comm, mul_smul]

/-- An instance of `VAddAssocClass M N α` states that the additive action of `M` on `α` is
determined by the additive actions of `M` on `N` and `N` on `α`. -/
class VAddAssocClass (M N α : Type*) [VAdd M N] [VAdd N α] [VAdd M α] : Prop where
  /-- Associativity of `+ᵥ` -/
  vadd_assoc : ∀ (x : M) (y : N) (z : α), (x +ᵥ y) +ᵥ z = x +ᵥ y +ᵥ z

/-- An instance of `IsScalarTower M N α` states that the multiplicative
action of `M` on `α` is determined by the multiplicative actions of `M` on `N`
and `N` on `α`. -/
@[to_additive]
class IsScalarTower (M N α : Type*) [SMul M N] [SMul N α] [SMul M α] : Prop where
  /-- Associativity of `•` -/
  smul_assoc : ∀ (x : M) (y : N) (z : α), (x • y) • z = x • y • z

@[to_additive (attr := simp)]
lemma smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarTower M N α] (x : M) (y : N)
    (z : α) : (x • y) • z = x • y • z := IsScalarTower.smul_assoc x y z

@[to_additive]
instance Semigroup.isScalarTower [Semigroup α] : IsScalarTower α α α := ⟨mul_assoc⟩

/-- A typeclass indicating that the right (aka `AddOpposite`) and left actions by `M` on `α` are
equal, that is that `M` acts centrally on `α`. This can be thought of as a version of commutativity
for `+ᵥ`. -/
class IsCentralVAdd (M α : Type*) [VAdd M α] [VAdd Mᵃᵒᵖ α] : Prop where
  /-- The right and left actions of `M` on `α` are equal. -/
  op_vadd_eq_vadd : ∀ (m : M) (a : α), AddOpposite.op m +ᵥ a = m +ᵥ a

/-- A typeclass indicating that the right (aka `MulOpposite`) and left actions by `M` on `α` are
equal, that is that `M` acts centrally on `α`. This can be thought of as a version of commutativity
for `•`. -/
@[to_additive]
class IsCentralScalar (M α : Type*) [SMul M α] [SMul Mᵐᵒᵖ α] : Prop where
  /-- The right and left actions of `M` on `α` are equal. -/
  op_smul_eq_smul : ∀ (m : M) (a : α), MulOpposite.op m • a = m • a

@[to_additive]
lemma IsCentralScalar.unop_smul_eq_smul {M α : Type*} [SMul M α] [SMul Mᵐᵒᵖ α]
    [IsCentralScalar M α] (m : Mᵐᵒᵖ) (a : α) : MulOpposite.unop m • a = m • a := by
  induction m; exact (IsCentralScalar.op_smul_eq_smul _ a).symm

export IsCentralVAdd (op_vadd_eq_vadd unop_vadd_eq_vadd)
export IsCentralScalar (op_smul_eq_smul unop_smul_eq_smul)

attribute [simp] IsCentralScalar.op_smul_eq_smul

-- these instances are very low priority, as there is usually a faster way to find these instances
@[to_additive]
instance (priority := 50) SMulCommClass.op_left [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵐᵒᵖ N α :=
  ⟨fun m n a ↦ by rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m a, smul_comm]⟩

@[to_additive]
instance (priority := 50) SMulCommClass.op_right [SMul M α] [SMul N α] [SMul Nᵐᵒᵖ α]
    [IsCentralScalar N α] [SMulCommClass M N α] : SMulCommClass M Nᵐᵒᵖ α :=
  ⟨fun m n a ↦ by rw [← unop_smul_eq_smul n (m • a), ← unop_smul_eq_smul n a, smul_comm]⟩

@[to_additive]
instance (priority := 50) IsScalarTower.op_left [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [SMul M N] [SMul Mᵐᵒᵖ N] [IsCentralScalar M N] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower Mᵐᵒᵖ N α where
  smul_assoc m n a := by rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m n, smul_assoc]

@[to_additive]
instance (priority := 50) IsScalarTower.op_right [SMul M α] [SMul M N] [SMul N α]
    [SMul Nᵐᵒᵖ α] [IsCentralScalar N α] [IsScalarTower M N α] : IsScalarTower M Nᵐᵒᵖ α where
  smul_assoc m n a := by
    rw [← unop_smul_eq_smul n a, ← unop_smul_eq_smul (m • n) a, MulOpposite.unop_smul, smul_assoc]

namespace SMul
variable [SMul M α]

/-- Auxiliary definition for `SMul.comp`, `MulAction.compHom`,
`DistribMulAction.compHom`, `Module.compHom`, etc. -/
@[to_additive (attr := simp) /-- Auxiliary definition for `VAdd.comp`, `AddAction.compHom`, etc. -/]
def comp.smul (g : N → M) (n : N) (a : α) : α := g n • a

variable (α)

/-- An action of `M` on `α` and a function `N → M` induces an action of `N` on `α`. -/
-- See note [reducible non-instances]
-- Since this is reducible, we make sure to go via
-- `SMul.comp.smul` to prevent typeclass inference unfolding too far
@[to_additive /-- An additive action of `M` on `α` and a function `N → M` induces an additive
action of `N` on `α`. -/]
abbrev comp (g : N → M) : SMul N α where smul := SMul.comp.smul g

variable {α}

/-- Given a tower of scalar actions `M → α → β`, if we use `SMul.comp`
to pull back both of `M`'s actions by a map `g : N → M`, then we obtain a new
tower of scalar actions `N → α → β`.

This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables. -/
@[to_additive
/-- Given a tower of additive actions `M → α → β`, if we use `SMul.comp` to pull back both of
`M`'s actions by a map `g : N → M`, then we obtain a new tower of scalar actions `N → α → β`.

This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables. -/]
lemma comp.isScalarTower [SMul M β] [SMul α β] [IsScalarTower M α β] (g : N → M) : by
    haveI := comp α g; haveI := comp β g; exact IsScalarTower N α β where
  __ := comp α g
  __ := comp β g
  smul_assoc n := smul_assoc (g n)

/-- This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables. -/
@[to_additive
/-- This cannot be an instance because it can cause infinite loops whenever the `VAdd` arguments
are still metavariables. -/]
lemma comp.smulCommClass [SMul β α] [SMulCommClass M β α] (g : N → M) :
    haveI := comp α g
    SMulCommClass N β α where
  __ := comp α g
  smul_comm n := smul_comm (g n)

/-- This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables. -/
@[to_additive
/-- This cannot be an instance because it can cause infinite loops whenever the `VAdd` arguments
are still metavariables. -/]
lemma comp.smulCommClass' [SMul β α] [SMulCommClass β M α] (g : N → M) :
    haveI := comp α g
    SMulCommClass β N α where
  __ := comp α g
  smul_comm _ n := smul_comm _ (g n)

end SMul

section

/-- Note that the `SMulCommClass α β β` typeclass argument is usually satisfied by `Algebra α β`. -/
@[to_additive]
lemma mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s : α) (x y : β) :
    x * s • y = s • (x * y) := (smul_comm s x y).symm

/-- Note that the `IsScalarTower α β β` typeclass argument is usually satisfied by `Algebra α β`. -/
@[to_additive]
lemma smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x * y = r • (x * y) := smul_assoc r x y

/-- Note that the `IsScalarTower α β β` typeclass argument is usually satisfied by `Algebra α β`. -/
@[to_additive]
lemma smul_div_assoc [DivInvMonoid β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x / y = r • (x / y) := by simp [div_eq_mul_inv, smul_mul_assoc]

@[to_additive]
lemma smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ] [SMul α δ] [SMul γ δ]
    [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommClass β γ δ] (a : α) (b : β) (c : γ)
    (d : δ) : (a • b) • c • d = (a • c) • b • d := by rw [smul_assoc, smul_assoc, smul_comm b]

/-- Note that the `IsScalarTower α β β` and `SMulCommClass α β β` typeclass arguments are usually
satisfied by `Algebra α β`. -/
@[to_additive]
lemma smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
    [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c : α) (d : β) :
    (a • b) * (c • d) = (a * c) • (b * d) := by
  have : SMulCommClass β α β := .symm ..; exact smul_smul_smul_comm a b c d

@[to_additive]
alias smul_mul_smul := smul_mul_smul_comm

/-- Note that the `IsScalarTower α β β` and `SMulCommClass α β β` typeclass arguments are usually
satisfied by `Algebra α β`. -/
@[to_additive]
lemma mul_smul_mul_comm [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
    [IsScalarTower α α β] [SMulCommClass α β β] (a b : α) (c d : β) :
    (a * b) • (c * d) = (a • c) * (b • d) := smul_smul_smul_comm a b c d

variable [SMul M α]

@[to_additive]
lemma Commute.smul_right [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute a (r • b) :=
  (mul_smul_comm _ _ _).trans ((congr_arg _ h).trans <| (smul_mul_assoc _ _ _).symm)

@[to_additive]
lemma Commute.smul_left [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute (r • a) b := (h.symm.smul_right r).symm

end

section
variable [Monoid M] [MulAction M α] {a : M}

@[to_additive]
lemma smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b := (mul_smul _ _ _).symm

variable (M)

@[to_additive (attr := simp)]
lemma one_smul (b : α) : (1 : M) • b = b := MulAction.one_smul _

/-- `SMul` version of `one_mul_eq_id` -/
@[to_additive /-- `VAdd` version of `zero_add_eq_id` -/]
lemma one_smul_eq_id : (((1 : M) • ·) : α → α) = id := funext <| one_smul _

/-- `SMul` version of `comp_mul_left` -/
@[to_additive /-- `VAdd` version of `comp_add_left` -/]
lemma comp_smul_left (a₁ a₂ : M) : (a₁ • ·) ∘ (a₂ • ·) = (((a₁ * a₂) • ·) : α → α) :=
  funext fun _ ↦ (mul_smul _ _ _).symm

variable {M}

@[to_additive (attr := simp)]
theorem smul_iterate (a : M) : ∀ n : ℕ, (a • · : α → α)^[n] = (a ^ n • ·)
  | 0 => by simp [funext_iff]
  | n + 1 => by ext; simp [smul_iterate, pow_succ, smul_smul]

@[to_additive]
lemma smul_iterate_apply (a : M) (n : ℕ) (x : α) : (a • ·)^[n] x = a ^ n • x := by
  rw [smul_iterate]

/-- Pullback a multiplicative action along an injective map respecting `•`.
See note [reducible non-instances]. -/
@[to_additive
    /-- Pullback an additive action along an injective map respecting `+ᵥ`. -/]
protected abbrev Function.Injective.mulAction [SMul M β] (f : β → α) (hf : Injective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulAction M β where
  one_smul x := hf <| (smul _ _).trans <| one_smul _ (f x)
  mul_smul c₁ c₂ x := hf <| by simp only [smul, mul_smul]

/-- Pushforward a multiplicative action along a surjective map respecting `•`.
See note [reducible non-instances]. -/
@[to_additive
    /-- Pushforward an additive action along a surjective map respecting `+ᵥ`. -/]
protected abbrev Function.Surjective.mulAction [SMul M β] (f : α → β) (hf : Surjective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulAction M β where
  one_smul := by simp [hf.forall, ← smul]
  mul_smul := by simp [hf.forall, ← smul, mul_smul]

section
variable (M)

/-- The regular action of a monoid on itself by left multiplication.

This is promoted to a module by `Semiring.toModule`. -/
-- see Note [lower instance priority]
@[to_additive
/-- The regular action of a monoid on itself by left addition.

This is promoted to an `AddTorsor` by `addGroup_is_addTorsor`. -/]
instance (priority := 910) Monoid.toMulAction : MulAction M M where
  smul := (· * ·)
  one_smul := one_mul
  mul_smul := mul_assoc

@[to_additive]
instance IsScalarTower.left : IsScalarTower M M α where
  smul_assoc x y z := mul_smul x y z

variable {M}

section Monoid
variable [Monoid N] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]

lemma smul_pow (r : M) (x : N) : ∀ n, (r • x) ^ n = r ^ n • x ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ', smul_pow _ _ n, smul_mul_smul_comm, ← pow_succ', ← pow_succ']

end Monoid

section Group
variable [Group G] [MulAction G α] {g : G} {a b : α}

@[to_additive (attr := simp)]
lemma inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a := by rw [smul_smul, inv_mul_cancel, one_smul]

@[to_additive (attr := simp)]
lemma smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a := by rw [smul_smul, mul_inv_cancel, one_smul]

@[to_additive] lemma inv_smul_eq_iff : g⁻¹ • a = b ↔ a = g • b :=
  ⟨fun h ↦ by rw [← h, smul_inv_smul], fun h ↦ by rw [h, inv_smul_smul]⟩

@[to_additive] lemma eq_inv_smul_iff : a = g⁻¹ • b ↔ g • a = b :=
  ⟨fun h ↦ by rw [h, smul_inv_smul], fun h ↦ by rw [← h, inv_smul_smul]⟩

section Mul
variable [Mul H] [MulAction G H] [SMulCommClass G H H] [IsScalarTower G H H] {a b : H}

@[simp] lemma Commute.smul_right_iff : Commute a (g • b) ↔ Commute a b :=
  ⟨fun h ↦ inv_smul_smul g b ▸ h.smul_right g⁻¹, fun h ↦ h.smul_right g⟩

@[simp] lemma Commute.smul_left_iff : Commute (g • a) b ↔ Commute a b := by
  rw [Commute.symm_iff, Commute.smul_right_iff, Commute.symm_iff]

end Mul

variable [Group H] [MulAction G H] [SMulCommClass G H H] [IsScalarTower G H H]

lemma smul_inv (g : G) (a : H) : (g • a)⁻¹ = g⁻¹ • a⁻¹ :=
  inv_eq_of_mul_eq_one_right <| by rw [smul_mul_smul_comm, mul_inv_cancel, mul_inv_cancel, one_smul]

lemma smul_zpow (g : G) (a : H) (n : ℤ) : (g • a) ^ n = g ^ n • a ^ n := by
  cases n <;> simp [smul_pow, smul_inv]

end Group
end

lemma SMulCommClass.of_commMonoid
    (A B G : Type*) [CommMonoid G] [SMul A G] [SMul B G]
    [IsScalarTower A G G] [IsScalarTower B G G] :
    SMulCommClass A B G where
  smul_comm r s x := by
    rw [← one_smul G (s • x), ← smul_assoc, ← one_smul G x, ← smul_assoc s 1 x,
      smul_comm, smul_assoc, one_smul, smul_assoc, one_smul]

lemma IsScalarTower.of_commMonoid (R₁ R : Type*)
    [Monoid R₁] [CommMonoid R] [MulAction R₁ R] [SMulCommClass R₁ R R] : IsScalarTower R₁ R R where
  smul_assoc x₁ y z := by rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← smul_comm, smul_eq_mul,
    mul_comm, ← smul_eq_mul]

lemma isScalarTower_iff_smulCommClass_of_commMonoid (R₁ R : Type*)
    [Monoid R₁] [CommMonoid R] [MulAction R₁ R] :
    SMulCommClass R₁ R R ↔ IsScalarTower R₁ R R :=
  ⟨fun _ ↦ IsScalarTower.of_commMonoid R₁ R, fun _ ↦ SMulCommClass.of_commMonoid R₁ R R⟩

end

section CompatibleScalar

@[to_additive]
lemma smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N α] [SMul M α]
    [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y := by
  rw [smul_assoc, one_smul]

@[to_additive (attr := simp)]
lemma smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTower M N N] (x : M) (y : N) :
    x • (1 : N) * y = x • y := by rw [smul_mul_assoc, one_mul]

@[to_additive (attr := simp)]
lemma mul_smul_one {M N} [MulOneClass N] [SMul M N] [SMulCommClass M N N] (x : M) (y : N) :
    y * x • (1 : N) = x • y := by rw [← smul_eq_mul, ← smul_comm, smul_eq_mul, mul_one]

@[to_additive]
lemma IsScalarTower.of_smul_one_mul {M N} [Monoid N] [SMul M N]
    (h : ∀ (x : M) (y : N), x • (1 : N) * y = x • y) : IsScalarTower M N N :=
  ⟨fun x y z ↦ by rw [← h, smul_eq_mul, mul_assoc, h, smul_eq_mul]⟩

@[to_additive]
lemma SMulCommClass.of_mul_smul_one {M N} [Monoid N] [SMul M N]
    (H : ∀ (x : M) (y : N), y * x • (1 : N) = x • y) : SMulCommClass M N N :=
  ⟨fun x y z ↦ by rw [← H x z, smul_eq_mul, ← H, smul_eq_mul, mul_assoc]⟩

/--
Let `Q / P / N / M` be a tower. If `P / N / M`, `Q / P / M` and `Q / P / N` are
scalar towers, then `Q / N / M` is also a scalar tower.
-/
@[to_additive] lemma IsScalarTower.to₁₂₄ (M N P Q)
    [SMul M N] [SMul M P] [SMul M Q] [SMul N P] [SMul N Q] [Monoid P] [MulAction P Q]
    [IsScalarTower M N P] [IsScalarTower M P Q] [IsScalarTower N P Q] : IsScalarTower M N Q where
  smul_assoc m n q := by rw [← smul_one_smul P, smul_assoc m, smul_assoc, smul_one_smul]

/--
Let `Q / P / N / M` be a tower. If `P / N / M`, `Q / N / M` and `Q / P / N` are
scalar towers, then `Q / P / M` is also a scalar tower.
-/
@[to_additive] lemma IsScalarTower.to₁₃₄ (M N P Q)
    [SMul M N] [SMul M P] [SMul M Q] [SMul P Q] [Monoid N] [MulAction N P] [MulAction N Q]
    [IsScalarTower M N P] [IsScalarTower M N Q] [IsScalarTower N P Q] : IsScalarTower M P Q where
  smul_assoc m p q := by rw [← smul_one_smul N m, smul_assoc, smul_one_smul]

/--
Let `Q / P / N / M` be a tower. If `P / N / M`, `Q / N / M` and `Q / P / M` are
scalar towers, then `Q / P / N` is also a scalar tower.
-/
@[to_additive] lemma IsScalarTower.to₂₃₄ (M N P Q)
    [SMul M N] [SMul M P] [SMul M Q] [SMul P Q] [Monoid N] [MulAction N P] [MulAction N Q]
    [IsScalarTower M N P] [IsScalarTower M N Q] [IsScalarTower M P Q]
    (h : Function.Surjective fun m : M ↦ m • (1 : N)) : IsScalarTower N P Q where
  smul_assoc n p q := by obtain ⟨m, rfl⟩ := h n; simp_rw [smul_one_smul, smul_assoc]

end CompatibleScalar

/-- Typeclass for multiplicative actions on multiplicative structures.

The key axiom here is `smul_mul : g • (x * y) = (g • x) * (g • y)`.
If `G` is a group (with group law multiplication) and `Γ` is its automorphism
group then there is a natural instance of `MulDistribMulAction Γ G`.

The axiom is also satisfied by a Galois group $Gal(L/K)$ acting on the field `L`,
but here you can use the even stronger class `MulSemiringAction`, which captures
how the action plays with both multiplication and addition. -/
@[ext]
class MulDistribMulAction (M N : Type*) [Monoid M] [Monoid N] extends MulAction M N where
  /-- Distributivity of `•` across `*` -/
  smul_mul : ∀ (r : M) (x y : N), r • (x * y) = r • x * r • y
  /-- Multiplying `1` by a scalar gives `1` -/
  smul_one : ∀ r : M, r • (1 : N) = 1

export MulDistribMulAction (smul_one)

section MulDistribMulAction
variable [Monoid M] [Monoid N] [MulDistribMulAction M N]

lemma smul_mul' (a : M) (b₁ b₂ : N) : a • (b₁ * b₂) = a • b₁ * a • b₂ :=
  MulDistribMulAction.smul_mul ..

end MulDistribMulAction

section IsCancelSMul

variable (G P : Type*)

/-- A vector addition is left-cancellative if it is pointwise injective on the left. -/
class IsLeftCancelVAdd [VAdd G P] : Prop where
  protected left_cancel' : ∀ (a : G) (b c : P), a +ᵥ b = a +ᵥ c → b = c

/-- A scalar multiplication is left-cancellative if it is pointwise injective on the left. -/
@[to_additive]
class IsLeftCancelSMul [SMul G P] : Prop where
  protected left_cancel' : ∀ (a : G) (b c : P), a • b = a • c → b = c

@[to_additive]
lemma IsLeftCancelSMul.left_cancel {G P} [SMul G P] [IsLeftCancelSMul G P] (a : G) (b c : P) :
    a • b = a • c → b = c := IsLeftCancelSMul.left_cancel' a b c

@[to_additive]
instance [LeftCancelMonoid G] : IsLeftCancelSMul G G where
  left_cancel' := IsLeftCancelMul.mul_left_cancel

/-- A vector addition is cancellative if it is pointwise injective on the left and right. -/
class IsCancelVAdd [VAdd G P] : Prop extends IsLeftCancelVAdd G P where
  protected right_cancel' : ∀ (a b : G) (c : P), a +ᵥ c = b +ᵥ c → a = b

/-- A scalar multiplication is cancellative if it is pointwise injective on the left and right. -/
@[to_additive]
class IsCancelSMul [SMul G P] : Prop extends IsLeftCancelSMul G P where
  protected right_cancel' : ∀ (a b : G) (c : P), a • c = b • c → a = b

@[to_additive]
lemma IsCancelSMul.left_cancel {G P} [SMul G P] [IsCancelSMul G P] (a : G) (b c : P) :
    a • b = a • c → b = c := IsLeftCancelSMul.left_cancel' a b c

@[to_additive]
lemma IsCancelSMul.right_cancel {G P} [SMul G P] [IsCancelSMul G P] (a b : G) (c : P) :
    a • c = b • c → a = b := IsCancelSMul.right_cancel' a b c

@[to_additive]
instance [CancelMonoid G] : IsCancelSMul G G where
  left_cancel' := IsLeftCancelMul.mul_left_cancel
  right_cancel' _ _ _ := mul_right_cancel

@[to_additive]
instance [Group G] [MulAction G P] : IsLeftCancelSMul G P where
  left_cancel' a b c h := by rw [← inv_smul_smul a b, h, inv_smul_smul]

end IsCancelSMul
