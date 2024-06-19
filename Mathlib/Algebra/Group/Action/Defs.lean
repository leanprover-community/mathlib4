/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.TypeTags
import Mathlib.Algebra.Opposites
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Common

#align_import group_theory.group_action.defs from "leanprover-community/mathlib"@"dad7ecf9a1feae63e6e49f07619b7087403fb8d4"

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

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {M N G A B α β γ δ : Type*}

/-! ### Faithful actions -/

/-- Typeclass for faithful actions. -/
class FaithfulVAdd (G : Type*) (P : Type*) [VAdd G P] : Prop where
  /-- Two elements `g₁` and `g₂` are equal whenever they act in the same way on all points. -/
  eq_of_vadd_eq_vadd : ∀ {g₁ g₂ : G}, (∀ p : P, g₁ +ᵥ p = g₂ +ᵥ p) → g₁ = g₂
#align has_faithful_vadd FaithfulVAdd

/-- Typeclass for faithful actions. -/
@[to_additive]
class FaithfulSMul (M : Type*) (α : Type*) [SMul M α] : Prop where
  /-- Two elements `m₁` and `m₂` are equal whenever they act in the same way on all points. -/
  eq_of_smul_eq_smul : ∀ {m₁ m₂ : M}, (∀ a : α, m₁ • a = m₂ • a) → m₁ = m₂
#align has_faithful_smul FaithfulSMul

export FaithfulSMul (eq_of_smul_eq_smul)
export FaithfulVAdd (eq_of_vadd_eq_vadd)

@[to_additive]
lemma smul_left_injective' [SMul M α] [FaithfulSMul M α] : Injective ((· • ·) : M → α → α) :=
  fun _ _ h ↦ FaithfulSMul.eq_of_smul_eq_smul (congr_fun h)
#align smul_left_injective' smul_left_injective'
#align vadd_left_injective' vadd_left_injective'

-- see Note [lower instance priority]
/-- See also `Monoid.toMulAction` and `MulZeroClass.toSMulWithZero`. -/
@[to_additive "See also `AddMonoid.toAddAction`"]
instance (priority := 910) Mul.toSMul (α : Type*) [Mul α] : SMul α α := ⟨(· * ·)⟩
#align has_mul.to_has_smul Mul.toSMul
#align has_add.to_has_vadd Add.toVAdd

@[to_additive (attr := simp)]
lemma smul_eq_mul (α : Type*) [Mul α] {a a' : α} : a • a' = a * a' := rfl
#align smul_eq_mul smul_eq_mul
#align vadd_eq_add vadd_eq_add

/-- `Monoid.toMulAction` is faithful on cancellative monoids. -/
@[to_additive " `AddMonoid.toAddAction` is faithful on additive cancellative monoids. "]
instance RightCancelMonoid.faithfulSMul [RightCancelMonoid α] : FaithfulSMul α α :=
  ⟨fun h ↦ mul_right_cancel (h 1)⟩
#align right_cancel_monoid.to_has_faithful_smul RightCancelMonoid.faithfulSMul
#align add_right_cancel_monoid.to_has_faithful_vadd AddRightCancelMonoid.faithfulVAdd

/-- Type class for additive monoid actions. -/
class AddAction (G : Type*) (P : Type*) [AddMonoid G] extends VAdd G P where
  /-- Zero is a neutral element for `+ᵥ` -/
  protected zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p
  /-- Associativity of `+` and `+ᵥ` -/
  add_vadd : ∀ (g₁ g₂ : G) (p : P), g₁ + g₂ +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)
#align add_action AddAction

/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
@[to_additive (attr := ext)]
class MulAction (α : Type*) (β : Type*) [Monoid α] extends SMul α β where
  /-- One is the neutral element for `•` -/
  protected one_smul : ∀ b : β, (1 : α) • b = b
  /-- Associativity of `•` and `*` -/
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b
#align mul_action MulAction
#align mul_action.ext MulAction.ext
#align add_action.ext_iff AddAction.ext_iff
#align mul_action.ext_iff MulAction.ext_iff
#align add_action.ext AddAction.ext

/-!
### (Pre)transitive action

`M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y` (or `g +ᵥ x = y`
for an additive action). A transitive action should furthermore have `α` nonempty.

In this section we define typeclasses `MulAction.IsPretransitive` and
`AddAction.IsPretransitive` and provide `MulAction.exists_smul_eq`/`AddAction.exists_vadd_eq`,
`MulAction.surjective_smul`/`AddAction.surjective_vadd` as public interface to access this
property. We do not provide typeclasses `*Action.IsTransitive`; users should assume
`[MulAction.IsPretransitive M α] [Nonempty α]` instead.
-/

/-- `M` acts pretransitively on `α` if for any `x y` there is `g` such that `g +ᵥ x = y`.
  A transitive action should furthermore have `α` nonempty. -/
class AddAction.IsPretransitive (M α : Type*) [VAdd M α] : Prop where
  /-- There is `g` such that `g +ᵥ x = y`. -/
  exists_vadd_eq : ∀ x y : α, ∃ g : M, g +ᵥ x = y
#align add_action.is_pretransitive AddAction.IsPretransitive

/-- `M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y`.
  A transitive action should furthermore have `α` nonempty. -/
@[to_additive]
class MulAction.IsPretransitive (M α : Type*) [SMul M α] : Prop where
  /-- There is `g` such that `g • x = y`. -/
  exists_smul_eq : ∀ x y : α, ∃ g : M, g • x = y
#align mul_action.is_pretransitive MulAction.IsPretransitive

namespace MulAction
variable (M) [SMul M α] [IsPretransitive M α]

@[to_additive]
lemma exists_smul_eq (x y : α) : ∃ m : M, m • x = y := IsPretransitive.exists_smul_eq x y
#align mul_action.exists_smul_eq MulAction.exists_smul_eq
#align add_action.exists_vadd_eq AddAction.exists_vadd_eq

@[to_additive]
lemma surjective_smul (x : α) : Surjective fun c : M ↦ c • x := exists_smul_eq M x
#align mul_action.surjective_smul MulAction.surjective_smul
#align add_action.surjective_vadd AddAction.surjective_vadd

/-- The regular action of a group on itself is transitive. -/
@[to_additive "The regular action of a group on itself is transitive."]
instance Regular.isPretransitive [Group G] : IsPretransitive G G :=
  ⟨fun x y ↦ ⟨y * x⁻¹, inv_mul_cancel_right _ _⟩⟩
#align mul_action.regular.is_pretransitive MulAction.Regular.isPretransitive
#align add_action.regular.is_pretransitive AddAction.Regular.isPretransitive

end MulAction

/-! ### Scalar tower and commuting actions -/

/-- A typeclass mixin saying that two additive actions on the same space commute. -/
class VAddCommClass (M N α : Type*) [VAdd M α] [VAdd N α] : Prop where
  /-- `+ᵥ` is left commutative -/
  vadd_comm : ∀ (m : M) (n : N) (a : α), m +ᵥ (n +ᵥ a) = n +ᵥ (m +ᵥ a)
#align vadd_comm_class VAddCommClass

/-- A typeclass mixin saying that two multiplicative actions on the same space commute. -/
@[to_additive]
class SMulCommClass (M N α : Type*) [SMul M α] [SMul N α] : Prop where
  /-- `•` is left commutative -/
  smul_comm : ∀ (m : M) (n : N) (a : α), m • n • a = n • m • a
#align smul_comm_class SMulCommClass

export MulAction (mul_smul)
export AddAction (add_vadd)
export SMulCommClass (smul_comm)
export VAddCommClass (vadd_comm)

library_note "bundled maps over different rings"/--
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
#align smul_comm_class.symm SMulCommClass.symm
#align vadd_comm_class.symm VAddCommClass.symm

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
#align smul_comm_class_self smulCommClass_self
#align vadd_comm_class_self vaddCommClass_self

/-- An instance of `VAddAssocClass M N α` states that the additive action of `M` on `α` is
determined by the additive actions of `M` on `N` and `N` on `α`. -/
class VAddAssocClass (M N α : Type*) [VAdd M N] [VAdd N α] [VAdd M α] : Prop where
  /-- Associativity of `+ᵥ` -/
  vadd_assoc : ∀ (x : M) (y : N) (z : α), x +ᵥ y +ᵥ z = x +ᵥ (y +ᵥ z)
#align vadd_assoc_class VAddAssocClass

/-- An instance of `IsScalarTower M N α` states that the multiplicative
action of `M` on `α` is determined by the multiplicative actions of `M` on `N`
and `N` on `α`. -/
@[to_additive VAddAssocClass] -- TODO auto-translating
class IsScalarTower (M N α : Type*) [SMul M N] [SMul N α] [SMul M α] : Prop where
  /-- Associativity of `•` -/
  smul_assoc : ∀ (x : M) (y : N) (z : α), (x • y) • z = x • y • z
#align is_scalar_tower IsScalarTower

@[to_additive (attr := simp)]
lemma smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarTower M N α] (x : M) (y : N)
    (z : α) : (x • y) • z = x • y • z := IsScalarTower.smul_assoc x y z
#align smul_assoc smul_assoc
#align vadd_assoc vadd_assoc

@[to_additive]
instance Semigroup.isScalarTower [Semigroup α] : IsScalarTower α α α := ⟨mul_assoc⟩
#align semigroup.is_scalar_tower Semigroup.isScalarTower
#align add_semigroup.vadd_assoc_class AddSemigroup.isScalarTower

/-- A typeclass indicating that the right (aka `AddOpposite`) and left actions by `M` on `α` are
equal, that is that `M` acts centrally on `α`. This can be thought of as a version of commutativity
for `+ᵥ`. -/
class IsCentralVAdd (M α : Type*) [VAdd M α] [VAdd Mᵃᵒᵖ α] : Prop where
  /-- The right and left actions of `M` on `α` are equal. -/
  op_vadd_eq_vadd : ∀ (m : M) (a : α), AddOpposite.op m +ᵥ a = m +ᵥ a
#align is_central_vadd IsCentralVAdd

/-- A typeclass indicating that the right (aka `MulOpposite`) and left actions by `M` on `α` are
equal, that is that `M` acts centrally on `α`. This can be thought of as a version of commutativity
for `•`. -/
@[to_additive]
class IsCentralScalar (M α : Type*) [SMul M α] [SMul Mᵐᵒᵖ α] : Prop where
  /-- The right and left actions of `M` on `α` are equal. -/
  op_smul_eq_smul : ∀ (m : M) (a : α), MulOpposite.op m • a = m • a
#align is_central_scalar IsCentralScalar

@[to_additive]
lemma IsCentralScalar.unop_smul_eq_smul {M α : Type*} [SMul M α] [SMul Mᵐᵒᵖ α]
    [IsCentralScalar M α] (m : Mᵐᵒᵖ) (a : α) : MulOpposite.unop m • a = m • a := by
  induction m using MulOpposite.rec'; exact (IsCentralScalar.op_smul_eq_smul _ a).symm
#align is_central_scalar.unop_smul_eq_smul IsCentralScalar.unop_smul_eq_smul
#align is_central_vadd.unop_vadd_eq_vadd IsCentralVAdd.unop_vadd_eq_vadd

export IsCentralVAdd (op_vadd_eq_vadd unop_vadd_eq_vadd)
export IsCentralScalar (op_smul_eq_smul unop_smul_eq_smul)

attribute [simp] IsCentralScalar.op_smul_eq_smul

-- these instances are very low priority, as there is usually a faster way to find these instances
@[to_additive]
instance (priority := 50) SMulCommClass.op_left [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵐᵒᵖ N α :=
  ⟨fun m n a ↦ by rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m a, smul_comm]⟩
#align smul_comm_class.op_left SMulCommClass.op_left
#align vadd_comm_class.op_left VAddCommClass.op_left

@[to_additive]
instance (priority := 50) SMulCommClass.op_right [SMul M α] [SMul N α] [SMul Nᵐᵒᵖ α]
    [IsCentralScalar N α] [SMulCommClass M N α] : SMulCommClass M Nᵐᵒᵖ α :=
  ⟨fun m n a ↦ by rw [← unop_smul_eq_smul n (m • a), ← unop_smul_eq_smul n a, smul_comm]⟩
#align smul_comm_class.op_right SMulCommClass.op_right
#align vadd_comm_class.op_right VAddCommClass.op_right

@[to_additive]
instance (priority := 50) IsScalarTower.op_left [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [SMul M N] [SMul Mᵐᵒᵖ N] [IsCentralScalar M N] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower Mᵐᵒᵖ N α where
  smul_assoc m n a := by rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m n, smul_assoc]
#align is_scalar_tower.op_left IsScalarTower.op_left
#align vadd_assoc_class.op_left VAddAssocClass.op_left

@[to_additive]
instance (priority := 50) IsScalarTower.op_right [SMul M α] [SMul M N] [SMul N α]
    [SMul Nᵐᵒᵖ α] [IsCentralScalar N α] [IsScalarTower M N α] : IsScalarTower M Nᵐᵒᵖ α where
  smul_assoc m n a := by
    rw [← unop_smul_eq_smul n a, ← unop_smul_eq_smul (m • n) a, MulOpposite.unop_smul, smul_assoc]
#align is_scalar_tower.op_right IsScalarTower.op_right
#align vadd_assoc_class.op_right VAddAssocClass.op_right

namespace SMul
variable [SMul M α]

/-- Auxiliary definition for `SMul.comp`, `MulAction.compHom`,
`DistribMulAction.compHom`, `Module.compHom`, etc. -/
@[to_additive (attr := simp) " Auxiliary definition for `VAdd.comp`, `AddAction.compHom`, etc. "]
def comp.smul (g : N → M) (n : N) (a : α) : α := g n • a
#align has_smul.comp.smul SMul.comp.smul
#align has_vadd.comp.vadd VAdd.comp.vadd

variable (α)

/-- An action of `M` on `α` and a function `N → M` induces an action of `N` on `α`. -/
-- See note [reducible non-instances]
-- Since this is reducible, we make sure to go via
-- `SMul.comp.smul` to prevent typeclass inference unfolding too far
@[to_additive (attr := reducible)
"An additive action of `M` on `α` and a function `N → M` induces an additive action of `N` on `α`."]
def comp (g : N → M) : SMul N α where smul := SMul.comp.smul g
#align has_smul.comp SMul.comp
#align has_vadd.comp VAdd.comp

variable {α}

/-- Given a tower of scalar actions `M → α → β`, if we use `SMul.comp`
to pull back both of `M`'s actions by a map `g : N → M`, then we obtain a new
tower of scalar actions `N → α → β`.

This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables. -/
@[to_additive
"Given a tower of additive actions `M → α → β`, if we use `SMul.comp` to pull back both of
`M`'s actions by a map `g : N → M`, then we obtain a new tower of scalar actions `N → α → β`.

This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables."]
lemma comp.isScalarTower [SMul M β] [SMul α β] [IsScalarTower M α β] (g : N → M) : by
    haveI := comp α g; haveI := comp β g; exact IsScalarTower N α β where
  __ := comp α g
  __ := comp β g
  smul_assoc n := smul_assoc (g n)
#align has_smul.comp.is_scalar_tower SMul.comp.isScalarTower
#align has_vadd.comp.vadd_assoc_class VAdd.comp.isScalarTower

/-- This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables. -/
@[to_additive
"This cannot be an instance because it can cause infinite loops whenever the `VAdd` arguments
are still metavariables."]
lemma comp.smulCommClass [SMul β α] [SMulCommClass M β α] (g : N → M) :
    haveI := comp α g
    SMulCommClass N β α where
  __ := comp α g
  smul_comm n := smul_comm (g n)
#align has_smul.comp.smul_comm_class SMul.comp.smulCommClass
#align has_vadd.comp.vadd_comm_class VAdd.comp.vaddCommClass

/-- This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables. -/
@[to_additive
"This cannot be an instance because it can cause infinite loops whenever the `VAdd` arguments
are still metavariables."]
lemma comp.smulCommClass' [SMul β α] [SMulCommClass β M α] (g : N → M) :
    haveI := comp α g
    SMulCommClass β N α where
  __ := comp α g
  smul_comm _ n := smul_comm _ (g n)
#align has_smul.comp.smul_comm_class' SMul.comp.smulCommClass'
#align has_vadd.comp.vadd_comm_class' VAdd.comp.vaddCommClass'

end SMul

section

/-- Note that the `SMulCommClass α β β` typeclass argument is usually satisfied by `Algebra α β`. -/
@[to_additive] -- Porting note: nolint to_additive_doc
lemma mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s : α) (x y : β) :
    x * s • y = s • (x * y) := (smul_comm s x y).symm
#align mul_smul_comm mul_smul_comm
#align add_vadd_comm add_vadd_comm

/-- Note that the `IsScalarTower α β β` typeclass argument is usually satisfied by `Algebra α β`. -/
@[to_additive] -- Porting note: nolint to_additive_doc
lemma smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x * y = r • (x * y) := smul_assoc r x y
#align smul_mul_assoc smul_mul_assoc
#align vadd_add_assoc vadd_add_assoc

/-- Note that the `IsScalarTower α β β` typeclass argument is usually satisfied by `Algebra α β`. -/
@[to_additive]
lemma smul_div_assoc [DivInvMonoid β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x / y = r • (x / y) := by simp [div_eq_mul_inv, smul_mul_assoc]

@[to_additive]
lemma smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ] [SMul α δ] [SMul γ δ]
    [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommClass β γ δ] (a : α) (b : β) (c : γ)
    (d : δ) : (a • b) • c • d = (a • c) • b • d := by rw [smul_assoc, smul_assoc, smul_comm b]
#align smul_smul_smul_comm smul_smul_smul_comm
#align vadd_vadd_vadd_comm vadd_vadd_vadd_comm

variable [SMul M α]

@[to_additive]
lemma Commute.smul_right [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute a (r • b) :=
  (mul_smul_comm _ _ _).trans ((congr_arg _ h).trans <| (smul_mul_assoc _ _ _).symm)
#align commute.smul_right Commute.smul_right
#align add_commute.vadd_right AddCommute.vadd_right

@[to_additive]
lemma Commute.smul_left [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute (r • a) b := (h.symm.smul_right r).symm
#align commute.smul_left Commute.smul_left
#align add_commute.vadd_left AddCommute.vadd_left

end

section
variable [Monoid M] [MulAction M α]

@[to_additive]
lemma smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b := (mul_smul _ _ _).symm
#align smul_smul smul_smul
#align vadd_vadd vadd_vadd

variable (M)

@[to_additive (attr := simp)]
lemma one_smul (b : α) : (1 : M) • b = b := MulAction.one_smul _
#align one_smul one_smul
#align zero_vadd zero_vadd

/-- `SMul` version of `one_mul_eq_id` -/
@[to_additive "`VAdd` version of `zero_add_eq_id`"]
lemma one_smul_eq_id : (((1 : M) • ·) : α → α) = id := funext <| one_smul _
#align one_smul_eq_id one_smul_eq_id
#align zero_vadd_eq_id zero_vadd_eq_id

/-- `SMul` version of `comp_mul_left` -/
@[to_additive "`VAdd` version of `comp_add_left`"]
lemma comp_smul_left (a₁ a₂ : M) : (a₁ • ·) ∘ (a₂ • ·) = (((a₁ * a₂) • ·) : α → α) :=
  funext fun _ ↦ (mul_smul _ _ _).symm
#align comp_smul_left comp_smul_left
#align comp_vadd_left comp_vadd_left

variable {M}

/-- Pullback a multiplicative action along an injective map respecting `•`.
See note [reducible non-instances]. -/
@[to_additive (attr := reducible)
    "Pullback an additive action along an injective map respecting `+ᵥ`."]
protected def Function.Injective.mulAction [SMul M β] (f : β → α) (hf : Injective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulAction M β where
  smul := (· • ·)
  one_smul x := hf <| (smul _ _).trans <| one_smul _ (f x)
  mul_smul c₁ c₂ x := hf <| by simp only [smul, mul_smul]
#align function.injective.mul_action Function.Injective.mulAction
#align function.injective.add_action Function.Injective.addAction

/-- Pushforward a multiplicative action along a surjective map respecting `•`.
See note [reducible non-instances]. -/
@[to_additive (attr := reducible)
    "Pushforward an additive action along a surjective map respecting `+ᵥ`."]
protected def Function.Surjective.mulAction [SMul M β] (f : α → β) (hf : Surjective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulAction M β where
  smul := (· • ·)
  one_smul := by simp [hf.forall, ← smul]
  mul_smul := by simp [hf.forall, ← smul, mul_smul]
#align function.surjective.mul_action Function.Surjective.mulAction
#align function.surjective.add_action Function.Surjective.addAction

/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →* S`.

See also `Function.Surjective.distribMulActionLeft` and `Function.Surjective.moduleLeft`.
-/
@[to_additive (attr := reducible)
"Push forward the action of `R` on `M` along a compatible surjective map `f : R →+ S`."]
def Function.Surjective.mulActionLeft {R S M : Type*} [Monoid R] [MulAction R M] [Monoid S]
    [SMul S M] (f : R →* S) (hf : Surjective f) (hsmul : ∀ (c) (x : M), f c • x = c • x) :
    MulAction S M where
  smul := (· • ·)
  one_smul b := by rw [← f.map_one, hsmul, one_smul]
  mul_smul := hf.forall₂.mpr fun a b x ↦ by simp only [← f.map_mul, hsmul, mul_smul]
#align function.surjective.mul_action_left Function.Surjective.mulActionLeft
#align function.surjective.add_action_left Function.Surjective.addActionLeft

section
variable (M)

/-- The regular action of a monoid on itself by left multiplication.

This is promoted to a module by `Semiring.toModule`. -/
-- see Note [lower instance priority]
@[to_additive
"The regular action of a monoid on itself by left addition.

This is promoted to an `AddTorsor` by `addGroup_is_addTorsor`."]
instance (priority := 910) Monoid.toMulAction : MulAction M M where
  smul := (· * ·)
  one_smul := one_mul
  mul_smul := mul_assoc
#align monoid.to_mul_action Monoid.toMulAction
#align add_monoid.to_add_action AddMonoid.toAddAction

@[to_additive]
instance IsScalarTower.left : IsScalarTower M M α where
  smul_assoc x y z := mul_smul x y z
#align is_scalar_tower.left IsScalarTower.left
#align vadd_assoc_class.left VAddAssocClass.left

variable {M}

/-- Note that the `IsScalarTower M α α` and `SMulCommClass M α α` typeclass arguments are
usually satisfied by `Algebra M α`. -/
@[to_additive] -- Porting note: nolint to_additive_doc
lemma smul_mul_smul [Mul α] (r s : M) (x y : α) [IsScalarTower M α α] [SMulCommClass M α α] :
    r • x * s • y = (r * s) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, ← smul_assoc, smul_eq_mul]
#align smul_mul_smul smul_mul_smul
#align vadd_add_vadd vadd_add_vadd

section Monoid
variable [Monoid N] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]

lemma smul_pow (r : M) (x : N) : ∀ n, (r • x) ^ n = r ^ n • x ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ', smul_pow _ _ n, smul_mul_smul, ← pow_succ', ← pow_succ']
#align smul_pow smul_pow

end Monoid
end

namespace MulAction

variable (M α) in
/-- Embedding of `α` into functions `M → α` induced by a multiplicative action of `M` on `α`. -/
@[to_additive
"Embedding of `α` into functions `M → α` induced by an additive action of `M` on `α`."]
def toFun : α ↪ M → α :=
  ⟨fun y x ↦ x • y, fun y₁ y₂ H ↦ one_smul M y₁ ▸ one_smul M y₂ ▸ by convert congr_fun H 1⟩
#align mul_action.to_fun MulAction.toFun
#align add_action.to_fun AddAction.toFun

@[to_additive (attr := simp)]
lemma toFun_apply (x : M) (y : α) : MulAction.toFun M α y x = x • y := rfl
#align mul_action.to_fun_apply MulAction.toFun_apply
#align add_action.to_fun_apply AddAction.toFun_apply

variable (α)

/-- A multiplicative action of `M` on `α` and a monoid homomorphism `N → M` induce
a multiplicative action of `N` on `α`.

See note [reducible non-instances]. -/
@[to_additive (attr := reducible)]
def compHom [Monoid N] (g : N →* M) : MulAction N α where
  smul := SMul.comp.smul g
  -- Porting note: was `by simp [g.map_one, MulAction.one_smul]`
  one_smul _ := by simpa [(· • ·)] using MulAction.one_smul ..
  -- Porting note: was `by simp [g.map_mul, MulAction.mul_smul]`
  mul_smul _ _ _ := by simpa [(· • ·)] using MulAction.mul_smul ..
#align mul_action.comp_hom MulAction.compHom
#align add_action.comp_hom AddAction.compHom

/-- An additive action of `M` on `α` and an additive monoid homomorphism `N → M` induce
an additive action of `N` on `α`.

See note [reducible non-instances]. -/
add_decl_doc AddAction.compHom

@[to_additive]
lemma compHom_smul_def
    {E F G : Type*} [Monoid E] [Monoid F] [MulAction F G] (f : E →* F) (a : E) (x : G) :
    letI : MulAction E G := MulAction.compHom _ f
    a • x = (f a) • x := rfl

/-- If an action is transitive, then composing this action with a surjective homomorphism gives
again a transitive action. -/
@[to_additive]
lemma isPretransitive_compHom {E F G : Type*} [Monoid E] [Monoid F] [MulAction F G]
    [IsPretransitive F G] {f : E →* F} (hf : Surjective f) :
    letI : MulAction E G := MulAction.compHom _ f
    IsPretransitive E G := by
  let _ : MulAction E G := MulAction.compHom _ f
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : F, m • x = y := exists_smul_eq F x y
  obtain ⟨e, rfl⟩ : ∃ e, f e = m := hf m
  exact ⟨e, rfl⟩

@[to_additive]
lemma IsPretransitive.of_smul_eq {M N α : Type*} [SMul M α] [SMul N α] [IsPretransitive M α]
    (f : M → N) (hf : ∀ {c : M} {x : α}, f c • x = c • x) : IsPretransitive N α where
  exists_smul_eq x y := (exists_smul_eq x y).elim fun m h ↦ ⟨f m, hf.trans h⟩

@[to_additive]
lemma IsPretransitive.of_compHom {M N α : Type*} [Monoid M] [Monoid N] [MulAction N α]
    (f : M →* N) [h : letI := compHom α f; IsPretransitive M α] : IsPretransitive N α :=
  letI := compHom α f; h.of_smul_eq f rfl

end MulAction
end

section CompatibleScalar

@[to_additive]
lemma smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N α] [SMul M α]
    [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y := by
  rw [smul_assoc, one_smul]
#align smul_one_smul smul_one_smul
#align vadd_zero_vadd vadd_zero_vadd

@[to_additive]
lemma MulAction.IsPretransitive.of_isScalarTower (M : Type*) {N α : Type*} [Monoid N] [SMul M N]
    [MulAction N α] [SMul M α] [IsScalarTower M N α] [IsPretransitive M α] : IsPretransitive N α :=
  of_smul_eq (fun x : M ↦ x • 1) (smul_one_smul N _ _)

@[to_additive (attr := simp)]
lemma smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTower M N N] (x : M) (y : N) :
    x • (1 : N) * y = x • y := by rw [smul_mul_assoc, one_mul]
#align smul_one_mul smul_one_mul
#align vadd_zero_add vadd_zero_add

@[to_additive (attr := simp)]
lemma mul_smul_one {M N} [MulOneClass N] [SMul M N] [SMulCommClass M N N] (x : M) (y : N) :
    y * x • (1 : N) = x • y := by rw [← smul_eq_mul, ← smul_comm, smul_eq_mul, mul_one]
#align mul_smul_one mul_smul_one
#align add_vadd_zero add_vadd_zero

@[to_additive]
lemma IsScalarTower.of_smul_one_mul {M N} [Monoid N] [SMul M N]
    (h : ∀ (x : M) (y : N), x • (1 : N) * y = x • y) : IsScalarTower M N N :=
  ⟨fun x y z ↦ by rw [← h, smul_eq_mul, mul_assoc, h, smul_eq_mul]⟩
#align is_scalar_tower.of_smul_one_mul IsScalarTower.of_smul_one_mul
#align vadd_assoc_class.of_vadd_zero_add VAddAssocClass.of_vadd_zero_add

@[to_additive]
lemma SMulCommClass.of_mul_smul_one {M N} [Monoid N] [SMul M N]
    (H : ∀ (x : M) (y : N), y * x • (1 : N) = x • y) : SMulCommClass M N N :=
  ⟨fun x y z ↦ by rw [← H x z, smul_eq_mul, ← H, smul_eq_mul, mul_assoc]⟩
#align smul_comm_class.of_mul_smul_one SMulCommClass.of_mul_smul_one
#align vadd_comm_class.of_add_vadd_zero VAddCommClass.of_add_vadd_zero

/-- If the multiplicative action of `M` on `N` is compatible with multiplication on `N`, then
`fun x ↦ x • 1` is a monoid homomorphism from `M` to `N`. -/
@[to_additive (attr := simps)
"If the additive action of `M` on `N` is compatible with addition on `N`, then
`fun x ↦ x +ᵥ 0` is an additive monoid homomorphism from `M` to `N`."]
def MonoidHom.smulOneHom {M N} [Monoid M] [MulOneClass N] [MulAction M N] [IsScalarTower M N N] :
    M →* N where
  toFun x := x • (1 : N)
  map_one' := one_smul _ _
  map_mul' x y := by rw [smul_one_mul, smul_smul]
#align smul_one_hom MonoidHom.smulOneHom
#align vadd_zero_hom AddMonoidHom.vaddZeroHom
#align smul_one_hom_apply MonoidHom.smulOneHom_apply
#align vadd_zero_hom_apply AddMonoidHom.vaddZeroHom_apply

/-- A monoid homomorphism between two monoids M and N can be equivalently specified by a
multiplicative action of M on N that is compatible with the multiplication on N. -/
@[to_additive
"A monoid homomorphism between two additive monoids M and N can be equivalently
specified by an additive action of M on N that is compatible with the addition on N."]
def monoidHomEquivMulActionIsScalarTower (M N) [Monoid M] [Monoid N] :
    (M →* N) ≃ {_inst : MulAction M N // IsScalarTower M N N} where
  toFun f := ⟨MulAction.compHom N f, SMul.comp.isScalarTower _⟩
  invFun := fun ⟨_, _⟩ ↦ MonoidHom.smulOneHom
  left_inv f := MonoidHom.ext fun m ↦ mul_one (f m)
  right_inv := fun ⟨_, _⟩ ↦ Subtype.ext <| MulAction.ext _ _ <| funext₂ <| smul_one_smul N

end CompatibleScalar

variable (α)

/-- The monoid of endomorphisms.

Note that this is generalized by `CategoryTheory.End` to categories other than `Type u`. -/
protected def Function.End := α → α
#align function.End Function.End

instance : Monoid (Function.End α) where
  one := id
  mul := (· ∘ ·)
  mul_assoc f g h := rfl
  mul_one f := rfl
  one_mul f := rfl
  npow n f := f^[n]
  npow_succ n f := Function.iterate_succ _ _

instance : Inhabited (Function.End α) := ⟨1⟩

variable {α}

/-- The tautological action by `Function.End α` on `α`.

This is generalized to bundled endomorphisms by:
* `Equiv.Perm.applyMulAction`
* `AddMonoid.End.applyDistribMulAction`
* `AddMonoid.End.applyModule`
* `AddAut.applyDistribMulAction`
* `MulAut.applyMulDistribMulAction`
* `LinearEquiv.applyDistribMulAction`
* `LinearMap.applyModule`
* `RingHom.applyMulSemiringAction`
* `RingAut.applyMulSemiringAction`
* `AlgEquiv.applyMulSemiringAction`
-/
instance Function.End.applyMulAction : MulAction (Function.End α) α where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align function.End.apply_mul_action Function.End.applyMulAction

@[simp] lemma Function.End.smul_def (f : Function.End α) (a : α) : f • a = f a := rfl
#align function.End.smul_def Function.End.smul_def

--TODO - This statement should be somethting like `toFun (f * g) = toFun f ∘ toFun g`
lemma Function.End.mul_def (f g : Function.End α) : (f * g) = f ∘ g := rfl

--TODO - This statement should be somethting like `toFun 1 = id`
lemma Function.End.one_def : (1 : Function.End α) = id := rfl

/-- `Function.End.applyMulAction` is faithful. -/
instance Function.End.apply_FaithfulSMul : FaithfulSMul (Function.End α) α :=
  ⟨fun {_ _} ↦ funext⟩
#align function.End.apply_has_faithful_smul Function.End.apply_FaithfulSMul

/-- The monoid hom representing a monoid action.

When `M` is a group, see `MulAction.toPermHom`. -/
def MulAction.toEndHom [Monoid M] [MulAction M α] : M →* Function.End α where
  toFun := (· • ·)
  map_one' := funext (one_smul M)
  map_mul' x y := funext (mul_smul x y)
#align mul_action.to_End_hom MulAction.toEndHom

/-- The monoid action induced by a monoid hom to `Function.End α`

See note [reducible non-instances]. -/
abbrev MulAction.ofEndHom [Monoid M] (f : M →* Function.End α) : MulAction M α :=
  MulAction.compHom α f
#align mul_action.of_End_hom MulAction.ofEndHom

/-! ### `Additive`, `Multiplicative` -/

section

open Additive Multiplicative

instance Additive.vadd [SMul α β] : VAdd (Additive α) β where vadd a := (toMul a • ·)
#align additive.has_vadd Additive.vadd

instance Multiplicative.smul [VAdd α β] : SMul (Multiplicative α) β where smul a := (toAdd a +ᵥ ·)
#align multiplicative.has_smul Multiplicative.smul

@[simp] lemma toMul_smul [SMul α β] (a) (b : β) : (toMul a : α) • b = a +ᵥ b := rfl
#align to_mul_smul toMul_smul

@[simp] lemma ofMul_vadd [SMul α β] (a : α) (b : β) : ofMul a +ᵥ b = a • b := rfl
#align of_mul_vadd ofMul_vadd

@[simp] lemma toAdd_vadd [VAdd α β] (a) (b : β) : (toAdd a : α) +ᵥ b = a • b := rfl
#align to_add_vadd toAdd_vadd

@[simp] lemma ofAdd_smul [VAdd α β] (a : α) (b : β) : ofAdd a • b = a +ᵥ b := rfl
#align of_add_smul ofAdd_smul

-- Porting note: I don't know why `one_smul` can do without an explicit α and `mul_smul` can't.
instance Additive.addAction [Monoid α] [MulAction α β] : AddAction (Additive α) β where
  zero_vadd := MulAction.one_smul
  add_vadd := MulAction.mul_smul (α := α)
#align additive.add_action Additive.addAction

instance Multiplicative.mulAction [AddMonoid α] [AddAction α β] :
    MulAction (Multiplicative α) β where
  one_smul := AddAction.zero_vadd
  mul_smul := AddAction.add_vadd (G := α)
#align multiplicative.mul_action Multiplicative.mulAction

instance Additive.addAction_isPretransitive [Monoid α] [MulAction α β]
    [MulAction.IsPretransitive α β] : AddAction.IsPretransitive (Additive α) β :=
  ⟨@MulAction.exists_smul_eq α _ _ _⟩
#align additive.add_action_is_pretransitive Additive.addAction_isPretransitive

instance Multiplicative.mulAction_isPretransitive [AddMonoid α] [AddAction α β]
    [AddAction.IsPretransitive α β] : MulAction.IsPretransitive (Multiplicative α) β :=
  ⟨@AddAction.exists_vadd_eq α _ _ _⟩
#align multiplicative.add_action_is_pretransitive Multiplicative.mulAction_isPretransitive

instance Additive.vaddCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    VAddCommClass (Additive α) (Additive β) γ :=
  ⟨@smul_comm α β _ _ _ _⟩
#align additive.vadd_comm_class Additive.vaddCommClass

instance Multiplicative.smulCommClass [VAdd α γ] [VAdd β γ] [VAddCommClass α β γ] :
    SMulCommClass (Multiplicative α) (Multiplicative β) γ :=
  ⟨@vadd_comm α β _ _ _ _⟩
#align multiplicative.smul_comm_class Multiplicative.smulCommClass

end

/-- The tautological additive action by `Additive (Function.End α)` on `α`. -/
instance AddAction.functionEnd : AddAction (Additive (Function.End α)) α := inferInstance
#align add_action.function_End AddAction.functionEnd

/-- The additive monoid hom representing an additive monoid action.

When `M` is a group, see `AddAction.toPermHom`. -/
def AddAction.toEndHom [AddMonoid M] [AddAction M α] : M →+ Additive (Function.End α) :=
  MonoidHom.toAdditive'' MulAction.toEndHom
#align add_action.to_End_hom AddAction.toEndHom

/-- The additive action induced by a hom to `Additive (Function.End α)`

See note [reducible non-instances]. -/
abbrev AddAction.ofEndHom [AddMonoid M] (f : M →+ Additive (Function.End α)) : AddAction M α :=
  AddAction.compHom α f
#align add_action.of_End_hom AddAction.ofEndHom
