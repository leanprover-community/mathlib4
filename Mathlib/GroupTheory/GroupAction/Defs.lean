/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import Mathlib.Algebra.Group.TypeTags
import Mathlib.Algebra.Group.Commute
import Mathlib.Algebra.Hom.Group
import Mathlib.Algebra.Opposites
import Mathlib.Logic.Embedding.Basic

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


variable {M N G A B α β γ δ : Type*}

open Function (Injective Surjective)

/-!
### Faithful actions
-/


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
theorem smul_left_injective' [SMul M α] [FaithfulSMul M α] :
    Function.Injective ((· • ·) : M → α → α) := fun _ _ h =>
  FaithfulSMul.eq_of_smul_eq_smul (congr_fun h)
#align smul_left_injective' smul_left_injective'
#align vadd_left_injective' vadd_left_injective'

-- see Note [lower instance priority]
/-- See also `Monoid.toMulAction` and `MulZeroClass.toSMulWithZero`. -/
@[to_additive "See also `AddMonoid.toAddAction`"]
instance (priority := 910) Mul.toSMul (α : Type*) [Mul α] : SMul α α :=
  ⟨(· * ·)⟩
#align has_mul.to_has_smul Mul.toSMul
#align has_add.to_has_vadd Add.toVAdd

@[to_additive (attr := simp)]
theorem smul_eq_mul (α : Type*) [Mul α] {a a' : α} : a • a' = a * a' :=
  rfl
#align smul_eq_mul smul_eq_mul
#align vadd_eq_add vadd_eq_add

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
`[MulAction.IsPretransitive M α] [Nonempty α]` instead. -/


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
theorem exists_smul_eq (x y : α) : ∃ m : M, m • x = y :=
  IsPretransitive.exists_smul_eq x y
#align mul_action.exists_smul_eq MulAction.exists_smul_eq
#align add_action.exists_vadd_eq AddAction.exists_vadd_eq

@[to_additive]
theorem surjective_smul (x : α) : Surjective fun c : M => c • x :=
  exists_smul_eq M x
#align mul_action.surjective_smul MulAction.surjective_smul
#align add_action.surjective_vadd AddAction.surjective_vadd

/-- The regular action of a group on itself is transitive. -/
@[to_additive "The regular action of a group on itself is transitive."]
instance Regular.isPretransitive [Group G] : IsPretransitive G G :=
  ⟨fun x y => ⟨y * x⁻¹, inv_mul_cancel_right _ _⟩⟩
#align mul_action.regular.is_pretransitive MulAction.Regular.isPretransitive
#align add_action.regular.is_pretransitive AddAction.Regular.isPretransitive

end MulAction

/-!
### Scalar tower and commuting actions
-/


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
theorem SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass N M α :=
  ⟨fun a' a b => (smul_comm a a' b).symm⟩
#align smul_comm_class.symm SMulCommClass.symm
#align vadd_comm_class.symm VAddCommClass.symm

/-- Commutativity of additive actions is a symmetric relation. This lemma can't be an instance
because this would cause a loop in the instance search graph. -/
add_decl_doc VAddCommClass.symm

theorem Function.Injective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N β]
    [SMulCommClass M N β] {f : α → β} (hf : Function.Injective f)
    (h₁ : ∀ (c : M) x, f (c • x) = c • f x) (h₂ : ∀ (c : N) x, f (c • x) = c • f x) :
    SMulCommClass M N α where
  smul_comm c₁ c₂ x := hf <| by simp only [h₁, h₂, smul_comm c₁ c₂ (f x)]
                                -- 🎉 no goals

theorem Function.Surjective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N β]
    [SMulCommClass M N α] {f : α → β} (hf : Function.Surjective f)
    (h₁ : ∀ (c : M) x, f (c • x) = c • f x) (h₂ : ∀ (c : N) x, f (c • x) = c • f x) :
    SMulCommClass M N β where
  smul_comm c₁ c₂ := hf.forall.2 fun x ↦ by simp only [← h₁, ← h₂, smul_comm c₁ c₂ x]
                                            -- 🎉 no goals

@[to_additive]
instance smulCommClass_self (M α : Type*) [CommMonoid M] [MulAction M α] : SMulCommClass M M α :=
  ⟨fun a a' b => by rw [← mul_smul, mul_comm, mul_smul]⟩
                    -- 🎉 no goals
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
theorem smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarTower M N α] (x : M)
    (y : N) (z : α) : (x • y) • z = x • y • z :=
  IsScalarTower.smul_assoc x y z
#align smul_assoc smul_assoc
#align vadd_assoc vadd_assoc

@[to_additive]
instance Semigroup.isScalarTower [Semigroup α] : IsScalarTower α α α :=
  ⟨mul_assoc⟩
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

attribute [simp] IsCentralScalar.op_smul_eq_smul

@[to_additive]
theorem IsCentralScalar.unop_smul_eq_smul {M α : Type*} [SMul M α] [SMul Mᵐᵒᵖ α]
    [IsCentralScalar M α] (m : Mᵐᵒᵖ) (a : α) : MulOpposite.unop m • a = m • a := by
  induction m using MulOpposite.rec'
  -- ⊢ MulOpposite.unop (MulOpposite.op X✝) • a = MulOpposite.op X✝ • a
  exact (IsCentralScalar.op_smul_eq_smul _ a).symm
  -- 🎉 no goals
#align is_central_scalar.unop_smul_eq_smul IsCentralScalar.unop_smul_eq_smul
#align is_central_vadd.unop_vadd_eq_vadd IsCentralVAdd.unop_vadd_eq_vadd

export IsCentralVAdd (op_vadd_eq_vadd unop_vadd_eq_vadd)

export IsCentralScalar (op_smul_eq_smul unop_smul_eq_smul)

-- these instances are very low priority, as there is usually a faster way to find these instances
@[to_additive]
instance (priority := 50) SMulCommClass.op_left [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵐᵒᵖ N α :=
  ⟨fun m n a => by rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m a, smul_comm]⟩
                   -- 🎉 no goals
#align smul_comm_class.op_left SMulCommClass.op_left
#align vadd_comm_class.op_left VAddCommClass.op_left

@[to_additive]
instance (priority := 50) SMulCommClass.op_right [SMul M α] [SMul N α] [SMul Nᵐᵒᵖ α]
    [IsCentralScalar N α] [SMulCommClass M N α] : SMulCommClass M Nᵐᵒᵖ α :=
  ⟨fun m n a => by rw [← unop_smul_eq_smul n (m • a), ← unop_smul_eq_smul n a, smul_comm]⟩
                   -- 🎉 no goals
#align smul_comm_class.op_right SMulCommClass.op_right
#align vadd_comm_class.op_right VAddCommClass.op_right

@[to_additive]
instance (priority := 50) IsScalarTower.op_left [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [SMul M N] [SMul Mᵐᵒᵖ N] [IsCentralScalar M N] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower Mᵐᵒᵖ N α :=
  ⟨fun m n a => by rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m n, smul_assoc]⟩
                   -- 🎉 no goals
#align is_scalar_tower.op_left IsScalarTower.op_left
#align vadd_assoc_class.op_left VAddAssocClass.op_left

@[to_additive]
instance (priority := 50) IsScalarTower.op_right [SMul M α] [SMul M N] [SMul N α]
    [SMul Nᵐᵒᵖ α] [IsCentralScalar N α] [IsScalarTower M N α] : IsScalarTower M Nᵐᵒᵖ α :=
  ⟨fun m n a => by
    rw [← unop_smul_eq_smul n a, ← unop_smul_eq_smul (m • n) a, MulOpposite.unop_smul, smul_assoc]⟩
    -- 🎉 no goals
#align is_scalar_tower.op_right IsScalarTower.op_right
#align vadd_assoc_class.op_right VAddAssocClass.op_right

namespace SMul

variable [SMul M α]

/-- Auxiliary definition for `SMul.comp`, `MulAction.compHom`,
`DistribMulAction.compHom`, `Module.compHom`, etc. -/
@[to_additive (attr := simp) " Auxiliary definition for `VAdd.comp`, `AddAction.compHom`, etc. "]
def comp.smul (g : N → M) (n : N) (a : α) : α :=
  g n • a
#align has_smul.comp.smul SMul.comp.smul
#align has_vadd.comp.vadd VAdd.comp.vadd

variable (α)

/-- An action of `M` on `α` and a function `N → M` induces an action of `N` on `α`.

See note [reducible non-instances]. Since this is reducible, we make sure to go via
`SMul.comp.smul` to prevent typeclass inference unfolding too far. -/
@[to_additive (attr := reducible)
      "An additive action of `M` on `α` and a function `N → M` induces
       an additive action of `N` on `α` "]
def comp (g : N → M) : SMul N α where smul := SMul.comp.smul g
#align has_smul.comp SMul.comp
#align has_vadd.comp VAdd.comp

variable {α}

/-- Given a tower of scalar actions `M → α → β`, if we use `SMul.comp`
to pull back both of `M`'s actions by a map `g : N → M`, then we obtain a new
tower of scalar actions `N → α → β`.

This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables.
-/
@[to_additive
      "Given a tower of additive actions `M → α → β`, if we use `SMul.comp` to pull back both of
       `M`'s actions by a map `g : N → M`, then we obtain a new tower of scalar actions `N → α → β`.

       This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
       are still metavariables."]
theorem comp.isScalarTower [SMul M β] [SMul α β] [IsScalarTower M α β] (g : N → M) : by
    haveI := comp α g; haveI := comp β g; exact IsScalarTower N α β :=
    -- ⊢ Sort ?u.10323
                       -- ⊢ Sort ?u.10323
                                          -- 🎉 no goals
  { comp α g, comp β g with
    smul_assoc := fun n => smul_assoc (g n) }
#align has_smul.comp.is_scalar_tower SMul.comp.isScalarTower
#align has_vadd.comp.vadd_assoc_class VAdd.comp.isScalarTower

/-- This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables.
-/
@[to_additive
      "This cannot be an instance because it can cause infinite loops whenever the `VAdd` arguments
       are still metavariables."]
theorem comp.smulCommClass [SMul β α] [SMulCommClass M β α] (g : N → M) :
    haveI := comp α g
    SMulCommClass N β α :=
  { comp α g with
    smul_comm := fun n => smul_comm (g n) }
#align has_smul.comp.smul_comm_class SMul.comp.smulCommClass
#align has_vadd.comp.vadd_comm_class VAdd.comp.vaddCommClass

/-- This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables.
-/
@[to_additive
      "This cannot be an instance because it can cause infinite loops whenever the `VAdd` arguments
       are still metavariables."]
theorem comp.smulCommClass' [SMul β α] [SMulCommClass β M α] (g : N → M) :
    haveI := comp α g
    SMulCommClass β N α :=
  { comp α g with
    smul_comm := fun _ n => smul_comm _ (g n) }
#align has_smul.comp.smul_comm_class' SMul.comp.smulCommClass'
#align has_vadd.comp.vadd_comm_class' VAdd.comp.vaddCommClass'

end SMul

section

/-- Note that the `SMulCommClass α β β` typeclass argument is usually satisfied by `Algebra α β`.
-/
@[to_additive] -- Porting note: nolint to_additive_doc
theorem mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s : α) (x y : β) :
    x * s • y = s • (x * y) :=
  (smul_comm s x y).symm
#align mul_smul_comm mul_smul_comm
#align add_vadd_comm add_vadd_comm

/-- Note that the `IsScalarTower α β β` typeclass argument is usually satisfied by `Algebra α β`.
-/
@[to_additive] -- Porting note: nolint to_additive_doc
theorem smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x * y = r • (x * y) :=
  smul_assoc r x y
#align smul_mul_assoc smul_mul_assoc
#align vadd_add_assoc vadd_add_assoc

@[to_additive]
theorem smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ] [SMul α δ] [SMul γ δ]
    [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommClass β γ δ] (a : α) (b : β) (c : γ)
    (d : δ) : (a • b) • c • d = (a • c) • b • d := by
  rw [smul_assoc, smul_assoc, smul_comm b]
  -- 🎉 no goals
#align smul_smul_smul_comm smul_smul_smul_comm
#align vadd_vadd_vadd_comm vadd_vadd_vadd_comm

variable [SMul M α]

@[to_additive]
theorem Commute.smul_right [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute a (r • b) :=
  (mul_smul_comm _ _ _).trans ((congr_arg _ h).trans <| (smul_mul_assoc _ _ _).symm)
#align commute.smul_right Commute.smul_right
#align add_commute.vadd_right AddCommute.vadd_right

@[to_additive]
theorem Commute.smul_left [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute (r • a) b :=
  (h.symm.smul_right r).symm
#align commute.smul_left Commute.smul_left
#align add_commute.vadd_left AddCommute.vadd_left

end

section ite

variable [SMul M α] (p : Prop) [Decidable p]

@[to_additive]
theorem ite_smul (a₁ a₂ : M) (b : α) : ite p a₁ a₂ • b = ite p (a₁ • b) (a₂ • b) := by
  split_ifs <;> rfl
  -- ⊢ a₁ • b = a₁ • b
                -- 🎉 no goals
                -- 🎉 no goals
#align ite_smul ite_smul
#align ite_vadd ite_vadd

@[to_additive]
theorem smul_ite (a : M) (b₁ b₂ : α) : a • ite p b₁ b₂ = ite p (a • b₁) (a • b₂) := by
  split_ifs <;> rfl
  -- ⊢ a • b₁ = a • b₁
                -- 🎉 no goals
                -- 🎉 no goals
#align smul_ite smul_ite
#align vadd_ite vadd_ite

end ite

section

variable [Monoid M] [MulAction M α]

@[to_additive]
theorem smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b :=
  (mul_smul _ _ _).symm
#align smul_smul smul_smul
#align vadd_vadd vadd_vadd

variable (M)

@[to_additive (attr := simp)]
theorem one_smul (b : α) : (1 : M) • b = b :=
  MulAction.one_smul _
#align one_smul one_smul
#align zero_vadd zero_vadd

/-- `SMul` version of `one_mul_eq_id` -/
@[to_additive "`VAdd` version of `zero_add_eq_id`"]
theorem one_smul_eq_id : ((· • ·) (1 : M) : α → α) = id :=
  funext <| one_smul _
#align one_smul_eq_id one_smul_eq_id
#align zero_vadd_eq_id zero_vadd_eq_id

/-- `SMul` version of `comp_mul_left` -/
@[to_additive "`VAdd` version of `comp_add_left`"]
theorem comp_smul_left (a₁ a₂ : M) : (· • ·) a₁ ∘ (· • ·) a₂ = ((· • ·) (a₁ * a₂) : α → α) :=
  funext fun _ => (mul_smul _ _ _).symm
#align comp_smul_left comp_smul_left
#align comp_vadd_left comp_vadd_left

variable {M}

/-- Pullback a multiplicative action along an injective map respecting `•`.
See note [reducible non-instances]. -/
@[to_additive (attr := reducible)
    "Pullback an additive action along an injective map respecting `+ᵥ`."]
protected def Function.Injective.mulAction [SMul M β] (f : β → α) (hf : Injective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) :
    MulAction M β where
  smul := (· • ·)
  one_smul x := hf <| (smul _ _).trans <| one_smul _ (f x)
  mul_smul c₁ c₂ x := hf <| by simp only [smul, mul_smul]
                               -- 🎉 no goals
#align function.injective.mul_action Function.Injective.mulAction
#align function.injective.add_action Function.Injective.addAction

/-- Pushforward a multiplicative action along a surjective map respecting `•`.
See note [reducible non-instances]. -/
@[to_additive (attr := reducible)
    "Pushforward an additive action along a surjective map respecting `+ᵥ`."]
protected def Function.Surjective.mulAction [SMul M β] (f : α → β) (hf : Surjective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) :
    MulAction M β where
  smul := (· • ·)
  one_smul y := by
    rcases hf y with ⟨x, rfl⟩
    -- ⊢ 1 • f x = f x
    rw [← smul, one_smul]
    -- 🎉 no goals
  mul_smul c₁ c₂ y := by
    rcases hf y with ⟨x, rfl⟩
    -- ⊢ (c₁ * c₂) • f x = c₁ • c₂ • f x
    simp only [← smul, mul_smul]
    -- 🎉 no goals
#align function.surjective.mul_action Function.Surjective.mulAction
#align function.surjective.add_action Function.Surjective.addAction

/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →* S`.

See also `Function.Surjective.distribMulActionLeft` and `Function.Surjective.moduleLeft`.
-/
@[to_additive (attr := reducible)
    "Push forward the action of `R` on `M` along a compatible surjective map `f : R →+ S`."]
def Function.Surjective.mulActionLeft {R S M : Type*} [Monoid R] [MulAction R M] [Monoid S]
    [SMul S M] (f : R →* S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) :
    MulAction S M where
  smul := (· • ·)
  one_smul b := by rw [← f.map_one, hsmul, one_smul]
                   -- 🎉 no goals
  mul_smul := hf.forall₂.mpr fun a b x => by simp only [← f.map_mul, hsmul, mul_smul]
                                             -- 🎉 no goals
#align function.surjective.mul_action_left Function.Surjective.mulActionLeft
#align function.surjective.add_action_left Function.Surjective.addActionLeft

section

variable (M)

-- see Note [lower instance priority]
/-- The regular action of a monoid on itself by left multiplication.

This is promoted to a module by `Semiring.toModule`. -/
@[to_additive]
instance (priority := 910) Monoid.toMulAction :
    MulAction M M where
  smul := (· * ·)
  one_smul := one_mul
  mul_smul := mul_assoc
#align monoid.to_mul_action Monoid.toMulAction
#align add_monoid.to_add_action AddMonoid.toAddAction

/-- The regular action of a monoid on itself by left addition.

This is promoted to an `AddTorsor` by `addGroup_is_addTorsor`. -/
add_decl_doc AddMonoid.toAddAction

@[to_additive]
instance IsScalarTower.left : IsScalarTower M M α :=
  ⟨fun x y z => mul_smul x y z⟩
#align is_scalar_tower.left IsScalarTower.left
#align vadd_assoc_class.left VAddAssocClass.left

variable {M}

/-- Note that the `IsScalarTower M α α` and `SMulCommClass M α α` typeclass arguments are
usually satisfied by `Algebra M α`. -/
@[to_additive] -- Porting note: nolint to_additive_doc
theorem smul_mul_smul [Mul α] (r s : M) (x y : α) [IsScalarTower M α α] [SMulCommClass M α α] :
    r • x * s • y = (r * s) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, ← smul_assoc, smul_eq_mul]
  -- 🎉 no goals
#align smul_mul_smul smul_mul_smul
#align vadd_add_vadd vadd_add_vadd

end

namespace MulAction

variable (M α)

/-- Embedding of `α` into functions `M → α` induced by a multiplicative action of `M` on `α`. -/
@[to_additive]
def toFun : α ↪ M → α :=
  ⟨fun y x => x • y, fun y₁ y₂ H => one_smul M y₁ ▸ one_smul M y₂ ▸ by convert congr_fun H 1⟩
                                                                       -- 🎉 no goals
#align mul_action.to_fun MulAction.toFun
#align add_action.to_fun AddAction.toFun

/-- Embedding of `α` into functions `M → α` induced by an additive action of `M` on `α`. -/
add_decl_doc AddAction.toFun

variable {M α}

@[to_additive (attr := simp)]
theorem toFun_apply (x : M) (y : α) : MulAction.toFun M α y x = x • y :=
  rfl
#align mul_action.to_fun_apply MulAction.toFun_apply
#align add_action.to_fun_apply AddAction.toFun_apply

variable (α)

/-- A multiplicative action of `M` on `α` and a monoid homomorphism `N → M` induce
a multiplicative action of `N` on `α`.

See note [reducible non-instances]. -/
@[to_additive (attr := reducible)]
def compHom [Monoid N] (g : N →* M) :
    MulAction N α where
  smul := SMul.comp.smul g
  -- Porting note: was `by simp [g.map_one, MulAction.one_smul]`
  one_smul _ := by simp [(· • ·)]; apply MulAction.one_smul
                   -- ⊢ SMul.smul 1 x✝ = x✝
                                   -- 🎉 no goals
  -- Porting note: was `by simp [g.map_mul, MulAction.mul_smul]`
  mul_smul _ _ _ := by simp [(· • ·)]; apply MulAction.mul_smul
                       -- ⊢ SMul.smul (↑g x✝² * ↑g x✝¹) x✝ = SMul.smul (↑g x✝²) (SMul.smul (↑g x✝¹) x✝)
                                       -- 🎉 no goals
#align mul_action.comp_hom MulAction.compHom
#align add_action.comp_hom AddAction.compHom

/-- An additive action of `M` on `α` and an additive monoid homomorphism `N → M` induce
an additive action of `N` on `α`.

See note [reducible non-instances]. -/
add_decl_doc AddAction.compHom

end MulAction

end

section CompatibleScalar

@[to_additive]
theorem smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N α] [SMul M α]
    [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y := by
  rw [smul_assoc, one_smul]
  -- 🎉 no goals
#align smul_one_smul smul_one_smul
#align vadd_zero_vadd vadd_zero_vadd

@[to_additive (attr := simp)]
theorem smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTower M N N] (x : M) (y : N) :
    x • (1 : N) * y = x • y := by rw [smul_mul_assoc, one_mul]
                                  -- 🎉 no goals
#align smul_one_mul smul_one_mul
#align vadd_zero_add vadd_zero_add

@[to_additive (attr := simp)]
theorem mul_smul_one {M N} [MulOneClass N] [SMul M N] [SMulCommClass M N N] (x : M) (y : N) :
    y * x • (1 : N) = x • y := by rw [← smul_eq_mul, ← smul_comm, smul_eq_mul, mul_one]
                                  -- 🎉 no goals
#align mul_smul_one mul_smul_one
#align add_vadd_zero add_vadd_zero

@[to_additive]
theorem IsScalarTower.of_smul_one_mul {M N} [Monoid N] [SMul M N]
    (h : ∀ (x : M) (y : N), x • (1 : N) * y = x • y) : IsScalarTower M N N :=
  ⟨fun x y z => by rw [← h, smul_eq_mul, mul_assoc, h, smul_eq_mul]⟩
                   -- 🎉 no goals
#align is_scalar_tower.of_smul_one_mul IsScalarTower.of_smul_one_mul
#align vadd_assoc_class.of_vadd_zero_add VAddAssocClass.of_vadd_zero_add

@[to_additive]
theorem SMulCommClass.of_mul_smul_one {M N} [Monoid N] [SMul M N]
    (H : ∀ (x : M) (y : N), y * x • (1 : N) = x • y) : SMulCommClass M N N :=
  ⟨fun x y z => by rw [← H x z, smul_eq_mul, ← H, smul_eq_mul, mul_assoc]⟩
                   -- 🎉 no goals
#align smul_comm_class.of_mul_smul_one SMulCommClass.of_mul_smul_one
#align vadd_comm_class.of_add_vadd_zero VAddCommClass.of_add_vadd_zero

/-- If the multiplicative action of `M` on `N` is compatible with multiplication on `N`, then
`fun x => x • 1` is a monoid homomorphism from `M` to `N`. -/
@[to_additive (attr := simps)
    "If the additive action of `M` on `N` is compatible with addition on `N`, then
    `fun x => x +ᵥ 0` is an additive monoid homomorphism from `M` to `N`."]
def smulOneHom {M N} [Monoid M] [Monoid N] [MulAction M N] [IsScalarTower M N N] :
    M →* N where
  toFun x := x • (1 : N)
  map_one' := one_smul _ _
  map_mul' x y := by rw [smul_one_mul, smul_smul]
                     -- 🎉 no goals
#align smul_one_hom smulOneHom
#align vadd_zero_hom vaddZeroHom
#align smul_one_hom_apply smulOneHom_apply
#align vadd_zero_hom_apply vaddZeroHom_apply

end CompatibleScalar

/-- Typeclass for scalar multiplication that preserves `0` on the right. -/
class SMulZeroClass (M A : Type*) [Zero A] extends SMul M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : ∀ a : M, a • (0 : A) = 0
#align smul_zero_class SMulZeroClass

section smul_zero

variable [Zero A] [SMulZeroClass M A]

@[simp]
theorem smul_zero (a : M) : a • (0 : A) = 0 :=
  SMulZeroClass.smul_zero _
#align smul_zero smul_zero

/-- Pullback a zero-preserving scalar multiplication along an injective zero-preserving map.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.smulZeroClass [Zero B] [SMul M B] (f : ZeroHom B A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) :
    SMulZeroClass M B where
  smul := (· • ·)
  smul_zero c := hf <| by simp only [smul, map_zero, smul_zero]
                          -- 🎉 no goals
#align function.injective.smul_zero_class Function.Injective.smulZeroClass

/-- Pushforward a zero-preserving scalar multiplication along a zero-preserving map.
See note [reducible non-instances]. -/
@[reducible]
protected def ZeroHom.smulZeroClass [Zero B] [SMul M B] (f : ZeroHom A B)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) :
    SMulZeroClass M B where
  -- Porting note: `simp` no longer works here.
  smul_zero c := by rw [← map_zero f, ← smul, smul_zero]
                    -- 🎉 no goals
#align zero_hom.smul_zero_class ZeroHom.smulZeroClass

/-- Push forward the multiplication of `R` on `M` along a compatible surjective map `f : R → S`.

See also `Function.Surjective.distribMulActionLeft`.
-/
@[reducible]
def Function.Surjective.smulZeroClassLeft {R S M : Type*} [Zero M] [SMulZeroClass R M]
    [SMul S M] (f : R → S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) :
    SMulZeroClass S M where
  smul := (· • ·)
  smul_zero := hf.forall.mpr fun c => by rw [hsmul, smul_zero]
                                         -- 🎉 no goals
#align function.surjective.smul_zero_class_left Function.Surjective.smulZeroClassLeft

variable (A)

/-- Compose a `SMulZeroClass` with a function, with scalar multiplication `f r' • m`.
See note [reducible non-instances]. -/
@[reducible]
def SMulZeroClass.compFun (f : N → M) :
    SMulZeroClass N A where
  smul := SMul.comp.smul f
  smul_zero x := smul_zero (f x)
#align smul_zero_class.comp_fun SMulZeroClass.compFun

/-- Each element of the scalars defines a zero-preserving map. -/
@[simps]
def SMulZeroClass.toZeroHom (x : M) :
    ZeroHom A A where
  toFun := (· • ·) x
  map_zero' := smul_zero x
#align smul_zero_class.to_zero_hom SMulZeroClass.toZeroHom
#align smul_zero_class.to_zero_hom_apply SMulZeroClass.toZeroHom_apply

end smul_zero

/-- Typeclass for scalar multiplication that preserves `0` and `+` on the right.

This is exactly `DistribMulAction` without the `MulAction` part.
-/
@[ext]
class DistribSMul (M A : Type*) [AddZeroClass A] extends SMulZeroClass M A where
  /-- Scalar multiplication distributes across addition -/
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y
#align distrib_smul DistribSMul
#align distrib_smul.ext DistribSMul.ext
#align distrib_smul.ext_iff DistribSMul.ext_iff

section DistribSMul

variable [AddZeroClass A] [DistribSMul M A]

theorem smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
  DistribSMul.smul_add _ _ _
#align smul_add smul_add

instance AddMonoidHom.smulZeroClass [AddZeroClass B] : SMulZeroClass M (B →+ A) where
  smul r f :=
    { toFun := (fun a => r • (f a))
      map_zero' := by simp only [map_zero, smul_zero]
                      -- 🎉 no goals
      map_add' := fun x y => by simp only [map_add, smul_add] }
                                -- 🎉 no goals
  smul_zero r := ext fun _ => smul_zero _

/-- Pullback a distributive scalar multiplication along an injective additive monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.distribSMul [AddZeroClass B] [SMul M B] (f : B →+ A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribSMul M B :=
  { hf.smulZeroClass f.toZeroHom smul with
    smul := (· • ·),
    smul_add := fun c x y => hf <| by simp only [smul, map_add, smul_add] }
                                      -- 🎉 no goals
#align function.injective.distrib_smul Function.Injective.distribSMul

/-- Pushforward a distributive scalar multiplication along a surjective additive monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.distribSMul [AddZeroClass B] [SMul M B] (f : A →+ B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribSMul M B :=
  { f.toZeroHom.smulZeroClass smul with
    smul := (· • ·),
    smul_add := fun c x y => by
      rcases hf x with ⟨x, rfl⟩
      -- ⊢ c • (↑f x + y) = c • ↑f x + c • y
      rcases hf y with ⟨y, rfl⟩
      -- ⊢ c • (↑f x + ↑f y) = c • ↑f x + c • ↑f y
      simp only [smul_add, ← smul, ← map_add] }
      -- 🎉 no goals
#align function.surjective.distrib_smul Function.Surjective.distribSMul

/-- Push forward the multiplication of `R` on `M` along a compatible surjective map `f : R → S`.

See also `Function.Surjective.distribMulActionLeft`.
-/
@[reducible]
def Function.Surjective.distribSMulLeft {R S M : Type*} [AddZeroClass M] [DistribSMul R M]
    [SMul S M] (f : R → S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : DistribSMul S M :=
  { hf.smulZeroClassLeft f hsmul with
    smul := (· • ·),
    smul_add := hf.forall.mpr fun c x y => by simp only [hsmul, smul_add] }
                                              -- 🎉 no goals
#align function.surjective.distrib_smul_left Function.Surjective.distribSMulLeft

variable (A)

/-- Compose a `DistribSMul` with a function, with scalar multiplication `f r' • m`.
See note [reducible non-instances]. -/
@[reducible]
def DistribSMul.compFun (f : N → M) : DistribSMul N A :=
  { SMulZeroClass.compFun A f with
    smul := SMul.comp.smul f,
    smul_add := fun x => smul_add (f x) }
#align distrib_smul.comp_fun DistribSMul.compFun

/-- Each element of the scalars defines an additive monoid homomorphism. -/
@[simps]
def DistribSMul.toAddMonoidHom (x : M) : A →+ A :=
  { SMulZeroClass.toZeroHom A x with toFun := (· • ·) x, map_add' := smul_add x }
#align distrib_smul.to_add_monoid_hom DistribSMul.toAddMonoidHom
#align distrib_smul.to_add_monoid_hom_apply DistribSMul.toAddMonoidHom_apply

end DistribSMul

/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
@[ext]
class DistribMulAction (M A : Type*) [Monoid M] [AddMonoid A] extends MulAction M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : ∀ a : M, a • (0 : A) = 0
  /-- Scalar multiplication distributes across addition -/
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y
#align distrib_mul_action DistribMulAction
#align distrib_mul_action.ext DistribMulAction.ext
#align distrib_mul_action.ext_iff DistribMulAction.ext_iff

section

variable [Monoid M] [AddMonoid A] [DistribMulAction M A]

-- See note [lower instance priority]
instance (priority := 100) DistribMulAction.toDistribSMul : DistribSMul M A :=
  { ‹DistribMulAction M A› with }
#align distrib_mul_action.to_distrib_smul DistribMulAction.toDistribSMul

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
@[reducible]
protected def Function.Injective.distribMulAction [AddMonoid B] [SMul M B] (f : B →+ A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribMulAction M B :=
  { hf.distribSMul f smul, hf.mulAction f smul with smul := (· • ·) }
#align function.injective.distrib_mul_action Function.Injective.distribMulAction

/-- Pushforward a distributive multiplicative action along a surjective additive monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.distribMulAction [AddMonoid B] [SMul M B] (f : A →+ B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribMulAction M B :=
  { hf.distribSMul f smul, hf.mulAction f smul with smul := (· • ·) }
#align function.surjective.distrib_mul_action Function.Surjective.distribMulAction

/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →* S`.

See also `Function.Surjective.mulActionLeft` and `Function.Surjective.moduleLeft`.
-/
@[reducible]
def Function.Surjective.distribMulActionLeft {R S M : Type*} [Monoid R] [AddMonoid M]
    [DistribMulAction R M] [Monoid S] [SMul S M] (f : R →* S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : DistribMulAction S M :=
  { hf.distribSMulLeft f hsmul, hf.mulActionLeft f hsmul with smul := (· • ·) }
#align function.surjective.distrib_mul_action_left Function.Surjective.distribMulActionLeft

variable (A)

/-- Compose a `DistribMulAction` with a `MonoidHom`, with action `f r' • m`.
See note [reducible non-instances]. -/
@[reducible]
def DistribMulAction.compHom [Monoid N] (f : N →* M) : DistribMulAction N A :=
  { DistribSMul.compFun A f, MulAction.compHom A f with smul := SMul.comp.smul f }
#align distrib_mul_action.comp_hom DistribMulAction.compHom

/-- Each element of the monoid defines an additive monoid homomorphism. -/
@[simps!]
def DistribMulAction.toAddMonoidHom (x : M) : A →+ A :=
  DistribSMul.toAddMonoidHom A x
#align distrib_mul_action.to_add_monoid_hom DistribMulAction.toAddMonoidHom
#align distrib_mul_action.to_add_monoid_hom_apply DistribMulAction.toAddMonoidHom_apply

variable (M)

/-- Each element of the monoid defines an additive monoid homomorphism. -/
@[simps]
def DistribMulAction.toAddMonoidEnd :
    M →* AddMonoid.End A where
  toFun := DistribMulAction.toAddMonoidHom A
  map_one' := AddMonoidHom.ext <| one_smul M
  map_mul' x y := AddMonoidHom.ext <| mul_smul x y
#align distrib_mul_action.to_add_monoid_End DistribMulAction.toAddMonoidEnd
#align distrib_mul_action.to_add_monoid_End_apply DistribMulAction.toAddMonoidEnd_apply

instance AddMonoid.nat_smulCommClass :
    SMulCommClass ℕ M
      A where smul_comm n x y := ((DistribMulAction.toAddMonoidHom A x).map_nsmul y n).symm
#align add_monoid.nat_smul_comm_class AddMonoid.nat_smulCommClass

-- `SMulCommClass.symm` is not registered as an instance, as it would cause a loop
instance AddMonoid.nat_smulCommClass' : SMulCommClass M ℕ A :=
  SMulCommClass.symm _ _ _
#align add_monoid.nat_smul_comm_class' AddMonoid.nat_smulCommClass'

end

section

variable [Monoid M] [AddGroup A] [DistribMulAction M A]

instance AddGroup.int_smulCommClass : SMulCommClass ℤ M A where
  smul_comm n x y := ((DistribMulAction.toAddMonoidHom A x).map_zsmul y n).symm
#align add_group.int_smul_comm_class AddGroup.int_smulCommClass

-- `SMulCommClass.symm` is not registered as an instance, as it would cause a loop
instance AddGroup.int_smulCommClass' : SMulCommClass M ℤ A :=
  SMulCommClass.symm _ _ _
#align add_group.int_smul_comm_class' AddGroup.int_smulCommClass'

@[simp]
theorem smul_neg (r : M) (x : A) : r • -x = -(r • x) :=
  eq_neg_of_add_eq_zero_left <| by rw [← smul_add, neg_add_self, smul_zero]
                                   -- 🎉 no goals
#align smul_neg smul_neg

theorem smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, smul_add, smul_neg]
  -- 🎉 no goals
#align smul_sub smul_sub

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
#align mul_distrib_mul_action MulDistribMulAction
#align mul_distrib_mul_action.ext MulDistribMulAction.ext
#align mul_distrib_mul_action.ext_iff MulDistribMulAction.ext_iff

export MulDistribMulAction (smul_one)

section

variable [Monoid M] [Monoid A] [MulDistribMulAction M A]

theorem smul_mul' (a : M) (b₁ b₂ : A) : a • (b₁ * b₂) = a • b₁ * a • b₂ :=
  MulDistribMulAction.smul_mul _ _ _
#align smul_mul' smul_mul'

/-- Pullback a multiplicative distributive multiplicative action along an injective monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulDistribMulAction [Monoid B] [SMul M B] (f : B →* A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B :=
  { hf.mulAction f smul with
    smul := (· • ·),
    smul_mul := fun c x y => hf <| by simp only [smul, f.map_mul, smul_mul'],
                                      -- 🎉 no goals
    smul_one := fun c => hf <| by simp only [smul, f.map_one, smul_one] }
                                  -- 🎉 no goals
#align function.injective.mul_distrib_mul_action Function.Injective.mulDistribMulAction

/-- Pushforward a multiplicative distributive multiplicative action along a surjective monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulDistribMulAction [Monoid B] [SMul M B] (f : A →* B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B :=
  { hf.mulAction f smul with
    smul := (· • ·),
    smul_mul := fun c x y => by
      rcases hf x with ⟨x, rfl⟩
      -- ⊢ c • (↑f x * y) = c • ↑f x * c • y
      rcases hf y with ⟨y, rfl⟩
      -- ⊢ c • (↑f x * ↑f y) = c • ↑f x * c • ↑f y
      simp only [smul_mul', ← smul, ← f.map_mul],
      -- 🎉 no goals
    smul_one := fun c => by rw [← f.map_one, ← smul, smul_one] }
                            -- 🎉 no goals
#align function.surjective.mul_distrib_mul_action Function.Surjective.mulDistribMulAction

variable (A)

/-- Compose a `MulDistribMulAction` with a `MonoidHom`, with action `f r' • m`.
See note [reducible non-instances]. -/
@[reducible]
def MulDistribMulAction.compHom [Monoid N] (f : N →* M) : MulDistribMulAction N A :=
  { MulAction.compHom A f with
    smul := SMul.comp.smul f,
    smul_one := fun x => smul_one (f x),
    smul_mul := fun x => smul_mul' (f x) }
#align mul_distrib_mul_action.comp_hom MulDistribMulAction.compHom

/-- Scalar multiplication by `r` as a `MonoidHom`. -/
def MulDistribMulAction.toMonoidHom (r : M) :
    A →* A where
  toFun := (· • ·) r
  map_one' := smul_one r
  map_mul' := smul_mul' r
#align mul_distrib_mul_action.to_monoid_hom MulDistribMulAction.toMonoidHom

variable {A}

@[simp]
theorem MulDistribMulAction.toMonoidHom_apply (r : M) (x : A) :
    MulDistribMulAction.toMonoidHom A r x = r • x :=
  rfl
#align mul_distrib_mul_action.to_monoid_hom_apply MulDistribMulAction.toMonoidHom_apply

variable (M A)

/-- Each element of the monoid defines a monoid homomorphism. -/
@[simps]
def MulDistribMulAction.toMonoidEnd :
    M →* Monoid.End A where
  toFun := MulDistribMulAction.toMonoidHom A
  map_one' := MonoidHom.ext <| one_smul M
  map_mul' x y := MonoidHom.ext <| mul_smul x y
#align mul_distrib_mul_action.to_monoid_End MulDistribMulAction.toMonoidEnd
#align mul_distrib_mul_action.to_monoid_End_apply MulDistribMulAction.toMonoidEnd_apply

end

section

variable [Monoid M] [Group A] [MulDistribMulAction M A]

@[simp]
theorem smul_inv' (r : M) (x : A) : r • x⁻¹ = (r • x)⁻¹ :=
  (MulDistribMulAction.toMonoidHom A r).map_inv x
#align smul_inv' smul_inv'

theorem smul_div' (r : M) (x y : A) : r • (x / y) = r • x / r • y :=
  map_div (MulDistribMulAction.toMonoidHom A r) x y
#align smul_div' smul_div'

end

variable (α)

/-- The monoid of endomorphisms.

Note that this is generalized by `CategoryTheory.End` to categories other than `Type u`. -/
protected def Function.End :=
  α → α
#align function.End Function.End

instance : Monoid (Function.End α) where
  one := id
  mul := (· ∘ ·)
  mul_assoc f g h := rfl
  mul_one f := rfl
  one_mul f := rfl

instance : Inhabited (Function.End α) :=
  ⟨1⟩

variable {α}

/-- The tautological action by `Function.End α` on `α`.

This is generalized to bundled endomorphisms by:
* `Equiv.Perm.applyMulAction`
* `AddMonoid.End.applyDistribMulAction`
* `AddAut.applyDistribMulAction`
* `MulAut.applyMulDistribMulAction`
* `RingHom.applyDistribMulAction`
* `LinearEquiv.applyDistribMulAction`
* `LinearMap.applyModule`
* `RingHom.applyMulSemiringAction`
* `AlgEquiv.applyMulSemiringAction`
-/
instance Function.End.applyMulAction :
    MulAction (Function.End α) α where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align function.End.apply_mul_action Function.End.applyMulAction

@[simp]
theorem Function.End.smul_def (f : Function.End α) (a : α) : f • a = f a :=
  rfl
#align function.End.smul_def Function.End.smul_def

--TODO - This statement should be somethting like `toFun (f * g) = toFun f ∘ toFun g`
theorem Function.End.mul_def (f g : Function.End α) : (f * g) = f ∘ g :=
  rfl

--TODO - This statement should be somethting like `toFun 1 = id`
theorem Function.End.one_def : (1 : Function.End α) = id :=
  rfl

/-- `Function.End.applyMulAction` is faithful. -/
instance Function.End.apply_FaithfulSMul : FaithfulSMul (Function.End α) α :=
  ⟨fun {_ _} => funext⟩
#align function.End.apply_has_faithful_smul Function.End.apply_FaithfulSMul

/-- The tautological action by `AddMonoid.End α` on `α`.

This generalizes `Function.End.applyMulAction`. -/
instance AddMonoid.End.applyDistribMulAction [AddMonoid α] :
    DistribMulAction (AddMonoid.End α) α where
  smul := (· <| ·)
  smul_zero := AddMonoidHom.map_zero
  smul_add := AddMonoidHom.map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align add_monoid.End.apply_distrib_mul_action AddMonoid.End.applyDistribMulAction

@[simp]
theorem AddMonoid.End.smul_def [AddMonoid α] (f : AddMonoid.End α) (a : α) : f • a = f a :=
  rfl
#align add_monoid.End.smul_def AddMonoid.End.smul_def

/-- `AddMonoid.End.applyDistribMulAction` is faithful. -/
instance AddMonoid.End.applyFaithfulSMul [AddMonoid α] :
    FaithfulSMul (AddMonoid.End α) α :=
  ⟨fun {_ _ h} => AddMonoidHom.ext h⟩
#align add_monoid.End.apply_has_faithful_smul AddMonoid.End.applyFaithfulSMul

/-- The monoid hom representing a monoid action.

When `M` is a group, see `MulAction.toPermHom`. -/
def MulAction.toEndHom [Monoid M] [MulAction M α] : M →* Function.End α where
  toFun := (· • ·)
  map_one' := funext (one_smul M)
  map_mul' x y := funext (mul_smul x y)
#align mul_action.to_End_hom MulAction.toEndHom

/-- The monoid action induced by a monoid hom to `Function.End α`

See note [reducible non-instances]. -/
@[reducible]
def MulAction.ofEndHom [Monoid M] (f : M →* Function.End α) : MulAction M α :=
  MulAction.compHom α f
#align mul_action.of_End_hom MulAction.ofEndHom

/-! ### `Additive`, `Multiplicative` -/

section

open Additive Multiplicative

instance Additive.vadd [SMul α β] : VAdd (Additive α) β :=
  ⟨fun a => (toMul a • ·)⟩
#align additive.has_vadd Additive.vadd

instance Multiplicative.smul [VAdd α β] : SMul (Multiplicative α) β :=
  ⟨fun a => (toAdd a +ᵥ ·)⟩
#align multiplicative.has_smul Multiplicative.smul

@[simp]
theorem toMul_smul [SMul α β] (a) (b : β) : (toMul a : α) • b = a +ᵥ b :=
  rfl
#align to_mul_smul toMul_smul

@[simp]
theorem ofMul_vadd [SMul α β] (a : α) (b : β) : ofMul a +ᵥ b = a • b :=
  rfl
#align of_mul_vadd ofMul_vadd

@[simp]
theorem toAdd_vadd [VAdd α β] (a) (b : β) : (toAdd a : α) +ᵥ b = a • b :=
  rfl
#align to_add_vadd toAdd_vadd

@[simp]
theorem ofAdd_smul [VAdd α β] (a : α) (b : β) : ofAdd a • b = a +ᵥ b :=
  rfl
#align of_add_smul ofAdd_smul

-- Porting note: I don't know why `one_smul` can do without an explicit α and `mul_smul` can't.
instance Additive.addAction [Monoid α] [MulAction α β] :
    AddAction (Additive α) β where
  zero_vadd := MulAction.one_smul
  add_vadd := @MulAction.mul_smul α _ _ _
#align additive.add_action Additive.addAction

instance Multiplicative.mulAction [AddMonoid α] [AddAction α β] :
    MulAction (Multiplicative α)
      β where
  one_smul := AddAction.zero_vadd
  mul_smul := @AddAction.add_vadd α _ _ _
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
instance AddAction.functionEnd : AddAction (Additive (Function.End α)) α :=
  inferInstance
#align add_action.function_End AddAction.functionEnd

/-- The additive monoid hom representing an additive monoid action.

When `M` is a group, see `AddAction.toPermHom`. -/
def AddAction.toEndHom [AddMonoid M] [AddAction M α] : M →+ Additive (Function.End α) :=
  MonoidHom.toAdditive'' MulAction.toEndHom
#align add_action.to_End_hom AddAction.toEndHom

/-- The additive action induced by a hom to `Additive (Function.End α)`

See note [reducible non-instances]. -/
@[reducible]
def AddAction.ofEndHom [AddMonoid M] (f : M →+ Additive (Function.End α)) : AddAction M α :=
  AddAction.compHom α f
#align add_action.of_End_hom AddAction.ofEndHom
