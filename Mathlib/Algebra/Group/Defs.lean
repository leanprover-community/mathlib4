/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Mathlib.Init.Zero
import Mathlib.Init.Data.Int.Notation
import Mathlib.Tactic.Spread
import Mathlib.Tactic.ToAdditive

/-!
# Typeclasses for (semi)groups and monoids

In this file we define typeclasses for algebraic structures with one binary operation.
The classes are named `(add_)?(comm_)?(semigroup|monoid|group)`, where `add_` means that
the class uses additive notation and `comm_` means that the class assumes that the binary
operation is commutative.

The file does not contain any lemmas except for

* axioms of typeclasses restated in the root namespace;
* lemmas required for instances.

For basic lemmas about these classes see `algebra.group.basic`.

We also introduce notation classes `has_smul` and `has_vadd` for multiplicative and additive
actions and register the following instances:

- `has_pow M ℕ`, for monoids `M`, and `has_pow G ℤ` for groups `G`;
- `has_smul ℕ M` for additive monoids `M`, and `has_smul ℤ G` for additive groups `G`.

## Notation

- `+`, `-`, `*`, `/`, `^` : the usual arithmetic operations; the underlying functions are
  `has_add.add`, `has_neg.neg`/`has_sub.sub`, `has_mul.mul`, `has_div.div`, and `has_pow.pow`.
- `a • b` is used as notation for `has_smul.smul a b`.
- `a +ᵥ b` is used as notation for `has_vadd.vadd a b`.

-/

open Function

/-- Type class for the `+ᵥ` notation. -/
class HasVadd (G : Type _) (P : Type _) where
  vadd : G → P → P

/-- Type class for the `-ᵥ` notation. -/
class HasVsub (G : outParam (Type _)) (P : Type _) where
  vsub : P → P → G

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
@[ext, to_additive]
class HasSmul (M : Type _) (α : Type _) where
  smul : M → α → α

infixl:65 " +ᵥ " => HasVadd.vadd
infixl:65 " -ᵥ " => HasVsub.vsub
infixr:73 " • " => HasSmul.smul

-- [todo] is this correct? I think it's needed to ensure that additiveTest
-- succeeds if the relevant arg involves Nat.
attribute [to_additive] Nat
attribute [to_additive] Int

attribute [to_additive Add] Mul
attribute [to_additive Sub] Div
attribute [to_additive HAdd] HMul
attribute [to_additive instHAdd] instHMul
attribute [to_additive HSub] HDiv
attribute [to_additive instHNeg] instHDiv

attribute [to_additive_reorder 1] HPow
attribute [to_additive_reorder 1 4] HPow.hPow
attribute [to_additive HMul] HPow

universe u

variable {G : Type _}

@[to_additive Zero]
class One (α : Type u) where
  one : α

@[to_additive Zero.toOfNat0]
instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

@[to_additive Zero.ofOfNat0]
instance One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

/-- Class of types that have an inversion operation. -/
@[to_additive Neg]
class Inv (α : Type u) where
  /-- Invert an element of α. -/
  inv : α → α

@[inheritDoc]
postfix:max "⁻¹" => Inv.inv

/-- The simpset `field_simps` is used by the tactic `field_simp` to
reduce an expression in a field to an expression of the form `n / d` where `n` and `d` are
division-free. -/
register_simp_attr field_simps

section Mul

variable [Mul G]

/-- `left_mul g` denotes left multiplication by `g` -/
@[to_additive "`left_add g` denotes left addition by `g`"]
def leftMul : G → G → G := fun g : G => fun x : G => g * x

/-- `right_mul g` denotes right multiplication by `g` -/
@[to_additive "`right_add g` denotes right addition by `g`"]
def rightMul : G → G → G := fun g : G => fun x : G => x * g

end Mul

/-- A semigroup is a type with an associative `(*)`. -/
@[ext]
class Semigroup (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

/-- An additive semigroup is a type with an associative `(+)`. -/
@[ext]
class AddSemigroup (G : Type u) extends Add G where
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

attribute [to_additive AddSemigroup] Semigroup

section Semigroup

variable [Semigroup G]

@[to_additive]
theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
  Semigroup.mul_assoc

end Semigroup

/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
@[ext]
class CommSemigroup (G : Type u) extends Semigroup G where
  mul_comm : ∀ a b : G, a * b = b * a

/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
@[ext]
class AddCommSemigroup (G : Type u) extends AddSemigroup G where
  add_comm : ∀ a b : G, a + b = b + a

attribute [to_additive AddCommSemigroup] CommSemigroup

section CommSemigroup

variable [CommSemigroup G]

@[to_additive]
theorem mul_comm : ∀ a b : G, a * b = b * a :=
  CommSemigroup.mul_comm

end CommSemigroup

/-- A `left_cancel_semigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
@[ext]
class LeftCancelSemigroup (G : Type u) extends Semigroup G where
  mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c

/-- An `add_left_cancel_semigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
@[ext]
class AddLeftCancelSemigroup (G : Type u) extends AddSemigroup G where
  add_left_cancel : ∀ a b c : G, a + b = a + c → b = c

attribute [to_additive AddLeftCancelSemigroup] LeftCancelSemigroup

section LeftCancelSemigroup

variable [LeftCancelSemigroup G] {a b c : G}

@[to_additive]
theorem mul_left_cancel : a * b = a * c → b = c :=
  LeftCancelSemigroup.mul_left_cancel a b c

@[to_additive]
theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancel, congr_arg _⟩

@[to_additive]
theorem mul_right_injective (a : G) : Function.injective ((· * ·) a) := fun _ _ => mul_left_cancel

@[simp, to_additive]
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
  (mul_right_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
  (mul_right_injective a).ne_iff

end LeftCancelSemigroup

/-- A `right_cancel_semigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
@[ext]
class RightCancelSemigroup (G : Type u) extends Semigroup G where
  mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c

/-- An `add_right_cancel_semigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
@[ext]
class AddRightCancelSemigroup (G : Type u) extends AddSemigroup G where
  add_right_cancel : ∀ a b c : G, a + b = c + b → a = c

attribute [to_additive AddRightCancelSemigroup] RightCancelSemigroup

section RightCancelSemigroup

variable [RightCancelSemigroup G] {a b c : G}

@[to_additive]
theorem mul_right_cancel : a * b = c * b → a = c :=
  RightCancelSemigroup.mul_right_cancel a b c

@[to_additive]
theorem mul_right_cancel_iff : b * a = c * a ↔ b = c :=
  ⟨mul_right_cancel, congr_arg (· * a)⟩

@[to_additive]
theorem mul_left_injective (a : G) : Function.injective (· * a) := fun _ _ => mul_right_cancel

@[simp, to_additive]
theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
  (mul_left_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c :=
  (mul_left_injective a).ne_iff

end RightCancelSemigroup

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
class MulOneClass (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a

/-- Typeclass for expressing that a type `M` with addition and a zero satisfies
`0 + a = a` and `a + 0 = a` for all `a : M`. -/
class AddZeroClass (M : Type u) extends Zero M, Add M where
  zero_add : ∀ a : M, 0 + a = a
  add_zero : ∀ a : M, a + 0 = a

attribute [to_additive AddZeroClass] MulOneClass

@[ext, to_additive]
theorem MulOneClass.ext {M : Type u} : ∀ ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul → m₁ = m₂ := by
  rintro ⟨⟨one₁⟩, ⟨mul₁⟩, one_mul₁, mul_one₁⟩ ⟨⟨one₂⟩, ⟨mul₂⟩, one_mul₂, mul_one₂⟩ ⟨rfl⟩
  -- FIXME:
  -- congr
  suffices one₁ = one₂ by cases this; rfl
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂)

section MulOneClass

variable {M : Type u} [MulOneClass M]

@[simp, to_additive]
theorem one_mul : ∀ a : M, 1 * a = a :=
  MulOneClass.one_mul

@[simp, to_additive]
theorem mul_one : ∀ a : M, a * 1 = a :=
  MulOneClass.mul_one

end MulOneClass

section

variable {M : Type u}

-- use `x * npow_rec n x` and not `npow_rec n x * x` in the definition to make sure that
-- definitional unfolding of `npow_rec` is blocked, to avoid deep recursion issues.
/-- The fundamental power operation in a monoid. `npow_rec n a = a*a*...*a` n times.
Use instead `a ^ n`,  which has better definitional behavior. -/
def npowRec [One M] [Mul M] : ℕ → M → M
  | 0, _ => 1
  | n + 1, a => a * npowRec n a

/-- The fundamental scalar multiplication in an additive monoid. `nsmul_rec n a = a+a+...+a` n
times. Use instead `n • a`, which has better definitional behavior. -/
def nsmulRec [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmulRec n a

attribute [to_additive nsmulRec] npowRec

end

library_note "forgetful inheritance"/--
Suppose that one can put two mathematical structures on a type, a rich one `R` and a poor one
`P`, and that one can deduce the poor structure from the rich structure through a map `F` (called a
forgetful functor) (think `R = metric_space` and `P = topological_space`). A possible
implementation would be to have a type class `rich` containing a field `R`, a type class `poor`
containing a field `P`, and an instance from `rich` to `poor`. However, this creates diamond
problems, and a better approach is to let `rich` extend `poor` and have a field saying that
`F R = P`.

To illustrate this, consider the pair `metric_space` / `topological_space`. Consider the topology
on a product of two metric spaces. With the first approach, it could be obtained by going first from
each metric space to its topology, and then taking the product topology. But it could also be
obtained by considering the product metric space (with its sup distance) and then the topology
coming from this distance. These would be the same topology, but not definitionally, which means
that from the point of view of Lean's kernel, there would be two different `topological_space`
instances on the product. This is not compatible with the way instances are designed and used:
there should be at most one instance of a kind on each type. This approach has created an instance
diamond that does not commute definitionally.

The second approach solves this issue. Now, a metric space contains both a distance, a topology, and
a proof that the topology coincides with the one coming from the distance. When one defines the
product of two metric spaces, one uses the sup distance and the product topology, and one has to
give the proof that the sup distance induces the product topology. Following both sides of the
instance diamond then gives rise (definitionally) to the product topology on the product space.

Another approach would be to have the rich type class take the poor type class as an instance
parameter. It would solve the diamond problem, but it would lead to a blow up of the number
of type classes one would need to declare to work with complicated classes, say a real inner
product space, and would create exponential complexity when working with products of
such complicated spaces, that are avoided by bundling things carefully as above.

Note that this description of this specific case of the product of metric spaces is oversimplified
compared to mathlib, as there is an intermediate typeclass between `metric_space` and
`topological_space` called `uniform_space`. The above scheme is used at both levels, embedding a
topology in the uniform space structure, and a uniform structure in the metric space structure.

Note also that, when `P` is a proposition, there is no such issue as any two proofs of `P` are
definitionally equivalent in Lean.

To avoid boilerplate, there are some designs that can automatically fill the poor fields when
creating a rich structure if one doesn't want to do something special about them. For instance,
in the definition of metric spaces, default tactics fill the uniform space fields if they are
not given explicitly. One can also have a helper function creating the rich structure from a
structure with fewer fields, where the helper function fills the remaining fields. See for instance
`uniform_space.of_core` or `real_inner_product.of_core`.

For more details on this question, called the forgetful inheritance pattern, see [Competing
inheritance paths in dependent type theory: a case study in functional
analysis](https://hal.inria.fr/hal-02463336).
-/


/-!
### Design note on `add_monoid` and `monoid`

An `add_monoid` has a natural `ℕ`-action, defined by `n • a = a + ... + a`, that we want to declare
as an instance as it makes it possible to use the language of linear algebra. However, there are
often other natural `ℕ`-actions. For instance, for any semiring `R`, the space of polynomials
`polynomial R` has a natural `R`-action defined by multiplication on the coefficients. This means
that `polynomial ℕ` would have two natural `ℕ`-actions, which are equal but not defeq. The same
goes for linear maps, tensor products, and so on (and even for `ℕ` itself).

To solve this issue, we embed an `ℕ`-action in the definition of an `add_monoid` (which is by
default equal to the naive action `a + ... + a`, but can be adjusted when needed), and declare
a `has_smul ℕ α` instance using this action. See Note [forgetful inheritance] for more
explanations on this pattern.

For example, when we define `polynomial R`, then we declare the `ℕ`-action to be by multiplication
on each coefficient (using the `ℕ`-action on `R` that comes from the fact that `R` is
an `add_monoid`). In this way, the two natural `has_smul ℕ (polynomial ℕ)` instances are defeq.

The tactic `to_additive` transfers definitions and results from multiplicative monoids to additive
monoids. To work, it has to map fields to fields. This means that we should also add corresponding
fields to the multiplicative structure `monoid`, which could solve defeq problems for powers if
needed. These problems do not come up in practice, so most of the time we will not need to adjust
the `npow` field when defining multiplicative objects.

A basic theory for the power function on monoids and the `ℕ`-action on additive monoids is built in
the file `algebra.group_power.basic`. For now, we only register the most basic properties that we
need right away.

In the definition, we use `n.succ` instead of `n + 1` in the `nsmul_succ'` and `npow_succ'` fields
to make sure that `to_additive` is not confused (otherwise, it would try to convert `1 : ℕ`
to `0 : ℕ`).
-/


/-- An `add_monoid` is an `add_semigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  nsmul : ℕ → M → M := nsmulRec
  nsmul_zero' : ∀ x, nsmul 0 x = 0 := by intros; rfl
  nsmul_succ' : ∀ (n : ℕ) (x), nsmul n.succ x = x + nsmul n x := by intros; rfl

/-- A `monoid` is a `semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[to_additive AddMonoid]
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  npow : ℕ → M → M := npowRec
  npow_zero' : ∀ x, npow 0 x = 1 := by intros; rfl
  npow_succ' : ∀ (n : ℕ) (x), npow n.succ x = x * npow n x := by intros; rfl

-- TODO I wouldn't have thought this is necessary. Is is a bug in `to_additive`?
attribute [to_additive AddMonoid.toAddZeroClass] Monoid.toMulOneClass

instance Monoid.Pow {M : Type _} [Monoid M] : Pow M ℕ :=
  ⟨fun x n => Monoid.npow n x⟩

@[defaultInstance high] instance Monoid.HPow {M : Type _} [Monoid M] : HPow M ℕ M :=
  ⟨λ a n => Monoid.npow n a⟩

instance AddMonoid.HasSmul {M : Type _} [AddMonoid M] : HasSmul ℕ M :=
  ⟨AddMonoid.nsmul⟩

attribute [to_additive AddMonoid.hasSmulNat] Monoid.Pow

section
-- FIXME The lemmas in this section should be done by `to_additive` below, but it fails.

variable {M : Type _} [AddMonoid M]

@[simp]
theorem nsmul_eq_smul (n : ℕ) (x : M) : AddMonoid.nsmul n x = n • x :=
  rfl

theorem zero_nsmul (a : M) : 0 • a = 0 :=
  AddMonoid.nsmul_zero' _

theorem succ_nsmul (a : M) (n : ℕ) : (n + 1) • a = a + n • a :=
  AddMonoid.nsmul_succ' n a

end

section

variable {M : Type _} [Monoid M]

@[simp, to_additive nsmul_eq_smul]
theorem npow_eq_pow (n : ℕ) (x : M) : Monoid.npow n x = x ^ n :=
  rfl

-- the attributes are intentionally out of order. `zero_smul` proves `zero_nsmul`.
@[to_additive zero_nsmul, simp]
theorem pow_zero (a : M) : a ^ 0 = 1 :=
  Monoid.npow_zero' _

@[to_additive succ_nsmul]
theorem pow_succ (a : M) (n : ℕ) : a ^ (n + 1) = a * a ^ n :=
  Monoid.npow_succ' n a

end

section Monoid

variable {M : Type u} [Monoid M]

@[to_additive]
theorem left_inv_eq_right_inv {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]

end Monoid

/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M

/-- A commutative monoid is a monoid with commutative `(*)`. -/
@[to_additive AddCommMonoid]
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M

attribute [to_additive AddCommMonoid.toAddCommSemigroup] CommMonoid.toCommSemigroup

section LeftCancelMonoid

/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_left_cancel_semigroup` is not enough. -/
class AddLeftCancelMonoid (M : Type u) extends AddLeftCancelSemigroup M, AddMonoid M

/-- A monoid in which multiplication is left-cancellative. -/
@[to_additive AddLeftCancelMonoid]
class LeftCancelMonoid (M : Type u) extends LeftCancelSemigroup M, Monoid M

attribute [to_additive AddLeftCancelMonoid.toAddMonoid] LeftCancelMonoid.toMonoid

end LeftCancelMonoid

section RightCancelMonoid

/-- An additive monoid in which addition is right-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_right_cancel_semigroup` is not enough. -/
class AddRightCancelMonoid (M : Type u) extends AddRightCancelSemigroup M, AddMonoid M

/-- A monoid in which multiplication is right-cancellative. -/
@[to_additive AddRightCancelMonoid]
class RightCancelMonoid (M : Type u) extends RightCancelSemigroup M, Monoid M

attribute [to_additive AddRightCancelMonoid.toAddMonoid] RightCancelMonoid.toMonoid

end RightCancelMonoid

section CancelMonoid

/-- An additive monoid in which addition is cancellative on both sides.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_right_cancel_semigroup` is not enough. -/
class AddCancelMonoid (M : Type u) extends AddLeftCancelMonoid M, AddRightCancelMonoid M

/-- A monoid in which multiplication is cancellative. -/
@[to_additive AddCancelMonoid]
class CancelMonoid (M : Type u) extends LeftCancelMonoid M, RightCancelMonoid M

attribute [to_additive AddCancelMonoid.toAddRightCancelMonoid] CancelMonoid.toRightCancelMonoid

/-- Commutative version of `add_cancel_monoid`. -/
class AddCancelCommMonoid (M : Type u) extends AddLeftCancelMonoid M, AddCommMonoid M

/-- Commutative version of `cancel_monoid`. -/
@[to_additive AddCancelCommMonoid]
class CancelCommMonoid (M : Type u) extends LeftCancelMonoid M, CommMonoid M

attribute [to_additive AddCancelCommMonoid.toAddCommMonoid] CancelCommMonoid.toCommMonoid

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CancelCommMonoid.toCancelMonoid (M : Type u) [CancelCommMonoid M] :
    CancelMonoid M :=
  { mul_right_cancel := fun a b c h => mul_left_cancel <| by rw [mul_comm, h, mul_comm] }

end CancelMonoid

/-- The fundamental power operation in a group. `zpow_rec n a = a*a*...*a` n times, for integer `n`.
Use instead `a ^ n`,  which has better definitional behavior. -/
def zpowRec {M : Type _} [One M] [Mul M] [Inv M] : ℤ → M → M
  | Int.ofNat n, a => npowRec n a
  | Int.negSucc n, a => (npowRec n.succ a)⁻¹

/-- The fundamental scalar multiplication in an additive group. `zsmul_rec n a = a+a+...+a` n
times, for integer `n`. Use instead `n • a`, which has better definitional behavior. -/
def zsmulRec {M : Type _} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmulRec n a
  | Int.negSucc n, a => -nsmulRec n.succ a

attribute [to_additive zsmulRec] zpowRec

section HasInvolutiveInv

/-- Auxiliary typeclass for types with an involutive `has_neg`. -/
class HasInvolutiveNeg (A : Type _) extends Neg A where
  neg_neg : ∀ x : A, - -x = x

/-- Auxiliary typeclass for types with an involutive `has_inv`. -/
@[to_additive HasInvolutiveNeg]
class HasInvolutiveInv (G : Type _) extends Inv G where
  inv_inv : ∀ x : G, x⁻¹⁻¹ = x

variable [HasInvolutiveInv G]

@[simp, to_additive]
theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
  HasInvolutiveInv.inv_inv _

end HasInvolutiveInv

/-!
### Design note on `div_inv_monoid`/`sub_neg_monoid` and `division_monoid`/`subtraction_monoid`

Those two pairs of made-up classes fulfill slightly different roles.

`div_inv_monoid`/`sub_neg_monoid` provides the minimum amount of information to define the
`ℤ` action (`zpow` or `zsmul`). Further, it provides a `div` field, matching the forgetful
inheritance pattern. This is useful to shorten extension clauses of stronger structures (`group`,
`group_with_zero`, `division_ring`, `field`) and for a few structures with a rather weak
pseudo-inverse (`matrix`).

`division_monoid`/`subtraction_monoid` is targeted at structures with stronger pseudo-inverses. It
is an ad hoc collection of axioms that are mainly respected by three things:
* Groups
* Groups with zero
* The pointwise monoids `set α`, `finset α`, `filter α`

It acts as a middle ground for structures with an inversion operator that plays well with
multiplication, except for the fact that it might not be a true inverse (`a / a ≠ 1` in general).
The axioms are pretty arbitrary (many other combinations are equivalent to it), but they are
independent:
* Without `division_monoid.div_eq_mul_inv`, you can define `/` arbitrarily.
* Without `division_monoid.inv_inv`, you can consider `with_top unit` with `a⁻¹ = ⊤` for all `a`.
* Without `division_monoid.mul_inv_rev`, you can consider `with_top α` with `a⁻¹ = a` for all `a`
  where `α` non commutative.
* Without `division_monoid.inv_eq_of_mul`, you can consider any `comm_monoid` with `a⁻¹ = a` for all
  `a`.

As a consequence, a few natural structures do not fit in this framework. For example, `ennreal`
respects everything except for the fact that `(0 * ∞)⁻¹ = 0⁻¹ = ∞` while `∞⁻¹ * 0⁻¹ = 0 * ∞ = 0`.
-/


/-- A `div_inv_monoid` is a `monoid` with operations `/` and `⁻¹` satisfying
`div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`.

This deduplicates the name `div_eq_mul_inv`.
The default for `div` is such that `a / b = a * b⁻¹` holds by definition.

Adding `div` as a field rather than defining `a / b := a * b⁻¹` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_div (foo X)` instance but no
`∀ X, has_inv (foo X)`, e.g. when `foo X` is a `euclidean_domain`. Suppose we
also have an instance `∀ X [cromulent X], group_with_zero (foo X)`. Then the
`(/)` coming from `group_with_zero_has_div` cannot be definitionally equal to
the `(/)` coming from `foo.has_div`.

In the same way, adding a `zpow` field makes it possible to avoid definitional failures
in diamonds. See the definition of `monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  div a b := a * b⁻¹
  div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by intros; rfl
  zpow : ℤ → G → G := zpowRec
  zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  zpow_succ' (n : ℕ) (a : G) : zpow (Int.ofNat n.succ) a = a * zpow (Int.ofNat n) a := by
    intros; rfl
  zpow_neg' (n : ℕ) (a : G) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ := by intros; rfl

/-- A `sub_neg_monoid` is an `add_monoid` with unary `-` and binary `-` operations
satisfying `sub_eq_add_neg : ∀ a b, a - b = a + -b`.

The default for `sub` is such that `a - b = a + -b` holds by definition.

Adding `sub` as a field rather than defining `a - b := a + -b` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_sub (foo X)` instance but no
`∀ X, has_neg (foo X)`. Suppose we also have an instance
`∀ X [cromulent X], add_group (foo X)`. Then the `(-)` coming from
`add_group.has_sub` cannot be definitionally equal to the `(-)` coming from
`foo.has_sub`.

In the same way, adding a `zsmul` field makes it possible to avoid definitional failures
in diamonds. See the definition of `add_monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  sub a b := a + -b
  sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by intros; rfl
  zsmul : ℤ → G → G := zsmulRec
  zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by intros; rfl
  zsmul_succ' (n : ℕ) (a : G) : zsmul (Int.ofNat n.succ) a = a + zsmul (Int.ofNat n) a := by
    intros; rfl
  zsmul_neg' (n : ℕ) (a : G) : zsmul (Int.negSucc n) a = -zsmul n.succ a := by intros; rfl

attribute [to_additive SubNegMonoid] DivInvMonoid

instance DivInvMonoid.hasPow {M} [DivInvMonoid M] : Pow M ℤ :=
  ⟨fun x n => DivInvMonoid.zpow n x⟩

instance SubNegMonoid.hasSmulInt {M} [SubNegMonoid M] : HasSmul ℤ M :=
  ⟨SubNegMonoid.zsmul⟩

attribute [to_additive SubNegMonoid.hasSmulInt] DivInvMonoid.hasPow

section DivInvMonoid

variable [DivInvMonoid G] {a b : G}

-- TODO restore @[to_additive zsmul_eq_smul]
@[simp]
theorem zpow_eq_pow (n : ℤ) (x : G) : DivInvMonoid.zpow n x = x ^ n :=
  rfl

-- TODO restore @[to_additive zero_zsmul]
@[simp]
theorem zpow_zero (a : G) : a ^ (0 : ℤ) = 1 :=
  DivInvMonoid.zpow_zero' a

-- TODO restore @[to_additive coe_nat_zsmul]
@[norm_cast]
theorem zpow_coe_nat (a : G) : ∀ n : ℕ, a ^ (n : ℤ) = a ^ n
  | 0 => (zpow_zero _).trans (pow_zero _).symm
  | n + 1 => calc
    a ^ (↑(n + 1) : ℤ) = a * a ^ (n : ℤ) := DivInvMonoid.zpow_succ' _ _
    _ = a * a ^ n := congr_arg ((· * ·) a) (zpow_coe_nat a n)
    _ = a ^ (n + 1) := (pow_succ _ _).symm

-- TODO restore @[to_additive of_nat_zsmul]
theorem zpow_of_nat (a : G) (n : ℕ) : a ^ Int.ofNat n = a ^ n :=
  zpow_coe_nat a n

-- TODO restore @[to_additive]
@[simp]
theorem zpow_neg_succ_of_nat (a : G) (n : ℕ) : a ^ (Int.negSucc n) = (a ^ (n + 1))⁻¹ := by
  rw [← zpow_coe_nat]
  exact DivInvMonoid.zpow_neg' n a

/-- Dividing by an element is the same as multiplying by its inverse.

This is a duplicate of `div_inv_monoid.div_eq_mul_inv` ensuring that the types unfold better.
-/
@[to_additive "Subtracting an element is the same as adding by its negative.
This is a duplicate of `sub_neg_monoid.sub_eq_mul_neg` ensuring that the types unfold better."]
theorem div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ :=
  DivInvMonoid.div_eq_mul_inv _ _

alias div_eq_mul_inv ← division_def

end DivInvMonoid

section InvOneClass

/-- Typeclass for expressing that `-0 = 0`. -/
class NegZeroClass (G : Type _) extends Zero G, Neg G where
  neg_zero : -(0 : G) = 0

/-- A `sub_neg_monoid` where `-0 = 0`. -/
class SubNegZeroMonoid (G : Type _) extends SubNegMonoid G, NegZeroClass G

/-- Typeclass for expressing that `1⁻¹ = 1`. -/
@[to_additive NegZeroClass]
class InvOneClass (G : Type _) extends One G, Inv G where
  inv_one : (1 : G)⁻¹ = 1

/-- A `div_inv_monoid` where `1⁻¹ = 1`. -/
@[to_additive SubNegZeroMonoid]
class DivInvOneMonoid (G : Type _) extends DivInvMonoid G, InvOneClass G

attribute [to_additive SubNegZeroMonoid.toNegZeroClass] DivInvOneMonoid.toInvOneClass

variable [InvOneClass G]

@[simp, to_additive]
theorem inv_one : (1 : G)⁻¹ = 1 :=
  InvOneClass.inv_one

end InvOneClass

/-- A `subtraction_monoid` is a `sub_neg_monoid` with involutive negation and such that
`-(a + b) = -b + -a` and `a + b = 0 → -a = b`. -/
class SubtractionMonoid (G : Type u) extends SubNegMonoid G, HasInvolutiveNeg G where
  neg_add_rev (a b : G) : -(a + b) = -b + -a
  /- Despite the asymmetry of `neg_eq_of_add`, the symmetric version is true thanks to the
  involutivity of negation. -/
  neg_eq_of_add (a b : G) : a + b = 0 → -a = b

/-- A `division_monoid` is a `div_inv_monoid` with involutive inversion and such that
`(a * b)⁻¹ = b⁻¹ * a⁻¹` and `a * b = 1 → a⁻¹ = b`.

This is the immediate common ancestor of `group` and `group_with_zero`. -/
@[to_additive SubtractionMonoid]
class DivisionMonoid (G : Type u) extends DivInvMonoid G, HasInvolutiveInv G where
  mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
  /- Despite the asymmetry of `inv_eq_of_mul`, the symmetric version is true thanks to the
  involutivity of inversion. -/
  inv_eq_of_mul (a b : G) : a * b = 1 → a⁻¹ = b

attribute [to_additive SubtractionMonoid.toHasInvolutiveNeg] DivisionMonoid.toHasInvolutiveInv

section DivisionMonoid

variable [DivisionMonoid G] {a b : G}

@[simp, to_additive neg_add_rev]
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  DivisionMonoid.mul_inv_rev _ _

@[to_additive]
theorem inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b :=
  DivisionMonoid.inv_eq_of_mul _ _

end DivisionMonoid

/-- Commutative `subtraction_monoid`. -/
class SubtractionCommMonoid (G : Type u) extends SubtractionMonoid G, AddCommMonoid G

/-- Commutative `division_monoid`.

This is the immediate common ancestor of `comm_group` and `comm_group_with_zero`. -/
@[to_additive SubtractionCommMonoid]
class DivisionCommMonoid (G : Type u) extends DivisionMonoid G, CommMonoid G

attribute [to_additive SubtractionCommMonoid.toAddCommMonoid] DivisionCommMonoid.toCommMonoid

/-- A `group` is a `monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`.

There is also a division operation `/` such that `a / b = a * b⁻¹`,
with a default so that `a / b = a * b⁻¹` holds by definition.
-/
class Group (G : Type u) extends DivInvMonoid G where
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1

/-- An `add_group` is an `add_monoid` with a unary `-` satisfying `-a + a = 0`.

There is also a binary operation `-` such that `a - b = a + -b`,
with a default so that `a - b = a + -b` holds by definition.
-/
class AddGroup (A : Type u) extends SubNegMonoid A where
  add_left_neg : ∀ a : A, -a + a = 0

attribute [to_additive AddGroup] Group

section Group

variable [Group G] {a b c : G}

@[simp, to_additive]
theorem mul_left_inv : ∀ a : G, a⁻¹ * a = 1 :=
  Group.mul_left_inv

@[to_additive]
theorem inv_mul_self (a : G) : a⁻¹ * a = 1 :=
  mul_left_inv a

@[to_additive]
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_self a) h

@[simp, to_additive]
theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
  by rw [← mul_left_inv a⁻¹, inv_eq_of_mul (mul_left_inv a)]

@[to_additive]
theorem mul_inv_self (a : G) : a * a⁻¹ = 1 :=
  mul_right_inv a

@[simp, to_additive]
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b :=
  by rw [← mul_assoc, mul_left_inv, one_mul]

@[simp, to_additive]
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b :=
  by rw [← mul_assoc, mul_right_inv, one_mul]

@[simp, to_additive]
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a :=
  by rw [mul_assoc, mul_right_inv, mul_one]

@[simp, to_additive]
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a :=
  by rw [mul_assoc, mul_left_inv, mul_one]

@[to_additive AddGroup.toSubtractionMonoid]
instance (priority := 100) Group.toDivisionMonoid : DivisionMonoid G :=
  { inv_inv := fun a => inv_eq_of_mul (mul_left_inv a)
    mul_inv_rev :=
      fun a b => inv_eq_of_mul <| by rw [mul_assoc, mul_inv_cancel_left, mul_right_inv]
    inv_eq_of_mul := fun _ _ => inv_eq_of_mul }

-- FIXME this isn't being copied by `to_additive`
-- FIXME how to set priority?
attribute [instance] AddGroup.toSubtractionMonoid

-- see Note [lower instance priority]
@[to_additive AddGroup.toAddCancelMonoid]
instance (priority := 100) Group.toCancelMonoid : CancelMonoid G :=
  { ‹Group G› with
    mul_right_cancel := fun a b c h => by rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right]
    mul_left_cancel := fun a b c h => by rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left] }

-- FIXME this isn't being copied by `to_additive`
-- FIXME how to set priority?
attribute [instance] AddGroup.toAddCancelMonoid

end Group

@[to_additive]
theorem Group.toDivInvMonoid_injective {G : Type _} :
    Function.injective (@Group.toDivInvMonoid G) := by rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

/-- An additive commutative group is an additive group with commutative `(+)`. -/
class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

/-- A commutative group is a group with commutative `(*)`. -/
@[to_additive AddCommGroup]
class CommGroup (G : Type u) extends Group G, CommMonoid G

attribute [to_additive AddCommGroup.toAddCommMonoid] CommGroup.toCommMonoid

attribute [instance] AddCommGroup.toAddCommMonoid

@[to_additive]
theorem CommGroup.toGroup_injective {G : Type u} : Function.injective (@CommGroup.toGroup G) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

section CommGroup

variable [CommGroup G]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CommGroup.toCancelCommMonoid : CancelCommMonoid G :=
  { ‹CommGroup G›, Group.toCancelMonoid with }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CommGroup.toDivisionCommMonoid : DivisionCommMonoid G :=
  { ‹CommGroup G›, Group.toDivisionMonoid with }

end CommGroup
