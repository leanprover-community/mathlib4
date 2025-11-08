/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Batteries.Logic
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Regular.Defs
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.MkIffOfInductiveProp
import Mathlib.Tactic.OfNat
import Mathlib.Tactic.Basic

/-!
# Typeclasses for (semi)groups and monoids

In this file we define typeclasses for algebraic structures with one binary operation.
The classes are named `(Add)?(Comm)?(Semigroup|Monoid|Group)`, where `Add` means that
the class uses additive notation and `Comm` means that the class assumes that the binary
operation is commutative.

The file does not contain any lemmas except for

* axioms of typeclasses restated in the root namespace;
* lemmas required for instances.

For basic lemmas about these classes see `Mathlib/Algebra/Group/Basic.lean`.

We register the following instances:

- `Pow M ℕ`, for monoids `M`, and `Pow G ℤ` for groups `G`;
- `SMul ℕ M` for additive monoids `M`, and `SMul ℤ G` for additive groups `G`.

## Notation

- `+`, `-`, `*`, `/`, `^` : the usual arithmetic operations; the underlying functions are
  `Add.add`, `Neg.neg`/`Sub.sub`, `Mul.mul`, `Div.div`, and `HPow.hPow`.

-/

assert_not_exists MonoidWithZero DenselyOrdered Function.const_injective

universe u v w

open Function

variable {G : Type*}

section Mul

variable [Mul G]

/-- A mixin for left cancellative multiplication. -/
@[mk_iff] class IsLeftCancelMul (G : Type u) [Mul G] : Prop where
  /-- Multiplication is left cancellative (i.e. left regular). -/
  protected mul_left_cancel (a : G) : IsLeftRegular a
/-- A mixin for right cancellative multiplication. -/
@[mk_iff] class IsRightCancelMul (G : Type u) [Mul G] : Prop where
  /-- Multiplication is right cancellative (i.e. right regular). -/
  protected mul_right_cancel (a : G) : IsRightRegular a
/-- A mixin for cancellative multiplication. -/
@[mk_iff]
class IsCancelMul (G : Type u) [Mul G] : Prop extends IsLeftCancelMul G, IsRightCancelMul G

/-- A mixin for left cancellative addition. -/
class IsLeftCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is left cancellative (i.e. left regular). -/
  protected add_left_cancel (a : G) : IsAddLeftRegular a

attribute [to_additive] IsLeftCancelMul
attribute [to_additive] isLeftCancelMul_iff

/-- A mixin for right cancellative addition. -/
class IsRightCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is right cancellative (i.e. right regular). -/
  protected add_right_cancel (a : G) : IsAddRightRegular a

attribute [to_additive] IsRightCancelMul
attribute [to_additive] isRightCancelMul_iff

/-- A mixin for cancellative addition. -/
@[mk_iff]
class IsCancelAdd (G : Type u) [Add G] : Prop extends IsLeftCancelAdd G, IsRightCancelAdd G

attribute [to_additive] IsCancelMul
attribute [to_additive existing] isCancelMul_iff

section Regular

variable {R : Type*}

@[to_additive] theorem isCancelMul_iff_forall_isRegular [Mul R] :
    IsCancelMul R ↔ ∀ r : R, IsRegular r := by
  rw [isCancelMul_iff, isLeftCancelMul_iff, isRightCancelMul_iff, ← forall_and]
  exact forall_congr' fun _ ↦ isRegular_iff.symm

/-- If all multiplications cancel on the left then every element is left-regular. -/
@[to_additive /-- If all additions cancel on the left then every element is add-left-regular. -/]
theorem IsLeftRegular.all [Mul R] [IsLeftCancelMul R] (g : R) : IsLeftRegular g :=
  (isLeftCancelMul_iff R).mp ‹_› _

/-- If all multiplications cancel on the right then every element is right-regular. -/
@[to_additive /-- If all additions cancel on the right then every element is add-right-regular. -/]
theorem IsRightRegular.all [Mul R] [IsRightCancelMul R] (g : R) : IsRightRegular g :=
  (isRightCancelMul_iff R).mp ‹_› _

/-- If all multiplications cancel then every element is regular. -/
@[to_additive /-- If all additions cancel then every element is add-regular. -/]
theorem IsRegular.all [Mul R] [IsCancelMul R] (g : R) : IsRegular g := ⟨.all g, .all g⟩

end Regular

section IsLeftCancelMul

variable [IsLeftCancelMul G] {a b c : G}

@[to_additive]
theorem mul_left_cancel : a * b = a * c → b = c :=
  (IsLeftCancelMul.mul_left_cancel a ·)

@[to_additive]
theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancel, congrArg _⟩

@[to_additive]
theorem mul_right_injective (a : G) : Injective (a * ·) := fun _ _ ↦ mul_left_cancel

@[to_additive (attr := simp)]
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
  (mul_right_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
  (mul_right_injective a).ne_iff

end IsLeftCancelMul

section IsRightCancelMul

variable [IsRightCancelMul G] {a b c : G}

@[to_additive]
theorem mul_right_cancel : a * b = c * b → a = c :=
  (IsRightCancelMul.mul_right_cancel b ·)

@[to_additive]
theorem mul_right_cancel_iff : b * a = c * a ↔ b = c :=
  ⟨mul_right_cancel, congrArg (· * a)⟩

@[to_additive]
theorem mul_left_injective (a : G) : Function.Injective (· * a) := fun _ _ ↦ mul_right_cancel

@[to_additive (attr := simp)]
theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
  (mul_left_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c :=
  (mul_left_injective a).ne_iff

end IsRightCancelMul

end Mul

/-- A semigroup is a type with an associative `(*)`. -/
@[ext]
class Semigroup (G : Type u) extends Mul G where
  /-- Multiplication is associative -/
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

/-- An additive semigroup is a type with an associative `(+)`. -/
@[ext]
class AddSemigroup (G : Type u) extends Add G where
  /-- Addition is associative -/
  protected add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

attribute [to_additive] Semigroup

section Semigroup

variable [Semigroup G]

@[to_additive]
theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
  Semigroup.mul_assoc

end Semigroup

/-- A commutative additive magma is a type with an addition which commutes. -/
@[ext]
class AddCommMagma (G : Type u) extends Add G where
  /-- Addition is commutative in an commutative additive magma. -/
  protected add_comm : ∀ a b : G, a + b = b + a

/-- A commutative multiplicative magma is a type with a multiplication which commutes. -/
@[ext]
class CommMagma (G : Type u) extends Mul G where
  /-- Multiplication is commutative in a commutative multiplicative magma. -/
  protected mul_comm : ∀ a b : G, a * b = b * a

attribute [to_additive] CommMagma

/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
@[ext]
class CommSemigroup (G : Type u) extends Semigroup G, CommMagma G where

/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
@[ext]
class AddCommSemigroup (G : Type u) extends AddSemigroup G, AddCommMagma G where

attribute [to_additive] CommSemigroup

section CommMagma

variable [CommMagma G] {a : G}

@[to_additive]
theorem mul_comm : ∀ a b : G, a * b = b * a := CommMagma.mul_comm

@[simp] lemma isLeftRegular_iff_isRegular : IsLeftRegular a ↔ IsRegular a := by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

@[simp] lemma isRightRegular_iff_isRegular : IsRightRegular a ↔ IsRegular a := by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

/-- Any `CommMagma G` that satisfies `IsRightCancelMul G` also satisfies `IsLeftCancelMul G`. -/
@[to_additive AddCommMagma.IsRightCancelAdd.toIsLeftCancelAdd /-- Any `AddCommMagma G` that
satisfies `IsRightCancelAdd G` also satisfies `IsLeftCancelAdd G`. -/]
lemma CommMagma.IsRightCancelMul.toIsLeftCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsLeftCancelMul G :=
  ⟨fun _ _ _ h => mul_right_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

/-- Any `CommMagma G` that satisfies `IsLeftCancelMul G` also satisfies `IsRightCancelMul G`. -/
@[to_additive AddCommMagma.IsLeftCancelAdd.toIsRightCancelAdd /-- Any `AddCommMagma G` that
satisfies `IsLeftCancelAdd G` also satisfies `IsRightCancelAdd G`. -/]
lemma CommMagma.IsLeftCancelMul.toIsRightCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsRightCancelMul G :=
  ⟨fun _ _ _ h => mul_left_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

/-- Any `CommMagma G` that satisfies `IsLeftCancelMul G` also satisfies `IsCancelMul G`. -/
@[to_additive AddCommMagma.IsLeftCancelAdd.toIsCancelAdd /-- Any `AddCommMagma G` that satisfies
`IsLeftCancelAdd G` also satisfies `IsCancelAdd G`. -/]
lemma CommMagma.IsLeftCancelMul.toIsCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsCancelMul G := { CommMagma.IsLeftCancelMul.toIsRightCancelMul G with }

/-- Any `CommMagma G` that satisfies `IsRightCancelMul G` also satisfies `IsCancelMul G`. -/
@[to_additive AddCommMagma.IsRightCancelAdd.toIsCancelAdd /-- Any `AddCommMagma G` that satisfies
`IsRightCancelAdd G` also satisfies `IsCancelAdd G`. -/]
lemma CommMagma.IsRightCancelMul.toIsCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsCancelMul G := { CommMagma.IsRightCancelMul.toIsLeftCancelMul G with }

end CommMagma

/-- A `LeftCancelSemigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
@[ext]
class LeftCancelSemigroup (G : Type u) extends Semigroup G, IsLeftCancelMul G

library_note2 «lower cancel priority» /--
We lower the priority of inheriting from cancellative structures.
This attempts to avoid expensive checks involving bundling and unbundling with the `IsDomain` class.
since `IsDomain` already depends on `Semiring`, we can synthesize that one first.
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Why.20is.20.60simpNF.60.20complaining.20here.3F
-/
attribute [instance 75] LeftCancelSemigroup.toSemigroup -- See note [lower cancel priority]

/-- An `AddLeftCancelSemigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
@[ext]
class AddLeftCancelSemigroup (G : Type u) extends AddSemigroup G, IsLeftCancelAdd G

attribute [instance 75] AddLeftCancelSemigroup.toAddSemigroup -- See note [lower cancel priority]

attribute [to_additive] LeftCancelSemigroup

/-- Any `LeftCancelSemigroup` satisfies `IsLeftCancelMul`. -/
add_decl_doc LeftCancelSemigroup.toIsLeftCancelMul

/-- Any `AddLeftCancelSemigroup` satisfies `IsLeftCancelAdd`. -/
add_decl_doc AddLeftCancelSemigroup.toIsLeftCancelAdd

/-- A `RightCancelSemigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
@[ext]
class RightCancelSemigroup (G : Type u) extends Semigroup G, IsRightCancelMul G

attribute [instance 75] RightCancelSemigroup.toSemigroup -- See note [lower cancel priority]

/-- An `AddRightCancelSemigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
@[ext]
class AddRightCancelSemigroup (G : Type u) extends AddSemigroup G, IsRightCancelAdd G

attribute [instance 75] AddRightCancelSemigroup.toAddSemigroup -- See note [lower cancel priority]

attribute [to_additive] RightCancelSemigroup

/-- Any `RightCancelSemigroup` satisfies `IsRightCancelMul`. -/
add_decl_doc RightCancelSemigroup.toIsRightCancelMul

/-- Any `AddRightCancelSemigroup` satisfies `IsRightCancelAdd`. -/
add_decl_doc AddRightCancelSemigroup.toIsRightCancelAdd

/-- Bundling an `Add` and `Zero` structure together without any axioms about their
compatibility. See `AddZeroClass` for the additional assumption that 0 is an identity. -/
class AddZero (M : Type*) extends Zero M, Add M

/-- Bundling a `Mul` and `One` structure together without any axioms about their
compatibility. See `MulOneClass` for the additional assumption that 1 is an identity. -/
@[to_additive, ext]
class MulOne (M : Type*) extends One M, Mul M

/-- Typeclass for expressing that a type `M` with addition and a zero satisfies
`0 + a = a` and `a + 0 = a` for all `a : M`. -/
class AddZeroClass (M : Type u) extends AddZero M where
  /-- Zero is a left neutral element for addition -/
  protected zero_add : ∀ a : M, 0 + a = a
  /-- Zero is a right neutral element for addition -/
  protected add_zero : ∀ a : M, a + 0 = a


/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
@[to_additive]
class MulOneClass (M : Type u) extends MulOne M where
  /-- One is a left neutral element for multiplication -/
  protected one_mul : ∀ a : M, 1 * a = a
  /-- One is a right neutral element for multiplication -/
  protected mul_one : ∀ a : M, a * 1 = a

@[to_additive (attr := ext)]
theorem MulOneClass.ext {M : Type u} : ∀ ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul → m₁ = m₂ := by
  rintro @⟨@⟨⟨one₁⟩, ⟨mul₁⟩⟩, one_mul₁, mul_one₁⟩ @⟨@⟨⟨one₂⟩, ⟨mul₂⟩⟩, one_mul₂, mul_one₂⟩ ⟨rfl⟩
  -- FIXME (See https://github.com/leanprover/lean4/issues/1711)
  -- congr
  suffices one₁ = one₂ by cases this; rfl
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂)

section MulOneClass

variable {M : Type u} [MulOneClass M]

@[to_additive (attr := simp)]
theorem one_mul : ∀ a : M, 1 * a = a :=
  MulOneClass.one_mul

@[to_additive (attr := simp)]
theorem mul_one : ∀ a : M, a * 1 = a :=
  MulOneClass.mul_one

end MulOneClass

section

variable {M : Type u}

attribute [to_additive existing] npowRec

variable [One M] [Semigroup M] (m n : ℕ) (hn : n ≠ 0) (a : M) (ha : 1 * a = a)
include hn ha

@[to_additive] theorem npowRec_add : npowRec (m + n) a = npowRec m a * npowRec n a := by
  obtain _ | n := n; · exact (hn rfl).elim
  induction n with
  | zero => simp only [npowRec, ha]
  | succ n ih => rw [← Nat.add_assoc, npowRec, ih n.succ_ne_zero]; simp only [npowRec, mul_assoc]

@[to_additive] theorem npowRec_succ : npowRec (n + 1) a = a * npowRec n a := by
  rw [Nat.add_comm, npowRec_add 1 n hn a ha, npowRec, npowRec, ha]

end

library_note2 «forgetful inheritance» /--
Suppose that one can put two mathematical structures on a type, a rich one `R` and a poor one
`P`, and that one can deduce the poor structure from the rich structure through a map `F` (called a
forgetful functor) (think `R = MetricSpace` and `P = TopologicalSpace`). A possible
implementation would be to have a type class `rich` containing a field `R`, a type class `poor`
containing a field `P`, and an instance from `rich` to `poor`. However, this creates diamond
problems, and a better approach is to let `rich` extend `poor` and have a field saying that
`F R = P`.

To illustrate this, consider the pair `MetricSpace` / `TopologicalSpace`. Consider the topology
on a product of two metric spaces. With the first approach, it could be obtained by going first from
each metric space to its topology, and then taking the product topology. But it could also be
obtained by considering the product metric space (with its sup distance) and then the topology
coming from this distance. These would be the same topology, but not definitionally, which means
that from the point of view of Lean's kernel, there would be two different `TopologicalSpace`
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
compared to mathlib, as there is an intermediate typeclass between `MetricSpace` and
`TopologicalSpace` called `UniformSpace`. The above scheme is used at both levels, embedding a
topology in the uniform space structure, and a uniform structure in the metric space structure.

Note also that, when `P` is a proposition, there is no such issue as any two proofs of `P` are
definitionally equivalent in Lean.

To avoid boilerplate, there are some designs that can automatically fill the poor fields when
creating a rich structure if one doesn't want to do something special about them. For instance,
in the definition of metric spaces, default tactics fill the uniform space fields if they are
not given explicitly. One can also have a helper function creating the rich structure from a
structure with fewer fields, where the helper function fills the remaining fields. See for instance
`UniformSpace.ofCore` or `RealInnerProduct.ofCore`.

For more details on this question, called the forgetful inheritance pattern, see [Competing
inheritance paths in dependent type theory: a case study in functional
analysis](https://hal.inria.fr/hal-02463336).
-/


/-!
### Design note on `AddMonoid` and `Monoid`

An `AddMonoid` has a natural `ℕ`-action, defined by `n • a = a + ... + a`, that we want to declare
as an instance as it makes it possible to use the language of linear algebra. However, there are
often other natural `ℕ`-actions. For instance, for any semiring `R`, the space of polynomials
`Polynomial R` has a natural `R`-action defined by multiplication on the coefficients. This means
that `Polynomial ℕ` would have two natural `ℕ`-actions, which are equal but not defeq. The same
goes for linear maps, tensor products, and so on (and even for `ℕ` itself).

To solve this issue, we embed an `ℕ`-action in the definition of an `AddMonoid` (which is by
default equal to the naive action `a + ... + a`, but can be adjusted when needed), and declare
a `SMul ℕ α` instance using this action. See Note [forgetful inheritance] for more
explanations on this pattern.

For example, when we define `Polynomial R`, then we declare the `ℕ`-action to be by multiplication
on each coefficient (using the `ℕ`-action on `R` that comes from the fact that `R` is
an `AddMonoid`). In this way, the two natural `SMul ℕ (Polynomial ℕ)` instances are defeq.

The tactic `to_additive` transfers definitions and results from multiplicative monoids to additive
monoids. To work, it has to map fields to fields. This means that we should also add corresponding
fields to the multiplicative structure `Monoid`, which could solve defeq problems for powers if
needed. These problems do not come up in practice, so most of the time we will not need to adjust
the `npow` field when defining multiplicative objects.
-/

/-- Exponentiation by repeated squaring. -/
@[to_additive /-- Scalar multiplication by repeated self-addition,
the additive version of exponentiation by repeated squaring. -/]
def npowBinRec {M : Type*} [One M] [Mul M] (k : ℕ) : M → M :=
  npowBinRec.go k 1
where
  /-- Auxiliary tail-recursive implementation for `npowBinRec`. -/
  @[to_additive nsmulBinRec.go /-- Auxiliary tail-recursive implementation for `nsmulBinRec`. -/]
  go (k : ℕ) : M → M → M :=
    k.binaryRec (fun y _ ↦ y) fun bn _n fn y x ↦ fn (cond bn (y * x) y) (x * x)

/--
A variant of `npowRec` which is a semigroup homomorphism from `ℕ₊` to `M`.
-/
def npowRec' {M : Type*} [One M] [Mul M] : ℕ → M → M
  | 0, _ => 1
  | 1, m => m
  | k + 2, m => npowRec' (k + 1) m * m

/--
A variant of `nsmulRec` which is a semigroup homomorphism from `ℕ₊` to `M`.
-/
def nsmulRec' {M : Type*} [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | 1, m => m
  | k + 2, m => nsmulRec' (k + 1) m + m

attribute [to_additive existing] npowRec'

@[to_additive]
theorem npowRec'_succ {M : Type*} [Mul M] [One M] {k : ℕ} (_ : k ≠ 0) (m : M) :
    npowRec' (k + 1) m = npowRec' k m * m :=
  match k with
  | _ + 1 => rfl

@[to_additive]
theorem npowRec'_two_mul {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) :
    npowRec' (2 * k) m = npowRec' k (m * m) := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | 1 => simp [npowRec']
    | k + 2 => simp [npowRec', ← mul_assoc, Nat.mul_add, ← ih]

@[to_additive]
theorem npowRec'_mul_comm {M : Type*} [Semigroup M] [One M] {k : ℕ} (k0 : k ≠ 0) (m : M) :
    m * npowRec' k m = npowRec' k m * m := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 1 => simp [npowRec']
    | k + 2 => simp [npowRec', ← mul_assoc, ih]

@[to_additive]
theorem npowRec_eq {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) :
    npowRec (k + 1) m = 1 * npowRec' (k + 1) m := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | k + 1 =>
      rw [npowRec, npowRec'_succ k.succ_ne_zero, ← mul_assoc]
      congr
      simp [ih]

@[to_additive]
theorem npowBinRec.go_spec {M : Type*} [Semigroup M] [One M] (k : ℕ) (m n : M) :
    npowBinRec.go (k + 1) m n = m * npowRec' (k + 1) n := by
  unfold go
  generalize hk : k + 1 = k'
  replace hk : k' ≠ 0 := by omega
  induction k' using Nat.binaryRecFromOne generalizing n m with
  | zero => simp at hk
  | one => simp [npowRec']
  | bit b k' k'0 ih =>
    rw [Nat.binaryRec_eq _ _ (Or.inl rfl), ih _ _ k'0]
    cases b <;> simp only [Nat.bit, cond_false, cond_true, npowRec'_two_mul]
    rw [npowRec'_succ (by cutsat), npowRec'_two_mul, ← npowRec'_two_mul,
      ← npowRec'_mul_comm (by cutsat), mul_assoc]

/--
An abbreviation for `npowRec` with an additional typeclass assumption on associativity
so that we can use `@[csimp]` to replace it with an implementation by repeated squaring
in compiled code.
-/
@[to_additive
/-- An abbreviation for `nsmulRec` with an additional typeclass assumptions on associativity
so that we can use `@[csimp]` to replace it with an implementation by repeated doubling in compiled
code as an automatic parameter. -/]
abbrev npowRecAuto {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) : M :=
  npowRec k m

/--
An abbreviation for `npowBinRec` with an additional typeclass assumption on associativity
so that we can use it in `@[csimp]` for more performant code generation.
-/
@[to_additive
/-- An abbreviation for `nsmulBinRec` with an additional typeclass assumption on associativity
so that we can use it in `@[csimp]` for more performant code generation
as an automatic parameter. -/]
abbrev npowBinRecAuto {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) : M :=
  npowBinRec k m

@[to_additive (attr := csimp)]
theorem npowRec_eq_npowBinRec : @npowRecAuto = @npowBinRecAuto := by
  funext M _ _ k m
  rw [npowBinRecAuto, npowRecAuto, npowBinRec]
  match k with
  | 0 => rw [npowRec, npowBinRec.go, Nat.binaryRec_zero]
  | k + 1 => rw [npowBinRec.go_spec, npowRec_eq]

/-- An `AddMonoid` is an `AddSemigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  /-- Multiplication by a natural number.
  Set this to `nsmulRec` unless `Module` diamonds are possible. -/
  protected nsmul : ℕ → M → M
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  protected nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  protected nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = nsmul n x + x := by intros; rfl

attribute [instance 150] AddSemigroup.toAdd
attribute [instance 50] AddZero.toAdd

/-- A `Monoid` is a `Semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[to_additive]
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  /-- Raising to the power of a natural number. -/
  protected npow : ℕ → M → M := npowRecAuto
  /-- Raising to the power `(0 : ℕ)` gives `1`. -/
  protected npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  /-- Raising to the power `(n + 1 : ℕ)` behaves as expected. -/
  protected npow_succ : ∀ (n : ℕ) (x), npow (n + 1) x = npow n x * x := by intros; rfl

@[default_instance high] instance Monoid.toNatPow {M : Type*} [Monoid M] : Pow M ℕ :=
  ⟨fun x n ↦ Monoid.npow n x⟩

instance AddMonoid.toNatSMul {M : Type*} [AddMonoid M] : SMul ℕ M :=
  ⟨AddMonoid.nsmul⟩

attribute [to_additive existing toNatSMul] Monoid.toNatPow

section Monoid
variable {M : Type*} [Monoid M] {a b c : M}

@[to_additive (attr := simp) nsmul_eq_smul]
theorem npow_eq_pow (n : ℕ) (x : M) : Monoid.npow n x = x ^ n :=
  rfl

@[to_additive] lemma left_inv_eq_right_inv (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]

-- This lemma is higher priority than later `zero_smul` so that the `simpNF` is happy
@[to_additive (attr := simp high) zero_nsmul]
theorem pow_zero (a : M) : a ^ 0 = 1 :=
  Monoid.npow_zero _

@[to_additive succ_nsmul]
theorem pow_succ (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a :=
  Monoid.npow_succ n a

@[to_additive (attr := simp) one_nsmul]
lemma pow_one (a : M) : a ^ 1 = a := by rw [pow_succ, pow_zero, one_mul]

@[to_additive succ_nsmul'] lemma pow_succ' (a : M) : ∀ n, a ^ (n + 1) = a * a ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ _ n, pow_succ, pow_succ', mul_assoc]

@[to_additive] lemma mul_pow_mul (a b : M) (n : ℕ) :
    (a * b) ^ n * a = a * (b * a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', ← ih, mul_assoc]

@[to_additive]
lemma pow_mul_comm' (a : M) (n : ℕ) : a ^ n * a = a * a ^ n := by rw [← pow_succ, pow_succ']

/-- Note that most of the lemmas about powers of two refer to it as `sq`. -/
@[to_additive two_nsmul] lemma pow_two (a : M) : a ^ 2 = a * a := by rw [pow_succ, pow_one]

-- TODO: Should `alias` automatically transfer `to_additive` statements?
@[to_additive existing two_nsmul] alias sq := pow_two

@[to_additive three'_nsmul]
lemma pow_three' (a : M) : a ^ 3 = a * a * a := by rw [pow_succ, pow_two]

@[to_additive three_nsmul]
lemma pow_three (a : M) : a ^ 3 = a * (a * a) := by rw [pow_succ', pow_two]

-- This lemma is higher priority than later `smul_zero` so that the `simpNF` is happy
@[to_additive (attr := simp high) nsmul_zero] lemma one_pow : ∀ n, (1 : M) ^ n = 1
  | 0 => pow_zero _
  | n + 1 => by rw [pow_succ, one_pow, one_mul]

@[to_additive add_nsmul]
lemma pow_add (a : M) (m : ℕ) : ∀ n, a ^ (m + n) = a ^ m * a ^ n
  | 0 => by rw [Nat.add_zero, pow_zero, mul_one]
  | n + 1 => by rw [pow_succ, ← mul_assoc, ← pow_add, ← pow_succ, Nat.add_assoc]

@[to_additive] lemma pow_mul_comm (a : M) (m n : ℕ) : a ^ m * a ^ n = a ^ n * a ^ m := by
  rw [← pow_add, ← pow_add, Nat.add_comm]

@[to_additive mul_nsmul] lemma pow_mul (a : M) (m : ℕ) : ∀ n, a ^ (m * n) = (a ^ m) ^ n
  | 0 => by rw [Nat.mul_zero, pow_zero, pow_zero]
  | n + 1 => by rw [Nat.mul_succ, pow_add, pow_succ, pow_mul]

@[to_additive mul_nsmul']
lemma pow_mul' (a : M) (m n : ℕ) : a ^ (m * n) = (a ^ n) ^ m := by rw [Nat.mul_comm, pow_mul]

@[to_additive nsmul_left_comm]
lemma pow_right_comm (a : M) (m n : ℕ) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]

end Monoid

/-- An additive monoid is torsion-free if scalar multiplication by every non-zero element `n : ℕ` is
injective. -/
@[mk_iff]
class IsAddTorsionFree (M : Type*) [AddMonoid M] where
  protected nsmul_right_injective ⦃n : ℕ⦄ (hn : n ≠ 0) : Injective fun a : M ↦ n • a

/-- A monoid is torsion-free if power by every non-zero element `n : ℕ` is injective. -/
@[to_additive, mk_iff]
class IsMulTorsionFree (M : Type*) [Monoid M] where
  protected pow_left_injective ⦃n : ℕ⦄ (hn : n ≠ 0) : Injective fun a : M ↦ a ^ n

attribute [to_additive existing] isMulTorsionFree_iff

/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M

/-- A commutative monoid is a monoid with commutative `(*)`. -/
@[to_additive]
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M

section LeftCancelMonoid

/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddLeftCancelSemigroup` is not enough. -/
class AddLeftCancelMonoid (M : Type u) extends AddMonoid M, AddLeftCancelSemigroup M

attribute [instance 75] AddLeftCancelMonoid.toAddMonoid -- See note [lower cancel priority]

/-- A monoid in which multiplication is left-cancellative. -/
@[to_additive]
class LeftCancelMonoid (M : Type u) extends Monoid M, LeftCancelSemigroup M

attribute [instance 75] LeftCancelMonoid.toMonoid -- See note [lower cancel priority]

end LeftCancelMonoid

section RightCancelMonoid

/-- An additive monoid in which addition is right-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddRightCancelSemigroup` is not enough. -/
class AddRightCancelMonoid (M : Type u) extends AddMonoid M, AddRightCancelSemigroup M

attribute [instance 75] AddRightCancelMonoid.toAddMonoid -- See note [lower cancel priority]

/-- A monoid in which multiplication is right-cancellative. -/
@[to_additive]
class RightCancelMonoid (M : Type u) extends Monoid M, RightCancelSemigroup M

attribute [instance 75] RightCancelMonoid.toMonoid -- See note [lower cancel priority]

end RightCancelMonoid

section CancelMonoid

/-- An additive monoid in which addition is cancellative on both sides.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddRightCancelMonoid` is not enough. -/
class AddCancelMonoid (M : Type u) extends AddLeftCancelMonoid M, AddRightCancelMonoid M

/-- A monoid in which multiplication is cancellative. -/
@[to_additive]
class CancelMonoid (M : Type u) extends LeftCancelMonoid M, RightCancelMonoid M

/-- Commutative version of `AddCancelMonoid`. -/
class AddCancelCommMonoid (M : Type u) extends AddCommMonoid M, AddLeftCancelMonoid M

attribute [instance 75] AddCancelCommMonoid.toAddCommMonoid -- See note [lower cancel priority]

/-- Commutative version of `CancelMonoid`. -/
@[to_additive]
class CancelCommMonoid (M : Type u) extends CommMonoid M, LeftCancelMonoid M

attribute [instance 75] CancelCommMonoid.toCommMonoid -- See note [lower cancel priority]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CancelCommMonoid.toCancelMonoid (M : Type u) [CancelCommMonoid M] :
    CancelMonoid M :=
  { CommMagma.IsLeftCancelMul.toIsRightCancelMul M with }

/-- Any `CancelMonoid G` satisfies `IsCancelMul G`. -/
@[to_additive /-- Any `AddCancelMonoid G` satisfies `IsCancelAdd G`. -/]
instance (priority := 100) CancelMonoid.toIsCancelMul (M : Type u) [CancelMonoid M] :
    IsCancelMul M where

end CancelMonoid

/-- The fundamental power operation in a group. `zpowRec n a = a*a*...*a` n times, for integer `n`.
Use instead `a ^ n`, which has better definitional behavior. -/
def zpowRec [One G] [Mul G] [Inv G] (npow : ℕ → G → G := npowRec) : ℤ → G → G
  | Int.ofNat n, a => npow n a
  | Int.negSucc n, a => (npow n.succ a)⁻¹

/-- The fundamental scalar multiplication in an additive group. `zpowRec n a = a+a+...+a` n
times, for integer `n`. Use instead `n • a`, which has better definitional behavior. -/
def zsmulRec [Zero G] [Add G] [Neg G] (nsmul : ℕ → G → G := nsmulRec) : ℤ → G → G
  | Int.ofNat n, a => nsmul n a
  | Int.negSucc n, a => -nsmul n.succ a

attribute [to_additive existing] zpowRec

section InvolutiveInv

/-- Auxiliary typeclass for types with an involutive `Neg`. -/
class InvolutiveNeg (A : Type*) extends Neg A where
  protected neg_neg : ∀ x : A, - -x = x

/-- Auxiliary typeclass for types with an involutive `Inv`. -/
@[to_additive]
class InvolutiveInv (G : Type*) extends Inv G where
  protected inv_inv : ∀ x : G, x⁻¹⁻¹ = x

variable [InvolutiveInv G]

@[to_additive (attr := simp)]
theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
  InvolutiveInv.inv_inv _

end InvolutiveInv

/-!
### Design note on `DivInvMonoid`/`SubNegMonoid` and `DivisionMonoid`/`SubtractionMonoid`

Those two pairs of made-up classes fulfill slightly different roles.

`DivInvMonoid`/`SubNegMonoid` provides the minimum amount of information to define the
`ℤ` action (`zpow` or `zsmul`). Further, it provides a `div` field, matching the forgetful
inheritance pattern. This is useful to shorten extension clauses of stronger structures (`Group`,
`GroupWithZero`, `DivisionRing`, `Field`) and for a few structures with a rather weak
pseudo-inverse (`Matrix`).

`DivisionMonoid`/`SubtractionMonoid` is targeted at structures with stronger pseudo-inverses. It
is an ad hoc collection of axioms that are mainly respected by three things:
* Groups
* Groups with zero
* The pointwise monoids `Set α`, `Finset α`, `Filter α`

It acts as a middle ground for structures with an inversion operator that plays well with
multiplication, except for the fact that it might not be a true inverse (`a / a ≠ 1` in general).
The axioms are pretty arbitrary (many other combinations are equivalent to it), but they are
independent:
* Without `DivisionMonoid.div_eq_mul_inv`, you can define `/` arbitrarily.
* Without `DivisionMonoid.inv_inv`, you can consider `WithTop Unit` with `a⁻¹ = ⊤` for all `a`.
* Without `DivisionMonoid.mul_inv_rev`, you can consider `WithTop α` with `a⁻¹ = a` for all `a`
  where `α` noncommutative.
* Without `DivisionMonoid.inv_eq_of_mul`, you can consider any `CommMonoid` with `a⁻¹ = a` for all
  `a`.

As a consequence, a few natural structures do not fit in this framework. For example, `ENNReal`
respects everything except for the fact that `(0 * ∞)⁻¹ = 0⁻¹ = ∞` while `∞⁻¹ * 0⁻¹ = 0 * ∞ = 0`.
-/

/-- In a class equipped with instances of both `Monoid` and `Inv`, this definition records what the
default definition for `Div` would be: `a * b⁻¹`.  This is later provided as the default value for
the `Div` instance in `DivInvMonoid`.

We keep it as a separate definition rather than inlining it in `DivInvMonoid` so that the `Div`
field of individual `DivInvMonoid`s constructed using that default value will not be unfolded at
`.instance` transparency. -/
def DivInvMonoid.div' {G : Type u} [Monoid G] [Inv G] (a b : G) : G := a * b⁻¹

/-- A `DivInvMonoid` is a `Monoid` with operations `/` and `⁻¹` satisfying
`div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`.

This deduplicates the name `div_eq_mul_inv`.
The default for `div` is such that `a / b = a * b⁻¹` holds by definition.

Adding `div` as a field rather than defining `a / b := a * b⁻¹` allows us to
avoid certain classes of unification failures, for example:
Let `Foo X` be a type with a `∀ X, Div (Foo X)` instance but no
`∀ X, Inv (Foo X)`, e.g. when `Foo X` is a `EuclideanDomain`. Suppose we
also have an instance `∀ X [Cromulent X], GroupWithZero (Foo X)`. Then the
`(/)` coming from `GroupWithZero.div` cannot be definitionally equal to
the `(/)` coming from `Foo.Div`.

In the same way, adding a `zpow` field makes it possible to avoid definitional failures
in diamonds. See the definition of `Monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  protected div := DivInvMonoid.div'
  /-- `a / b := a * b⁻¹` -/
  protected div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by intros; rfl
  /-- The power operation: `a ^ n = a * ··· * a`; `a ^ (-n) = a⁻¹ * ··· a⁻¹` (`n` times) -/
  protected zpow : ℤ → G → G := zpowRec npowRec
  /-- `a ^ 0 = 1` -/
  protected zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  /-- `a ^ (n + 1) = a ^ n * a` -/
  protected zpow_succ' (n : ℕ) (a : G) : zpow n.succ a = zpow n a * a := by
    intros; rfl
  /-- `a ^ -(n + 1) = (a ^ (n + 1))⁻¹` -/
  protected zpow_neg' (n : ℕ) (a : G) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ := by intros; rfl

/-- In a class equipped with instances of both `AddMonoid` and `Neg`, this definition records what
the default definition for `Sub` would be: `a + -b`.  This is later provided as the default value
for the `Sub` instance in `SubNegMonoid`.

We keep it as a separate definition rather than inlining it in `SubNegMonoid` so that the `Sub`
field of individual `SubNegMonoid`s constructed using that default value will not be unfolded at
`.instance` transparency. -/
def SubNegMonoid.sub' {G : Type u} [AddMonoid G] [Neg G] (a b : G) : G := a + -b

attribute [to_additive existing SubNegMonoid.sub'] DivInvMonoid.div'

/-- A `SubNegMonoid` is an `AddMonoid` with unary `-` and binary `-` operations
satisfying `sub_eq_add_neg : ∀ a b, a - b = a + -b`.

The default for `sub` is such that `a - b = a + -b` holds by definition.

Adding `sub` as a field rather than defining `a - b := a + -b` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, Sub (Foo X)` instance but no
`∀ X, Neg (Foo X)`. Suppose we also have an instance
`∀ X [Cromulent X], AddGroup (Foo X)`. Then the `(-)` coming from
`AddGroup.sub` cannot be definitionally equal to the `(-)` coming from
`Foo.Sub`.

In the same way, adding a `zsmul` field makes it possible to avoid definitional failures
in diamonds. See the definition of `AddMonoid` and Note [forgetful inheritance] for more
explanations on this.
-/
class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  protected sub := SubNegMonoid.sub'
  protected sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by intros; rfl
  /-- Multiplication by an integer.
  Set this to `zsmulRec` unless `Module` diamonds are possible. -/
  protected zsmul : ℤ → G → G
  protected zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by intros; rfl
  protected zsmul_succ' (n : ℕ) (a : G) :
      zsmul n.succ a = zsmul n a + a := by
    intros; rfl
  protected zsmul_neg' (n : ℕ) (a : G) : zsmul (Int.negSucc n) a = -zsmul n.succ a := by
    intros; rfl

attribute [to_additive SubNegMonoid] DivInvMonoid

instance DivInvMonoid.toZPow {M} [DivInvMonoid M] : Pow M ℤ :=
  ⟨fun x n ↦ DivInvMonoid.zpow n x⟩

instance SubNegMonoid.toZSMul {M} [SubNegMonoid M] : SMul ℤ M :=
  ⟨SubNegMonoid.zsmul⟩

attribute [to_additive existing] DivInvMonoid.toZPow

/-- A group is called *cyclic* if it is generated by a single element. -/
class IsAddCyclic (G : Type u) [SMul ℤ G] : Prop where
  protected exists_zsmul_surjective : ∃ g : G, Function.Surjective (· • g : ℤ → G)

/-- A group is called *cyclic* if it is generated by a single element. -/
@[to_additive]
class IsCyclic (G : Type u) [Pow G ℤ] : Prop where
  protected exists_zpow_surjective : ∃ g : G, Function.Surjective (g ^ · : ℤ → G)

@[to_additive]
theorem exists_zpow_surjective (G : Type*) [Pow G ℤ] [IsCyclic G] :
    ∃ g : G, Function.Surjective (g ^ · : ℤ → G) :=
  IsCyclic.exists_zpow_surjective

section DivInvMonoid

variable [DivInvMonoid G]

@[to_additive (attr := simp) zsmul_eq_smul] theorem zpow_eq_pow (n : ℤ) (x : G) :
    DivInvMonoid.zpow n x = x ^ n :=
  rfl

@[to_additive (attr := simp) zero_zsmul] theorem zpow_zero (a : G) : a ^ (0 : ℤ) = 1 :=
  DivInvMonoid.zpow_zero' a

@[to_additive (attr := simp, norm_cast) natCast_zsmul]
theorem zpow_natCast (a : G) : ∀ n : ℕ, a ^ (n : ℤ) = a ^ n
  | 0 => (zpow_zero _).trans (pow_zero _).symm
  | n + 1 => calc
    a ^ (↑(n + 1) : ℤ) = a ^ (n : ℤ) * a := DivInvMonoid.zpow_succ' _ _
    _ = a ^ n * a := congrArg (· * a) (zpow_natCast a n)
    _ = a ^ (n + 1) := (pow_succ _ _).symm


@[to_additive ofNat_zsmul]
lemma zpow_ofNat (a : G) (n : ℕ) : a ^ (ofNat(n) : ℤ) = a ^ OfNat.ofNat n :=
  zpow_natCast ..

theorem zpow_negSucc (a : G) (n : ℕ) : a ^ (Int.negSucc n) = (a ^ (n + 1))⁻¹ := by
  rw [← zpow_natCast]
  exact DivInvMonoid.zpow_neg' n a

theorem negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : ℕ) :
    Int.negSucc n • a = -((n + 1) • a) := by
  rw [← natCast_zsmul]
  exact SubNegMonoid.zsmul_neg' n a

attribute [to_additive existing (attr := simp) negSucc_zsmul] zpow_negSucc

/-- Dividing by an element is the same as multiplying by its inverse.

This is a duplicate of `DivInvMonoid.div_eq_mul_inv` ensuring that the types unfold better.
-/
@[to_additive /-- Subtracting an element is the same as adding by its negative.
This is a duplicate of `SubNegMonoid.sub_eq_add_neg` ensuring that the types unfold better. -/]
theorem div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ :=
  DivInvMonoid.div_eq_mul_inv _ _

alias division_def := div_eq_mul_inv

@[to_additive]
theorem inv_eq_one_div (x : G) : x⁻¹ = 1 / x := by rw [div_eq_mul_inv, one_mul]

@[to_additive]
theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc _ _ _]

@[to_additive (attr := simp)]
theorem one_div (a : G) : 1 / a = a⁻¹ :=
  (inv_eq_one_div a).symm

@[to_additive (attr := simp) one_zsmul]
lemma zpow_one (a : G) : a ^ (1 : ℤ) = a := by rw [zpow_ofNat, pow_one]

@[to_additive two_zsmul] lemma zpow_two (a : G) : a ^ (2 : ℤ) = a * a := by rw [zpow_ofNat, pow_two]

@[to_additive neg_one_zsmul]
lemma zpow_neg_one (x : G) : x ^ (-1 : ℤ) = x⁻¹ :=
  (zpow_negSucc x 0).trans <| congr_arg Inv.inv (pow_one x)

@[to_additive]
lemma zpow_neg_coe_of_pos (a : G) : ∀ {n : ℕ}, 0 < n → a ^ (-(n : ℤ)) = (a ^ n)⁻¹
  | _ + 1, _ => zpow_negSucc _ _

end DivInvMonoid

section InvOneClass

/-- Typeclass for expressing that `-0 = 0`. -/
class NegZeroClass (G : Type*) extends Zero G, Neg G where
  protected neg_zero : -(0 : G) = 0

/-- A `SubNegMonoid` where `-0 = 0`. -/
class SubNegZeroMonoid (G : Type*) extends SubNegMonoid G, NegZeroClass G

/-- Typeclass for expressing that `1⁻¹ = 1`. -/
@[to_additive]
class InvOneClass (G : Type*) extends One G, Inv G where
  protected inv_one : (1 : G)⁻¹ = 1

/-- A `DivInvMonoid` where `1⁻¹ = 1`. -/
@[to_additive]
class DivInvOneMonoid (G : Type*) extends DivInvMonoid G, InvOneClass G

variable [InvOneClass G]

@[to_additive (attr := simp)]
theorem inv_one : (1 : G)⁻¹ = 1 :=
  InvOneClass.inv_one

end InvOneClass

/-- A `SubtractionMonoid` is a `SubNegMonoid` with involutive negation and such that
`-(a + b) = -b + -a` and `a + b = 0 → -a = b`. -/
class SubtractionMonoid (G : Type u) extends SubNegMonoid G, InvolutiveNeg G where
  protected neg_add_rev (a b : G) : -(a + b) = -b + -a
  /-- Despite the asymmetry of `neg_eq_of_add`, the symmetric version is true thanks to the
  involutivity of negation. -/
  protected neg_eq_of_add (a b : G) : a + b = 0 → -a = b

/-- A `DivisionMonoid` is a `DivInvMonoid` with involutive inversion and such that
`(a * b)⁻¹ = b⁻¹ * a⁻¹` and `a * b = 1 → a⁻¹ = b`.

This is the immediate common ancestor of `Group` and `GroupWithZero`. -/
@[to_additive]
class DivisionMonoid (G : Type u) extends DivInvMonoid G, InvolutiveInv G where
  protected mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
  /-- Despite the asymmetry of `inv_eq_of_mul`, the symmetric version is true thanks to the
  involutivity of inversion. -/
  protected inv_eq_of_mul (a b : G) : a * b = 1 → a⁻¹ = b

section DivisionMonoid

variable [DivisionMonoid G] {a b : G}

@[to_additive (attr := simp) neg_add_rev]
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  DivisionMonoid.mul_inv_rev _ _

@[to_additive]
theorem inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b :=
  DivisionMonoid.inv_eq_of_mul _ _

@[to_additive]
theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a := by
  rw [← inv_eq_of_mul_eq_one_right h, inv_inv]

@[to_additive]
theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ :=
  (inv_eq_of_mul_eq_one_left h).symm

end DivisionMonoid

/-- Commutative `SubtractionMonoid`. -/
class SubtractionCommMonoid (G : Type u) extends SubtractionMonoid G, AddCommMonoid G

/-- Commutative `DivisionMonoid`.

This is the immediate common ancestor of `CommGroup` and `CommGroupWithZero`. -/
@[to_additive SubtractionCommMonoid]
class DivisionCommMonoid (G : Type u) extends DivisionMonoid G, CommMonoid G

/-- A `Group` is a `Monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`.

There is also a division operation `/` such that `a / b = a * b⁻¹`,
with a default so that `a / b = a * b⁻¹` holds by definition.

Use `Group.ofLeftAxioms` or `Group.ofRightAxioms` to define a group structure
on a type with the minimum proof obligations.
-/
class Group (G : Type u) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

/-- An `AddGroup` is an `AddMonoid` with a unary `-` satisfying `-a + a = 0`.

There is also a binary operation `-` such that `a - b = a + -b`,
with a default so that `a - b = a + -b` holds by definition.

Use `AddGroup.ofLeftAxioms` or `AddGroup.ofRightAxioms` to define an
additive group structure on a type with the minimum proof obligations.
-/
class AddGroup (A : Type u) extends SubNegMonoid A where
  protected neg_add_cancel : ∀ a : A, -a + a = 0

attribute [to_additive] Group

section Group

variable [Group G] {a b : G}

@[to_additive (attr := simp)]
theorem inv_mul_cancel (a : G) : a⁻¹ * a = 1 :=
  Group.inv_mul_cancel a

@[to_additive]
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_cancel a) h

@[to_additive (attr := simp)]
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  rw [← inv_mul_cancel a⁻¹, inv_eq_of_mul (inv_mul_cancel a)]

@[to_additive (attr := simp) sub_self]
theorem div_self' (a : G) : a / a = 1 := by rw [div_eq_mul_inv, mul_inv_cancel a]

@[to_additive (attr := simp)]
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]

@[to_additive (attr := simp)]
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv_cancel, one_mul]

@[to_additive (attr := simp)]
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_inv_cancel, mul_one]

@[to_additive (attr := simp)]
theorem mul_div_cancel_right (a b : G) : a * b / b = a := by
  rw [div_eq_mul_inv, mul_inv_cancel_right a b]

@[to_additive (attr := simp)]
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul_cancel, mul_one]

@[to_additive (attr := simp)]
theorem div_mul_cancel (a b : G) : a / b * b = a := by
  rw [div_eq_mul_inv, inv_mul_cancel_right a b]

@[to_additive]
instance (priority := 100) Group.toDivisionMonoid : DivisionMonoid G :=
  { inv_inv := fun a ↦ inv_eq_of_mul (inv_mul_cancel a)
    mul_inv_rev :=
      fun a b ↦ inv_eq_of_mul <| by rw [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
    inv_eq_of_mul := fun _ _ ↦ inv_eq_of_mul }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) Group.toCancelMonoid : CancelMonoid G where
  mul_right_cancel := fun a b c h ↦ by
    rw [← mul_inv_cancel_right b a, show b * a = c * a from h, mul_inv_cancel_right]
  mul_left_cancel := fun a {b c} h ↦ by
    rw [← inv_mul_cancel_left a b, show a * b = a * c from h, inv_mul_cancel_left]

end Group

/-- An additive commutative group is an additive group with commutative `(+)`. -/
class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

/-- A commutative group is a group with commutative `(*)`. -/
@[to_additive]
class CommGroup (G : Type u) extends Group G, CommMonoid G

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

@[to_additive (attr := simp)] lemma inv_mul_cancel_comm (a b : G) : a⁻¹ * b * a = b := by
  rw [mul_comm, mul_inv_cancel_left]

@[to_additive (attr := simp)]
lemma mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b := by rw [mul_comm, inv_mul_cancel_left]

@[to_additive (attr := simp)] lemma inv_mul_cancel_comm_assoc (a b : G) : a⁻¹ * (b * a) = b := by
  rw [mul_comm, mul_inv_cancel_right]

@[to_additive (attr := simp)] lemma mul_inv_cancel_comm_assoc (a b : G) : a * (b * a⁻¹) = b := by
  rw [mul_comm, inv_mul_cancel_right]

end CommGroup

section IsCommutative

/-- A Prop stating that the addition is commutative. -/
class IsAddCommutative (M : Type*) [Add M] : Prop where
  is_comm : Std.Commutative (α := M) (· + ·)

/-- A Prop stating that the multiplication is commutative. -/
@[to_additive]
class IsMulCommutative (M : Type*) [Mul M] : Prop where
  is_comm : Std.Commutative (α := M) (· * ·)

@[to_additive]
instance (priority := 100) CommMonoid.ofIsMulCommutative {M : Type*} [Monoid M]
    [IsMulCommutative M] :
    CommMonoid M where
  mul_comm := IsMulCommutative.is_comm.comm

@[to_additive]
instance (priority := 100) CommGroup.ofIsMulCommutative {G : Type*} [Group G] [IsMulCommutative G] :
    CommGroup G where

end IsCommutative

/-! We initialize all projections for `@[simps]` here, so that we don't have to do it in later
files.

Note: the lemmas generated for the `npow`/`zpow` projections will *not* apply to `x ^ y`, since the
argument order of these projections doesn't match the argument order of `^`.
The `nsmul`/`zsmul` lemmas will be correct. -/
initialize_simps_projections Semigroup
initialize_simps_projections AddSemigroup
initialize_simps_projections CommSemigroup
initialize_simps_projections AddCommSemigroup
initialize_simps_projections LeftCancelSemigroup
initialize_simps_projections AddLeftCancelSemigroup
initialize_simps_projections RightCancelSemigroup
initialize_simps_projections AddRightCancelSemigroup
initialize_simps_projections Monoid
initialize_simps_projections AddMonoid
initialize_simps_projections CommMonoid
initialize_simps_projections AddCommMonoid
initialize_simps_projections LeftCancelMonoid
initialize_simps_projections AddLeftCancelMonoid
initialize_simps_projections RightCancelMonoid
initialize_simps_projections AddRightCancelMonoid
initialize_simps_projections CancelMonoid
initialize_simps_projections AddCancelMonoid
initialize_simps_projections CancelCommMonoid
initialize_simps_projections AddCancelCommMonoid
initialize_simps_projections DivInvMonoid
initialize_simps_projections SubNegMonoid
initialize_simps_projections DivInvOneMonoid
initialize_simps_projections SubNegZeroMonoid
initialize_simps_projections DivisionMonoid
initialize_simps_projections SubtractionMonoid
initialize_simps_projections DivisionCommMonoid
initialize_simps_projections SubtractionCommMonoid
initialize_simps_projections Group
initialize_simps_projections AddGroup
initialize_simps_projections CommGroup
initialize_simps_projections AddCommGroup
