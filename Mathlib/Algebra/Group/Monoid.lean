/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
module

public import Batteries.Logic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Data.Nat.BinaryRec
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Push.Attr

/-!
# Monoids

This file defines additive and multiplicative algebraic structures with a distinguished zero or one,
up to and including monoids. Structures that do not require an identity are defined in
`Mathlib.Algebra.Group.Semigroup`.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered Function.const_injective

open Function

variable {G : Type*}

/-- Bundling an `Add` and `Zero` structure together without any axioms about their
compatibility. See `AddZeroClass` for the additional assumption that 0 is an identity. -/
class AddZero (M : Type*) extends Zero M, Add M

/-- Bundling a `Mul` and `One` structure together without any axioms about their
compatibility. See `MulOneClass` for the additional assumption that 1 is an identity. -/
@[to_additive (attr := ext)]
class MulOne (M : Type*) extends One M, Mul M

/-- An additive monoid is Dedekind-finite if every left inverse is also a right inverse.
Also called von Neumann-finite or directly finite. -/
class IsDedekindFiniteAddMonoid (M : Type*) [AddZero M] : Prop where
  add_eq_zero_symm {a b : M} : a + b = 0 → b + a = 0

/-- A monoid is Dedekind-finite if every left inverse is also a right inverse.
It is more common to talk about Dedekind-finite rings, but https://arxiv.org/abs/2102.01598
does define Dedekind-finite monoids in §2.2. -/
@[to_additive (attr := mk_iff)] class IsDedekindFiniteMonoid (M : Type*) [MulOne M] : Prop where
  mul_eq_one_symm {a b : M} : a * b = 1 → b * a = 1

export IsDedekindFiniteMonoid (mul_eq_one_symm)
export IsDedekindFiniteAddMonoid (add_eq_zero_symm)
attribute [to_additive existing] isDedekindFiniteMonoid_iff

@[to_additive] theorem mul_eq_one_comm {M} [MulOne M] [IsDedekindFiniteMonoid M] {a b : M} :
    a * b = 1 ↔ b * a = 1 where
  mp := mul_eq_one_symm
  mpr := mul_eq_one_symm

@[to_additive] instance (priority := low) (M) [MulOne M] [IsMulCommutative M] :
    IsDedekindFiniteMonoid M where
  mul_eq_one_symm := mul_comm' .. |>.trans

/-- Typeclass for expressing that a type `M` with addition and a zero satisfies
`0 + a = a` and `a + 0 = a` for all `a : M`. -/
class AddZeroClass (M : Type*) extends Zero M, Add M, AddZero M where
  /-- Zero is a left neutral element for addition -/
  protected zero_add : ∀ a : M, 0 + a = a
  /-- Zero is a right neutral element for addition -/
  protected add_zero : ∀ a : M, a + 0 = a

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
@[to_additive]
class MulOneClass (M : Type*) extends One M, Mul M, MulOne M where
  /-- One is a left neutral element for multiplication -/
  protected one_mul : ∀ a : M, 1 * a = a
  /-- One is a right neutral element for multiplication -/
  protected mul_one : ∀ a : M, a * 1 = a

@[to_additive (attr := ext)]
theorem MulOneClass.ext {M : Type*} : ∀ ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul → m₁ = m₂ := by
  rintro @⟨⟨one₁⟩, ⟨mul₁⟩, one_mul₁, mul_one₁⟩ @⟨⟨one₂⟩, ⟨mul₂⟩, one_mul₂, mul_one₂⟩ ⟨rfl⟩
  congr
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂)

section MulOneClass

variable {M : Type*} [MulOneClass M]

@[to_additive (attr := simp)]
theorem one_mul : ∀ a : M, 1 * a = a :=
  MulOneClass.one_mul

@[to_additive (attr := simp)]
theorem mul_one : ∀ a : M, a * 1 = a :=
  MulOneClass.mul_one

end MulOneClass

section IsUnital

/-- A multiplicative magma is **unital** if there exists a unit.

**Note**: Do not use this unless it is the only reasonable way to phrase or prove a statement.
In general you should use `NonUnitalRing`, `Ring`, etc. -/
@[mk_iff] class IsUnital (A : Type*) [Mul A] : Prop where
  isUnital : ∃ u : A, ∀ x : A, u * x = x ∧ x * u = x

/-- A multiplicative magma is **not-unital** if there does not exist a unit.

**Note**: Do not use this unless it is the only reasonable way to phrase or prove a statement.
In general you should use `NonUnitalRing`, `Ring`, etc. -/
@[mk_iff] class IsNotUnital (A : Type*) [Mul A] : Prop where
  isNotUnital : ∀ u : A, ∃ x : A, u * x ≠ x ∨ x * u ≠ x

variable {A : Type*}

@[simp, push] lemma not_isUnital_iff_isNotUnital [Mul A] : ¬IsUnital A ↔ IsNotUnital A := by
  simp [isUnital_iff, isNotUnital_iff, -not_and, Classical.not_and_iff_not_or_not]

@[simp, push] lemma not_isNotUnital_iff_isUnital [Mul A] : ¬IsNotUnital A ↔ IsUnital A := by
  grind [not_isUnital_iff_isNotUnital]

/-- A unital magma is `MulOneClass`.

This constructor is primarily intended to be used within proofs since it creates bad definitional
equalities. -/
noncomputable abbrev IsUnital.toMulOneClass [Mul A] [IsUnital A] : MulOneClass A where
  one := isUnital.choose
  one_mul a := (isUnital.choose_spec a).1
  mul_one a := (isUnital.choose_spec a).2

lemma MulOneClass.isUnital [MulOneClass A] : IsUnital A where
  isUnital := ⟨1, fun x ↦ ⟨one_mul x, mul_one x⟩⟩

end IsUnital

section

variable {M : Type*}

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

library_note «forgetful inheritance» /--
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
    | k + 2 =>
      simp [npowRec', ← mul_assoc, ← ih, Nat.mul_succ]

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
  replace hk : k' ≠ 0 := by lia
  induction k' using Nat.binaryRecFromOne generalizing n m with
  | zero => simp at hk
  | one => simp [npowRec']
  | bit b k' k'0 ih =>
    rw [Nat.binaryRec_eq _ _ (Or.inl rfl), ih _ _ k'0]
    cases b <;> simp only [Nat.bit, Bool.cond_false, Bool.cond_true, npowRec'_two_mul]
    rw [npowRec'_succ (by lia), npowRec'_two_mul, ← npowRec'_two_mul,
      ← npowRec'_mul_comm (by lia), mul_assoc]

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

@[to_additive] theorem npowBinRec_zero {M : Type*} [Mul M] [One M] (m : M) :
    npowBinRec 0 m = 1 := rfl

@[to_additive] theorem npowBinRec_succ {M : Type*} [Semigroup M] [One M] (n : ℕ) (m : M) :
    npowBinRec (n + 1) m = npowBinRec n m * m := by
  iterate 2 rw [← npowBinRecAuto, ← npowRec_eq_npowBinRec]
  rfl

/-- `NSMul` is an implementation detail of `AddMonoid`. It is needed because it is
impossible to extend `SMul ℕ M` and `SMul ℤ M` at the same time. -/
class NSMul (M : Type*) where
  /-- Multiplication by a natural number.
  Set this to `nsmulRec` unless `Module` diamonds are possible. -/
  protected nsmul : ℕ → M → M

/-- `NPow` is an implementation detail of `Monoid`. It is needed because it is
impossible to extend `Pow M ℕ` and `Pow M ℤ` at the same time. -/
@[to_additive]
class NPow (M : Type*) where
  /-- Raising to the power of a natural number. -/
  protected npow : ℕ → M → M

@[default_instance high, to_additive toSMul]
instance NPow.toPow {M : Type*} [NPow M] : Pow M ℕ :=
  ⟨fun x n ↦ NPow.npow n x⟩

@[to_additive ofSMul]
instance NPow.ofPow {M : Type*} [Pow M ℕ] : NPow M := ⟨fun n x ↦ Pow.pow x n⟩

/-- An `AddMonoid` is an `AddSemigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
class AddMonoid (M : Type*) extends Zero M, Add M, AddSemigroup M, AddZeroClass M, NSMul M where
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  protected nsmul_zero (x : M) : 0 • x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  protected nsmul_succ (n : ℕ) (x : M) : (n + 1) • x = n • x + x := by intros; rfl

attribute [instance 150] AddSemigroup.toAdd
attribute [instance 50] AddZero.toAdd

/-- A `Monoid` is a `Semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[to_additive]
class Monoid (M : Type*) extends One M, Mul M, Semigroup M, MulOneClass M, NPow M where
  npow := npowRecAuto
  /-- Raising to the power `(0 : ℕ)` gives `1`. -/
  protected npow_zero (x : M) : x ^ 0 = 1 := by intros; rfl
  /-- Raising to the power `(n + 1 : ℕ)` behaves as expected. -/
  protected npow_succ (n : ℕ) (x : M) : x ^ (n + 1) = x ^ n * x := by intros; rfl

section Monoid
variable {M : Type*} [Monoid M] {a b c : M}

@[to_additive (attr := simp) nsmul_eq_smul]
theorem npow_eq_pow (n : ℕ) (x : M) : NPow.npow n x = x ^ n :=
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

@[to_additive one_nsmul, simp]
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

@[to_additive] protected lemma IsLeftRegular.mul_eq_one_symm {a b : M} (reg : IsLeftRegular a)
    (eq : a * b = 1) : b * a = 1 :=
  reg <| by simp [← mul_assoc, eq]

@[to_additive] protected lemma IsRightRegular.mul_eq_one_symm {a b : M} (reg : IsRightRegular a)
    (eq : b * a = 1) : a * b = 1 :=
  reg <| by simp [mul_assoc, eq]

variable (M)

@[to_additive] instance [IsLeftCancelMul M] : IsDedekindFiniteMonoid M where
  mul_eq_one_symm := (IsLeftCancelMul.mul_left_cancel _).mul_eq_one_symm

@[to_additive] instance [IsRightCancelMul M] : IsDedekindFiniteMonoid M where
  mul_eq_one_symm := (IsRightCancelMul.mul_right_cancel _).mul_eq_one_symm

namespace IsDedekindFiniteMonoid

/-- A monoid is Dedekind-finite if every element with a left inverse also has a right inverse. -/
@[to_additive] lemma of_exists_self_mul_eq_one (ex : ∀ x y : M, x * y = 1 → ∃ z, y * z = 1) :
    IsDedekindFiniteMonoid M where
  mul_eq_one_symm {x y} h := by
    have ⟨z, hz⟩ := ex x y h
    rwa [show x = z by simpa [← mul_assoc, h] using congr_arg (x * ·) hz.symm]

/-- A monoid is Dedekind-finite if every element with a right inverse also has a left inverse. -/
@[to_additive] lemma of_exists_mul_self_eq_one (ex : ∀ x y : M, x * y = 1 → ∃ z, z * x = 1) :
    IsDedekindFiniteMonoid M where
  mul_eq_one_symm {x y} h := by
    have ⟨z, hz⟩ := ex x y h
    rwa [show y = z by simpa [mul_assoc, h] using congr_arg (· * y) hz.symm]

end IsDedekindFiniteMonoid

end Monoid

attribute [local instance] IsUnital.toMulOneClass in
/-- A unital semigroup is a monoid.

This constructor is primarily intended to be used within proofs since it creates bad definitional
equalities. -/
noncomputable abbrev IsUnital.toMonoid {A : Type*} [Semigroup A] [IsUnital A] : Monoid A where

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
class AddCommMonoid (M : Type*) extends AddMonoid M, AddCommSemigroup M

/-- A commutative monoid is a monoid with commutative `(*)`. -/
@[to_additive]
class CommMonoid (M : Type*) extends Monoid M, CommSemigroup M

/-- Shortcut instance for `IsCommutativeHMul M → IsDedekindFiniteMonoid M`.

This is assigned default rather than low priority because it gives the most common examples
of Dedekind-finite monoids and is used the most often. Benchmark results indicate default
priority performs better than low or high priority. -/
@[to_additive] instance (M) [CommMonoid M] : IsDedekindFiniteMonoid M := inferInstance

section LeftCancelMonoid

/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddLeftCancelSemigroup` is not enough. -/
class AddLeftCancelMonoid (M : Type*) extends AddMonoid M, AddLeftCancelSemigroup M

attribute [instance 75] AddLeftCancelMonoid.toAddMonoid -- See note [lower cancel priority]

/-- A monoid in which multiplication is left-cancellative. -/
@[to_additive]
class LeftCancelMonoid (M : Type*) extends Monoid M, LeftCancelSemigroup M

attribute [instance 75] LeftCancelMonoid.toMonoid -- See note [lower cancel priority]

end LeftCancelMonoid

section RightCancelMonoid

/-- An additive monoid in which addition is right-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddRightCancelSemigroup` is not enough. -/
class AddRightCancelMonoid (M : Type*) extends AddMonoid M, AddRightCancelSemigroup M

attribute [instance 75] AddRightCancelMonoid.toAddMonoid -- See note [lower cancel priority]

/-- A monoid in which multiplication is right-cancellative. -/
@[to_additive]
class RightCancelMonoid (M : Type*) extends Monoid M, RightCancelSemigroup M

attribute [instance 75] RightCancelMonoid.toMonoid -- See note [lower cancel priority]

end RightCancelMonoid

section CancelMonoid

/-- An additive monoid in which addition is cancellative on both sides.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddRightCancelMonoid` is not enough. -/
class AddCancelMonoid (M : Type*) extends AddLeftCancelMonoid M, AddRightCancelMonoid M

/-- A monoid in which multiplication is cancellative. -/
@[to_additive]
class CancelMonoid (M : Type*) extends LeftCancelMonoid M, RightCancelMonoid M

/-- Commutative version of `AddCancelMonoid`. -/
class AddCancelCommMonoid (M : Type*) extends AddCommMonoid M, AddLeftCancelMonoid M

attribute [instance 75] AddCancelCommMonoid.toAddCommMonoid -- See note [lower cancel priority]

/-- Commutative version of `CancelMonoid`. -/
@[to_additive]
class CancelCommMonoid (M : Type*) extends CommMonoid M, LeftCancelMonoid M

attribute [instance 75] CancelCommMonoid.toCommMonoid -- See note [lower cancel priority]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CancelCommMonoid.toCancelMonoid (M : Type*) [CancelCommMonoid M] :
    CancelMonoid M :=
  { CommMagma.IsLeftCancelMul.toIsRightCancelMul M with }

/-- Any `CancelMonoid G` satisfies `IsCancelMul G`. -/
@[to_additive /-- Any `AddCancelMonoid G` satisfies `IsCancelAdd G`. -/]
instance (priority := 100) CancelMonoid.toIsCancelMul (M : Type*) [CancelMonoid M] :
    IsCancelMul M where

end CancelMonoid

/-! We initialize the projections for the monoid structures for `@[simps]` here.

The lemmas generated for the `npow`/`zpow` projections will *not* apply to `x ^ y`, since the
argument order of these projections does not match the argument order of `^`. The `nsmul`/`zsmul`
lemmas are correct. -/
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
