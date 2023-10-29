/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Mathlib.Init.ZeroOne
import Mathlib.Init.Data.Int.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Basic

#align_import algebra.group.defs from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

/-!
# Typeclasses for (semi)groups and monoids

In this file we define typeclasses for algebraic structures with one binary operation.
The classes are named `(Add)?(Comm)?(Semigroup|Monoid|Group)`, where `Add` means that
the class uses additive notation and `Comm` means that the class assumes that the binary
operation is commutative.

The file does not contain any lemmas except for

* axioms of typeclasses restated in the root namespace;
* lemmas required for instances.

For basic lemmas about these classes see `Algebra.Group.Basic`.

We also introduce notation classes `SMul` and `VAdd` for multiplicative and additive
actions and register the following instances:

- `Pow M ℕ`, for monoids `M`, and `Pow G ℤ` for groups `G`;
- `SMul ℕ M` for additive monoids `M`, and `SMul ℤ G` for additive groups `G`.

## Notation

- `+`, `-`, `*`, `/`, `^` : the usual arithmetic operations; the underlying functions are
  `Add.add`, `Neg.neg`/`Sub.sub`, `Mul.mul`, `Div.div`, and `HPow.hPow`.
- `a • b` is used as notation for `HSMul.hSMul a b`.
- `a +ᵥ b` is used as notation for `HVAdd.hVAdd a b`.

-/

set_option autoImplicit true

open Function

/--
The notation typeclass for heterogeneous additive actions.
This enables the notation `a +ᵥ b : γ` where `a : α`, `b : β`.
-/
class HVAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a +ᵥ b` computes the sum of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hVAdd : α → β → γ

/--
The notation typeclass for heterogeneous scalar multiplication.
This enables the notation `a • b : γ` where `a : α`, `b : β`.
-/
class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a • b` computes the product of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hSMul : α → β → γ

attribute [notation_class  smul Simps.copySecond] HSMul
attribute [notation_class nsmul Simps.nsmulArgs]  HSMul
attribute [notation_class zsmul Simps.zsmulArgs]  HSMul

/-- Type class for the `+ᵥ` notation. -/
class VAdd (G : Type u) (P : Type v) where
  vadd : G → P → P
#align has_vadd VAdd

/-- Type class for the `-ᵥ` notation. -/
class VSub (G : outParam (Type*)) (P : Type*) where
  vsub : P → P → G
#align has_vsub VSub

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
@[to_additive (attr := ext)]
class SMul (M : Type u) (α : Type v) where
  smul : M → α → α
#align has_smul SMul

infixl:65 " +ᵥ " => HVAdd.hVAdd
infixl:65 " -ᵥ " => VSub.vsub
infixr:73 " • " => HSMul.hSMul

attribute [to_additive existing] Mul Div HMul instHMul HDiv instHDiv HSMul
attribute [to_additive (reorder := 1 2) SMul] Pow
attribute [to_additive (reorder := 1 2)] HPow
attribute [to_additive existing (reorder := 1 2, 5 6) hSMul] HPow.hPow
attribute [to_additive existing (reorder := 1 2, 4 5) smul] Pow.pow

@[to_additive (attr := default_instance)]
instance instHSMul [SMul α β] : HSMul α β β where
  hSMul := SMul.smul

attribute [to_additive existing (reorder := 1 2)] instHPow

universe u

variable {G : Type*}

/-- Class of types that have an inversion operation. -/
@[to_additive, notation_class]
class Inv (α : Type u) where
  /-- Invert an element of α. -/
  inv : α → α
#align has_inv Inv

@[inherit_doc]
postfix:max "⁻¹" => Inv.inv

section Mul

variable [Mul G]

/-- `leftMul g` denotes left multiplication by `g` -/
@[to_additive "`leftAdd g` denotes left addition by `g`"]
def leftMul : G → G → G := fun g : G ↦ fun x : G ↦ g * x
#align left_mul leftMul
#align left_add leftAdd

/-- `rightMul g` denotes right multiplication by `g` -/
@[to_additive "`rightAdd g` denotes right addition by `g`"]
def rightMul : G → G → G := fun g : G ↦ fun x : G ↦ x * g
#align right_mul rightMul
#align right_add rightAdd

/-- A mixin for left cancellative multiplication. -/
class IsLeftCancelMul (G : Type u) [Mul G] : Prop where
  /-- Multiplication is left cancellative. -/
  protected mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c
/-- A mixin for right cancellative multiplication. -/
class IsRightCancelMul (G : Type u) [Mul G] : Prop where
  /-- Multiplication is right cancellative. -/
  protected mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c
/-- A mixin for cancellative multiplication. -/
class IsCancelMul (G : Type u) [Mul G] extends IsLeftCancelMul G, IsRightCancelMul G : Prop
#align is_cancel_mul IsCancelMul
#align is_right_cancel_mul IsRightCancelMul
#align is_left_cancel_mul IsLeftCancelMul

/-- A mixin for left cancellative addition. -/
class IsLeftCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is left cancellative. -/
  protected add_left_cancel : ∀ a b c : G, a + b = a + c → b = c
#align is_left_cancel_add IsLeftCancelAdd

attribute [to_additive IsLeftCancelAdd] IsLeftCancelMul

/-- A mixin for right cancellative addition. -/
class IsRightCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is right cancellative. -/
  protected add_right_cancel : ∀ a b c : G, a + b = c + b → a = c
#align is_right_cancel_add IsRightCancelAdd

attribute [to_additive IsRightCancelAdd] IsRightCancelMul

/-- A mixin for cancellative addition. -/
class IsCancelAdd (G : Type u) [Add G] extends IsLeftCancelAdd G, IsRightCancelAdd G : Prop
#align is_cancel_add IsCancelAdd

attribute [to_additive IsCancelAdd] IsCancelMul

section IsLeftCancelMul

variable [IsLeftCancelMul G] {a b c : G}

@[to_additive]
theorem mul_left_cancel : a * b = a * c → b = c :=
  IsLeftCancelMul.mul_left_cancel a b c
#align mul_left_cancel mul_left_cancel
#align add_left_cancel add_left_cancel

@[to_additive]
theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancel, congr_arg _⟩
#align mul_left_cancel_iff mul_left_cancel_iff
#align add_left_cancel_iff add_left_cancel_iff

@[to_additive]
theorem mul_right_injective (a : G) : Function.Injective ((· * ·) a) := fun _ _ ↦ mul_left_cancel
#align mul_right_injective mul_right_injective
#align add_right_injective add_right_injective

@[to_additive (attr := simp)]
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
  (mul_right_injective a).eq_iff
#align mul_right_inj mul_right_inj
#align add_right_inj add_right_inj

@[to_additive]
theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
  (mul_right_injective a).ne_iff
#align mul_ne_mul_right mul_ne_mul_right
#align add_ne_add_right add_ne_add_right

end IsLeftCancelMul

section IsRightCancelMul

variable [IsRightCancelMul G] {a b c : G}

@[to_additive]
theorem mul_right_cancel : a * b = c * b → a = c :=
  IsRightCancelMul.mul_right_cancel a b c
#align mul_right_cancel mul_right_cancel
#align add_right_cancel add_right_cancel

@[to_additive]
theorem mul_right_cancel_iff : b * a = c * a ↔ b = c :=
  ⟨mul_right_cancel, congr_arg (· * a)⟩
#align mul_right_cancel_iff mul_right_cancel_iff
#align add_right_cancel_iff add_right_cancel_iff

@[to_additive]
theorem mul_left_injective (a : G) : Function.Injective (· * a) := fun _ _ ↦ mul_right_cancel
#align mul_left_injective mul_left_injective
#align add_left_injective add_left_injective

@[to_additive (attr := simp)]
theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
  (mul_left_injective a).eq_iff
#align mul_left_inj mul_left_inj
#align add_left_inj add_left_inj

@[to_additive]
theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c :=
  (mul_left_injective a).ne_iff
#align mul_ne_mul_left mul_ne_mul_left
#align add_ne_add_left add_ne_add_left

end IsRightCancelMul

end Mul

/-- A semigroup is a type with an associative `(*)`. -/
@[ext]
class Semigroup (G : Type u) extends Mul G where
  /-- Multiplication is associative -/
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
#align semigroup Semigroup
#align semigroup.ext Semigroup.ext
#align semigroup.ext_iff Semigroup.ext_iff

/-- An additive semigroup is a type with an associative `(+)`. -/
@[ext]
class AddSemigroup (G : Type u) extends Add G where
  /-- Addition is associative -/
  protected add_assoc : ∀ a b c : G, a + b + c = a + (b + c)
#align add_semigroup AddSemigroup
#align add_semigroup.ext AddSemigroup.ext
#align add_semigroup.ext_iff AddSemigroup.ext_iff

attribute [to_additive] Semigroup

section Semigroup

variable [Semigroup G]

@[to_additive]
theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
  Semigroup.mul_assoc
#align mul_assoc mul_assoc
#align add_assoc add_assoc

@[to_additive]
instance Semigroup.to_isAssociative : IsAssociative G (· * ·) :=
  ⟨mul_assoc⟩
#align semigroup.to_is_associative Semigroup.to_isAssociative
#align add_semigroup.to_is_associative AddSemigroup.to_isAssociative

end Semigroup

/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
@[ext]
class CommSemigroup (G : Type u) extends Semigroup G where
  /-- Multiplication is commutative in a commutative semigroup. -/
  protected mul_comm : ∀ a b : G, a * b = b * a
#align comm_semigroup CommSemigroup
#align comm_semigroup.ext_iff CommSemigroup.ext_iff
#align comm_semigroup.ext CommSemigroup.ext

/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
@[ext]
class AddCommSemigroup (G : Type u) extends AddSemigroup G where
  /-- Addition is commutative in an additive commutative semigroup. -/
  protected add_comm : ∀ a b : G, a + b = b + a
#align add_comm_semigroup AddCommSemigroup
#align add_comm_semigroup.ext AddCommSemigroup.ext
#align add_comm_semigroup.ext_iff AddCommSemigroup.ext_iff

attribute [to_additive] CommSemigroup

section CommSemigroup

variable [CommSemigroup G]

@[to_additive]
theorem mul_comm : ∀ a b : G, a * b = b * a :=
  CommSemigroup.mul_comm
#align mul_comm mul_comm
#align add_comm add_comm

@[to_additive]
instance CommSemigroup.to_isCommutative : IsCommutative G (· * ·) :=
  ⟨mul_comm⟩
#align comm_semigroup.to_is_commutative CommSemigroup.to_isCommutative
#align add_comm_semigroup.to_is_commutative AddCommSemigroup.to_isCommutative

/-- Any `CommSemigroup G` that satisfies `IsRightCancelMul G` also satisfies
`IsLeftCancelMul G`. -/
@[to_additive AddCommSemigroup.IsRightCancelAdd.toIsLeftCancelAdd "Any
`AddCommSemigroup G` that satisfies `IsRightCancelAdd G` also satisfies
`IsLeftCancelAdd G`."]
lemma CommSemigroup.IsRightCancelMul.toIsLeftCancelMul (G : Type u) [CommSemigroup G]
    [IsRightCancelMul G] : IsLeftCancelMul G :=
  ⟨fun _ _ _ h => mul_right_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩
#align comm_semigroup.is_right_cancel_mul.to_is_left_cancel_mul CommSemigroup.IsRightCancelMul.toIsLeftCancelMul
#align add_comm_semigroup.is_right_cancel_add.to_is_left_cancel_add AddCommSemigroup.IsRightCancelAdd.toIsLeftCancelAdd

/-- Any `CommSemigroup G` that satisfies `IsLeftCancelMul G` also satisfies
`IsRightCancelMul G`. -/
@[to_additive AddCommSemigroup.IsLeftCancelAdd.toIsRightCancelAdd "Any
`AddCommSemigroup G` that satisfies `IsLeftCancelAdd G` also satisfies
`IsRightCancelAdd G`."]
lemma CommSemigroup.IsLeftCancelMul.toIsRightCancelMul (G : Type u) [CommSemigroup G]
    [IsLeftCancelMul G] : IsRightCancelMul G :=
  ⟨fun _ _ _ h => mul_left_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩
#align comm_semigroup.is_left_cancel_mul.to_is_right_cancel_mul CommSemigroup.IsLeftCancelMul.toIsRightCancelMul
#align add_comm_semigroup.is_left_cancel_add.to_is_right_cancel_add AddCommSemigroup.IsLeftCancelAdd.toIsRightCancelAdd

/-- Any `CommSemigroup G` that satisfies `IsLeftCancelMul G` also satisfies
`IsCancelMul G`. -/
@[to_additive AddCommSemigroup.IsLeftCancelAdd.toIsCancelAdd "Any
`AddCommSemigroup G` that satisfies `IsLeftCancelAdd G` also satisfies
`IsCancelAdd G`."]
lemma CommSemigroup.IsLeftCancelMul.toIsCancelMul (G : Type u) [CommSemigroup G]
    [IsLeftCancelMul G] : IsCancelMul G :=
  { CommSemigroup.IsLeftCancelMul.toIsRightCancelMul G with }
#align comm_semigroup.is_left_cancel_mul.to_is_cancel_mul CommSemigroup.IsLeftCancelMul.toIsCancelMul
#align add_comm_semigroup.is_left_cancel_add.to_is_cancel_add AddCommSemigroup.IsLeftCancelAdd.toIsCancelAdd

/-- Any `CommSemigroup G` that satisfies `IsRightCancelMul G` also satisfies
`IsCancelMul G`. -/
@[to_additive AddCommSemigroup.IsRightCancelAdd.toIsCancelAdd "Any
`AddCommSemigroup G` that satisfies `IsRightCancelAdd G` also satisfies
`IsCancelAdd G`."]
lemma CommSemigroup.IsRightCancelMul.toIsCancelMul (G : Type u) [CommSemigroup G]
    [IsRightCancelMul G] : IsCancelMul G :=
  { CommSemigroup.IsRightCancelMul.toIsLeftCancelMul G with }
#align comm_semigroup.is_right_cancel_mul.to_is_cancel_mul CommSemigroup.IsRightCancelMul.toIsCancelMul
#align add_comm_semigroup.is_right_cancel_add.to_is_cancel_add AddCommSemigroup.IsRightCancelAdd.toIsCancelAdd

end CommSemigroup

/-- A `LeftCancelSemigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
@[ext]
class LeftCancelSemigroup (G : Type u) extends Semigroup G where
  protected mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c
#align left_cancel_semigroup LeftCancelSemigroup
#align left_cancel_semigroup.ext_iff LeftCancelSemigroup.ext_iff
#align left_cancel_semigroup.ext LeftCancelSemigroup.ext

library_note "lower cancel priority" /--
We lower the priority of inheriting from cancellative structures.
This attemts to avoid expensive checks involving bundling and unbundling with the `IsDomain` class.
since `IsDomain` already depends on `Semiring`, we can synthesize that one first.
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Why.20is.20.60simpNF.60.20complaining.20here.3F
-/
attribute [instance 75] LeftCancelSemigroup.toSemigroup -- See note [lower cancel priority]

/-- An `AddLeftCancelSemigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
@[ext]
class AddLeftCancelSemigroup (G : Type u) extends AddSemigroup G where
  protected add_left_cancel : ∀ a b c : G, a + b = a + c → b = c
#align add_left_cancel_semigroup AddLeftCancelSemigroup
#align add_left_cancel_semigroup.ext AddLeftCancelSemigroup.ext
#align add_left_cancel_semigroup.ext_iff AddLeftCancelSemigroup.ext_iff

attribute [instance 75] AddLeftCancelSemigroup.toAddSemigroup -- See note [lower cancel priority]

attribute [to_additive] LeftCancelSemigroup

/-- Any `LeftCancelSemigroup` satisfies `IsLeftCancelMul`. -/
@[to_additive AddLeftCancelSemigroup.toIsLeftCancelAdd "Any `AddLeftCancelSemigroup` satisfies
`IsLeftCancelAdd`."]
instance (priority := 100) LeftCancelSemigroup.toIsLeftCancelMul (G : Type u)
    [LeftCancelSemigroup G] : IsLeftCancelMul G :=
  { mul_left_cancel := LeftCancelSemigroup.mul_left_cancel }
#align left_cancel_semigroup.to_is_left_cancel_mul LeftCancelSemigroup.toIsLeftCancelMul
#align add_left_cancel_semigroup.to_is_left_cancel_add AddLeftCancelSemigroup.toIsLeftCancelAdd

/-- A `RightCancelSemigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
@[ext]
class RightCancelSemigroup (G : Type u) extends Semigroup G where
  protected mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c
#align right_cancel_semigroup RightCancelSemigroup
#align right_cancel_semigroup.ext_iff RightCancelSemigroup.ext_iff
#align right_cancel_semigroup.ext RightCancelSemigroup.ext

attribute [instance 75] RightCancelSemigroup.toSemigroup -- See note [lower cancel priority]

/-- An `AddRightCancelSemigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
@[ext]
class AddRightCancelSemigroup (G : Type u) extends AddSemigroup G where
  protected add_right_cancel : ∀ a b c : G, a + b = c + b → a = c
#align add_right_cancel_semigroup AddRightCancelSemigroup
#align add_right_cancel_semigroup.ext_iff AddRightCancelSemigroup.ext_iff
#align add_right_cancel_semigroup.ext AddRightCancelSemigroup.ext

attribute [instance 75] AddRightCancelSemigroup.toAddSemigroup -- See note [lower cancel priority]

attribute [to_additive] RightCancelSemigroup

/-- Any `RightCancelSemigroup` satisfies `IsRightCancelMul`. -/
@[to_additive AddRightCancelSemigroup.toIsRightCancelAdd "Any `AddRightCancelSemigroup` satisfies
`IsRightCancelAdd`."]
instance (priority := 100) RightCancelSemigroup.toIsRightCancelMul (G : Type u)
    [RightCancelSemigroup G] : IsRightCancelMul G :=
  { mul_right_cancel := RightCancelSemigroup.mul_right_cancel }
#align right_cancel_semigroup.to_is_right_cancel_mul RightCancelSemigroup.toIsRightCancelMul
#align add_right_cancel_semigroup.to_is_right_cancel_add AddRightCancelSemigroup.toIsRightCancelAdd

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
class MulOneClass (M : Type u) extends One M, Mul M where
  /-- One is a left neutral element for multiplication -/
  protected one_mul : ∀ a : M, 1 * a = a
  /-- One is a right neutral element for multiplication -/
  protected mul_one : ∀ a : M, a * 1 = a
#align mul_one_class MulOneClass

/-- Typeclass for expressing that a type `M` with addition and a zero satisfies
`0 + a = a` and `a + 0 = a` for all `a : M`. -/
class AddZeroClass (M : Type u) extends Zero M, Add M where
  /-- Zero is a left neutral element for addition -/
  protected zero_add : ∀ a : M, 0 + a = a
  /-- Zero is a right neutral element for addition -/
  protected add_zero : ∀ a : M, a + 0 = a
#align add_zero_class AddZeroClass

attribute [to_additive] MulOneClass

@[to_additive (attr := ext)]
theorem MulOneClass.ext {M : Type u} : ∀ ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul → m₁ = m₂ := by
  rintro @⟨⟨one₁⟩, ⟨mul₁⟩, one_mul₁, mul_one₁⟩ @⟨⟨one₂⟩, ⟨mul₂⟩, one_mul₂, mul_one₂⟩ ⟨rfl⟩
  -- FIXME (See https://github.com/leanprover/lean4/issues/1711)
  -- congr
  suffices one₁ = one₂ by cases this; rfl
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂)
#align mul_one_class.ext MulOneClass.ext
#align add_zero_class.ext AddZeroClass.ext

section MulOneClass

variable {M : Type u} [MulOneClass M]

@[to_additive (attr := simp)]
theorem one_mul : ∀ a : M, 1 * a = a :=
  MulOneClass.one_mul
#align one_mul one_mul
#align zero_add zero_add

@[to_additive (attr := simp)]
theorem mul_one : ∀ a : M, a * 1 = a :=
  MulOneClass.mul_one
#align mul_one mul_one
#align add_zero add_zero

end MulOneClass

section

variable {M : Type u}

-- use `x * npowRec n x` and not `npowRec n x * x` in the definition to make sure that
-- definitional unfolding of `npowRec` is blocked, to avoid deep recursion issues.
/-- The fundamental power operation in a monoid. `npowRec n a = a*a*...*a` n times.
Use instead `a ^ n`, which has better definitional behavior. -/
def npowRec [One M] [Mul M] : ℕ → M → M
  | 0, _ => 1
  | n + 1, a => a * npowRec n a
#align npow_rec npowRec

/-- The fundamental scalar multiplication in an additive monoid. `nsmulRec n a = a+a+...+a` n
times. Use instead `n • a`, which has better definitional behavior. -/
def nsmulRec [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmulRec n a
#align nsmul_rec nsmulRec

attribute [to_additive existing] npowRec

end

library_note "forgetful inheritance"/--
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

A basic theory for the power function on monoids and the `ℕ`-action on additive monoids is built in
the file `Algebra.GroupPower.Basic`. For now, we only register the most basic properties that we
need right away.
-/


/-- An `AddMonoid` is an `AddSemigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  protected nsmul : ℕ → M → M := nsmulRec
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  protected nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  protected nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl
#align add_monoid AddMonoid

attribute [instance 150] AddSemigroup.toAdd
attribute [instance 50] AddZeroClass.toAdd

#align add_monoid.nsmul_zero' AddMonoid.nsmul_zero
#align add_monoid.nsmul_succ' AddMonoid.nsmul_succ

/-- A `Monoid` is a `Semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[to_additive]
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  /-- Raising to the power of a natural number. -/
  protected npow : ℕ → M → M := npowRec
  /-- Raising to the power `(0 : ℕ)` gives `1`. -/
  protected npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  /-- Raising to the power `(n + 1 : ℕ)` behaves as expected. -/
  protected npow_succ : ∀ (n : ℕ) (x), npow (n + 1) x = x * npow n x := by intros; rfl
#align monoid Monoid

#align monoid.npow_zero' Monoid.npow_zero
#align monoid.npow_succ' Monoid.npow_succ

-- Bug #660
attribute [to_additive existing] Monoid.toMulOneClass

@[default_instance high] instance Monoid.Pow {M : Type*} [Monoid M] : Pow M ℕ :=
  ⟨fun x n ↦ Monoid.npow n x⟩
#align monoid.has_pow Monoid.Pow

instance AddMonoid.SMul {M : Type*} [AddMonoid M] : SMul ℕ M :=
  ⟨AddMonoid.nsmul⟩
#align add_monoid.has_smul_nat AddMonoid.SMul

attribute [to_additive existing SMul] Monoid.Pow

section

variable {M : Type*} [Monoid M]

@[to_additive (attr := simp) nsmul_eq_smul]
theorem npow_eq_pow (n : ℕ) (x : M) : Monoid.npow n x = x ^ n :=
  rfl
#align npow_eq_pow npow_eq_pow
#align nsmul_eq_smul nsmul_eq_smul

-- the attributes are intentionally out of order. `zero_smul` proves `zero_nsmul`.
@[to_additive zero_nsmul, simp]
theorem pow_zero (a : M) : a ^ 0 = 1 :=
  Monoid.npow_zero _
#align pow_zero pow_zero
#align zero_nsmul zero_nsmul

@[to_additive succ_nsmul]
theorem pow_succ (a : M) (n : ℕ) : a ^ (n + 1) = a * a ^ n :=
  Monoid.npow_succ n a
#align pow_succ pow_succ
#align succ_nsmul succ_nsmul

end

section Monoid

variable {M : Type u} [Monoid M]

@[to_additive]
theorem left_inv_eq_right_inv {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]
#align left_inv_eq_right_inv left_inv_eq_right_inv
#align left_neg_eq_right_neg left_neg_eq_right_neg

end Monoid

/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M
#align add_comm_monoid AddCommMonoid

/-- A commutative monoid is a monoid with commutative `(*)`. -/
@[to_additive]
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M
#align comm_monoid CommMonoid

attribute [to_additive existing] CommMonoid.toCommSemigroup

section LeftCancelMonoid

/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddLeftCancelSemigroup` is not enough. -/
class AddLeftCancelMonoid (M : Type u) extends AddLeftCancelSemigroup M, AddMonoid M
#align add_left_cancel_monoid AddLeftCancelMonoid

attribute [instance 75] AddLeftCancelMonoid.toAddMonoid -- See note [lower cancel priority]

/-- A monoid in which multiplication is left-cancellative. -/
@[to_additive]
class LeftCancelMonoid (M : Type u) extends LeftCancelSemigroup M, Monoid M
#align left_cancel_monoid LeftCancelMonoid

attribute [instance 75] LeftCancelMonoid.toMonoid -- See note [lower cancel priority]

attribute [to_additive existing] LeftCancelMonoid.toMonoid

end LeftCancelMonoid

section RightCancelMonoid

/-- An additive monoid in which addition is right-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddRightCancelSemigroup` is not enough. -/
class AddRightCancelMonoid (M : Type u) extends AddRightCancelSemigroup M, AddMonoid M
#align add_right_cancel_monoid AddRightCancelMonoid

attribute [instance 75] AddRightCancelMonoid.toAddMonoid -- See note [lower cancel priority]

/-- A monoid in which multiplication is right-cancellative. -/
@[to_additive]
class RightCancelMonoid (M : Type u) extends RightCancelSemigroup M, Monoid M
#align right_cancel_monoid RightCancelMonoid

attribute [instance 75] RightCancelMonoid.toMonoid -- See note [lower cancel priority]

attribute [to_additive existing] RightCancelMonoid.toMonoid

end RightCancelMonoid

section CancelMonoid

/-- An additive monoid in which addition is cancellative on both sides.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddRightCancelMonoid` is not enough. -/
class AddCancelMonoid (M : Type u) extends AddLeftCancelMonoid M, AddRightCancelMonoid M
#align add_cancel_monoid AddCancelMonoid

/-- A monoid in which multiplication is cancellative. -/
@[to_additive]
class CancelMonoid (M : Type u) extends LeftCancelMonoid M, RightCancelMonoid M
#align cancel_monoid CancelMonoid

attribute [to_additive existing] CancelMonoid.toRightCancelMonoid

/-- Commutative version of `AddCancelMonoid`. -/
class AddCancelCommMonoid (M : Type u) extends AddLeftCancelMonoid M, AddCommMonoid M
#align add_cancel_comm_monoid AddCancelCommMonoid

attribute [instance 75] AddCancelCommMonoid.toAddCommMonoid -- See note [lower cancel priority]

/-- Commutative version of `CancelMonoid`. -/
@[to_additive]
class CancelCommMonoid (M : Type u) extends LeftCancelMonoid M, CommMonoid M
#align cancel_comm_monoid CancelCommMonoid

attribute [instance 75] CancelCommMonoid.toCommMonoid -- See note [lower cancel priority]

attribute [to_additive existing] CancelCommMonoid.toCommMonoid

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CancelCommMonoid.toCancelMonoid (M : Type u) [CancelCommMonoid M] :
    CancelMonoid M :=
  { CommSemigroup.IsLeftCancelMul.toIsRightCancelMul M with }
#align cancel_comm_monoid.to_cancel_monoid CancelCommMonoid.toCancelMonoid
#align add_cancel_comm_monoid.to_cancel_add_monoid AddCancelCommMonoid.toAddCancelMonoid

/-- Any `CancelMonoid G` satisfies `IsCancelMul G`. -/
@[to_additive toIsCancelAdd "Any `AddCancelMonoid G` satisfies `IsCancelAdd G`."]
instance (priority := 100) CancelMonoid.toIsCancelMul (M : Type u) [CancelMonoid M] :
    IsCancelMul M :=
  { mul_left_cancel := LeftCancelSemigroup.mul_left_cancel
    mul_right_cancel := RightCancelSemigroup.mul_right_cancel }
#align cancel_monoid.to_is_cancel_mul CancelMonoid.toIsCancelMul
#align add_cancel_monoid.to_is_cancel_add AddCancelMonoid.toIsCancelAdd

end CancelMonoid

/-- The fundamental power operation in a group. `zpowRec n a = a*a*...*a` n times, for integer `n`.
Use instead `a ^ n`, which has better definitional behavior. -/
def zpowRec {M : Type*} [One M] [Mul M] [Inv M] : ℤ → M → M
  | Int.ofNat n, a => npowRec n a
  | Int.negSucc n, a => (npowRec n.succ a)⁻¹
#align zpow_rec zpowRec

/-- The fundamental scalar multiplication in an additive group. `zpowRec n a = a+a+...+a` n
times, for integer `n`. Use instead `n • a`, which has better definitional behavior. -/
def zsmulRec {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmulRec n a
  | Int.negSucc n, a => -nsmulRec n.succ a
#align zsmul_rec zsmulRec

attribute [to_additive existing] zpowRec

section InvolutiveInv

/-- Auxiliary typeclass for types with an involutive `Neg`. -/
class InvolutiveNeg (A : Type*) extends Neg A where
  protected neg_neg : ∀ x : A, - -x = x

#align has_involutive_neg InvolutiveNeg

/-- Auxiliary typeclass for types with an involutive `Inv`. -/
@[to_additive]
class InvolutiveInv (G : Type*) extends Inv G where
  protected inv_inv : ∀ x : G, x⁻¹⁻¹ = x

#align has_involutive_inv InvolutiveInv

variable [InvolutiveInv G]

@[to_additive (attr := simp)]
theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
  InvolutiveInv.inv_inv _
#align inv_inv inv_inv
#align neg_neg neg_neg

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
  where `α` non commutative.
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
  protected zpow : ℤ → G → G := zpowRec
  /-- `a ^ 0 = 1` -/
  protected zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  /-- `a ^ (n + 1) = a * a ^ n` -/
  protected zpow_succ' (n : ℕ) (a : G) : zpow (Int.ofNat n.succ) a = a * zpow (Int.ofNat n) a := by
    intros; rfl
  /-- `a ^ -(n + 1) = (a ^ (n + 1))⁻¹` -/
  protected zpow_neg' (n : ℕ) (a : G) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ := by intros; rfl
#align div_inv_monoid DivInvMonoid

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
  protected zsmul : ℤ → G → G := zsmulRec
  protected zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by intros; rfl
  protected zsmul_succ' (n : ℕ) (a : G) :
      zsmul (Int.ofNat n.succ) a = a + zsmul (Int.ofNat n) a := by
    intros; rfl
  protected zsmul_neg' (n : ℕ) (a : G) : zsmul (Int.negSucc n) a = -zsmul n.succ a := by intros; rfl
#align sub_neg_monoid SubNegMonoid

attribute [to_additive SubNegMonoid] DivInvMonoid

instance DivInvMonoid.Pow {M} [DivInvMonoid M] : Pow M ℤ :=
  ⟨fun x n ↦ DivInvMonoid.zpow n x⟩
#align div_inv_monoid.has_pow DivInvMonoid.Pow

instance SubNegMonoid.SMulInt {M} [SubNegMonoid M] : SMul ℤ M :=
  ⟨SubNegMonoid.zsmul⟩
#align sub_neg_monoid.has_smul_int SubNegMonoid.SMulInt

attribute [to_additive existing SubNegMonoid.SMulInt] DivInvMonoid.Pow

section DivInvMonoid

variable [DivInvMonoid G] {a b : G}

@[to_additive (attr := simp) zsmul_eq_smul] theorem zpow_eq_pow (n : ℤ) (x : G) :
    DivInvMonoid.zpow n x = x ^ n :=
  rfl
#align zsmul_eq_smul zsmul_eq_smul
#align zpow_eq_pow zpow_eq_pow

@[to_additive (attr := simp) zero_zsmul] theorem zpow_zero (a : G) : a ^ (0 : ℤ) = 1 :=
  DivInvMonoid.zpow_zero' a
#align zpow_zero zpow_zero
#align zero_zsmul zero_zsmul

@[to_additive (attr := norm_cast) ofNat_zsmul]
theorem zpow_ofNat (a : G) : ∀ n : ℕ, a ^ (n : ℤ) = a ^ n
  | 0 => (zpow_zero _).trans (pow_zero _).symm
  | n + 1 => calc
    a ^ (↑(n + 1) : ℤ) = a * a ^ (n : ℤ) := DivInvMonoid.zpow_succ' _ _
    _ = a * a ^ n := congr_arg ((· * ·) a) (zpow_ofNat a n)
    _ = a ^ (n + 1) := (pow_succ _ _).symm
#align zpow_coe_nat zpow_ofNat
#align zpow_of_nat zpow_ofNat
#align of_nat_zsmul ofNat_zsmul

theorem zpow_negSucc (a : G) (n : ℕ) : a ^ (Int.negSucc n) = (a ^ (n + 1))⁻¹ := by
  rw [← zpow_ofNat]
  exact DivInvMonoid.zpow_neg' n a
#align zpow_neg_succ_of_nat zpow_negSucc

theorem negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : ℕ) :
    Int.negSucc n • a = -((n + 1) • a) := by
  rw [← ofNat_zsmul]
  exact SubNegMonoid.zsmul_neg' n a
#align zsmul_neg_succ_of_nat negSucc_zsmul

attribute [to_additive existing (attr := simp) negSucc_zsmul] zpow_negSucc

/-- Dividing by an element is the same as multiplying by its inverse.

This is a duplicate of `DivInvMonoid.div_eq_mul_inv` ensuring that the types unfold better.
-/
@[to_additive "Subtracting an element is the same as adding by its negative.
This is a duplicate of `SubNegMonoid.sub_eq_mul_neg` ensuring that the types unfold better."]
theorem div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ :=
  DivInvMonoid.div_eq_mul_inv _ _
#align div_eq_mul_inv div_eq_mul_inv
#align sub_eq_add_neg sub_eq_add_neg

alias division_def := div_eq_mul_inv
#align division_def division_def

end DivInvMonoid

section InvOneClass

/-- Typeclass for expressing that `-0 = 0`. -/
class NegZeroClass (G : Type*) extends Zero G, Neg G where
  protected neg_zero : -(0 : G) = 0
#align neg_zero_class NegZeroClass

/-- A `SubNegMonoid` where `-0 = 0`. -/
class SubNegZeroMonoid (G : Type*) extends SubNegMonoid G, NegZeroClass G
#align sub_neg_zero_monoid SubNegZeroMonoid

/-- Typeclass for expressing that `1⁻¹ = 1`. -/
@[to_additive]
class InvOneClass (G : Type*) extends One G, Inv G where
  protected inv_one : (1 : G)⁻¹ = 1
#align inv_one_class InvOneClass

/-- A `DivInvMonoid` where `1⁻¹ = 1`. -/
@[to_additive SubNegZeroMonoid]
class DivInvOneMonoid (G : Type*) extends DivInvMonoid G, InvOneClass G
#align div_inv_one_monoid DivInvOneMonoid

-- FIXME: `to_additive` is not operating on the second parent. (#660)
attribute [to_additive existing] DivInvOneMonoid.toInvOneClass

variable [InvOneClass G]

@[to_additive (attr := simp)]
theorem inv_one : (1 : G)⁻¹ = 1 :=
  InvOneClass.inv_one
#align inv_one inv_one
#align neg_zero neg_zero

end InvOneClass

/-- A `SubtractionMonoid` is a `SubNegMonoid` with involutive negation and such that
`-(a + b) = -b + -a` and `a + b = 0 → -a = b`. -/
class SubtractionMonoid (G : Type u) extends SubNegMonoid G, InvolutiveNeg G where
  protected neg_add_rev (a b : G) : -(a + b) = -b + -a
  /- Despite the asymmetry of `neg_eq_of_add`, the symmetric version is true thanks to the
  involutivity of negation. -/
  protected neg_eq_of_add (a b : G) : a + b = 0 → -a = b
#align subtraction_monoid SubtractionMonoid

/-- A `DivisionMonoid` is a `DivInvMonoid` with involutive inversion and such that
`(a * b)⁻¹ = b⁻¹ * a⁻¹` and `a * b = 1 → a⁻¹ = b`.

This is the immediate common ancestor of `Group` and `GroupWithZero`. -/
@[to_additive SubtractionMonoid]
class DivisionMonoid (G : Type u) extends DivInvMonoid G, InvolutiveInv G where
  protected mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
  /- Despite the asymmetry of `inv_eq_of_mul`, the symmetric version is true thanks to the
  involutivity of inversion. -/
  protected inv_eq_of_mul (a b : G) : a * b = 1 → a⁻¹ = b
#align division_monoid DivisionMonoid

attribute [to_additive existing] DivisionMonoid.toInvolutiveInv

section DivisionMonoid

variable [DivisionMonoid G] {a b : G}

@[to_additive (attr := simp) neg_add_rev]
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  DivisionMonoid.mul_inv_rev _ _
#align mul_inv_rev mul_inv_rev
#align neg_add_rev neg_add_rev

@[to_additive]
theorem inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b :=
  DivisionMonoid.inv_eq_of_mul _ _
#align inv_eq_of_mul_eq_one_right inv_eq_of_mul_eq_one_right
#align neg_eq_of_add_eq_zero_right neg_eq_of_add_eq_zero_right

@[to_additive]
theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a :=
  by rw [← inv_eq_of_mul_eq_one_right h, inv_inv]
#align inv_eq_of_mul_eq_one_left inv_eq_of_mul_eq_one_left
#align neg_eq_of_add_eq_zero_left neg_eq_of_add_eq_zero_left

@[to_additive]
theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ :=
  (inv_eq_of_mul_eq_one_left h).symm
#align eq_inv_of_mul_eq_one_left eq_inv_of_mul_eq_one_left
#align eq_neg_of_add_eq_zero_left eq_neg_of_add_eq_zero_left

end DivisionMonoid

/-- Commutative `SubtractionMonoid`. -/
class SubtractionCommMonoid (G : Type u) extends SubtractionMonoid G, AddCommMonoid G
#align subtraction_comm_monoid SubtractionCommMonoid

/-- Commutative `DivisionMonoid`.

This is the immediate common ancestor of `CommGroup` and `CommGroupWithZero`. -/
@[to_additive SubtractionCommMonoid]
class DivisionCommMonoid (G : Type u) extends DivisionMonoid G, CommMonoid G
#align division_comm_monoid DivisionCommMonoid

attribute [to_additive existing] DivisionCommMonoid.toCommMonoid

/-- A `Group` is a `Monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`.

There is also a division operation `/` such that `a / b = a * b⁻¹`,
with a default so that `a / b = a * b⁻¹` holds by definition.

Use `Group.ofLeftAxioms` or `Group.ofRightAxioms` to define a group structure
on a type with the minumum proof obligations.
-/
class Group (G : Type u) extends DivInvMonoid G where
  protected mul_left_inv : ∀ a : G, a⁻¹ * a = 1
#align group Group

/-- An `AddGroup` is an `AddMonoid` with a unary `-` satisfying `-a + a = 0`.

There is also a binary operation `-` such that `a - b = a + -b`,
with a default so that `a - b = a + -b` holds by definition.

Use `AddGroup.ofLeftAxioms` or `AddGroup.ofRightAxioms` to define an
additive group structure on a type with the minumum proof obligations.
-/
class AddGroup (A : Type u) extends SubNegMonoid A where
  protected add_left_neg : ∀ a : A, -a + a = 0
#align add_group AddGroup

attribute [to_additive] Group

section Group

variable [Group G] {a b c : G}

@[to_additive (attr := simp)]
theorem mul_left_inv : ∀ a : G, a⁻¹ * a = 1 :=
  Group.mul_left_inv
#align mul_left_inv mul_left_inv
#align add_left_neg add_left_neg

@[to_additive]
theorem inv_mul_self (a : G) : a⁻¹ * a = 1 :=
  mul_left_inv a
#align inv_mul_self inv_mul_self
#align neg_add_self neg_add_self

@[to_additive]
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_self a) h

@[to_additive (attr := simp)]
theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
  by rw [← mul_left_inv a⁻¹, inv_eq_of_mul (mul_left_inv a)]
#align mul_right_inv mul_right_inv
#align add_right_neg add_right_neg

@[to_additive]
theorem mul_inv_self (a : G) : a * a⁻¹ = 1 :=
  mul_right_inv a
#align mul_inv_self mul_inv_self
#align add_neg_self add_neg_self

@[to_additive (attr := simp)]
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b :=
  by rw [← mul_assoc, mul_left_inv, one_mul]
#align inv_mul_cancel_left inv_mul_cancel_left
#align neg_add_cancel_left neg_add_cancel_left

@[to_additive (attr := simp)]
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b :=
  by rw [← mul_assoc, mul_right_inv, one_mul]
#align mul_inv_cancel_left mul_inv_cancel_left
#align add_neg_cancel_left add_neg_cancel_left

@[to_additive (attr := simp)]
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a :=
  by rw [mul_assoc, mul_right_inv, mul_one]
#align mul_inv_cancel_right mul_inv_cancel_right
#align add_neg_cancel_right add_neg_cancel_right

@[to_additive (attr := simp)]
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a :=
  by rw [mul_assoc, mul_left_inv, mul_one]
#align inv_mul_cancel_right inv_mul_cancel_right
#align neg_add_cancel_right neg_add_cancel_right

@[to_additive AddGroup.toSubtractionMonoid]
instance (priority := 100) Group.toDivisionMonoid : DivisionMonoid G :=
  { inv_inv := fun a ↦ inv_eq_of_mul (mul_left_inv a)
    mul_inv_rev :=
      fun a b ↦ inv_eq_of_mul <| by rw [mul_assoc, mul_inv_cancel_left, mul_right_inv]
    inv_eq_of_mul := fun _ _ ↦ inv_eq_of_mul }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) Group.toCancelMonoid : CancelMonoid G :=
  { ‹Group G› with
    mul_right_cancel := fun a b c h ↦ by rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right]
    mul_left_cancel := fun a b c h ↦ by rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left] }

end Group

@[to_additive]
theorem Group.toDivInvMonoid_injective {G : Type*} :
    Function.Injective (@Group.toDivInvMonoid G) := by rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl
#align group.to_div_inv_monoid_injective Group.toDivInvMonoid_injective
#align add_group.to_sub_neg_add_monoid_injective AddGroup.toSubNegAddMonoid_injective

/-- An additive commutative group is an additive group with commutative `(+)`. -/
class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G
#align add_comm_group AddCommGroup

/-- A commutative group is a group with commutative `(*)`. -/
@[to_additive]
class CommGroup (G : Type u) extends Group G, CommMonoid G
#align comm_group CommGroup

attribute [to_additive existing] CommGroup.toCommMonoid

@[to_additive]
theorem CommGroup.toGroup_injective {G : Type u} : Function.Injective (@CommGroup.toGroup G) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl
#align comm_group.to_group_injective CommGroup.toGroup_injective
#align add_comm_group.to_add_group_injective AddCommGroup.toAddGroup_injective

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
