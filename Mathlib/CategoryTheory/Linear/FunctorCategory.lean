/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import Mathlib.Tactic.ToAdditive

import Mathlib.Util.CountHeartbeats
import Batteries.Tactic.ShowUnused

universe uvw -- leave this here to make some vim macros work



section Mathlib.Algebra.Group.ZeroOne

class Zero.{u} (α : Type u) where
  zero : α

instance (priority := 300) Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1

universe u

@[to_additive]
class One (α : Type u) where
  one : α

@[to_additive existing Zero.toOfNat0]
instance (priority := 300) One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

attribute [to_additive_change_numeral 2] OfNat OfNat.ofNat

end Mathlib.Algebra.Group.ZeroOne


section Mathlib.Algebra.Group.Defs

universe u v w

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

It is assumed to represent a left action in some sense.
The notation `a • b` is augmented with a macro (below) to have it elaborate as a left action.
Only the `b` argument participates in the elaboration algorithm: the algorithm uses the type of `b`
when calculating the type of the surrounding arithmetic expression
and it tries to insert coercions into `b` to get some `b'`
such that `a • b'` has the same type as `b'`.
See the module documentation near the macro for more details.
-/
class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a • b` computes the product of `a` and `b`.
  The meaning of this notation is type-dependent, but it is intended to be used for left actions. -/
  hSMul : α → β → γ

attribute [notation_class  smul Simps.copySecond] HSMul
attribute [notation_class nsmul Simps.nsmulArgs]  HSMul
attribute [notation_class zsmul Simps.zsmulArgs]  HSMul

/-- Type class for the `+ᵥ` notation. -/
class VAdd (G : Type u) (P : Type v) where
  /-- `a +ᵥ b` computes the sum of `a` and `b`. The meaning of this notation is type-dependent,
  but it is intended to be used for left actions. -/
  vadd : G → P → P

/-- Type class for the `-ᵥ` notation. -/
class VSub (G : outParam <| Type u) (P : Type v) where
  /-- `a -ᵥ b` computes the difference of `a` and `b`. The meaning of this notation is
  type-dependent, but it is intended to be used for additive torsors. -/
  vsub : P → P → G

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
@[to_additive (attr := ext)]
class SMul (M : Type u) (α : Type v) where
  /-- `a • b` computes the product of `a` and `b`. The meaning of this notation is type-dependent,
  but it is intended to be used for left actions. -/
  smul : M → α → α

@[inherit_doc] infixl:65 " +ᵥ " => HVAdd.hVAdd
@[inherit_doc] infixl:65 " -ᵥ " => VSub.vsub
@[inherit_doc] infixr:73 " • " => HSMul.hSMul

/-!
We have a macro to make `x • y` notation participate in the expression tree elaborator,
like other arithmetic expressions such as `+`, `*`, `/`, `^`, `=`, inequalities, etc.
The macro is using the `leftact%` elaborator introduced in
[this RFC](https://github.com/leanprover/lean4/issues/2854).

As a concrete example of the effect of this macro, consider
```lean
variable [Ring R] [AddCommMonoid M] [Module R M] (r : R) (N : Submodule R M) (m : M) (n : N)
#check m + r • n
```
Without the macro, the expression would elaborate as `m + ↑(r • n : ↑N) : M`.
With the macro, the expression elaborates as `m + r • (↑n : M) : M`.
To get the first interpretation, one can write `m + (r • n :)`.

Here is a quick review of the expression tree elaborator:
1. It builds up an expression tree of all the immediately accessible operations
   that are marked with `binop%`, `unop%`, `leftact%`, `rightact%`, `binrel%`, etc.
2. It elaborates every leaf term of this tree
   (without an expected type, so as if it were temporarily wrapped in `(... :)`).
3. Using the types of each elaborated leaf, it computes a supremum type they can all be
   coerced to, if such a supremum exists.
4. It inserts coercions around leaf terms wherever needed.

The hypothesis is that individual expression trees tend to be calculations with respect
to a single algebraic structure.

Note(kmill): If we were to remove `HSMul` and switch to using `SMul` directly,
then the expression tree elaborator would not be able to insert coercions within the right operand;
they would likely appear as `↑(x • y)` rather than `x • ↑y`, unlike other arithmetic operations.
-/

@[inherit_doc HSMul.hSMul]
macro_rules | `($x • $y) => `(leftact% HSMul.hSMul $x $y)

attribute [to_additive existing] Mul Div HMul instHMul HDiv instHDiv HSMul
attribute [to_additive (reorder := 1 2) SMul] Pow
attribute [to_additive (reorder := 1 2)] HPow
attribute [to_additive existing (reorder := 1 2, 5 6) hSMul] HPow.hPow
attribute [to_additive existing (reorder := 1 2, 4 5) smul] Pow.pow

@[to_additive (attr := default_instance)]
instance instHSMul {α β} [SMul α β] : HSMul α β β where
  hSMul := SMul.smul

@[to_additive]
theorem SMul.smul_eq_hSMul {α β} [SMul α β] : (SMul.smul : α → β → β) = HSMul.hSMul := rfl

attribute [to_additive existing (reorder := 1 2)] instHPow

variable {G : Type u}

/-- Class of types that have an inversion operation. -/
@[to_additive, notation_class]
class Inv (α : Type u) where
  /-- Invert an element of α. -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv.inv

section Mul

variable [Mul G]

/-- `leftMul g` denotes left multiplication by `g` -/
@[to_additive "`leftAdd g` denotes left addition by `g`"]
def leftMul : G → G → G := fun g : G ↦ fun x : G ↦ g * x

/-- `rightMul g` denotes right multiplication by `g` -/
@[to_additive "`rightAdd g` denotes right addition by `g`"]
def rightMul : G → G → G := fun g : G ↦ fun x : G ↦ x * g

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

/-- A mixin for left cancellative addition. -/
class IsLeftCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is left cancellative. -/
  protected add_left_cancel : ∀ a b c : G, a + b = a + c → b = c

attribute [to_additive IsLeftCancelAdd] IsLeftCancelMul

/-- A mixin for right cancellative addition. -/
class IsRightCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is right cancellative. -/
  protected add_right_cancel : ∀ a b c : G, a + b = c + b → a = c

attribute [to_additive IsRightCancelAdd] IsRightCancelMul

/-- A mixin for cancellative addition. -/
class IsCancelAdd (G : Type u) [Add G] extends IsLeftCancelAdd G, IsRightCancelAdd G : Prop

attribute [to_additive IsCancelAdd] IsCancelMul

section IsLeftCancelMul

variable [IsLeftCancelMul G] {a b c : G}

@[to_additive]
theorem mul_left_cancel : a * b = a * c → b = c :=
  IsLeftCancelMul.mul_left_cancel a b c

@[to_additive]
theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancel, congrArg _⟩

end IsLeftCancelMul

section IsRightCancelMul

variable [IsRightCancelMul G] {a b c : G}

@[to_additive]
theorem mul_right_cancel : a * b = c * b → a = c :=
  IsRightCancelMul.mul_right_cancel a b c

@[to_additive]
theorem mul_right_cancel_iff : b * a = c * a ↔ b = c :=
  ⟨mul_right_cancel, congrArg (· * a)⟩

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
attribute [to_additive existing] CommSemigroup.toCommMagma

section CommMagma

variable [CommMagma G]

@[to_additive]
theorem mul_comm : ∀ a b : G, a * b = b * a := CommMagma.mul_comm

/-- Any `CommMagma G` that satisfies `IsRightCancelMul G` also satisfies `IsLeftCancelMul G`. -/
@[to_additive AddCommMagma.IsRightCancelAdd.toIsLeftCancelAdd "Any `AddCommMagma G` that satisfies
`IsRightCancelAdd G` also satisfies `IsLeftCancelAdd G`."]
theorem CommMagma.IsRightCancelMul.toIsLeftCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsLeftCancelMul G :=
  ⟨fun _ _ _ h => mul_right_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

/-- Any `CommMagma G` that satisfies `IsLeftCancelMul G` also satisfies `IsRightCancelMul G`. -/
@[to_additive AddCommMagma.IsLeftCancelAdd.toIsRightCancelAdd "Any `AddCommMagma G` that satisfies
`IsLeftCancelAdd G` also satisfies `IsRightCancelAdd G`."]
theorem CommMagma.IsLeftCancelMul.toIsRightCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsRightCancelMul G :=
  ⟨fun _ _ _ h => mul_left_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

/-- Any `CommMagma G` that satisfies `IsLeftCancelMul G` also satisfies `IsCancelMul G`. -/
@[to_additive AddCommMagma.IsLeftCancelAdd.toIsCancelAdd "Any `AddCommMagma G` that satisfies
`IsLeftCancelAdd G` also satisfies `IsCancelAdd G`."]
theorem CommMagma.IsLeftCancelMul.toIsCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsCancelMul G := { CommMagma.IsLeftCancelMul.toIsRightCancelMul G with }

/-- Any `CommMagma G` that satisfies `IsRightCancelMul G` also satisfies `IsCancelMul G`. -/
@[to_additive AddCommMagma.IsRightCancelAdd.toIsCancelAdd "Any `AddCommMagma G` that satisfies
`IsRightCancelAdd G` also satisfies `IsCancelAdd G`."]
theorem CommMagma.IsRightCancelMul.toIsCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsCancelMul G := { CommMagma.IsRightCancelMul.toIsLeftCancelMul G with }

end CommMagma

/-- A `LeftCancelSemigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
@[ext]
class LeftCancelSemigroup (G : Type u) extends Semigroup G where
  protected mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c

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

attribute [instance 75] AddLeftCancelSemigroup.toAddSemigroup -- See note [lower cancel priority]

attribute [to_additive] LeftCancelSemigroup

/-- Any `LeftCancelSemigroup` satisfies `IsLeftCancelMul`. -/
@[to_additive AddLeftCancelSemigroup.toIsLeftCancelAdd "Any `AddLeftCancelSemigroup` satisfies
`IsLeftCancelAdd`."]
instance (priority := 100) LeftCancelSemigroup.toIsLeftCancelMul (G : Type u)
    [LeftCancelSemigroup G] : IsLeftCancelMul G :=
  { mul_left_cancel := LeftCancelSemigroup.mul_left_cancel }

/-- A `RightCancelSemigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
@[ext]
class RightCancelSemigroup (G : Type u) extends Semigroup G where
  protected mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c

attribute [instance 75] RightCancelSemigroup.toSemigroup -- See note [lower cancel priority]

/-- An `AddRightCancelSemigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
@[ext]
class AddRightCancelSemigroup (G : Type u) extends AddSemigroup G where
  protected add_right_cancel : ∀ a b c : G, a + b = c + b → a = c

attribute [instance 75] AddRightCancelSemigroup.toAddSemigroup -- See note [lower cancel priority]

attribute [to_additive] RightCancelSemigroup

/-- Any `RightCancelSemigroup` satisfies `IsRightCancelMul`. -/
@[to_additive AddRightCancelSemigroup.toIsRightCancelAdd "Any `AddRightCancelSemigroup` satisfies
`IsRightCancelAdd`."]
instance (priority := 100) RightCancelSemigroup.toIsRightCancelMul (G : Type u)
    [RightCancelSemigroup G] : IsRightCancelMul G :=
  { mul_right_cancel := RightCancelSemigroup.mul_right_cancel }

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
class MulOneClass (M : Type u) extends One M, Mul M where
  /-- One is a left neutral element for multiplication -/
  protected one_mul : ∀ a : M, 1 * a = a
  /-- One is a right neutral element for multiplication -/
  protected mul_one : ∀ a : M, a * 1 = a

/-- Typeclass for expressing that a type `M` with addition and a zero satisfies
`0 + a = a` and `a + 0 = a` for all `a : M`. -/
class AddZeroClass (M : Type u) extends Zero M, Add M where
  /-- Zero is a left neutral element for addition -/
  protected zero_add : ∀ a : M, 0 + a = a
  /-- Zero is a right neutral element for addition -/
  protected add_zero : ∀ a : M, a + 0 = a

attribute [to_additive] MulOneClass

@[to_additive (attr := ext)]
theorem MulOneClass.ext {M : Type u} : ∀ ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul → m₁ = m₂ := by
  rintro @⟨⟨one₁⟩, ⟨mul₁⟩, one_mul₁, mul_one₁⟩ @⟨⟨one₂⟩, ⟨mul₂⟩, one_mul₂, mul_one₂⟩ ⟨rfl⟩
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

/-- The fundamental power operation in a monoid. `npowRec n a = a*a*...*a` n times.
Use instead `a ^ n`, which has better definitional behavior. -/
def npowRec [One M] [Mul M] : ℕ → M → M
  | 0, _ => 1
  | n + 1, a => npowRec n a * a

/-- The fundamental scalar multiplication in an additive monoid. `nsmulRec n a = a+a+...+a` n
times. Use instead `n • a`, which has better definitional behavior. -/
def nsmulRec [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => nsmulRec n a + a

attribute [to_additive existing] npowRec

end

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
attribute [instance 50] AddZeroClass.toAdd

/-- A `Monoid` is a `Semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[to_additive]
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  /-- Raising to the power of a natural number. -/
  protected npow : ℕ → M → M := npowRec
  /-- Raising to the power `(0 : ℕ)` gives `1`. -/
  protected npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  /-- Raising to the power `(n + 1 : ℕ)` behaves as expected. -/
  protected npow_succ : ∀ (n : ℕ) (x), npow (n + 1) x = npow n x * x := by intros; rfl

-- Bug #660
attribute [to_additive existing] Monoid.toMulOneClass

@[default_instance high] instance Monoid.toNatPow {M : Type u} [Monoid M] : Pow M ℕ :=
  ⟨fun x n ↦ Monoid.npow n x⟩

instance AddMonoid.toNatSMul {M : Type u} [AddMonoid M] : SMul ℕ M :=
  ⟨AddMonoid.nsmul⟩

attribute [to_additive existing toNatSMul] Monoid.toNatPow

section Monoid
variable {M : Type u} [Monoid M] {a b c : M} {m n : ℕ}

@[to_additive (attr := simp) nsmul_eq_smul]
theorem npow_eq_pow (n : ℕ) (x : M) : Monoid.npow n x = x ^ n :=
  rfl

@[to_additive] theorem left_inv_eq_right_inv (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]

end Monoid

/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M

/-- A commutative monoid is a monoid with commutative `(*)`. -/
@[to_additive]
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M

attribute [to_additive existing] CommMonoid.toCommSemigroup

section LeftCancelMonoid

/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddLeftCancelSemigroup` is not enough. -/
class AddLeftCancelMonoid (M : Type u) extends AddLeftCancelSemigroup M, AddMonoid M

attribute [instance 75] AddLeftCancelMonoid.toAddMonoid -- See note [lower cancel priority]

/-- A monoid in which multiplication is left-cancellative. -/
@[to_additive]
class LeftCancelMonoid (M : Type u) extends LeftCancelSemigroup M, Monoid M

attribute [instance 75] LeftCancelMonoid.toMonoid -- See note [lower cancel priority]

attribute [to_additive existing] LeftCancelMonoid.toMonoid

end LeftCancelMonoid

section RightCancelMonoid

/-- An additive monoid in which addition is right-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddRightCancelSemigroup` is not enough. -/
class AddRightCancelMonoid (M : Type u) extends AddRightCancelSemigroup M, AddMonoid M

attribute [instance 75] AddRightCancelMonoid.toAddMonoid -- See note [lower cancel priority]

/-- A monoid in which multiplication is right-cancellative. -/
@[to_additive]
class RightCancelMonoid (M : Type u) extends RightCancelSemigroup M, Monoid M

attribute [instance 75] RightCancelMonoid.toMonoid -- See note [lower cancel priority]

attribute [to_additive existing] RightCancelMonoid.toMonoid

end RightCancelMonoid

section CancelMonoid

/-- An additive monoid in which addition is cancellative on both sides.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddRightCancelMonoid` is not enough. -/
class AddCancelMonoid (M : Type u) extends AddLeftCancelMonoid M, AddRightCancelMonoid M

/-- A monoid in which multiplication is cancellative. -/
@[to_additive]
class CancelMonoid (M : Type u) extends LeftCancelMonoid M, RightCancelMonoid M

attribute [to_additive existing] CancelMonoid.toRightCancelMonoid


/-- Any `CancelMonoid G` satisfies `IsCancelMul G`. -/
@[to_additive toIsCancelAdd "Any `AddCancelMonoid G` satisfies `IsCancelAdd G`."]
instance (priority := 100) CancelMonoid.toIsCancelMul (M : Type u) [CancelMonoid M] :
    IsCancelMul M :=
  { mul_left_cancel := LeftCancelSemigroup.mul_left_cancel
    mul_right_cancel := RightCancelSemigroup.mul_right_cancel }

end CancelMonoid

/-- The fundamental power operation in a group. `zpowRec n a = a*a*...*a` n times, for integer `n`.
Use instead `a ^ n`, which has better definitional behavior. -/
def zpowRec [One G] [Mul G] [Inv G] (npow : ℕ → G → G := npowRec) : Int → G → G
  | Int.ofNat n, a => npow n a
  | Int.negSucc n, a => (npow n.succ a)⁻¹

/-- The fundamental scalar multiplication in an additive group. `zpowRec n a = a+a+...+a` n
times, for integer `n`. Use instead `n • a`, which has better definitional behavior. -/
def zsmulRec [Zero G] [Add G] [Neg G] (nsmul : ℕ → G → G := nsmulRec) : Int → G → G
  | Int.ofNat n, a => nsmul n a
  | Int.negSucc n, a => -nsmul n.succ a

attribute [to_additive existing] zpowRec

section InvolutiveInv

/-- Auxiliary typeclass for types with an involutive `Neg`. -/
class InvolutiveNeg (A : Type u) extends Neg A where
  protected neg_neg : ∀ x : A, - -x = x

/-- Auxiliary typeclass for types with an involutive `Inv`. -/
@[to_additive]
class InvolutiveInv (G : Type u) extends Inv G where
  protected inv_inv : ∀ x : G, x⁻¹⁻¹ = x

variable [InvolutiveInv G]

@[to_additive (attr := simp)]
theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
  InvolutiveInv.inv_inv _

end InvolutiveInv

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
  protected zpow : Int → G → G := zpowRec npowRec
  /-- `a ^ 0 = 1` -/
  protected zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  /-- `a ^ (n + 1) = a ^ n * a` -/
  protected zpow_succ' (n : ℕ) (a : G) : zpow (Int.ofNat n.succ) a = zpow (Int.ofNat n) a  * a := by
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
  protected zsmul : Int → G → G
  protected zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by intros; rfl
  protected zsmul_succ' (n : ℕ) (a : G) :
      zsmul (Int.ofNat n.succ) a = zsmul (Int.ofNat n) a + a := by
    intros; rfl
  protected zsmul_neg' (n : ℕ) (a : G) : zsmul (Int.negSucc n) a = -zsmul n.succ a := by
    intros; rfl

attribute [to_additive SubNegMonoid] DivInvMonoid

instance DivInvMonoid.Pow {M} [DivInvMonoid M] : Pow M Int :=
  ⟨fun x n ↦ DivInvMonoid.zpow n x⟩

instance SubNegMonoid.SMulInt {M} [SubNegMonoid M] : SMul Int M :=
  ⟨SubNegMonoid.zsmul⟩

attribute [to_additive existing SubNegMonoid.SMulInt] DivInvMonoid.Pow

section DivInvMonoid

variable [DivInvMonoid G] {a b : G}

/-- Dividing by an element is the same as multiplying by its inverse.

This is a duplicate of `DivInvMonoid.div_eq_mul_inv` ensuring that the types unfold better.
-/
@[to_additive "Subtracting an element is the same as adding by its negative.
This is a duplicate of `SubNegMonoid.sub_eq_mul_neg` ensuring that the types unfold better."]
theorem div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ :=
  DivInvMonoid.div_eq_mul_inv _ _


end DivInvMonoid

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

attribute [to_additive existing] DivisionMonoid.toInvolutiveInv

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

attribute [to_additive existing] DivisionCommMonoid.toCommMonoid

/-- A `Group` is a `Monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`.

There is also a division operation `/` such that `a / b = a * b⁻¹`,
with a default so that `a / b = a * b⁻¹` holds by definition.

Use `Group.ofLeftAxioms` or `Group.ofRightAxioms` to define a group structure
on a type with the minumum proof obligations.
-/
class Group (G : Type u) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

/-- An `AddGroup` is an `AddMonoid` with a unary `-` satisfying `-a + a = 0`.

There is also a binary operation `-` such that `a - b = a + -b`,
with a default so that `a - b = a + -b` holds by definition.

Use `AddGroup.ofLeftAxioms` or `AddGroup.ofRightAxioms` to define an
additive group structure on a type with the minumum proof obligations.
-/
class AddGroup (A : Type u) extends SubNegMonoid A where
  protected neg_add_cancel : ∀ a : A, -a + a = 0

attribute [to_additive] Group

section Group

variable [Group G] {a b c : G}

@[to_additive (attr := simp)]
theorem inv_mul_cancel (a : G) : a⁻¹ * a = 1 :=
  Group.inv_mul_cancel a

@[to_additive]
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_cancel a) h

@[to_additive (attr := simp)]
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  rw [← inv_mul_cancel a⁻¹, inv_eq_of_mul (inv_mul_cancel a)]

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
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul_cancel, mul_one]

@[to_additive]
instance (priority := 100) Group.toDivisionMonoid : DivisionMonoid G :=
  { inv_inv := fun a ↦ inv_eq_of_mul (inv_mul_cancel a)
    mul_inv_rev :=
      fun a b ↦ inv_eq_of_mul <| by rw [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
    inv_eq_of_mul := fun _ _ ↦ inv_eq_of_mul }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) Group.toCancelMonoid : CancelMonoid G :=
  { ‹Group G› with
    mul_right_cancel := fun a b c h ↦ by rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right]
    mul_left_cancel := fun a b c h ↦ by rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left] }

end Group

/-- An additive commutative group is an additive group with commutative `(+)`. -/
class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

/-- A commutative group is a group with commutative `(*)`. -/
@[to_additive]
class CommGroup (G : Type u) extends Group G, CommMonoid G

attribute [to_additive existing] CommGroup.toCommMonoid

end Mathlib.Algebra.Group.Defs

-- section Mathlib.Algebra.Group.Defs.Modified
-- 
-- class AddMonoid (M : Type u) extends Zero M, Add M where
-- 
-- class AddCommMonoid (M : Type u) extends AddMonoid M where
--   add_comm : ∀ a b : M, a + b = b + a
-- 
-- class AddGroup (M : Type u) extends AddMonoid M, Neg M, Sub M where
-- 
-- end Mathlib.Algebra.Group.Defs.Modified

universe x w v u v' u' v₁ v₂ v₃ u₁ u₂ u₃

section Mathlib.Data.Nat.Cast.Defs

variable {R : Type u}

/-- The numeral `((0+1)+⋯)+1`. -/
protected def Nat.unaryCast [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1

/-! ### Additive monoids with one -/

/-- An `AddMonoidWithOne` is an `AddMonoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`. -/
class AddMonoidWithOne (R : Type u) extends NatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  /-- The canonical map `ℕ → R` sends `0 : ℕ` to `0 : R`. -/
  natCast_zero : natCast 0 = 0 := by intros; rfl
  /-- The canonical map `ℕ → R` is a homomorphism. -/
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1 := by intros; rfl

/-- An `AddCommMonoidWithOne` is an `AddMonoidWithOne` satisfying `a + b = b + a`.  -/
class AddCommMonoidWithOne (R : Type u) extends AddMonoidWithOne R, AddCommMonoid R

end Mathlib.Data.Nat.Cast.Defs


section Mathlib.Algebra.Group.Hom.Defs.Modified

structure AddMonoidHom (M : Type u) (N : Type v) [AddMonoid M] [AddMonoid N] where
  toFun : M → N
  map_zero' : toFun 0 = 0
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y

infixr:25 " →+ " => AddMonoidHom

namespace AddMonoidHom

variable {M : Type u} {N : Type v}

instance [AddMonoid M] [AddMonoid N] : CoeFun (M →+ N) (fun _ => M → N) where
  coe := toFun

section

variable [AddMonoid M] [AddGroup N]

/-- Makes a group homomorphism from a proof that the map preserves multiplication. -/
def mk' (f : M → N) (map_add : ∀ a b : M, f (a + b) = f a + f b) : M →+ N where
  toFun := f
  map_add' := map_add
  map_zero' := by rw [← add_right_cancel_iff, ← map_add _ 0, zero_add, zero_add]

end

section

variable [AddGroup M] [AddGroup N]

theorem map_zero (f : M →+ N) : f 0 = 0 := by
  have := calc 0 + f 0
            = f (0 + 0) := by simp
          _ = f 0 + f 0 := by rw [f.map_add']
  rw [add_right_cancel_iff] at this
  exact this.symm

theorem map_neg (f : M →+ N) (m : M) : f (-m) = - (f m) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← f.map_add']
  simp [f.map_zero]

theorem map_sub (f : M →+ N) (m n : M) : f (m - n) = f m - f n := by
  rw [sub_eq_add_neg, sub_eq_add_neg, f.map_add', f.map_neg]

end

end AddMonoidHom

end Mathlib.Algebra.Group.Hom.Defs.Modified

section Mathlib.Algebra.GroupWithZero.Defs

variable {G₀ : Type u} {M₀ : Type u₁} {M₀' : Type u₂} {G₀' : Type u₃}

/-- Typeclass for expressing that a type `M₀` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`. -/
class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
  /-- Zero is a left absorbing element for multiplication -/
  zero_mul : ∀ a : M₀, 0 * a = 0
  /-- Zero is a right absorbing element for multiplication -/
  mul_zero : ∀ a : M₀, a * 0 = 0

export MulZeroClass (zero_mul mul_zero)
attribute [simp] zero_mul mul_zero

/-- A type `M₀` is a “monoid with zero” if it is a monoid with zero element, and `0` is left
and right absorbing. -/
class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulOneClass M₀, MulZeroClass M₀

end Mathlib.Algebra.GroupWithZero.Defs


section Mathlib.Algebra.Group.Action.Defs

variable {M : Type u} {α : Type v}

/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
class MulAction (α : Type u) (β : Type v) [Monoid α] extends SMul α β where
  /-- One is the neutral element for `•` -/
  protected one_smul : ∀ b : β, (1 : α) • b = b
  /-- Associativity of `•` and `*` -/
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b

variable [Monoid M] [MulAction M α]

variable (M)

theorem one_smul (b : α) : (1 : M) • b = b := MulAction.one_smul _

end Mathlib.Algebra.Group.Action.Defs


section Mathlib.Algebra.GroupWithZero.Action.Defs

/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
class DistribMulAction (M : Type u) (A : Type v) [Monoid M] [AddMonoid A] extends MulAction M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : ∀ a : M, a • (0 : A) = 0
  /-- Scalar multiplication distributes across addition -/
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y

export DistribMulAction (smul_zero smul_add)

end Mathlib.Algebra.GroupWithZero.Action.Defs


section Mathlib.Algebra.GroupWithZero.Action.Defs.Modifications

/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
class DistribMulAction' (M : Type u) (A : Type v) [Monoid M] [AddMonoid A] extends SMul M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : ∀ a : M, a • (0 : A) = 0
  /-- Scalar multiplication distributes across addition -/
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y
  /-- One is the neutral element for `•` -/
  one_smul : ∀ b : A, (1 : M) • b = b
  /-- Associativity of `•` and `*` -/
  mul_smul : ∀ (x y : M) (b : A), (x * y) • b = x • y • b

variable {M : Type u} {A : Type v}

export DistribMulAction' (smul_zero smul_add one_smul mul_smul)

end Mathlib.Algebra.GroupWithZero.Action.Defs.Modifications

section Mathlib.Algebra.Ring.Defs

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
class Distrib (R : Type u) extends Mul R, Add R where
  /-- Multiplication is left distributive over addition -/
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

/-- A `Semiring` is a type with addition, multiplication, a `0` and a `1` where addition is
commutative and associative, multiplication is associative and left and right distributive over
addition, and `0` and `1` are additive and multiplicative identities. -/
class Semiring (α : Type u) extends AddCommMonoid α, Distrib α, Monoid α, MulZeroClass α,
    AddCommMonoidWithOne α

end Mathlib.Algebra.Ring.Defs


section Mathlib.Algebra.Module.Defs

open Function

/-- A module is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `R` and an additive monoid of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
  DistribMulAction R M where
  /-- Scalar multiplication distributes over addition from the right. -/
  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  /-- Scalar multiplication by zero gives zero. -/
  protected zero_smul : ∀ x : M, (0 : R) • x = 0

export Module (add_smul zero_smul)

end Mathlib.Algebra.Module.Defs


section Mathlib.Combinatorics.Quiver.Basic

/-- A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
a type `a ⟶ b` of arrows from `a` to `b`.

For graphs with no repeated edges, one can use `Quiver.{0} V`, which ensures
`a ⟶ b : Prop`. For multigraphs, one can use `Quiver.{v+1} V`, which ensures
`a ⟶ b : Type v`.

Because `Category` will later extend this class, we call the field `Hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` notation instead.
-/
class Quiver (V : Type u) where
  /-- The type of edges/arrows/morphisms between a given source and target. -/
  Hom : V → V → Sort v

/--
Notation for the type of edges/arrows/morphisms between a given source and target
in a quiver or category.
-/
infixr:10 " ⟶ " => Quiver.Hom

/-- A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `Prefunctor`. -/
structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  /-- The action of a (pre)functor on vertices/objects. -/
  obj : V → W
  /-- The action of a (pre)functor on edges/arrows/morphisms. -/
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

end Mathlib.Combinatorics.Quiver.Basic


section Mathlib.CategoryTheory.Category.Basic

namespace CategoryTheory

/-- A preliminary structure on the way to defining a category,
containing the data, but none of the axioms. -/
class CategoryStruct (obj : Type u) extends Quiver.{v + 1} obj : Type max u (v + 1) where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g`. -/
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

/-- Notation for the identity morphism in a category. -/
scoped notation "𝟙" => CategoryStruct.id  -- type as \b1

/-- Notation for composition of morphisms in a category. -/
scoped infixr:80 " ≫ " => CategoryStruct.comp -- type as \gg

/-- The typeclass `Category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `Category.{v} C`. (See also `LargeCategory` and `SmallCategory`.)

See <https://stacks.math.columbia.edu/tag/0014>.
-/
class Category (obj : Type u) extends CategoryStruct.{v} obj : Type max u (v + 1) where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h

attribute [simp] Category.id_comp Category.comp_id Category.assoc
attribute [trans] CategoryStruct.comp

end CategoryTheory

end Mathlib.CategoryTheory.Category.Basic


section Mathlib.CategoryTheory.Functor.Basic

namespace CategoryTheory

section

/-- `Functor C D` represents a functor between categories `C` and `D`.

To apply a functor `F` to an object use `F.obj X`, and to a morphism use `F.map f`.

The axiom `map_id` expresses preservation of identities, and
`map_comp` expresses functoriality.

See <https://stacks.math.columbia.edu/tag/001B>.
-/
structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
    extends Prefunctor C D : Type max v₁ v₂ u₁ u₂ where
  /-- A functor preserves identity morphisms. -/
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X)
  /-- A functor preserves composition. -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g

/-- The prefunctor between the underlying quivers. -/
add_decl_doc Functor.toPrefunctor

end

/-- Notation for a functor between categories. -/
-- A functor is basically a function, so give ⥤ a similar precedence to → (25).
-- For example, `C × D ⥤ E` should parse as `(C × D) ⥤ E` not `C × (D ⥤ E)`.
infixr:26 " ⥤ " => Functor -- type as \func

attribute [simp] Functor.map_id Functor.map_comp

end CategoryTheory

end Mathlib.CategoryTheory.Functor.Basic

section Mathlib.CategoryTheory.NatTrans

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- `NatTrans F G` represents a natural transformation between functors `F` and `G`.

The field `app` provides the components of the natural transformation.

Naturality is expressed by `α.naturality`.
-/
@[ext]
structure NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where
  /-- The component of a natural transformation. -/
  app : ∀ X : C, F.obj X ⟶ G.obj X
  /-- The naturality square for a given morphism. -/
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f

-- Rather arbitrarily, we say that the 'simpler' form is
-- components of natural transformations moving earlier.
attribute [simp] NatTrans.naturality

@[simp]
theorem NatTrans.naturality_assoc {F G : C ⥤ D} (self : NatTrans F G) ⦃X Y : C⦄ (f : X ⟶ Y) {Z : D}
    (h : G.obj Y ⟶ Z) : F.map f ≫ self.app Y ≫ h = self.app X ≫ G.map f ≫ h := by
  rw [← Category.assoc, NatTrans.naturality, Category.assoc]

namespace NatTrans

/-- `NatTrans.id F` is the identity natural transformation on a functor `F`. -/
protected def id (F : C ⥤ D) : NatTrans F F where
  app X := 𝟙 (F.obj X)
  naturality := by 
    intro X Y f
    simp_all only [Category.comp_id, Category.id_comp]

@[simp]
theorem id_app' (F : C ⥤ D) (X : C) : (NatTrans.id F).app X = 𝟙 (F.obj X) := rfl

open Category

open CategoryTheory.Functor

section

variable {F G H I : C ⥤ D}

/-- `vcomp α β` is the vertical compositions of natural transformations. -/
def vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := α.app X ≫ β.app X
  naturality := by 
    intro X Y f
    simp_all only [naturality_assoc, naturality, assoc]

-- functor_category will rewrite (vcomp α β) to (α ≫ β), so this is not a
-- suitable simp lemma.  We will declare the variant vcomp_app' there.
theorem vcomp_app (α : NatTrans F G) (β : NatTrans G H) (X : C) :
    (vcomp α β).app X = α.app X ≫ β.app X := rfl

end

/-- The diagram
    F(f)      F(g)      F(h)
F X ----> F Y ----> F U ----> F U
 |         |         |         |
 | α(X)    | α(Y)    | α(U)    | α(V)
 v         v         v         v
G X ----> G Y ----> G U ----> G V
    G(f)      G(g)      G(h)
commutes.
-/
example {F G : C ⥤ D} (α : NatTrans F G) {X Y U V : C} (f : X ⟶ Y) (g : Y ⟶ U) (h : U ⟶ V) :
    α.app X ≫ G.map f ≫ G.map g ≫ G.map h = F.map f ≫ F.map g ≫ F.map h ≫ α.app V := by
  simp

end NatTrans

end CategoryTheory
end Mathlib.CategoryTheory.NatTrans

section Mathlib.CategoryTheory.Functor.Category

namespace CategoryTheory

open NatTrans Category CategoryTheory.Functor

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

attribute [local simp] vcomp_app

variable {C D} {E : Type u₃} [Category.{v₃} E]
variable {F G H I : C ⥤ D}

/-- `Functor.category C D` gives the category structure on functors and natural transformations
between categories `C` and `D`.

Notice that if `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/
instance Functor.category : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β
  id_comp := by 
    intro X Y f
    simp_all only
    ext x : 2
    simp_all only [vcomp_app, id_app', id_comp]
  comp_id := by 
    intro X Y f
    simp_all only
    ext x : 2
    simp_all only [vcomp_app, id_app', comp_id]
  assoc := by 
    intro W X Y Z f g h
    simp_all only
    ext x : 2
    simp_all only [vcomp_app, assoc]

namespace NatTrans

-- Porting note: the behaviour of `ext` has changed here.
-- We need to provide a copy of the `NatTrans.ext` lemma,
-- written in terms of `F ⟶ G` rather than `NatTrans F G`,
-- or `ext` will not retrieve it from the cache.
@[ext]
theorem ext' {α β : F ⟶ G} (w : α.app = β.app) : α = β := NatTrans.ext w

end NatTrans

open NatTrans

end CategoryTheory
end Mathlib.CategoryTheory.Functor.Category

noncomputable
section Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

open scoped Classical

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]
variable (D : Type u') [Category.{v'} D]

/-- A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. -/
class HasZeroMorphisms where
  /-- Every morphism space has zero -/
  [zero : ∀ X Y : C, Zero (X ⟶ Y)]
  /-- `f` composed with `0` is `0` -/
  comp_zero : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
  /-- `0` composed with `f` is `0` -/
  zero_comp : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)

attribute [instance] HasZeroMorphisms.zero

variable {C}

@[simp]
theorem comp_zero [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y} {Z : C} :
    f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) :=
  HasZeroMorphisms.comp_zero f Z

@[simp]
theorem zero_comp [HasZeroMorphisms C] {X : C} {Y Z : C} {f : Y ⟶ Z} :
    (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) :=
  HasZeroMorphisms.zero_comp X f

end CategoryTheory.Limits

end Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

section Mathlib.CategoryTheory.Preadditive.Basic

open CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A category is called preadditive if `P ⟶ Q` is an abelian group such that composition is
    linear in both variables. -/
class Preadditive where
  homGroup : ∀ P Q : C, AddCommGroup (P ⟶ Q) := by infer_instance
  add_comp : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g
  comp_add : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g'

attribute [inherit_doc Preadditive] Preadditive.homGroup Preadditive.add_comp Preadditive.comp_add

attribute [instance] Preadditive.homGroup

attribute [simp] Preadditive.add_comp

-- (the linter doesn't like `simp` on this lemma)
attribute [simp] Preadditive.comp_add

end CategoryTheory

namespace CategoryTheory

namespace Preadditive

open AddMonoidHom

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Composition by a fixed left argument as a group homomorphism -/
def leftComp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
  mk' (fun g => f ≫ g) fun g g' => by simp

/-- Composition by a fixed right argument as a group homomorphism -/
def rightComp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
  mk' (fun f => f ≫ g) fun f f' => by simp

variable {P Q R : C} (f f' : P ⟶ Q) (g g' : Q ⟶ R)

@[simp]
theorem sub_comp : (f - f') ≫ g = f ≫ g - f' ≫ g :=
  map_sub (rightComp P g) f f'

@[simp]
theorem comp_sub : f ≫ (g - g') = f ≫ g - f ≫ g' :=
  map_sub (leftComp R f) g g'

@[simp]
theorem neg_comp : (-f) ≫ g = -f ≫ g :=
  map_neg (rightComp P g) f

@[simp]
theorem comp_neg : f ≫ (-g) = -f ≫ g :=
  map_neg (leftComp R f) g

instance (priority := 100) preadditiveHasZeroMorphisms : HasZeroMorphisms C where
  zero := inferInstance
  comp_zero f R := show leftComp R f 0 = 0 from map_zero _
  zero_comp P _ _ f := show rightComp P f 0 = 0 from map_zero _

end Preadditive

end CategoryTheory

end Mathlib.CategoryTheory.Preadditive.Basic

section Mathlib.CategoryTheory.Preadditive.Basic

namespace CategoryTheory

open CategoryTheory.Limits Preadditive

variable {C : Type u₁} {D : Type u₂} [Category C] [Category D] [Preadditive D]

instance {F G : C ⥤ D} : Zero (F ⟶ G) where
  zero :=
   { app := fun X => 0
     naturality := by 
       intro X Y f
       simp_all only [comp_zero, zero_comp] }

instance {F G : C ⥤ D} : Add (F ⟶ G) where
  add α β :=
  { app := fun X => α.app X + β.app X,
    naturality := by 
      intro X Y f
      simp_all only [comp_add, NatTrans.naturality, add_comp] }

instance {F G : C ⥤ D} : Neg (F ⟶ G) where
  neg α :=
  { app := fun X => -α.app X,
    naturality := by 
      intro X Y f
      simp_all only [comp_neg, NatTrans.naturality, neg_comp] }

instance functorCategoryPreadditive : Preadditive (C ⥤ D) where
  homGroup F G :=
    { nsmul := nsmulRec
      zsmul := zsmulRec
      sub := fun α β =>
      { app := fun X => α.app X - β.app X
        naturality := by 
          intro X Y f
          simp_all only [comp_sub, NatTrans.naturality, sub_comp] }
      add_assoc := by
        intros
        ext
        apply add_assoc
      zero_add := by
        intros
        dsimp
        ext
        apply zero_add
      add_zero := by
        intros
        dsimp
        ext
        apply add_zero
      add_comm := by
        intros
        dsimp
        ext
        apply add_comm
      sub_eq_add_neg := by
        intros
        dsimp
        ext
        apply sub_eq_add_neg
      neg_add_cancel := by
        intros
        dsimp
        ext
        apply neg_add_cancel }
  add_comp := by
    intros
    dsimp
    ext
    apply add_comp
  comp_add := by
    intros
    dsimp
    ext
    apply comp_add

end CategoryTheory

end Mathlib.CategoryTheory.Preadditive.Basic

section Mathlib.CategoryTheory.Linear.Basic

open CategoryTheory.Limits

namespace CategoryTheory

/-- A category is called `R`-linear if `P ⟶ Q` is an `R`-module such that composition is
    `R`-linear in both variables. -/
class Linear (R : Type w) [Semiring R] (C : Type u) [Category.{v} C] [Preadditive C] where
  homModule : ∀ X Y : C, Module R (X ⟶ Y) := by infer_instance
  /-- compatibility of the scalar multiplication with the post-composition -/
  smul_comp : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g
  /-- compatibility of the scalar multiplication with the pre-composition -/
  comp_smul : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g

attribute [instance] Linear.homModule

attribute [simp] Linear.smul_comp Linear.comp_smul

-- (the linter doesn't like `simp` on the `_assoc` lemma)
end CategoryTheory

end Mathlib.CategoryTheory.Linear.Basic

open CategoryTheory

namespace CategoryTheory

open CategoryTheory.Limits Linear
open CategoryTheory.Linear

variable {R : Type u₃} [Semiring R]
variable {C : Type u₁} {D : Type u₂} [Category C] [Category D] [Preadditive D] [Linear R D]

/- count_heartbeats in -/
/- instance functorCategoryLinear : Linear R (C ⥤ D) where -/
/-   homModule F G := -/
/-     { -/ 
/-       smul := fun r α ↦ -/ 
/-         { app := fun X ↦ r • α.app X -/
/-           naturality := by -/
/-             intros -/
/-             rw [Linear.comp_smul, Linear.smul_comp, α.naturality] } -/
/-       one_smul := by -/
/-         intros -/
/-         ext -/
/-         apply MulAction.one_smul -/
/-       zero_smul := by -/
/-         intros -/
/-         ext -/
/-         apply Module.zero_smul -/
/-       smul_zero := by -/
/-         intros -/
/-         ext -/
/-         apply DistribMulAction.smul_zero -/
/-       add_smul := by -/
/-         intros -/
/-         ext -/
/-         apply Module.add_smul -/
/-       smul_add := by -/
/-         intros -/
/-         ext -/
/-         apply DistribMulAction.smul_add -/
/-       mul_smul := by -/
/-         intros -/
/-         ext -/
/-         apply MulAction.mul_smul -/
/-         } -/
/-   smul_comp := by -/
/-     intros -/
/-     ext -/
/-     apply Linear.smul_comp -/
/-   comp_smul := by -/
/-     intros -/
/-     ext -/
/-     apply Linear.comp_smul -/

instance functorCategorySMul (F G : C ⥤ D) : SMul R (F ⟶ G) where
  smul r α := 
    { app := fun X => r • α.app X
      naturality := by
        intros
        rw [Linear.comp_smul, Linear.smul_comp, α.naturality] }

instance functorCategoryLinear' : Linear R (C ⥤ D) where
  homModule F G :=
    { one_smul := by
        intros
        ext
        apply MulAction.one_smul
      zero_smul := by
        intros
        ext
        apply Module.zero_smul
      smul_zero := by
        intros
        ext
        apply DistribMulAction.smul_zero
      add_smul := by
        intros
        ext
        apply Module.add_smul
      smul_add := by
        intros
        ext
        apply DistribMulAction.smul_add
      mul_smul := by
        intros
        ext
        apply MulAction.mul_smul
        }
  smul_comp := by
    intros
    ext
    apply Linear.smul_comp
  comp_smul := by
    intros
    ext
    apply Linear.comp_smul

end CategoryTheory

/- #show_unused CategoryTheory.functorCategoryLinear -/
#show_unused CategoryTheory.functorCategoryLinear'
