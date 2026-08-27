/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
module

public import Mathlib.Algebra.Regular.Defs
public import Mathlib.Tactic.MkIffOfInductiveProp
public import Mathlib.Tactic.Simps

/-!
# Semigroups and algebraic structures without identities

This file defines additive and multiplicative semigroups and related structures that do not require
a distinguished one or zero. This includes cancellation and commutativity mixins and their basic
supporting lemmas and instances.
-/

public section

open Function

variable {G : Type*}

section Mul

variable [Mul G]

/-- A mixin for left cancellative multiplication. -/
@[mk_iff] class IsLeftCancelMul (G : Type*) [Mul G] : Prop where
  /-- Multiplication is left cancellative (i.e. left regular). -/
  protected mul_left_cancel (a : G) : IsLeftRegular a
/-- A mixin for right cancellative multiplication. -/
@[mk_iff] class IsRightCancelMul (G : Type*) [Mul G] : Prop where
  /-- Multiplication is right cancellative (i.e. right regular). -/
  protected mul_right_cancel (a : G) : IsRightRegular a
/-- A mixin for cancellative multiplication. -/
@[mk_iff]
class IsCancelMul (G : Type*) [Mul G] : Prop extends IsLeftCancelMul G, IsRightCancelMul G

/-- A mixin for left cancellative addition. -/
class IsLeftCancelAdd (G : Type*) [Add G] : Prop where
  /-- Addition is left cancellative (i.e. left regular). -/
  protected add_left_cancel (a : G) : IsAddLeftRegular a

attribute [to_additive] IsLeftCancelMul
attribute [to_additive] isLeftCancelMul_iff

/-- A mixin for right cancellative addition. -/
class IsRightCancelAdd (G : Type*) [Add G] : Prop where
  /-- Addition is right cancellative (i.e. right regular). -/
  protected add_right_cancel (a : G) : IsAddRightRegular a

attribute [to_additive] IsRightCancelMul
attribute [to_additive] isRightCancelMul_iff

/-- A mixin for cancellative addition. -/
@[mk_iff]
class IsCancelAdd (G : Type*) [Add G] : Prop extends IsLeftCancelAdd G, IsRightCancelAdd G

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
class Semigroup (G : Type*) extends Mul G where
  /-- Multiplication is associative -/
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

/-- An additive semigroup is a type with an associative `(+)`. -/
@[ext]
class AddSemigroup (G : Type*) extends Add G where
  /-- Addition is associative -/
  protected add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

attribute [to_additive] Semigroup

section Semigroup

variable [Semigroup G]

@[to_additive]
theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
  Semigroup.mul_assoc

end Semigroup

section IsCommutative

/-- A Prop stating that the addition is commutative. -/
class IsAddCommutative (M : Type*) [Add M] : Prop where
  is_comm : Std.Commutative (α := M) (· + ·)

/-- A Prop stating that the multiplication is commutative. -/
@[to_additive existing]
class IsMulCommutative (M : Type*) [Mul M] : Prop where
  is_comm : Std.Commutative (α := M) (· * ·)

attribute [instance] IsAddCommutative.is_comm
attribute [instance] IsMulCommutative.is_comm

@[to_additive]
lemma isMulCommutative_iff {M : Type*} [Mul M] : IsMulCommutative M ↔ ∀ a b : M, a * b = b * a := by
  grind [IsMulCommutative, Std.Commutative]

@[to_additive]
alias ⟨_, IsMulCommutative.of_comm⟩ := isMulCommutative_iff

/-- An alternative to `mul_comm` which uses the mixin `IsMulCommutative` instead of bundled
commutative algebraic structures. In general, you should prefer `mul_comm` unless you are working
with commutative subobjects in a noncommutative algebraic structure. -/
@[to_additive
/-- An alternative to `add_comm` which uses the mixin `IsAddCommutative` instead of bundled
commutative algebraic structures. In general, you should prefer `add_comm` unless you are working
with commutative subobjects in a noncommutative algebraic structure. -/ ]
lemma mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) : a * b = b * a :=
  IsMulCommutative.is_comm.comm ..

end IsCommutative

/-- A commutative additive magma is a type with an addition which commutes. -/
@[ext]
class AddCommMagma (G : Type*) extends Add G where
  /-- Addition is commutative in a commutative additive magma. -/
  protected add_comm : ∀ a b : G, a + b = b + a

/-- A commutative multiplicative magma is a type with a multiplication which commutes. -/
@[ext]
class CommMagma (G : Type*) extends Mul G where
  /-- Multiplication is commutative in a commutative multiplicative magma. -/
  protected mul_comm : ∀ a b : G, a * b = b * a

attribute [to_additive] CommMagma

/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
@[ext]
class CommSemigroup (G : Type*) extends Semigroup G, CommMagma G where

/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
@[ext]
class AddCommSemigroup (G : Type*) extends AddSemigroup G, AddCommMagma G where

attribute [to_additive] CommSemigroup

section CommMagma

variable [CommMagma G] {a : G}

@[to_additive]
theorem mul_comm : ∀ a b : G, a * b = b * a := CommMagma.mul_comm

@[to_additive]
instance CommMagma.to_isCommutative : IsMulCommutative G := ⟨⟨mul_comm⟩⟩

@[to_additive (attr := simp)]
lemma isLeftRegular_iff_isRegular : IsLeftRegular a ↔ IsRegular a := by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

@[to_additive (attr := simp)]
lemma isRightRegular_iff_isRegular : IsRightRegular a ↔ IsRegular a := by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

/-- Any `CommMagma G` that satisfies `IsRightCancelMul G` also satisfies `IsLeftCancelMul G`. -/
@[to_additive AddCommMagma.IsRightCancelAdd.toIsLeftCancelAdd /-- Any `AddCommMagma G` that
satisfies `IsRightCancelAdd G` also satisfies `IsLeftCancelAdd G`. -/]
lemma CommMagma.IsRightCancelMul.toIsLeftCancelMul (G : Type*) [CommMagma G] [IsRightCancelMul G] :
    IsLeftCancelMul G :=
  ⟨fun _ _ _ h => mul_right_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

/-- Any `CommMagma G` that satisfies `IsLeftCancelMul G` also satisfies `IsRightCancelMul G`. -/
@[to_additive AddCommMagma.IsLeftCancelAdd.toIsRightCancelAdd /-- Any `AddCommMagma G` that
satisfies `IsLeftCancelAdd G` also satisfies `IsRightCancelAdd G`. -/]
lemma CommMagma.IsLeftCancelMul.toIsRightCancelMul (G : Type*) [CommMagma G] [IsLeftCancelMul G] :
    IsRightCancelMul G :=
  ⟨fun _ _ _ h => mul_left_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

/-- Any `CommMagma G` that satisfies `IsLeftCancelMul G` also satisfies `IsCancelMul G`. -/
@[to_additive AddCommMagma.IsLeftCancelAdd.toIsCancelAdd /-- Any `AddCommMagma G` that satisfies
`IsLeftCancelAdd G` also satisfies `IsCancelAdd G`. -/]
lemma CommMagma.IsLeftCancelMul.toIsCancelMul (G : Type*) [CommMagma G] [IsLeftCancelMul G] :
    IsCancelMul G := { CommMagma.IsLeftCancelMul.toIsRightCancelMul G with }

/-- Any `CommMagma G` that satisfies `IsRightCancelMul G` also satisfies `IsCancelMul G`. -/
@[to_additive AddCommMagma.IsRightCancelAdd.toIsCancelAdd /-- Any `AddCommMagma G` that satisfies
`IsRightCancelAdd G` also satisfies `IsCancelAdd G`. -/]
lemma CommMagma.IsRightCancelMul.toIsCancelMul (G : Type*) [CommMagma G] [IsRightCancelMul G] :
    IsCancelMul G := { CommMagma.IsRightCancelMul.toIsLeftCancelMul G with }

end CommMagma

/-- A `LeftCancelSemigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
@[ext]
class LeftCancelSemigroup (G : Type*) extends Semigroup G, IsLeftCancelMul G

library_note «lower cancel priority» /--
We lower the priority of inheriting from cancellative structures.
This attempts to avoid expensive checks involving bundling and unbundling with the `IsDomain` class.
since `IsDomain` already depends on `Semiring`, we can synthesize that one first.
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Why.20is.20.60simpNF.60.20complaining.20here.3F
-/
attribute [instance 75] LeftCancelSemigroup.toSemigroup -- See note [lower cancel priority]

/-- An `AddLeftCancelSemigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
@[ext]
class AddLeftCancelSemigroup (G : Type*) extends AddSemigroup G, IsLeftCancelAdd G

attribute [instance 75] AddLeftCancelSemigroup.toAddSemigroup -- See note [lower cancel priority]

attribute [to_additive] LeftCancelSemigroup

/-- Any `LeftCancelSemigroup` satisfies `IsLeftCancelMul`. -/
add_decl_doc LeftCancelSemigroup.toIsLeftCancelMul

/-- Any `AddLeftCancelSemigroup` satisfies `IsLeftCancelAdd`. -/
add_decl_doc AddLeftCancelSemigroup.toIsLeftCancelAdd

/-- A `RightCancelSemigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
@[ext]
class RightCancelSemigroup (G : Type*) extends Semigroup G, IsRightCancelMul G

attribute [instance 75] RightCancelSemigroup.toSemigroup -- See note [lower cancel priority]

/-- An `AddRightCancelSemigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
@[ext]
class AddRightCancelSemigroup (G : Type*) extends AddSemigroup G, IsRightCancelAdd G

attribute [instance 75] AddRightCancelSemigroup.toAddSemigroup -- See note [lower cancel priority]

attribute [to_additive] RightCancelSemigroup

/-- Any `RightCancelSemigroup` satisfies `IsRightCancelMul`. -/
add_decl_doc RightCancelSemigroup.toIsRightCancelMul

/-- Any `AddRightCancelSemigroup` satisfies `IsRightCancelAdd`. -/
add_decl_doc AddRightCancelSemigroup.toIsRightCancelAdd


/-! We initialize the projections for the semigroup structures for `@[simps]` here. -/
initialize_simps_projections Semigroup
initialize_simps_projections AddSemigroup
initialize_simps_projections CommSemigroup
initialize_simps_projections AddCommSemigroup
initialize_simps_projections LeftCancelSemigroup
initialize_simps_projections AddLeftCancelSemigroup
initialize_simps_projections RightCancelSemigroup
initialize_simps_projections AddRightCancelSemigroup
