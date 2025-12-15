import Mathlib.Tactic.FastInstance
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Spread

namespace testing
set_option autoImplicit false

-- For debugging:
--set_option trace.Elab.fast_instance true

/-!
Testing a diamond: CommSemigroup
-/

class Mul (α : Type*) where
  mul : α → α → α

class Semigroup (α : Type*) extends Mul α where
  mul_assoc (x y z : α) : mul x (mul y z) = mul (mul x y) z

class CommMagma (α : Type*) extends Mul α where
  mul_comm (x y : α) : mul x y = mul y x

class CommSemigroup (α : Type*) extends Semigroup α, CommMagma α

structure Wrapped (α : Type*) where
  val : α

variable {α : Type*}

theorem val_injective : Function.Injective (Wrapped.val (α := α))
  | ⟨_⟩, ⟨_⟩, rfl => rfl

instance [Mul α] : Mul (Wrapped α) where mul m n := ⟨Mul.mul m.1 n.1⟩

@[reducible] def Function.Injective.semigroup {α β : Type*} [Mul α] [Semigroup β]
    (f : α → β) (hf : Function.Injective f)
    (hmul : ∀ x y, f (Mul.mul x y) = Mul.mul (f x) (f y)) :
    Semigroup α :=
  { ‹Mul α› with
    mul_assoc := fun x y z => by apply hf; rw [hmul, hmul, hmul, hmul, Semigroup.mul_assoc] }

@[reducible] def Function.Injective.commMagma {α β : Type*} [Mul α] [CommMagma β]
    (f : α → β) (hf : Function.Injective f)
    (hmul : ∀ x y, f (Mul.mul x y) = Mul.mul (f x) (f y)) :
    CommMagma α where
  mul_comm x y := by
    apply hf
    rw [hmul, hmul, CommMagma.mul_comm]

@[reducible] def Function.Injective.commSemigroup {α β : Type*} [Mul α] [CommSemigroup β]
    (f : α → β) (hf : Function.Injective f)
    (hmul : ∀ x y, f (Mul.mul x y) = Mul.mul (f x) (f y)) :
    CommSemigroup α where
  toSemigroup := Function.Injective.semigroup f hf hmul
  __ := Function.Injective.commMagma f hf hmul

instance instSemigroup [Semigroup α] : Semigroup (Wrapped α) :=
  fast_instance% Function.Injective.semigroup _ val_injective (fun _ _ => rfl)

instance instCommSemigroup [CommSemigroup α] : CommSemigroup (Wrapped α) :=
  fast_instance% Function.Injective.commSemigroup _ val_injective (fun _ _ => rfl)

/--
info: def testing.instSemigroup.{u_1} : {α : Type u_1} → [Semigroup α] → Semigroup (Wrapped α) :=
fun {α} [inst : Semigroup α] => @Semigroup.mk (Wrapped α) (@instMulWrapped α (@Semigroup.toMul α inst)) ⋯
-/
#guard_msgs in
set_option pp.explicit true in
#print instSemigroup
/--
info: def testing.instCommSemigroup.{u_1} : {α : Type u_1} → [CommSemigroup α] → CommSemigroup (Wrapped α) :=
fun {α} [inst : CommSemigroup α] =>
  @CommSemigroup.mk (Wrapped α) (@instSemigroup α (@CommSemigroup.toSemigroup α inst)) ⋯
-/
#guard_msgs in
set_option pp.explicit true in
#print instCommSemigroup


/-!
Non-defeq error
-/
instance : Mul Nat := ⟨(· * · )⟩

/--
error: Provided instance
  { mul := fun x y => y * x }
is not defeq to inferred instance
  instMulNat

Use `set_option trace.Elab.fast_instance true` to analyze the error.

Trace of fields visited: []
---
info: { mul := fun x y => y * x } : Mul Nat
-/
#guard_msgs in
#check fast_instance% { mul := fun x y => y * x : Mul Nat }


/-!
Checking handling of non-structure classes.
-/

class Dec (p : Prop) where
  [dec : Decidable p]

axiom It : Prop

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
abbrev dec1 : Decidable It := isTrue sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
def dec2 : Decidable It := isTrue sorry

/-- info: @Dec.mk It (@isTrue It dec1._proof_1) : Dec It -/
#guard_msgs in
set_option pp.explicit true in
#check fast_instance% { dec := dec1 : Dec It }

/--
error: Provided instance does not reduce to a constructor application
  dec2
Reduces to an application of testing.dec2.

This instance is not a structure and not canonical. Use a separate 'instance' command to define it.

Use `set_option trace.Elab.fast_instance true` to analyze the error.

Trace of fields visited: [testing.Dec.dec]
---
info: @Dec.mk It dec2 : Dec It
-/
#guard_msgs in
set_option pp.explicit true in
#check fast_instance% { dec := dec2 : Dec It }
