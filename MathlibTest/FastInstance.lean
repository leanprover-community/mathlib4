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
info: @[instance_reducible] def testing.instSemigroup.{u_1} : {α : Type u_1} → [Semigroup α] → Semigroup (Wrapped α) :=
fun {α} [inst : Semigroup α] => @Semigroup.mk (Wrapped α) (@instMulWrapped α (@Semigroup.toMul α inst)) ⋯
-/
#guard_msgs in
set_option pp.explicit true in
#print instSemigroup
/--
info: @[instance_reducible] def testing.instCommSemigroup.{u_1} : {α : Type u_1} →
  [CommSemigroup α] → CommSemigroup (Wrapped α) :=
fun {α} [inst : CommSemigroup α] =>
  @CommSemigroup.mk (Wrapped α) (@instSemigroup α (@CommSemigroup.toSemigroup α inst)) ⋯
-/
#guard_msgs in
set_option pp.explicit true in
#print instCommSemigroup


/-!
Non-defeq error
-/
instance : Mul Nat := ⟨(· * ·)⟩

/--
warning: An instance of `Mul Nat` already exists.
Please use `inferInstance` instead of `fast_instance%`

Note: This linter can be disabled with `set_option linter.fast_instance_existing false`
---
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

/-- warning: declaration uses `sorry` -/
#guard_msgs in
abbrev dec1 : Decidable It := isTrue sorry

/-- warning: declaration uses `sorry` -/
#guard_msgs in
def dec2 : Decidable It := isTrue sorry

/-- info: @Dec.mk It (@isTrue It _check._proof_1) : Dec It -/
#guard_msgs (info, drop warning) in
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

/-! The provided instance does not reduce to a constructor application but it is defeq to what
`inferInstance` would synthesize, so we allow it. -/
/--
info: let this := dec2;
@Dec.mk It this : Dec It
-/
#guard_msgs in
set_option pp.explicit true in
#check let := dec2; fast_instance% { dec := dec2 : Dec It }

class DecEq (α : Type*) where
  [decEq : DecidableEq α]

def UnitAlias : Type :=
  Unit

/-! The root is an instance family. -/
example : DecidableEq UnitAlias :=
  fast_instance% fun _ _ ↦ isTrue rfl

/-! The root is an instance family, and the instances do not reduce to a constructor application. -/
/--
error: Provided instance does not reduce to a constructor application
  decidable_of_iff (() = ()) ⋯
Reduces to an application of decidable_of_iff.

This instance is not a structure and not canonical. Use a separate 'instance' command to define it.

Use `set_option trace.Elab.fast_instance true` to analyze the error.

Trace of fields visited: []
-/
#guard_msgs in
example : DecidableEq UnitAlias :=
  fast_instance% fun _ _ ↦ decidable_of_iff (() = ()) .rfl

/-! The root is an instance family, and the instances do not reduce to a constructor application,
but are equal defeq to what `inferInstance` would synthesize, so we allow it with a warning. -/
/--
warning: An instance of `Decidable (a = b)` already exists.
Please use `inferInstance` instead of `fast_instance%`

Note: This linter can be disabled with `set_option linter.fast_instance_existing false`
-/
#guard_msgs in
example : DecidableEq UnitAlias :=
  let (a b : UnitAlias) : Decidable (a = b) := isTrue rfl
  fast_instance% fun _ _ ↦ inferInstance

/-! A nested instance field contains an instance family. -/
example : DecEq UnitAlias :=
  fast_instance% { decEq := fun _ _ ↦ isTrue rfl }

/-! A nested instance field contains an instance family, and the instances do not reduce to a
constructor application. -/
/--
error: Provided instance does not reduce to a constructor application
  sorry
Reduces to an application of sorryAx.

This instance is not a structure and not canonical. Use a separate 'instance' command to define it.

Use `set_option trace.Elab.fast_instance true` to analyze the error.

Trace of fields visited: [testing.DecEq.decEq]
-/
#guard_msgs in
example : DecEq α :=
  fast_instance% { decEq := fun a b ↦ sorry }

/- A nested instance field contains an instance family, and the instances do not reduce to a
constructor application, it is defeq to what `inferInstance` would synthesize so we allow it. -/
#guard_msgs (drop warning) in
example : DecEq α :=
  let : DecidableEq α := fun a b ↦ sorry
  fast_instance% { decEq := this : DecEq α }

/-! The root is not a class. -/
/--
error: Can only be used for classes, but type is
  Unit

Use `set_option trace.Elab.fast_instance true` to analyze the error.

Trace of fields visited: []
-/
#guard_msgs in
example : Unit := fast_instance% ()

class UnitClass where
  [unit : Unit]

/-! A nested instance field is not a class. -/
/--
error: Can only be used for classes, but type is
  Unit

Use `set_option trace.Elab.fast_instance true` to analyze the error.

Trace of fields visited: [testing.UnitClass.unit]
-/
#guard_msgs in
example : UnitClass := fast_instance% { unit := () }

/-! The root is a family but not of classes. -/
/--
error: Can only be used for classes, but type is
  Unit

Use `set_option trace.Elab.fast_instance true` to analyze the error.

Trace of fields visited: []
-/
#guard_msgs in
example : Unit → Unit := fast_instance% fun _ ↦ ()

class Func where
  [func : Unit → Unit]

/-! A nested instance field is a family but not of classes. -/
/--
error: Can only be used for classes, but type is
  Unit

Use `set_option trace.Elab.fast_instance true` to analyze the error.

Trace of fields visited: [testing.Func.func]
-/
#guard_msgs in
example : Func := fast_instance% { func := fun _ ↦ () }

/-!
Checking that proof fields whose types already match at instances transparency
are used directly, without wrapping in an auxiliary theorem.
-/

class Pointed (α : Type) where
  val : α
  h : True

abbrev myPointed : Pointed Nat := ⟨0, trivial⟩

/-- info: { val := 0, h := _check._proof_1 } : Pointed Nat -/
#guard_msgs in
#check fast_instance% (myPointed : Pointed Nat)
