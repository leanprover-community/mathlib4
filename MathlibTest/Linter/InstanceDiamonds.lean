module

public import Mathlib.Init

@[expose] public section

class A (α : Type) where
  x : α

instance instAInt₁ : A Int where
  x := 2

-- The linter operates in the public scope, so it doesn't unfold `unexposedTwo`.
@[no_expose] def unexposedTwo : Int := 2

instance instAInt₂ : A Int where
  x := unexposedTwo

instance instANat₁ : A Nat where
  x := 3

def exposedThree : Nat := 3

instance instANat₂ : A Nat where
  x := exposedThree

class B (α : Type) where
  x : α → α

def MyNat := Nat
-- These instances form a diamond because the binder types are different.
instance instBMyNat₁ : B MyNat := ⟨fun n : MyNat ↦ n.succ⟩
instance instBMyNat₂ : B MyNat := ⟨fun n : Nat ↦ n.succ⟩


class Group (α : Type*) extends Mul α, One α

def GroupWrapper (α : Type*) := α

instance {α} [Group α] : Group (GroupWrapper α) := inferInstanceAs <| Group α
-- Oops, we accidentally wrote the `One` and `Mul` instances after the `Group` instance.
-- Luckily, this is caught by the linter!
instance {α} [Mul α] : Mul (GroupWrapper α) := inferInstanceAs <| Mul α
instance {α} [One α] : One (GroupWrapper α) := inferInstanceAs <| One α

-- Declaring `MulBar` before `MulFoo` here affects the synthesis order,
-- so also behviour of the linter.
class MulBar (α : Type) extends Mul α
class MulFoo (α : Type) extends Mul α
class MulFooBar (α : Type) extends MulFoo α, MulBar α

instance : MulFoo MyNat where
  mul a b := a.mul b

def mul' := Nat.mul

instance : MulBar MyNat where
  mul a b := mul' a b

instance : MulFooBar MyNat where

def MulWrapper (α : Type*) := α

instance {α} [MulFoo α] : MulFoo (MulWrapper α) := inferInstanceAs <| MulFoo α
instance {α} [MulBar α] : MulBar (MulWrapper α) := inferInstanceAs <| MulBar α
instance {α} [MulFooBar α] : MulFooBar (MulWrapper α) := inferInstanceAs <| MulFooBar α

-- There is an instance diamond here but this is an edge case that is not caught by the linter.
example {α} [MulFooBar α] :
    (instMulFooBarMulWrapper.toMul : Mul (MulWrapper α)) = instMulBarMulWrapper.toMul := by
  fail_if_success with_implicit rfl
  rfl

/--
error: /- The `instanceDiamonds` linter reports:
FOUND BAD INSTANCE DIAMONDS
This linter can be disabled with `@[nolint instanceDiamonds]`. -/
#check instANat₁ /- This equality does not hold at implicit transparency:
`(instANat₁ : A Nat) = instANat₂` -/
#check instANat₂ /- This equality does not hold at implicit transparency:
`(instANat₂ : A Nat) = instANat₁` -/
#check instBMyNat₁ /- This equality does not hold at implicit transparency:
`(instBMyNat₁ : B MyNat) = instBMyNat₂` -/
#check instBMyNat₂ /- This equality does not hold at implicit transparency:
`(instBMyNat₂ : B MyNat) = instBMyNat₁` -/
#check @instGroupGroupWrapper /- This equality does not hold at implicit transparency:
`(instGroupGroupWrapper.toMul : Mul (GroupWrapper α)) = instMulGroupWrapper`
Similarly for [instGroupGroupWrapper.toOne] -/
#check instMulBarMyNat /- This equality does not hold at implicit transparency:
`(instMulBarMyNat.toMul : Mul MyNat) = instMulFooMyNat.toMul` -/
-/
#guard_msgs in
#lint- only instanceDiamonds
