module

public import Mathlib.Init

@[expose] public section

class A (α : Type) where
  x : α

instance instAInt₁ : A Int where
  x := 2

-- The linter operates in the public scope, do it doesn't unfold `unexposedTwo`.
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

instance {α} [Mul α] : Mul (GroupWrapper α) := inferInstanceAs <| Mul α
instance {α} [Group α] : Group (GroupWrapper α) := inferInstanceAs <| Group α
-- Oops, we accidentally wrote the `One` instance after the `Group` instance.
-- Luckily, this is caught by the linter!
instance {α} [One α] : One (GroupWrapper α) := inferInstanceAs <| One α


/--
error: -- Found 5 errors in 24 declarations (plus 26 automatically generated ones) in the current file with 1 linters

/- The `instanceDiamonds` linter reports:
FOUND BAD INSTANCE DIAMONDS
This linter can be disabled with `@[nolint instanceDiamonds]`. -/
#check instANat₁ /- The instance
  instANat₁ : A Nat
is not definitionally equal (at implicit transparency) to
  instANat₂ -/
#check instANat₂ /- The instance
  instANat₂ : A Nat
is not definitionally equal (at implicit transparency) to
  instANat₁ -/
#check instBMyNat₁ /- The instance
  instBMyNat₁ : B MyNat
is not definitionally equal (at implicit transparency) to
  instBMyNat₂ -/
#check instBMyNat₂ /- The instance
  instBMyNat₂ : B MyNat
is not definitionally equal (at implicit transparency) to
  instBMyNat₁ -/
#check @instGroupGroupWrapper /- The instance
  instGroupGroupWrapper.toOne : One (GroupWrapper α)
is not definitionally equal (at implicit transparency) to
  instOneGroupWrapper -/
-/
#guard_msgs in
#lint only instanceDiamonds
