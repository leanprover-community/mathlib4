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


/--
error: -- Found 5 errors in 24 declarations (plus 27 automatically generated ones) in the current file with 1 linters

/- The `instanceDiamonds` linter reports:
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
-/
#guard_msgs in
#lint only instanceDiamonds
