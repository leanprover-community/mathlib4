module

public import Mathlib.Data.Nat.Bits

@[expose] public section

def Nat.popcountTR (n : Nat) : Nat :=
  n.binaryRec (·) (fun b _ f x ↦ f (x + b.toNat)) 0

/-- info: 1 -/
#guard_msgs in
#eval Nat.popcountTR (2 ^ 20240)
