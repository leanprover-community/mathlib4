import Mathlib

-- Test the annotation of `natCast_pow_eq_zero_of_le`
example (p m : Nat): n ≤ m → (p ^ m : ZMod (p ^ n)) = 0 := by aesop
