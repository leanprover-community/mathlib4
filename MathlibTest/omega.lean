import Mathlib.Tactic.OmegaExtensions

section ENat

example (a b : ENat) (h : a = b) : a - b = b - a := by
  enat_to_nat
  omega

example (a b : ENat) (h : a ≤ b) : a - b < b + 1 := by
  enat_to_nat
  omega

example (a b : ENat) (h : a ≤ b) : a - 2 * b ≤ b + 1 := by
  enat_to_nat
  omega

example (a b c : ENat) (hab : a ≥ b) (hbc : b ≥ c) : a ≥ c := by
  enat_to_nat
  omega

example (a b : ENat) (h : a = b) : a - b = b - a := by
  -- to test if the tactic works with inaccessible names
  let a : ℤ := 42
  let b : ℤ := 32
  enat_to_nat
  omega

end ENat

section PNat

example (a b : PNat) (h : a < b) : 1 < b := by
  pnat_to_nat
  omega

example (a b : PNat) (h : a = b) : b = a := by
  pnat_to_nat
  omega

example (a b : PNat) (h : a = b) : b = a := by
  -- to test if the tactic works with inaccessible names
  let a : ℤ := 42
  pnat_to_nat
  omega

end PNat
