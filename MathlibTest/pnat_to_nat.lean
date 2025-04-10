import Mathlib.Tactic.PNatToNat

example (a b : PNat) (h : a < b) : 1 < b := by
  pnat_to_nat
  omega

example (a b : PNat) (h : a = b) : b = a := by
  -- to test if the tactic works with inaccessible names
  let a : ℤ := 42
  pnat_to_nat
  omega

example (a b : PNat) (h : a < b) : 1 < b := by
  have := a.pos
  pnat_to_nat
  omega
