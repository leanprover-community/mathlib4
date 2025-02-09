import Mathlib.Tactic.OmegaExtensions

example (a b : ENat) (h : a = b) : a - b = b - a := by
  -- let a : ℤ := 42
  -- -- unhygienic
  -- cases_first_ENat
  enat_omega

example (a b : ENat) (h : a ≤ b) : a - b < b + 1 := by
  enat_omega

example (a b : ENat) (h : a ≤ b) : a - 2 * b ≤ b + 1 := by
  enat_omega

example (a b c : ENat) (hab : a ≥ b) (hbc : b ≥ c) : a ≥ c := by
  enat_omega

example (a b : ENat) (h : a = b) : a - b = b - a := by
  -- let a : ℤ := 42
  enat_omega

example (a b : PNat) (h : a < b) : 1 < b := by
  pnat_omega

example (a b : PNat) (h : a = b) : b = a := by
  pnat_omega

example (a b : PNat) (h : a = b) : b = a := by
  let a : ℤ := 42
  pnat_omega
