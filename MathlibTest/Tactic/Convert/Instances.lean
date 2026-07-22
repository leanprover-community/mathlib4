import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
import Mathlib.Tactic.Convert

private axiom test_sorry : ∀ {α}, α

/-! `convert` should not pop up goals about instances. -/
example {a b c : ℕ} (hab : instLTNat.lt a b) : Nat.instLinearOrder.toLT.lt a c := by
  convert (preTransparency := .reducible) hab
  · guard_target =ₛ Nat.instLinearOrder.toLT = instLTNat
    exact test_sorry
  · guard_target =ₛ c = b
    exact test_sorry

#guard_msgs in
example {a b c : ℕ} (hab : instLTNat.lt a b) : Nat.instLinearOrder.toLT.lt a c := by
  convert (preTransparency := .instances) hab
  guard_target =ₛ c = b
  exact test_sorry

example (q z : Nat) : semigroupDvd.dvd q z := by
  convert_to (preTransparency := .reducible) q ^ 1 ∣ z
  · guard_target =ₛ semigroupDvd = Nat.instDvd
    exact test_sorry
  · guard_target =ₛ q = q ^ 1
    exact test_sorry
  · guard_target =ₛ q ^ 1 ∣ z
    exact test_sorry

example (q z : Nat) : semigroupDvd.dvd q z := by
  convert_to (preTransparency := .instances) q ^ 1 ∣ z
  · guard_target =ₛ q = q ^ 1
    exact test_sorry
  · guard_target =ₛ q ^ 1 ∣ z
    exact test_sorry
