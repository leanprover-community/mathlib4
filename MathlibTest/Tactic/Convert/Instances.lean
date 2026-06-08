import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
import Mathlib.Tactic.Convert

/-! `convert` should not pop up goals about instances. -/

/--
error: unsolved goals
case e'_2
a b c : ℕ
hab : a < b
⊢ Nat.instLinearOrder.toLT = instLTNat

case e'_4
a b c : ℕ
hab : a < b
⊢ c = b
-/
#guard_msgs in
example {a b c : ℕ} (hab : instLTNat.lt a b) : Nat.instLinearOrder.toLT.lt a c := by
  convert (preTransparency := .reducible) hab

/--
error: unsolved goals
case e'_4
a b c : ℕ
hab : a < b
⊢ c = b
-/
#guard_msgs in
example {a b c : ℕ} (hab : instLTNat.lt a b) : Nat.instLinearOrder.toLT.lt a c := by
  convert (preTransparency := .instances) hab

/--
error: unsolved goals
case e'_2
q z : ℕ
⊢ semigroupDvd = Nat.instDvd

case e'_3
q z : ℕ
⊢ q = q ^ 1

q z : ℕ
⊢ q ^ 1 ∣ z
-/
#guard_msgs in
example (q z : Nat) : semigroupDvd.dvd q z := by
  convert_to (preTransparency := .reducible) q ^ 1 ∣ z

/--
error: unsolved goals
case e'_3
q z : ℕ
⊢ q = q ^ 1

q z : ℕ
⊢ q ^ 1 ∣ z
-/
#guard_msgs in
example (q z : Nat) : semigroupDvd.dvd q z := by
  convert_to (preTransparency := .instances) q ^ 1 ∣ z
