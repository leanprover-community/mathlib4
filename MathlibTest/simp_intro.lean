import Mathlib.Tactic.SimpIntro

set_option autoImplicit true

example : x + 0 = y → x = y := by simp_intro h₁
example : x + 0 ≠ y → x ≠ y := by simp_intro h₁ h₂ -- h₂ is bound but not needed
example : x + 0 ≠ y → x ≠ y := by simp_intro h₁ h₂ h₃ -- h₃ is not bound

example (h : x = z) : x + 0 = y → x = z := by simp_intro [h]

example (h : y = z) : x + 0 = y → x = z := by
  simp_intro
  guard_target = x = y → x = z
  simp_intro .. [h]

example (h : y = z) : x + 0 = y → x = z := by simp_intro _; exact h

example : ∀ (r : Nat → Prop), (∀ x, x > 0 → r x) → ∀ y z, y = 0 → z > y → r z := by
  simp_intro ..

example : ∀ (r : Nat → Prop), (∀ x, x > 0 → r x) → ∀ y z, y = 0 → z > y → r z := by
  simp_intro r hr y z hy hz
