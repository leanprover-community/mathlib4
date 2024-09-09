import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Tactic.NoncommRing

local infix:70 " ⚬ " => fun a b => a * b + b * a

variable {R : Type _} [Ring R]
variable (a b c : R)

example : 0 = 0 := by noncomm_ring
example : a = a := by noncomm_ring

example : (a + b) * c = a * c + b * c := by noncomm_ring
example : a * (b + c) = a * b + a * c := by noncomm_ring
example : a - b = a + -b := by noncomm_ring
example : a * b * c = a * (b * c) := by noncomm_ring
example : a + a = 2 * a := by noncomm_ring

example : a + a = a * 2 := by noncomm_ring
example : -a - a = a * (-2) := by noncomm_ring
example : -a = (-1) * a := by noncomm_ring
example : a + a + a = 3 * a := by noncomm_ring
example : a ^ 2 = a * a := by noncomm_ring
example : a ^ 3 = a * a * a := by noncomm_ring
example : (-a) * b = -(a * b) := by noncomm_ring
example : a * (-b) = -(a * b) := by noncomm_ring
example : a * (b + c + b + c - 2*b) = 2*a*c := by noncomm_ring
example : a * (b + c + b + c - (2 : ℕ) • b) = 2*a*c := by noncomm_ring
example : (a + b)^2 = a^2 + a*b + b*a + b^2 := by noncomm_ring
example : (a - b)^2 = a^2 - a*b - b*a + b^2 := by noncomm_ring
example : (a + b)^3 = a^3 + a^2*b + a*b*a + a*b^2 + b*a^2 + b*a*b + b^2*a + b^3 := by noncomm_ring
example : (a - b)^3 = a^3 - a^2*b - a*b*a + a*b^2 - b*a^2 + b*a*b + b^2*a - b^3 := by noncomm_ring

example : ⁅a, a⁆ = 0 := by simp only [Ring.lie_def]; noncomm_ring
example : ⁅a, b⁆ = -⁅b, a⁆ := by simp only [Ring.lie_def]; noncomm_ring
example : ⁅a + b, c⁆ = ⁅a, c⁆ + ⁅b, c⁆ := by simp only [Ring.lie_def]; noncomm_ring
example : ⁅a, b + c⁆ = ⁅a, b⁆ + ⁅a, c⁆ := by simp only [Ring.lie_def]; noncomm_ring
example : ⁅a, ⁅b, c⁆⁆ + ⁅b, ⁅c, a⁆⁆ + ⁅c, ⁅a, b⁆⁆ = 0 := by simp only [Ring.lie_def]; noncomm_ring
example : ⁅⁅a, b⁆, c⁆ + ⁅⁅b, c⁆, a⁆ + ⁅⁅c, a⁆, b⁆ = 0 := by simp only [Ring.lie_def]; noncomm_ring
example : ⁅a, ⁅b, c⁆⁆ = ⁅⁅a, b⁆, c⁆ + ⁅b, ⁅a, c⁆⁆ := by simp only [Ring.lie_def]; noncomm_ring
example : ⁅⁅a, b⁆, c⁆ = ⁅⁅a, c⁆, b⁆ + ⁅a, ⁅b, c⁆⁆ := by simp only [Ring.lie_def]; noncomm_ring
example : ⁅a * b, c⁆ = a * ⁅b, c⁆ + ⁅a, c⁆ * b := by simp only [Ring.lie_def]; noncomm_ring
example : ⁅a, b * c⁆ = ⁅a, b⁆ * c + b * ⁅a, c⁆ := by simp only [Ring.lie_def]; noncomm_ring
example : ⁅3 * a, a⁆ = 0 := by simp only [Ring.lie_def]; noncomm_ring
example : ⁅a * -5, a⁆ = 0 := by simp only [Ring.lie_def]; noncomm_ring
example : ⁅a^3, a⁆ = 0 := by simp only [Ring.lie_def]; noncomm_ring

example : a ⚬ a = 2*a^2 := by noncomm_ring
example : (2 * a) ⚬ a = 4*a^2 := by noncomm_ring
example : a ⚬ b = b ⚬ a := by noncomm_ring
example : a ⚬ (b + c) = a ⚬ b + a ⚬ c := by noncomm_ring
example : (a + b) ⚬ c = a ⚬ c + b ⚬ c := by noncomm_ring
example : (a ⚬ b) ⚬ (a ⚬ a) = a ⚬ (b ⚬ (a ⚬ a)) := by noncomm_ring

example : ⁅a, b ⚬ c⁆ = ⁅a, b⁆ ⚬ c + b ⚬ ⁅a, c⁆ := by simp only [Ring.lie_def]; noncomm_ring
example : ⁅a ⚬ b, c⁆ = a ⚬ ⁅b, c⁆ + ⁅a, c⁆ ⚬ b := by simp only [Ring.lie_def]; noncomm_ring
example : (a ⚬ b) ⚬ c - a ⚬ (b ⚬ c) = -⁅⁅a, b⁆, c⁆ + ⁅a, ⁅b, c⁆⁆ := by
  simp only [Ring.lie_def]; noncomm_ring

example : a + -b = -b + a := by
  -- This should print "`noncomm_ring` simp lemmas don't apply; try `abel` instead"
  -- but I don't know how to test for this:
  -- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.60fail.60.20that.20doesn't.20print.20the.20goal.3F/near/382280010
  fail_if_success noncomm_ring
  abel
example : a ^ 50 * a ^ 37 = a ^ 23 * a ^ 64 := by noncomm_ring

/- some examples using arguments -/
example (h : ∀ a : R, (2 : ℤ) • a = 0) : (a + 1) ^ 2 = a ^ 2 + 1 := by
  noncomm_ring [h]
example (h : a = b) (h2 : a = c) : a = c := by
  fail_if_success noncomm_ring [h]
  noncomm_ring [h2]
