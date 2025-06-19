import Mathlib.Algebra.Ring.GrindInstances
import Mathlib

example {a b : ℤ}
    (h₀ : a = 0 ↔ b = 0)
    (h₁ : a * b ∈ ({0, 1, 2, 3, 4} : Set ℤ)) :
    (a, b) ∈ ({
        (0, 0),
        (1, 1), (-1, -1),
        (1, 2), (2, 1), (-1, -2), (-2, -1),
        (1, 3), (3, 1), (-1, -3), (-3, -1),
        (4, 1), (1, 4), (-4, -1), (-1, -4), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) := by
  generalize hn : a * b = n
  rw [hn] at h₁
  obtain rfl|hn₀ := eq_or_ne n 0
  · obtain rfl : a = 0 := by simpa [h₀] using hn
    obtain rfl : b = 0 := by simp at h₀; exact h₀
    decide +kernel
  have han : a.natAbs ≤ n.natAbs := Nat.le_of_dvd (by omega) (by subst n; simp)
  obtain rfl : b = n / a := by
    obtain rfl|ha := eq_or_ne a 0
    · subst n; simp_all
    · exact (Int.ediv_eq_of_eq_mul_right ha hn.symm).symm
  lift n to ℕ using (by sorry)
  simp only [Int.natAbs_natCast] at han
  generalize ha' : a.natAbs = a'
  rw [ha'] at han
  rw [a.natAbs_eq_iff] at ha'
  have hn4 : n ≤ 4 := by simp at h₁; omega
  interval_cases n
  all_goals
    interval_cases a' <;> rcases ha' with rfl|rfl <;> decide

example (a b z : ℤ) (hz : z ≠ 0) :
    a * b = z ∧ z ≠ 0 ↔
      ∃ a', (-|z| ≤ a' ∧ a' < 0 ∨ 0 < a' ∧ a' ≤ |z|) ∧ a' * (z / a') = z ∧ a' = a ∧ z / a' = b := by
  refine ⟨?_, ?_⟩
  · rintro ⟨rfl, h⟩
    have ha : a ≠ 0 := left_ne_zero_of_mul h
    replace hb : 1 ≤ |b| := Int.one_le_abs <| right_ne_zero_of_mul h
    refine ⟨a, ⟨?_, by rw [mul_div_cancel_left₀ _ ha], rfl, by rw [mul_div_cancel_left₀ _ ha]⟩⟩
    rcases a.eq_nat_or_neg with ⟨n, hn | hn⟩ <;> simp_all only [hn]
    · rw [abs_mul, Nat.abs_cast]
      exact Or.inr ⟨by omega, by nlinarith⟩
    · rw [neg_mul, abs_neg, neg_le_neg_iff, abs_mul, Nat.abs_cast]
      exact Or.inl ⟨by nlinarith, by omega⟩
  · rintro ⟨a, ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩, h₂, rfl, h₃⟩ <;> rw [← h₃] <;> grind

example (R : Type*) [CommRing R] [CharZero R] [NoZeroDivisors R] (x y z : R)
    (hij : x = 2 * y ∨ x = 3 * y ∨ y = 2 * x ∨ y = 3 * x)
    (hik : x = 2 * z ∨ x = 3 * z ∨ z = 2 * x ∨ z = 3 * x)
    (hjk : y = 2 * z ∨ y = 3 * z ∨ z = 2 * y ∨ z = 3 * y) :
    z = y := by
  sorry

#min_imports
