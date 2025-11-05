import Mathlib

theorem EuclideanDomain.ediv_pow {R : Type*} [EuclideanDomain R] {a b : R} {n : ℕ} (hab : b ∣ a) :
    (a / b) ^ n = a ^ n / b ^ n := by
  obtain ⟨c, rfl⟩ := hab
  obtain rfl | hb := eq_or_ne b 0
  · obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
  · simp [hb, mul_pow]

#find_home EuclideanDomain.ediv_pow
