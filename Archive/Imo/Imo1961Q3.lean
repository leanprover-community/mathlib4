import Mathlib

@[simp]
theorem neg_one_pow_eq_one_iff {R : Type*} [Ring R] [CharZero R] [NoZeroDivisors R] {n : ℕ} :
    (-1 : R) ^ n = 1 ↔ Even n := by
  cases n.even_xor_odd <;> simp [*]

@[simp]
theorem neg_one_pow_eq_neg_one_iff {R : Type*} [Ring R] [CharZero R] [NoZeroDivisors R] {n : ℕ} :
    (-1 : R) ^ n = -1 ↔ Odd n := by
  cases n.even_xor_odd <;> simp [*]

open Real

namespace Real

theorem pow_eq_one {x : ℝ} {n : ℕ} (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 ∨ x = -1 ∧ Even n := by
  constructor
  · intro h
    have hx : |x| = 1 := by simp [← pow_eq_one_iff_of_nonneg (abs_nonneg x) hn, ← abs_pow, h]
    refine (eq_or_eq_neg_of_abs_eq hx).imp_right fun hx' ↦ ⟨hx', ?_⟩
    simpa [hx'] using h
  · rintro (rfl | ⟨rfl, hn'⟩) <;> simp [*]

theorem pow_eq_neg_one {x : ℝ} {n : ℕ} : x ^ n = -1 ↔ x = -1 ∧ Odd n := by
  rcases eq_or_ne n 0 with rfl | hn; · simp
  constructor
  · intro h
    have hx : |x| = 1 := by simp [← pow_eq_one_iff_of_nonneg (abs_nonneg x) hn, ← abs_pow, h]
    rcases eq_or_eq_neg_of_abs_eq hx with rfl | rfl <;> simp_all
  · rintro ⟨rfl, hn⟩
    rwa [neg_one_pow_eq_neg_one_iff]

theorem cos_eq_neg_one_iff {x : ℝ} : cos x = -1 ↔ ∃ k : ℤ, (2 * k + 1) * π = x := by
  rw [← neg_eq_iff_eq_neg, ← cos_sub_pi, cos_eq_one_iff]
  simp [eq_sub_iff_add_eq, add_mul, mul_assoc, mul_left_comm]

theorem cos_even_int_mul_pi {k : ℤ} (hk : Even k) : cos (k * π) = 1 := by
  rcases hk with ⟨k, rfl⟩
  convert cos_int_mul_two_pi k using 2
  push_cast
  ring

theorem cos_odd_int_mul_pi {k : ℤ} (hk : Odd k) : cos (k * π) = -1 := by
  rcases hk with ⟨k, rfl⟩
  simpa [add_mul] using cos_even_int_mul_pi (even_two_mul k)

theorem sin_eq_one_iff {x : ℝ} : sin x = 1 ↔ ∃ k : ℤ, π / 2 + k * (2 * π) = x := by
  simp_rw [← cos_sub_pi_div_two, cos_eq_one_iff, eq_sub_iff_add_eq']

theorem sin_eq_neg_one_iff {x : ℝ} : sin x = -1 ↔ ∃ k : ℤ, -(π / 2) + k * (2 * π) = x := by
  rw [← neg_eq_iff_eq_neg, ← sin_neg, sin_eq_one_iff, neg_surjective.exists]
  simp only [← neg_eq_iff_eq_neg]
  simp [add_comm]

@[simp]
theorem abs_cos_int_mul_pi (k : ℤ) : |cos (k * π)| = 1 := by
  cases k.even_or_odd with
  | inl hk => simp [cos_even_int_mul_pi hk]
  | inr hk => simp [cos_odd_int_mul_pi hk, abs]

theorem cos_int_mul_pi_pow_even (k : ℤ) {n : ℕ} (hn : Even n) : (cos (k * π)) ^ n = 1 := by
  rw [← hn.pow_abs, abs_cos_int_mul_pi, one_pow]

theorem Imo1961Q3 {n : ℕ} {x : ℝ} (h₀ : n ≠ 0) :
    (cos x) ^ n - (sin x) ^ n = 1 ↔
      (∃ k : ℤ, x = k * π) ∧ Even n ∨ (∃ k : ℤ, x = k * (2 * π)) ∧ Odd n ∨
        (∃ k : ℤ, x =  -(π / 2) + k * (2 * π)) ∧ Odd n := by
  constructor
  · intro h
    rcases eq_or_ne (sin x) 0 with hsinx | hsinx
    · rw [hsinx, zero_pow' _ h₀, sub_zero, pow_eq_one h₀, cos_eq_one_iff, cos_eq_neg_one_iff] at h
      rcases h with ⟨k, rfl⟩ | ⟨⟨k, rfl⟩, hn⟩
      · cases n.even_or_odd with
        | inl hn => refine .inl ⟨⟨k * 2, ?_⟩, hn⟩; simp [mul_assoc]
        | inr hn => exact .inr <| .inl ⟨⟨_, rfl⟩, hn⟩
      · exact .inl ⟨⟨2 * k + 1, mod_cast rfl⟩, hn⟩
    · rcases eq_or_ne (cos x) 0 with hcosx | hcosx
      · right; right
        rw [hcosx, zero_pow' _ h₀, zero_sub, ← neg_inj, neg_neg, pow_eq_neg_one,
          sin_eq_neg_one_iff] at h
        simpa only [eq_comm] using h
      · have hcos1 : |cos x| < 1 := by
          rw [abs_cos_eq_sqrt_one_sub_sin_sq, sqrt_lt' one_pos]
          simp [sq_pos_of_ne_zero _ hsinx]
        have hsin1 : |sin x| < 1 := by
          rw [abs_sin_eq_sqrt_one_sub_cos_sq, sqrt_lt' one_pos]
          simp [sq_pos_of_ne_zero _ hcosx]
        match n with
        | 1 =>
          rw [pow_one, pow_one, sub_eq_iff_eq_add] at h
          have : 2 * sin x * cos x = 0 := by
            simpa [h, add_sq, add_assoc, ← two_mul, mul_add, mul_assoc, ← sq]
              using cos_sq_add_sin_sq x
          simp [hsinx, hcosx] at this
        | 2 =>
          rw [← cos_sq_add_sin_sq x, sub_eq_add_neg, add_right_inj, neg_eq_self_iff] at h
          exact absurd (pow_eq_zero h) hsinx
        | (n + 1 + 2) =>
          set m := n + 1
          refine absurd ?_ h.not_lt
          calc
            (cos x) ^ (m + 2) - (sin x) ^ (m + 2) ≤ |cos x| ^ (m + 2) + |sin x| ^ (m + 2) := by
              simp only [← abs_pow, sub_eq_add_neg]
              gcongr
              exacts [le_abs_self _, neg_le_abs _]
            _ = |cos x| ^ m * cos x ^ 2 + |sin x| ^ m * sin x ^ 2 := by simp [pow_add]
            _ < 1 ^ m * cos x ^ 2 + 1 ^ m * sin x ^ 2 := by gcongr
            _ = 1 := by simp
  · rintro (⟨⟨k, rfl⟩, hn⟩ | ⟨⟨k, rfl⟩, -⟩ | ⟨⟨k, rfl⟩, hn⟩)
    · rw [sin_int_mul_pi, zero_pow' _ h₀, sub_zero, cos_int_mul_pi_pow_even _ hn]
    · have : sin (k * (2 * π)) = 0 := by simpa [mul_assoc] using sin_int_mul_pi (k * 2)
      simp [h₀, this]
    · simp [hn.neg_pow, h₀]
