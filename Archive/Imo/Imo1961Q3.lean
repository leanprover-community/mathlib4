import Mathlib

open Real

namespace Real

theorem cos_even_int_mul_pi {k : ℤ} (hk : Even k) : cos (k * π) = 1 := by
  rcases hk with ⟨k, rfl⟩
  convert cos_int_mul_two_pi k using 2
  push_cast
  ring

theorem cos_odd_int_mul_pi {k : ℤ} (hk : Odd k) : cos (k * π) = -1 := by
  rcases hk with ⟨k, rfl⟩
  simpa [add_mul] using cos_even_int_mul_pi (even_two_mul k)

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
    · rw [hsinx, zero_pow' _ h₀, sub_zero, pow_eq_one_iff_of_ne_zero h₀, cos_eq_one_iff,
        cos_eq_neg_one_iff] at h
      rcases h with ⟨k, rfl⟩ | ⟨⟨k, rfl⟩, hn⟩
      · cases n.even_or_odd with
        | inl hn => refine .inl ⟨⟨k * 2, ?_⟩, hn⟩; simp [mul_assoc]
        | inr hn => exact .inr <| .inl ⟨⟨_, rfl⟩, hn⟩
      · exact .inl ⟨⟨2 * k + 1, by push_cast; ring⟩, hn⟩
    · rcases eq_or_ne (cos x) 0 with hcosx | hcosx
      · right; right
        rw [hcosx, zero_pow' _ h₀, zero_sub, ← neg_inj, neg_neg, pow_eq_neg_one_iff,
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
