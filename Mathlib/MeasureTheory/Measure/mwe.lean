import Mathlib

variable {α : Type*} {ε : ENNReal}

open scoped ENNReal

lemma aux : ∑' (a : ℕ), (1 : ℝ≥0∞) / (2 ^ (a + 1)) = 1 := by
  simp only [one_div, pow_add, pow_one]
  calc ∑' i, ((2 : ℝ≥0∞) ^ i * 2)⁻¹
  _ = ∑' i, (2⁻¹ ^ i) * 2⁻¹ := by
        congr with i
        rw [ENNReal.mul_inv (by simp) (by simp), ENNReal.inv_pow]
  _ = (∑' i, 2⁻¹ ^ i) * 2⁻¹ := by rw [ENNReal.tsum_mul_right]
  _ = (1 - 2⁻¹)⁻¹ * 2⁻¹ := by rw [ENNReal.tsum_geometric]
  _ = 1 := by simp [ENNReal.one_sub_inv_two, inv_inv, ENNReal.mul_inv_cancel]

lemma aux2 : ∑' (a : ℕ), ε / (2 ^ (a + 1)) = ε := by
  simp only [div_eq_mul_inv, pow_add, pow_one]
  calc ∑' i, ε * ((2 : ℝ≥0∞) ^ i * 2)⁻¹
  _ = ∑' i, ε * (2⁻¹ ^ i) * 2⁻¹ := by
        congr with i
        rw [ENNReal.mul_inv (by simp) (by simp), ENNReal.inv_pow, mul_assoc]
  _ = (∑' i, ε * 2⁻¹ ^ i) * 2⁻¹ := by rw [ENNReal.tsum_mul_right]
  _ = ε * (∑' i, 2⁻¹ ^ i) * 2⁻¹ := by rw [ENNReal.tsum_mul_left]
  _ = ε * (1 - 2⁻¹)⁻¹ * 2⁻¹ := by rw [ENNReal.tsum_geometric]
  _ = ε := by
    simp only [ENNReal.one_sub_inv_two, inv_inv, mul_assoc]
    rw [ENNReal.mul_inv_cancel two_ne_zero ENNReal.two_ne_top]
    simp

theorem ENNReal.tsum_geometric_add_one (r : ℝ≥0∞) : ∑' n : ℕ, r ^ (n + 1) = r * (1 - r)⁻¹ := by
  calc ∑' n : ℕ, r ^ (n + 1)
  _ = ∑' n : ℕ, r * r ^ (n) := by
        congr with n
        exact pow_succ' r n
  _ = r * ∑' n : ℕ, r ^ n := by rw [ENNReal.tsum_mul_left]
  _ = r * (1 - r)⁻¹ := by rw [ENNReal.tsum_geometric r]

theorem ENNReal.tsum_geometric_add_one_mul_const (r : ℝ≥0∞) : ∑' n : ℕ, ε * r ^ (n + 1) = ε * r * (1 - r)⁻¹ := by
  calc ∑' n : ℕ, ε * r ^ (n + 1)
  _ = ε * ∑' n : ℕ, r ^ (n + 1) := by rw [ENNReal.tsum_mul_left]
  _ = ε * r * (1 - r)⁻¹ := by rw [mul_assoc, ENNReal.tsum_geometric_add_one r]
