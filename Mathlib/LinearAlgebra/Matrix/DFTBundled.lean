import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

open BigOperators Real Complex

-- /-- The DFT operation defined via a Sum -/
-- noncomputable def dft (v : (Fin n) → ℂ) : (Fin n) → ℂ :=
-- fun k : Fin n =>  ∑ p : (Fin n),  (Complex.exp (2 * π * I * k * p / n)) * (v p)

-- noncomputable def dft (n : ℕ) (v : (Fin n) → ℂ) : (Fin n) → ℂ :=

-- def z (n : ℕ) := fun (k p: Fin n) => fourier
variable (n : ℕ) (k : Fin n)

noncomputable def Fin.toRealAngle [NeZero n] : Fin n →+ Real.Angle where
  toFun := fun k => (((2*π*(k:ℝ))/(n:ℝ)) : Angle)
  map_zero' := by simp
  map_add' := by
    intro x y ;
    dsimp
    rw [← Real.Angle.coe_add, ← add_div, ← mul_add, ← Nat.cast_add,
      Real.Angle.angle_eq_iff_two_pi_dvd_sub]
    by_cases h : n ≤ (x:ℕ) + (y:ℕ)
    · use -1
      rw [← sub_div, ← mul_sub, div_eq_iff, mul_assoc (2*π), mul_right_inj']
      norm_cast
      simp only [Int.negSucc_mul_ofNat, Nat.one_mul]
      rw [← neg_eq_iff_eq_neg,  Int.subNatNat_eq_coe, neg_sub, Fin.add_def]
      dsimp
      rw [Nat.cast_add, sub_eq_iff_eq_add]
      norm_cast
      rw [Nat.mod_eq, if_pos, Nat.mod_eq, if_neg, ← Nat.add_sub_assoc, Nat.add_sub_cancel_left]
      exact h
      simp only [not_and, not_le]
      intro _
      apply Nat.sub_lt_left_of_lt_add _
      apply Nat.add_lt_add (Fin.is_lt _) (Fin.is_lt _)
      exact h
      refine ⟨ Nat.pos_of_ne_zero ?_, h⟩
      apply NeZero.ne
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, pi_ne_zero]
      apply NeZero.ne
    · push_neg at h
      use 0
      rw [← sub_div, ← mul_sub, div_eq_iff, mul_assoc (2*π), mul_right_inj']
      rw [sub_eq_iff_eq_add]
      simp only [Int.cast_zero, zero_mul, Nat.cast_add, zero_add]
      rw [Fin.add_def]
      dsimp
      rw [Nat.mod_eq_of_lt h]
      norm_cast
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, pi_ne_zero]
      apply NeZero.ne





















-- #check Fin.toRealAngle

-- #check (AddCircle (2 : ℝ))

-- #check (@fourier (n : ℝ) 0) k
