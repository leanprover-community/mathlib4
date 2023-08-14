import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.ZMod.Quotient

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
      rw [← sub_div, ← mul_sub, div_eq_iff, mul_assoc (2*π), mul_right_inj', Nat.cast_add,
        Int.cast_neg, Int.cast_one, neg_mul, one_mul, ← neg_eq_iff_eq_neg, neg_sub, Fin.add_def]
      dsimp
      rw [sub_eq_iff_eq_add]
      norm_cast
      rw [Nat.mod_eq, if_pos, Nat.mod_eq, if_neg, ← Nat.add_sub_assoc, Nat.add_sub_cancel_left]
      exact h
      simp only [not_and, not_le]
      intro _
      apply Nat.sub_lt_left_of_lt_add h (Nat.add_lt_add (Fin.is_lt _) (Fin.is_lt _))
      exact ⟨ Nat.pos_of_ne_zero (NeZero.ne _), h⟩
      exact two_pi_pos.ne'
      exact NeZero.ne _
    · push_neg at h
      use 0
      rw [← sub_div, ← mul_sub, div_eq_iff (NeZero.ne _), mul_assoc (2*π),
        mul_right_inj' two_pi_pos.ne', sub_eq_iff_eq_add, Int.cast_zero, zero_mul,
        Nat.cast_add, zero_add, Fin.add_def]
      dsimp
      rw [Nat.mod_eq_of_lt h, Nat.cast_add]
