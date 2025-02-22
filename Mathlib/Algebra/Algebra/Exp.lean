import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.Nilpotent.Basic
import LeanCopilot

namespace Algebra

variable (R : Type*) [Field R]
variable (A : Type*)


section Semi

variable [Semiring A] [Algebra R A]

noncomputable def exp (a : A) : A :=
  ∑ n ∈ Finset.range (nilpotencyClass a), (n.factorial : R)⁻¹ • (a ^ n)

theorem exp_eq_truncated {k : ℕ} (a : A) (h : a ^ k = 0) :
    ∑ n ∈ Finset.range k, (Nat.factorial n : R)⁻¹ • (a ^ n) = exp R A a := by
  have h₁ : nilpotencyClass a ≤ k := by
    exact csInf_le' h
  have h₂ : ∑ n ∈ Finset.range k, (Nat.factorial n : R)⁻¹ • (a ^ n) =
      ∑ n ∈ Finset.range (nilpotencyClass a), (Nat.factorial n : R)⁻¹ • (a ^ n) +
        ∑ n ∈ Finset.Ico (nilpotencyClass a) k, (Nat.factorial n : R)⁻¹ • (a ^ n) :=
    (Finset.sum_range_add_sum_Ico _ h₁).symm
  suffices h₃ : ∑ n ∈ Finset.Ico (nilpotencyClass a) k, (Nat.factorial n : R)⁻¹ • (a ^ n) = 0 by
    dsimp [exp]
    rw [h₂, h₃, add_zero]
  suffices h₅ : ∀ n ∈ Finset.Ico (nilpotencyClass a) k, (Nat.factorial n : R)⁻¹ • (a ^ n) = 0 by
    apply Finset.sum_eq_zero h₅
  intro t _
  have h₆ : nilpotencyClass a ≤ t := by
    simp_all only [Finset.mem_Ico]
  suffices h₆ : a ^ t = 0 by
    simp_all only [Finset.mem_Ico, true_and, smul_zero]
  have h₈ : IsNilpotent a := by
    use k
  have h₉ := pow_nilpotencyClass h₈
  have h10 : t = nilpotencyClass a + (t - nilpotencyClass a) := by
    simp_all only [Finset.mem_Ico, true_and, add_tsub_cancel_of_le]
  rw [h10]
  rw [pow_add]
  rw [h₉]
  exact zero_mul (a ^ (t - nilpotencyClass a))

theorem exp_zero_eq_one : exp R A 0 = 1 := by
  have h : (0 : A) ^ 1 = 0 := by
    exact pow_one 0
  have h1 := exp_eq_truncated R A (0 : A) h
  simp at h1
  apply h1.symm


theorem zero_ev {k l : ℕ} {a : A} (h₁ : a ^ k = 0) (h₂ : k ≤ l) : a ^ l = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h₂
  rw [pow_add, h₁, zero_mul]

--example (n : ℕ) (a : A) : (n.factorial : R) • ((n.factorial : R)⁻¹ • a) = a := by
--have h1 : (n.factorial : R) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
--simp_all only [ne_eq, Nat.cast_eq_zero, not_false_eq_true, smul_inv_smul₀]
  --exact mul_inv_cancel₀ h1

-- useful: add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero
-- useful: add_pow (h : Commute x y) (n : ℕ) : ...
-- useful: isNilpotent_add (h_comm : Commute x y) ...

variable [CharZero R]
theorem exp_add_of_commute (a b : A) (h₁ : Commute a b) (h₂ : IsNilpotent a) (h₃ : IsNilpotent b) :
    exp R A (a + b) = exp R A a * exp R A b := by
  have h : a * b = b * a := h₁
  sorry



end Semi

section Full

variable [CharZero R]
variable [Ring A] [Algebra R A]

theorem exp_of_nilpotent_is_unit (a : A) (h : IsNilpotent a) : IsUnit (exp R A a) := by
  have h₀ : a + (-a) = 0 := by
    exact add_neg_cancel a
  have h0 : (-a) + a = 0 := by
    exact neg_add_cancel a
  have h₁ : Commute a (-a) := by
    simp_all only [Commute.neg_right_iff, Commute.refl]
  have h1 : Commute (-a) a := by
    simp_all only [add_neg_cancel, Commute.neg_right_iff, Commute.refl, Commute.neg_left_iff]
  have h₃ : IsNilpotent (-a) := IsNilpotent.neg h
  have h₄ := exp_add_of_commute R A a (-a) h₁ h h₃
  rw [h₀] at h₄
  rw [exp_zero_eq_one R A] at h₄
  dsimp [IsUnit]
  apply isUnit_iff_exists.2
  use exp R A (-a)
  constructor
  · apply h₄.symm
  have h₅ := exp_add_of_commute R A (-a) a h1 h₃ h
  rw [h0] at h₅
  rw [exp_zero_eq_one R A] at h₅
  apply h₅.symm


end Full

end Algebra
