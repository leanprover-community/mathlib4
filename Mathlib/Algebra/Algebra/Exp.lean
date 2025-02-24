import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Sigma.Basic
import LeanCopilot





namespace Algebra

variable (R : Type*) [Field R]
variable (A : Type*)


section Semi

variable [Semiring A] [Algebra R A]


theorem reorder (N : ℕ) {f : ℕ → ℕ → A} : ∑ j ∈ Finset.range (2 * N + 1), ∑ i ∈ Finset.range (j + 1), f i j = ∑ ij ∈ (Finset.range (2 * N + 1)).product (Finset.range (2 * N + 1)) |>.filter (fun ij => ij.1 ≤ ij.2), f ij.1 ij.2 := by
  rw [Finset.sum_sigma']
  apply Finset.sum_bij
    (fun ⟨j, i⟩ _ => (i, j))
  simp
  intro h1
  intro h2
  intro h3
  constructor
  constructor
  · exact Nat.lt_of_lt_of_le h3 h2
  · exact h2
  · exact Nat.le_of_lt_succ h3
  simp
  intro h4
  intro h5
  intro h6
  intro h7
  intro h8
  intro h9
  intro h10
  intro h11
  · refine Sigma.ext h11 ?_
    exact heq_of_eq h10
  simp
  intro h1
  intro h2
  intro h3
  intro h4
  intro h5
  use h2, h1
  constructor
  constructor
  exact h4
  exact Nat.lt_add_one_of_le h5
  exact Prod.mk.inj_iff.mp rfl
  simp

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

theorem ttttt (n : ℕ) : (n.factorial : R)⁻¹  * (n.factorial : R) = 1 := by
  have h1 : (n.factorial : R) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp_all only [ne_eq, Nat.cast_eq_zero, not_false_eq_true, inv_mul_cancel₀]


theorem exp_add_of_commute (a b : A) (h₁ : Commute a b) (h₂ : IsNilpotent a) (h₃ : IsNilpotent b) :
    exp R A (a + b) = exp R A a * exp R A b := by
  obtain ⟨n₁, hn₁⟩ := h₂
  obtain ⟨n₂, hn₂⟩ := h₃
  let N :=  n₁ ⊔ n₂
  have huh₁ : n₁ ≤ N + 1 := by
    refine Nat.le_add_right_of_le ?_
    simp_all only [le_sup_left, N]
  have huh₂ : n₂ ≤ N + 1 := by
    refine Nat.le_add_right_of_le ?_
    simp_all only [le_sup_right, N]
  have h₃ : a ^ (N + 1) = 0 := zero_ev A hn₁ huh₁
  have h₄ : b ^ (N + 1) = 0 := zero_ev A hn₂ huh₂
  have help : (N + 1) + (N + 1) <= (2 * N + 1) + 1 := by
    calc (N + 1) + (N + 1) = 2 * (N + 1) := by rw [← Nat.two_mul (N + 1)]
    _ = 2 * N + 2 := by rw [Nat.mul_add_one]
    _ = (2 * N + 1) + 1 := by rw [Nat.add_assoc]
    _ ≤ (2 * N + 1) + 1 := by exact le_refl (2 * N + 2)
  have h₅ : (a + b) ^ (2 * N + 1) = 0 :=
    Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero h₁ h₃ h₄ help
  rw [← exp_eq_truncated R A (a + b) h₅, ← exp_eq_truncated R A a h₃, ← exp_eq_truncated R A b h₄]

 -- have  hh (n : ℕ) (a : A) : n * a = (n : R) • a := by
  --  norm_cast
  --  simp_all only [nsmul_eq_mul, N]

  have e₁ :=
    calc
      ∑ n ∈ Finset.range (2 * N + 1), (n.factorial : R)⁻¹ • (a + b) ^ n = ∑ n ∈ Finset.range (2 * N + 1), (n.factorial : R)⁻¹ • (a + b) ^ n := rfl
      _ = ∑ n ∈ Finset.range (2 * N + 1), (n.factorial : R)⁻¹ • (a + b) ^ n := rfl
      _ = ∑ n ∈ Finset.range (2 * N + 1), (n.factorial : R)⁻¹ • (∑ m ∈ Finset.range (n + 1), a ^ m * b ^ (n - m) * n.choose m) := by
        apply Finset.sum_congr rfl
        intros n hn
        rw [Commute.add_pow h₁ n]
      _ = ∑ n ∈ Finset.range (2 * N + 1), (∑ m ∈ Finset.range (n + 1), (n.factorial : R)⁻¹ • (a ^ m * b ^ (n - m) * n.choose m)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.smul_sum]
      _ = ∑ n ∈ Finset.range (2 * N + 1), (∑ m ∈ Finset.range (n + 1), ((m.factorial : R)⁻¹ * ((n - m).factorial : R)⁻¹) • (a ^ m * b ^ (n - m))) := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro m hm
        have hhh0 : a ^ m * b ^ (n - m) * (n.choose m) = (n.choose m) * (a ^ m * b ^ (n - m)) := by
          rw [Nat.cast_commute (n.choose m)]

        have  hh (n : ℕ) (a : A) : n * a = (n : R) • a := by
          norm_cast
          simp
        have hhh : (n.factorial : R)⁻¹ • (a ^ m * b ^ (n - m) * (n.choose m)) = ((n.factorial : R)⁻¹ * (n.choose m)) • (a ^ m * b ^ (n - m)) := by
          rw [hhh0]
          rw [hh (n.choose m)]
          rw [← smul_assoc]
          norm_cast
        rw [hhh]
        suffices h11 : (n.factorial : R)⁻¹ * (n.choose m) = ((m.factorial : R)⁻¹ * ((n - m).factorial : R)⁻¹) by
          simp_all only [Finset.mem_range, N]
        have t : m ≤ n := by
          simp_all only [Finset.mem_range, N]
          omega
        rw [Nat.choose_eq_factorial_div_factorial t]
        rw [Nat.cast_div]
        rw [mul_div]
        have qqq := ttttt R n
        rw [qqq]
        simp
        rw [mul_comm]
        apply Nat.factorial_mul_factorial_dvd_factorial
        apply t
        rw [Nat.cast_mul]
        apply mul_ne_zero
        have h1 : (m.factorial : R) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
        apply h1
        have h2 : ((n - m).factorial : R) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - m)
        apply h2
      _ = ∑ ij ∈ (Finset.range (2 * N + 1)).product (Finset.range (2 * N + 1)) |>.filter (fun ij => ij.1 ≤ ij.2), ((ij.1.factorial : R)⁻¹ * ((ij.2 - ij.1).factorial : R)⁻¹) • (a ^ ij.1 * b ^ (ij.2 - ij.1)) := by rw [reorder]
      _ = ∑ ij ∈ (Finset.range (2 * N + 1)).product (Finset.range (2 * N + 1)) |>.filter (fun ij => ij.1 + ij.2 <= 2 * N), ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
        apply Finset.sum_bij
          (fun ⟨i, j⟩ _ => (i, j - i))
        simp
        intro h1 h2 h3 h4 h5
        constructor
        constructor
        apply h3
        exact tsub_lt_of_lt h4
        rw [Nat.add_sub_of_le h5]
        exact Nat.le_of_lt_succ h4
        simp
        intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
        constructor
        apply h11
        rw [h11] at h12
        omega
        simp
        intro h1 h2 h3 h4 h5
        use h1, h1 + h2
        constructor
        constructor
        constructor
        apply h3
        exact Nat.lt_add_one_of_le h5
        exact Nat.le_add_right h1 h2
        constructor
        rfl
        omega
        simp
  have e2 :=
    calc
      (∑ n ∈ Finset.range (N + 1), (n.factorial : R)⁻¹ • a ^ n) * ∑ n ∈ Finset.range (N + 1), (n.factorial : R)⁻¹ • b ^ n = (∑ n ∈ Finset.range (N + 1), (n.factorial : R)⁻¹ • a ^ n) * ∑ n ∈ Finset.range (N + 1), (n.factorial : R)⁻¹ • b ^ n := by rfl
      _ = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), (i.factorial : R)⁻¹ • a ^ i * (j.factorial : R)⁻¹ • b ^ j := by rw [Finset.sum_mul_sum]
      _ = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ((i.factorial : R)⁻¹ * (j.factorial : R)⁻¹) • (a ^ i * b ^ j) := by
       apply Finset.sum_congr rfl
       intro n hn
       apply Finset.sum_congr rfl
       intro m hm
       rw [smul_mul_assoc]
       have ppp : a ^ n * (m.factorial : R)⁻¹ • b ^ m = (m.factorial : R)⁻¹ • (a ^ n *  b ^ m) := by
         simp_all only [Finset.product_eq_sprod, Finset.mem_range, Algebra.mul_smul_comm, N]
       rw [ppp]
       rw [smul_smul]
      _ = ∑ ij ∈ (Finset.range (N + 1)).product (Finset.range (N + 1)), ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
        rw [Finset.sum_sigma']
        apply Finset.sum_bij
          (fun ⟨i, j⟩ _ => (i, j))
        simp
        simp
        intro h1 h2 h3 h4 h5 h6 h7 h8
        refine Sigma.ext h7 ?_
        exact heq_of_eq h8
        simp
        intro h1 h2 h3 h4
        constructor
        apply h3
        apply h4
        simp

  have e4 : ∑ ij ∈ (Finset.range (2 * N + 1)).product (Finset.range (2 * N + 1)), ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) =
    ∑ ij ∈ ((Finset.range (2 * N + 1)).product (Finset.range (2 * N + 1))) with ij.1 + ij.2 ≤ 2 * N, ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) +
    ∑ ij ∈ ((Finset.range (2 * N + 1)).product (Finset.range (2 * N + 1))) with ¬ ij.1 + ij.2 ≤ 2 * N, ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
      rw [Finset.sum_filter_add_sum_filter_not]

  have e5 : ∑ ij ∈ ((Finset.range (2 * N + 1)).product (Finset.range (2 * N + 1))) with ¬ ij.1 + ij.2 ≤ 2 * N, ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp at hi
    obtain ⟨hi1, hi2⟩ := hi
    have help : N + 1 ≤ i.1 ∨ N + 1 ≤ i.2 := by
      by_contra h
      simp at h
      obtain ⟨hi11, hi21⟩ := h
      linarith
    cases help with
    | inl h1 =>
      have qqq : a ^ (i.1) = 0 := zero_ev A h₃ h1
      rw [qqq]
      simp
    | inr h1 =>
      have qqq : b ^ (i.2) = 0 := zero_ev A h₄ h1
      rw [qqq]
      simp
  rw [e5] at e4
  simp at e4
  simp at e₁
  rw [← e4] at e₁
  simp at e2
  have e5 : ∑ ij ∈ (Finset.range (2 * N + 1)).product (Finset.range (2 * N + 1)), ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) =
    ∑ ij ∈ ((Finset.range (2 * N + 1)).product (Finset.range (2 * N + 1))) with ij.1 ≤ N ∧ ij.2 ≤ N, ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) +
    ∑ ij ∈ ((Finset.range (2 * N + 1)).product (Finset.range (2 * N + 1))) with ¬ (ij.1 ≤ N ∧ ij.2 ≤ N), ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
      rw [Finset.sum_filter_add_sum_filter_not]

  have e6 : ∑ ij ∈ ((Finset.range (2 * N + 1)).product (Finset.range (2 * N + 1))) with ¬ (ij.1 ≤ N ∧ ij.2 ≤ N), ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    push_neg at hi
    simp at hi
    obtain ⟨aa, ba⟩ := hi
    have rrr : N + 1 ≤ i.1 ∨ N + 1 ≤ i.2 := by
      by_contra hh
      push_neg at hh
      have h₁1 : i.1 < N + 1 := hh.1
      have h₂1 : i.2 < N + 1 := hh.2
      have h₃1 : i.1 ≤ N := by
        exact Nat.le_of_lt_succ h₁1
      have ttt := ba h₃1
      linarith
    cases rrr with
    | inl h1 =>
      have qqq : a ^ (i.1) = 0 := zero_ev A h₃ h1
      rw [qqq]
      simp
    | inr h1 =>
      have qqq : b ^ (i.2) = 0 := zero_ev A h₄ h1
      rw [qqq]
      simp
  rw [e6] at e5
  simp at e5
  have lll: ∑ ij ∈ (Finset.range (2 * N + 1)).product (Finset.range (2 * N + 1)) with ij.1 ≤ N ∧ ij.2 ≤ N, ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) = ∑ ij ∈ (Finset.range (N + 1)).product (Finset.range (N + 1)), ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
    let aaaaa := ((Finset.range (2 * N + 1)).product (Finset.range (2 * N + 1))).filter (fun ij => ij.1 ≤ N ∧ ij.2 ≤ N)
    let bbbbb := (Finset.range (N + 1)).product (Finset.range (N + 1))
    have key : aaaaa = bbbbb := by
      dsimp [aaaaa, bbbbb]
      ext x
      constructor
      intro hhh
      simp at hhh
      obtain ⟨hhh1, hhh2⟩ := hhh
      obtain ⟨hhh1a, hhh1b⟩ := hhh1
      obtain ⟨hhh2a, hhh2b⟩ := hhh2
      simp
      constructor
      exact Nat.lt_add_one_of_le hhh2a
      exact Nat.lt_add_one_of_le hhh2b
      intro hhh
      simp at hhh
      obtain ⟨hhh1, hhh2⟩ := hhh
      simp
      constructor
      constructor
      linarith [hhh1]
      linarith [hhh2]
      constructor
      exact Nat.le_of_lt_succ hhh1
      exact Nat.le_of_lt_succ hhh2


    apply Finset.sum_congr
    simp at key
    simp
    apply key
    intro x hx
    rfl
    --congr
    --ext ⟨i, j⟩
    --simp
    --intro hi
    --have rrr : N + 1 ≤ i ∨ N + 1 ≤ j := by
    --  by_contra hh
    --  push_neg at hh
    --  have h₁1 : i < N + 1 := hh.1
    --  have h₂1 : j < N + 1 := hh.2
    --  have h₃1 : i ≤ N := by
    --    exact Nat.le_of_lt_succ h₁1
    --  have ttt := hi h₃1
    --  linarith
    --cases rrr with
    --| inl h1 =>
    --  have qqq : a ^ (i) = 0 := zero_ev A h₃ h1
    --  rw [qqq]
    --  simp
    --| inr h1 =>
    --  have qqq : b ^ (j) = 0 := zero_ev A h₄ h1
    --  rw [qqq]
    --  simp
  rw [e5] at e₁
  simp at lll
  rw [lll] at e₁
  rw [e2.symm] at e₁
  apply e₁



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
