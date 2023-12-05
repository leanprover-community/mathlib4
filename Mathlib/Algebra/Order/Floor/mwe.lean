import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Factorization.Basic

namespace Nat
variable {a b n : ℕ}

noncomputable def ceilingRoot (n a : ℕ) : ℕ := (a.factorization ⌈/⌉ n).prod (· ^ ·)

@[simp] lemma ceilingRoot_zero_left (a : ℕ) : ceilingRoot 0 a = 1 := by simp [ceilingRoot]
@[simp] lemma ceilingRoot_zero_right (n : ℕ) : ceilingRoot n 0 = 1 := by simp [ceilingRoot]
@[simp] lemma ceilingRoot_one_left (ha : a ≠ 0) : ceilingRoot 1 a = a := by simp [ceilingRoot, ha]
@[simp] lemma ceilingRoot_one_right (n : ℕ) : ceilingRoot n 1 = 1 := by simp [ceilingRoot]

@[simp] lemma ceilingRoot_pow_self (hn : n ≠ 0) (a : ℕ) :
    ceilingRoot n (a ^ n) = a := by simp [ceilingRoot, pos_iff_ne_zero.2 hn]

lemma pow_dvd_iff : a ^ n ∣ b ↔ factorization

end Nat
