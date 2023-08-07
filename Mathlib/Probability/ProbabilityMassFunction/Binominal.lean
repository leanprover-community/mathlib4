import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Nat.Choose.Multinomial


noncomputable section

namespace Pmf.Binominal

def mf_binom (p : ENNReal) (n : ℕ) (i : Fin (n+1)) : ENNReal :=
  p^(i : ℕ) * (1-p)^(n - (i : ℕ)) * (n.choose i : ℕ)

@[simp]
lemma mf_binom_0 p n : mf_binom p n 0 = (1-p)^n := by simp [mf_binom]

@[simp]
lemma mf_binom_n p n : mf_binom p n n = p^n := by simp [mf_binom, Nat.mod_eq_of_lt]

lemma sum_mf_binom (p n) (h : p ≤ 1) : Finset.sum .univ (mf_binom p n) = 1 := by calc
  _ = Finset.sum (Finset.range (n + 1)) fun m ↦ p ^ m * (1 - p) ^ (n - m) * ↑(Nat.choose n m) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp at hi
    rw [dif_pos hi]
    rfl
  _ = (p + (1-p))^n := (add_pow _ _ _).symm
  _ = 1 := by simp [h]

end Pmf.Binominal

open Pmf.Binominal

namespace Pmf

def binominal (p : ENNReal) (h : p ≤ 1) (n : ℕ) : Pmf (Fin (n + 1)) :=
  .ofFintype (mf_binom p n) (sum_mf_binom p n h)

-- Not a simp, so that this gets unrolled only intenitionally

theorem binominal_apply : binominal p h n i =
  p^(i : ℕ) * (1-p)^(n - (i : ℕ)) * (n.choose i : ℕ) := rfl

@[simp]
theorem binominal_apply_0 : binominal p h n 0 = (1-p)^n := mf_binom_0 p n

@[simp]
theorem binominal_apply_n : binominal p h n n = p^n := mf_binom_n p n

#find (Fin 1 → Bool)

theorem binominal_one_eq_bernoulli :
  binominal p h 1 = (bernoulli p h).map (cond · 1 0) := by
    ext ⟨i, hi⟩
    match i with
    | 0 => simp [tsum_bool, binominal_apply]
    | 1 => simp [tsum_bool, binominal_apply]
    | .succ (.succ i) => linarith
