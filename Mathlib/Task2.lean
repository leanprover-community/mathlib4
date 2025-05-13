import Mathlib

open Real Finset

lemma Pigeonhole {A : Type*} {s : Finset A} (hs : s.Nonempty) (x : A → ℝ) :
    ∃ j ∈ s, x j * s.card ≥ (∑ i ∈ s, x i) := by
  by_contra! nh
  have : ∑ j ∈ s, (x j * s.card) < ∑ j ∈ s, (∑ i ∈ s, x i) := sum_lt_sum_of_nonempty hs nh
  rw [sum_const, nsmul_eq_mul, mul_comm, sum_mul] at this
  simp only [lt_self_iff_false] at this

-- Since the sum $S_2^{+}$contains at most $n-1$ terms (the numbers cannot all be greater than 0 )
theorem sublemma {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hsum : ∑ i : Fin n, x i = 0) (hsumsq : ∑ i : Fin n, (x i) ^ 2 = 1) :
    ({i | x i ≥ 0} : Finset (Fin n)).card ≤ n - 1 := by
  by_contra! nh
  have : ({i | x i ≥ 0} : Finset (Fin n)) = (⊤ : Finset (Fin n)) := by
    refine (eq_of_subset_of_card_le (filter_subset (fun i ↦ x i ≥ 0) univ) ?_)
    rw [top_eq_univ, Finset.card_univ, Fintype.card_fin]
    omega
  have le : ∀ i, x i ≥ 0 := fun i ↦ by
    have : i ∈ ({i | x i ≥ 0} : Finset (Fin n)) := by simp [this]
    simpa
  have : ∀ i, (x i) ^ 2 = 0 := by simp [(Fintype.sum_eq_zero_iff_of_nonneg le).mp hsum]
  linarith [Fintype.sum_eq_zero (fun a ↦ x a ^ 2) this]


theorem sublemma2 {n : ℕ} (x : Fin n → ℝ)
    (hsum : ∑ i : Fin n, x i = 0) (hsumsq : ∑ i : Fin n, (x i) ^ 2 = 1) :
    ({i | x i ≥ 0} : Finset (Fin n)).Nonempty := by
  by_contra! nh
  simp at nh
  have le : ∀ i, x i ≤ 0 := fun i ↦ by
    have : i ∉ ({i | 0 ≤ x i} : Finset (Fin n)) := by simp [nh]
    simp at this
    exact le_of_lt this
  have : ∀ i, (x i) ^ 2 = 0 := by simp [(Fintype.sum_eq_zero_iff_of_nonpos le).mp hsum]
  linarith [Fintype.sum_eq_zero (fun a ↦ x a ^ 2) this]

theorem sublemma3 (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hsum : ∑ i : Fin n, x i = 0) (hsumsq : ∑ i : Fin n, (x i)^2 = 1) :
     1 ≤ n * ∑ i with 0 ≤ x i, x i ^ 2 := by
  --We denote by $\mathrm{N}^{+}$the number of indices $i$ such that $x_i>0$ and by $\mathrm{N}^{-}$
  --We also denote:
  --$$
  --S_1^{+}=\sum_{i \text { such that } x_i>0} x_i \quad \text { and } \quad S_1^{-}=\sum_{i \text {
  --such that } x_i \leqslant 0}\left(-x_i\right)
  --$$
  have : 1 - (∑ i with x i ≥ 0, (x i) ^ 2) ≤ (n - 1 : ℕ) * (∑ i with x i ≥ 0, (x i) ^ 2) := by calc
    _ = (∑ i with x i < 0, (- x i) ^ 2) := by
      simp [← hsumsq, ←(sum_filter_add_sum_filter_not univ (fun k ↦ x k ≥ 0) fun k ↦ x k ^ 2)]
    _ ≤ (∑ i with x i < 0, (- x i)) ^ 2 := sum_sq_le_sq_sum_of_nonneg fun i hi ↦ by
      simp only [mem_filter, mem_univ, true_and] at hi
      simp [le_of_lt hi]
    _ = (∑ i with x i ≥ 0, x i) ^ 2 := by
      have : ∑ i with x i ≥ 0 , x i + ∑ i with ¬ x i ≥ 0, x i = 0 := by
        rw [sum_filter_add_sum_filter_not univ (fun k ↦ x k ≥ 0) x, hsum]
      --the number of indices $i$ such that $x_i \leqslant 0$, such that $\mathrm{N}^{+}+
      --\mathrm{N}^{-}=\mathrm{n}$.
      have : ∑ i with x i ≥ 0 , x i = - ∑ i with x i < 0, x i := by
        simpa only [eq_neg_iff_add_eq_zero, ge_iff_le, not_le] using this
      simp [this]
    -- The purpose of these quantities is that they allow both to reformulate the assumptions and to
    -- use well-known inequalities such as the Cauchy-Schwarz inequality.
    _ ≤ ({i | x i ≥ 0} : Finset (Fin n)).card * (∑ i with x i ≥ 0, (x i) ^ 2)  := by
      have : (∑ i with x i ≥ 0, x i) ^ (2 : ℝ) ≤ ({i | x i ≥ 0} : Finset (Fin n)).card ^
          ((2 : ℝ) - 1) * ∑ i with x i ≥ 0, x i ^ (2 : ℝ) :=
        have le : (1 : ℝ) ≤ 2 := by norm_num
        have pos : ∀ i ∈ ({i | x i ≥ 0} : Finset (Fin n)), 0 ≤ x i := fun i hi ↦ by simpa using hi
        rpow_sum_le_const_mul_sum_rpow_of_nonneg (f := x) {i | x i ≥ 0} le pos
      have eq : (2 : ℝ) - 1 = 1 := by norm_num
      simpa [eq] using this
    --$$
    --1-S_2^{+}=S_2^{-} \leqslant\left(S_1^{-}\right)^2=\left(S_1^{+}\right)^2 \leqslant N^{+}
    --S_2^{+} \leqslant(n-1) S_2^{+}
    --$$
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (sublemma hn x hsum hsumsq))
      (Finset.sum_nonneg fun i a ↦ sq_nonneg (x i))
  have eq: (n - 1 : ℕ) * ∑ i with x i ≥ 0, x i ^ 2 + ∑ i with x i ≥ 0, x i ^ 2
      = n * ∑ i with x i ≥ 0, x i ^ 2 := by
    set s := ∑ i with x i ≥ 0, x i ^ 2
    simp [Nat.cast_pred (Nat.zero_lt_of_lt hn), this, sub_one_mul (↑n) s]
  ----To bring out the square root in the result, we will use $S_2^{+}$. More specifically, we will
  -- show that $S_2^{+} \geqslant \frac{1}{n}$.
  simpa [tsub_le_iff_right, eq] using this

/- Let $n \geqslant 2$ and let $k, x_2, \ldots, x_n$ be real numbers such that $x_1+x_2+\cdots+x_n
=0$ and $x_1^2+x_2^2+$ $\cdots+x_n^2=1$. Show that there exists an index $i$ such that $x_i \ge
 \frac{1}{\sqrt{n(n-1)}}$. -/
theorem inequalities_607194 (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hsum : ∑ i : Fin n, x i = 0) (hsumsq : ∑ i : Fin n, (x i)^2 = 1) :
    ∃ i : Fin n, x i ≥ 1 / sqrt (n * (n - 1)) := by
  -- , one of these terms is greater than $\frac{1}{n(n-1)}$, meaning that $x_i^2 \geqslant
  -- \frac{1}{\sqrt{n(n-1)}}$ for some $i$ with $x_i>0$, which allows us to conclude.
  obtain ⟨j, ⟨jin, hj⟩⟩ := Pigeonhole (sublemma2 x hsum hsumsq) (fun k ↦ x k ^ 2)
  have le1 : 1 ≤ n * ∑ i with 0 ≤ x i, x i ^ 2 := sublemma3 n hn x hsum hsumsq
  use j
  have : x j ^ 2 * (n - 1) ≥ 1 / n := by calc
    _ ≥ x j ^ 2 * ({i | x i ≥ 0} : Finset (Fin n)).card := by
      refine mul_le_mul_of_nonneg (Preorder.le_refl (x j ^ 2)) ?_ (sq_nonneg (x j)) ?_
      have eq1 : (({i | x i ≥ 0} :Finset (Fin n)).card : ℝ) ≤ ((n - 1 : ℕ) : ℝ) :=
        Nat.cast_le.mpr (sublemma hn x hsum hsumsq)
      rwa [Nat.cast_pred (Nat.zero_lt_of_lt hn)] at eq1
      simp [Nat.one_le_of_lt hn]
    _ ≥ ∑ i ∈ {i | x i ≥ 0}, x i ^ 2 := hj
    _ ≥ _ := by
      refine (div_le_iff₀' ?_).mpr le1
      simp [Nat.zero_lt_of_lt hn]
  have hc : (n - 1 : ℝ) > 0 := by simp; linarith
  have := (div_le_iff₀ (b := (1 : ℝ) / (n : ℝ)) (a :=  x j ^ 2) hc).mpr this
  rw [div_div] at this
  set t := ((n : ℝ) * (n - (1 : ℝ)))
  have eq : 1 / √t = √(1 / t) := by simp only [one_div, sqrt_inv]
  rw [eq]
  refine (sqrt_le_iff (x := 1/t) (y := x j)).mpr ⟨by simpa using jin, this⟩
