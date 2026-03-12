import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace Kolmogorov

section Deterministic

variable {Ω α : Type*} [AddCommGroup α]

/-- The `n`-th partial sum of a sequence. -/
def partialSum (X : ℕ → Ω → α) (n : ℕ) : Ω → α :=
  fun ω => ∑ i ∈ Finset.range n, X i ω

@[simp] lemma partialSum_apply (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) :
    partialSum X n ω = ∑ i ∈ Finset.range n, X i ω := rfl

@[simp] lemma partialSum_zero (X : ℕ → Ω → α) :
    partialSum X 0 = 0 := by
  ext ω
  simp [partialSum]

lemma partialSum_succ (X : ℕ → Ω → α) (n : ℕ) :
    partialSum X (n + 1) = fun ω => partialSum X n ω + X n ω := by
  ext ω
  simp [partialSum, Finset.sum_range_succ]

/-- Reindex a tail sum as the difference of two initial partial sums. -/
lemma sum_range_shift_eq_sub (f : ℕ → α) (m n : ℕ) :
    (∑ i ∈ Finset.range n, f (m + i)) =
      ((∑ i ∈ Finset.range (m + n), f i) - ∑ i ∈ Finset.range m, f i) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hsum : (∑ i ∈ Finset.range (m + (n + 1)), f i) =
          (∑ i ∈ Finset.range (m + n), f i) + f (m + n) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (Finset.sum_range_succ (f := fun i => f i) (n := m + n))
      rw [hsum]
      simp [sub_eq_add_neg, add_assoc, add_comm]

/-- The tail block `f (m + 1), ..., f (m + n)` is a difference of partial sums. -/
lemma sum_range_shift_succ_eq_sub (f : ℕ → α) (m n : ℕ) :
    (∑ i ∈ Finset.range n, f (m + 1 + i)) =
      ((∑ i ∈ Finset.range (m + n + 1), f i) - ∑ i ∈ Finset.range (m + 1), f i) := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    sum_range_shift_eq_sub f (m + 1) n

/-- Tail partial sums can be expressed as a difference of initial partial sums. -/
lemma partialSum_tail_eq_sub (X : ℕ → Ω → α) (m n : ℕ) :
    partialSum (fun k => X (m + 1 + k)) n =
      fun ω => partialSum X (m + n + 1) ω - partialSum X (m + 1) ω := by
  ext ω
  simpa [partialSum] using sum_range_shift_succ_eq_sub (fun i => X i ω) m n

end Deterministic

section Real

variable {Ω : Type*}

/-- The maximum absolute value of the partial sums `partialSum X k` for `k ≤ n`. -/
def partialSumMax (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (Finset.range (n + 1)).sup' (by simp) (fun k => |partialSum X k ω|)

lemma abs_partialSum_le_partialSumMax (X : ℕ → Ω → ℝ) (n k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) (ω : Ω) :
    |partialSum X k ω| ≤ partialSumMax X n ω := by
  exact Finset.le_sup' (fun j => |partialSum X j ω|) hk

/-- Any tail difference of partial sums is bounded by the maximal tail partial sum. -/
lemma abs_sub_partialSum_le_partialSumMax_tail (X : ℕ → Ω → ℝ) (m n k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) (ω : Ω) :
    |partialSum X (m + k + 1) ω - partialSum X (m + 1) ω|
      ≤ partialSumMax (fun j => X (m + 1 + j)) n ω := by
  have htail : partialSum (fun j => X (m + 1 + j)) k ω =
      partialSum X (m + k + 1) ω - partialSum X (m + 1) ω := by
    simpa using congrArg (fun g => g ω) (partialSum_tail_eq_sub (X := X) (m := m) (n := k))
  rw [← htail]
  exact abs_partialSum_le_partialSumMax (X := fun j => X (m + 1 + j)) (n := n) (k := k) hk ω

end Real

end Kolmogorov
