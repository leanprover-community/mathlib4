import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Probability.Moments.Variance

open scoped BigOperators ProbabilityTheory
open MeasureTheory
open ProbabilityTheory

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

lemma partialSum_measurable {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (n : ℕ)
    (hX : ∀ k, Measurable (X k)) : Measurable (partialSum X n) := by
  simpa [partialSum] using Finset.measurable_sum (Finset.range n) (fun i _ => hX i)

lemma partialSum_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (n : ℕ)
    (hX : ∀ k ∈ Finset.range n, MemLp (X k) 2 μ) : MemLp (partialSum X n) 2 μ := by
  let h := memLp_finset_sum' (s := Finset.range n) hX
  refine h.ae_eq ?_
  filter_upwards with ω
  simp [partialSum]

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

lemma partialSumMax_nonneg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ partialSumMax X n ω := by
  have h := abs_partialSum_le_partialSumMax X n 0 (by simp) ω
  simpa using h

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

lemma partialSumMax_measurable {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (n : ℕ)
    (hX : ∀ k, Measurable (X k)) : Measurable (partialSumMax X n) := by
  simpa [partialSumMax] using
    (Finset.measurable_range_sup'' (n := n) (f := fun k ω => |partialSum X k ω|)
      (fun k hk => continuous_abs.measurable.comp (partialSum_measurable X k hX)))

lemma measurableSet_partialSumMax_ge {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (n : ℕ) (ε : ℝ) (hX : ∀ k, Measurable (X k)) :
    MeasurableSet {ω | ε ≤ partialSumMax X n ω} := by
  exact measurableSet_le measurable_const (partialSumMax_measurable X n hX)

lemma tail_event_subset_partialSumMax_event (X : ℕ → Ω → ℝ) (m n k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) (ε : ℝ) :
    {ω | ε ≤ |partialSum X (m + k + 1) ω - partialSum X (m + 1) ω|} ⊆
      {ω | ε ≤ partialSumMax (fun j => X (m + 1 + j)) n ω} := by
  intro ω hω
  exact le_trans hω (abs_sub_partialSum_le_partialSumMax_tail X m n k hk ω)

lemma measurableSet_tail_partialSum_sub_ge {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (m k : ℕ) (ε : ℝ) (hX : ∀ k, Measurable (X k)) :
    MeasurableSet {ω | ε ≤ |partialSum X (m + k + 1) ω - partialSum X (m + 1) ω|} := by
  exact measurableSet_le measurable_const
    (continuous_abs.measurable.comp
      ((partialSum_measurable X (m + k + 1) hX).sub (partialSum_measurable X (m + 1) hX)))

lemma measure_tail_event_le_measure_partialSumMax_event {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (m n k : ℕ) (hk : k ∈ Finset.range (n + 1)) (ε : ℝ) :
    μ {ω | ε ≤ |partialSum X (m + k + 1) ω - partialSum X (m + 1) ω|} ≤
      μ {ω | ε ≤ partialSumMax (fun j => X (m + 1 + j)) n ω} := by
  exact measure_mono (tail_event_subset_partialSumMax_event X m n k hk ε)

lemma le_partialSumMax_iff (X : ℕ → Ω → ℝ) (n : ℕ) (ε : ℝ) (ω : Ω) :
    ε ≤ partialSumMax X n ω ↔ ∃ k ∈ Finset.range (n + 1), ε ≤ |partialSum X k ω| := by
  simp [partialSumMax, Finset.le_sup'_iff]

lemma partialSumMax_event_eq_biUnion (X : ℕ → Ω → ℝ) (n : ℕ) (ε : ℝ) :
    {ω | ε ≤ partialSumMax X n ω} =
      ⋃ k ∈ Finset.range (n + 1), {ω | ε ≤ |partialSum X k ω|} := by
  ext ω
  simp [le_partialSumMax_iff]

lemma event_two_mul_partialSumMax_ge_eq (X : ℕ → Ω → ℝ) (n : ℕ) (ε : ℝ) :
    {ω | ε ≤ 2 * partialSumMax X n ω} = {ω | ε / 2 ≤ partialSumMax X n ω} := by
  ext ω
  constructor <;> intro h
  · change ε ≤ 2 * partialSumMax X n ω at h
    change ε / 2 ≤ partialSumMax X n ω
    nlinarith [partialSumMax_nonneg X n ω]
  · change ε / 2 ≤ partialSumMax X n ω at h
    change ε ≤ 2 * partialSumMax X n ω
    nlinarith [partialSumMax_nonneg X n ω]

lemma partialSumMax_tail_event_eq_biUnion_sub (X : ℕ → Ω → ℝ) (m n : ℕ) (ε : ℝ) :
    {ω | ε ≤ partialSumMax (fun j => X (m + 1 + j)) n ω} =
      ⋃ k ∈ Finset.range (n + 1),
        {ω | ε ≤ |partialSum X (m + k + 1) ω - partialSum X (m + 1) ω|} := by
  rw [partialSumMax_event_eq_biUnion]
  ext ω
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk, hω⟩
    have hEq : |partialSum (fun j => X (m + 1 + j)) k ω| =
        |partialSum X (m + k + 1) ω - partialSum X (m + 1) ω| := by
      simpa using congrArg abs
        (congrArg (fun g => g ω) (partialSum_tail_eq_sub (X := X) (m := m) (n := k)))
    refine ⟨k, hk, ?_⟩
    rw [← hEq]
    exact hω
  · rintro ⟨k, hk, hω⟩
    have hEq : |partialSum (fun j => X (m + 1 + j)) k ω| =
        |partialSum X (m + k + 1) ω - partialSum X (m + 1) ω| := by
      simpa using congrArg abs
        (congrArg (fun g => g ω) (partialSum_tail_eq_sub (X := X) (m := m) (n := k)))
    refine ⟨k, hk, ?_⟩
    rw [hEq]
    exact hω

lemma measure_partialSumMax_event_le_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) (ε : ℝ) :
    μ {ω | ε ≤ partialSumMax X n ω} ≤
      ∑ k ∈ Finset.range (n + 1), μ {ω | ε ≤ |partialSum X k ω|} := by
  rw [partialSumMax_event_eq_biUnion]
  simpa using measure_biUnion_finset_le (μ := μ) (Finset.range (n + 1))
    (fun k => {ω | ε ≤ |partialSum X k ω|})

lemma measure_partialSumMax_tail_event_le_sum_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (m n : ℕ) (ε : ℝ) :
    μ {ω | ε ≤ partialSumMax (fun j => X (m + 1 + j)) n ω} ≤
      ∑ k ∈ Finset.range (n + 1),
        μ {ω | ε ≤ |partialSum X (m + k + 1) ω - partialSum X (m + 1) ω|} := by
  rw [partialSumMax_tail_event_eq_biUnion_sub]
  simpa using measure_biUnion_finset_le (μ := μ) (Finset.range (n + 1))
    (fun k => {ω | ε ≤ |partialSum X (m + k + 1) ω - partialSum X (m + 1) ω|})

lemma measure_event_two_mul_partialSumMax_tail_le_sum_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (m n : ℕ) (ε : ℝ) :
    μ {ω | ε ≤ 2 * partialSumMax (fun j => X (m + 1 + j)) n ω} ≤
      ∑ k ∈ Finset.range (n + 1),
        μ {ω | ε / 2 ≤ |partialSum X (m + k + 1) ω - partialSum X (m + 1) ω|} := by
  rw [event_two_mul_partialSumMax_ge_eq]
  exact measure_partialSumMax_tail_event_le_sum_sub μ X m n (ε / 2)

lemma measure_event_two_mul_partialSumMax_tail_le_sum_sub'
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ) (m n : ℕ) (ε : ℝ) :
    μ {ω | ε ≤ 2 * partialSumMax (fun j => X (m + 1 + j)) n ω} ≤
      ∑ k ∈ Finset.range (n + 1),
        μ {ω | ε / 2 ≤ |partialSum (fun j => X (m + 1 + j)) k ω|} := by
  rw [event_two_mul_partialSumMax_ge_eq]
  exact measure_partialSumMax_event_le_sum μ (fun j => X (m + 1 + j)) n (ε / 2)

lemma measure_partialSum_ge_le_variance_div_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (n : ℕ)
    (hX : ∀ k ∈ Finset.range n, MemLp (X k) 2 μ) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |partialSum X n ω - μ[partialSum X n]|} ≤
      ENNReal.ofReal (variance (partialSum X n) μ / ε ^ 2) := by
  apply meas_ge_le_variance_div_sq
  · exact partialSum_memLp (μ := μ) X n hX
  · exact hε

lemma measure_partialSum_tail_ge_le_variance_div_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ k ∈ Finset.range n, MemLp (X (m + 1 + k)) 2 μ) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |partialSum (fun j => X (m + 1 + j)) n ω - μ[partialSum (fun j => X (m + 1 + j)) n]|} ≤
      ENNReal.ofReal (variance (partialSum (fun j => X (m + 1 + j)) n) μ / ε ^ 2) := by
  exact measure_partialSum_ge_le_variance_div_sq (μ := μ) (fun j => X (m + 1 + j)) n hX hε

lemma variance_partialSum_eq_sum_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (n : ℕ)
    (hX : ∀ k ∈ Finset.range n, MemLp (X k) 2 μ)
    (hindep : Set.Pairwise ↑(Finset.range n) fun i j => X i ⟂ᵢ[μ] X j) :
    variance (partialSum X n) μ = ∑ k ∈ Finset.range n, variance (X k) μ := by
  have hsum := IndepFun.variance_sum (μ := μ) (s := Finset.range n) hX hindep
  have hAE : partialSum X n =ᵐ[μ] ∑ i ∈ Finset.range n, X i := by
    filter_upwards with ω
    simp [partialSum]
  rw [variance_congr hAE]
  exact hsum

lemma variance_partialSum_tail_eq_sum_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ k ∈ Finset.range n, MemLp (X (m + 1 + k)) 2 μ)
    (hindep : Set.Pairwise ↑(Finset.range n) fun i j => X (m + 1 + i) ⟂ᵢ[μ] X (m + 1 + j)) :
    variance (partialSum (fun j => X (m + 1 + j)) n) μ =
      ∑ k ∈ Finset.range n, variance (X (m + 1 + k)) μ := by
  exact variance_partialSum_eq_sum_variance (μ := μ) (fun j => X (m + 1 + j)) n hX hindep

end Real

end Kolmogorov
