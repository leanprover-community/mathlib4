import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Filter.Ring
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Probability.CondVar
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.Adapted

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

lemma partialSum_stronglyMeasurable_natural {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, StronglyMeasurable (X k)) :
    ∀ {n i : ℕ}, n ≤ i + 1 → StronglyMeasurable[Filtration.natural X hX i] (partialSum X n)
  | 0, i, _ => by
      simpa [partialSum_zero] using
        (stronglyMeasurable_zero : StronglyMeasurable[Filtration.natural X hX i] (0 : Ω → ℝ))
  | n + 1, i, hni => by
      rw [partialSum_succ]
      refine (partialSum_stronglyMeasurable_natural X hX (n := n)
        (i := i) (Nat.le_trans (Nat.le_succ n) hni)).add ?_
      exact (Filtration.stronglyAdapted_natural hX n).mono
        ((Filtration.natural X hX).mono (Nat.succ_le_succ_iff.mp hni))

lemma stronglyAdapted_partialSum_succ_natural {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, StronglyMeasurable (X k)) :
    StronglyAdapted (Filtration.natural X hX) (fun n => partialSum X (n + 1)) := by
  intro n
  exact partialSum_stronglyMeasurable_natural X hX (n := n + 1) (i := n) le_rfl

lemma partialSum_succ_sub_partialSum (X : ℕ → Ω → α) (n : ℕ) :
    partialSum X (n + 2) - partialSum X (n + 1) = X (n + 1) := by
  ext ω
  have h :=
    congrArg (fun f : Ω → α => f ω - partialSum X (n + 1) ω) (partialSum_succ X (n + 1))
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h

end Deterministic

section Real

variable {Ω : Type*}

lemma condExp_natural_eq_zero_of_mean_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hindep : iIndepFun X μ)
    {i j : ℕ} (hij : i < j) (hmean : μ[X j] = 0) :
    μ[X j | Filtration.natural X hX i] =ᵐ[μ] 0 := by
  simpa [hmean] using hindep.condExp_natural_ae_eq_of_lt hX hij

lemma condExp_partialSum_succ_sub_eq_zero_of_mean_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hindep : iIndepFun X μ)
    (hmean : ∀ k, μ[X k] = 0) (i : ℕ) :
    μ[partialSum X (i + 2) - partialSum X (i + 1) | Filtration.natural X hX i] =ᵐ[μ] 0 := by
  rw [partialSum_succ_sub_partialSum]
  exact condExp_natural_eq_zero_of_mean_zero X hX hindep i.lt_succ_self (hmean (i + 1))

lemma martingale_partialSum_succ_natural_of_mean_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0) :
    Martingale (fun n => partialSum X (n + 1)) (Filtration.natural X hX) μ := by
  refine martingale_of_condExp_sub_eq_zero_nat
    (𝒢 := Filtration.natural X hX)
    (f := fun n => partialSum X (n + 1))
    (hadp := stronglyAdapted_partialSum_succ_natural X hX)
    (hint := fun i => ?_)
    (hf := fun i => ?_)
  · exact (partialSum_memLp (μ := μ) X (i + 1) fun k _ => hLp k).integrable (by norm_num)
  · exact condExp_partialSum_succ_sub_eq_zero_of_mean_zero X hX hindep hmean i

lemma partialSum_succ_sq_nonneg (X : ℕ → Ω → ℝ) :
    0 ≤ fun n ω => partialSum X (n + 1) ω ^ 2 := by
  intro n ω
  exact sq_nonneg _

lemma stronglyAdapted_partialSum_succ_sq_natural {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, StronglyMeasurable (X k)) :
    StronglyAdapted (Filtration.natural X hX) (fun n ω => partialSum X (n + 1) ω ^ 2) := by
  intro n
  exact ((stronglyAdapted_partialSum_succ_natural X hX n).measurable.pow_const 2).stronglyMeasurable

lemma integrable_partialSum_succ_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hLp : ∀ k, MemLp (X k) 2 μ) (n : ℕ) :
    Integrable (fun ω => partialSum X (n + 1) ω ^ 2) μ := by
  exact (partialSum_memLp (μ := μ) X (n + 1) fun k _ => hLp k).integrable_sq

lemma partialSum_succ_sq_le_condExp_partialSum_succ_sq_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0) (i : ℕ) :
    (fun ω => partialSum X (i + 1) ω ^ 2) ≤ᵐ[μ]
      μ[(fun ω => partialSum X (i + 2) ω ^ 2) | Filtration.natural X hX i] := by
  let S : Ω → ℝ := partialSum X (i + 2)
  have hLpS : MemLp S 2 μ := by
    simpa [S] using partialSum_memLp (μ := μ) X (i + 2) (fun k _ => hLp k)
  have hcond : μ[S | Filtration.natural X hX i] =ᵐ[μ] partialSum X (i + 1) := by
    simpa [S] using
      (martingale_partialSum_succ_natural_of_mean_zero (μ := μ) X hX hLp hindep hmean).condExp_ae_eq
        (i := i) (j := i + 1) i.le_succ
  have hsq : μ[S | Filtration.natural X hX i] ^ 2 =ᵐ[μ] fun ω => partialSum X (i + 1) ω ^ 2 := by
    simpa using hcond.pow_const 2
  have hvar_nonneg : 0 ≤ᵐ[μ] Var[S; μ | Filtration.natural X hX i] := by
    simpa [ProbabilityTheory.condVar, S] using
      (condExp_nonneg (μ := μ) (m := Filtration.natural X hX i)
        (f := fun ω => (S ω - μ[S | Filtration.natural X hX i] ω) ^ 2)
        (Filter.Eventually.of_forall fun ω => sq_nonneg _))
  have hvar_eq : Var[S; μ | Filtration.natural X hX i] =ᵐ[μ]
      μ[(fun ω => S ω ^ 2) | Filtration.natural X hX i] -
        μ[S | Filtration.natural X hX i] ^ 2 := by
    simpa [S] using
      (condVar_ae_eq_condExp_sq_sub_sq_condExp (μ := μ) (m := Filtration.natural X hX i)
        ((Filtration.natural X hX).le i) hLpS)
  filter_upwards [hvar_nonneg, hvar_eq, hsq] with ω hnn hEq hSq
  have hEq' :
      Var[S; μ | Filtration.natural X hX i] ω =
        μ[(fun ω => partialSum X (i + 2) ω ^ 2) | Filtration.natural X hX i] ω -
          μ[S | Filtration.natural X hX i] ω ^ 2 := by
    simpa [S] using hEq
  have hSq' : μ[S | Filtration.natural X hX i] ω ^ 2 = partialSum X (i + 1) ω ^ 2 := by
    simpa using hSq
  have hsub :
      0 ≤
        μ[(fun ω => partialSum X (i + 2) ω ^ 2) | Filtration.natural X hX i] ω -
          partialSum X (i + 1) ω ^ 2 := by
    have hsub_eq :
        μ[(fun ω => partialSum X (i + 2) ω ^ 2) | Filtration.natural X hX i] ω -
            partialSum X (i + 1) ω ^ 2 =
          Var[S; μ | Filtration.natural X hX i] ω := by
      calc
        μ[(fun ω => partialSum X (i + 2) ω ^ 2) | Filtration.natural X hX i] ω -
            partialSum X (i + 1) ω ^ 2 =
            μ[(fun ω => partialSum X (i + 2) ω ^ 2) | Filtration.natural X hX i] ω -
              μ[S | Filtration.natural X hX i] ω ^ 2 := by rw [← hSq']
        _ = Var[S; μ | Filtration.natural X hX i] ω := by linarith [hEq']
    rw [hsub_eq]
    exact hnn
  exact sub_nonneg.mp hsub

lemma submartingale_partialSum_succ_sq_natural_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0) :
    Submartingale (fun n ω => partialSum X (n + 1) ω ^ 2) (Filtration.natural X hX) μ := by
  refine submartingale_of_condExp_sub_nonneg_nat
    (𝒢 := Filtration.natural X hX)
    (f := fun n ω => partialSum X (n + 1) ω ^ 2)
    (hadp := stronglyAdapted_partialSum_succ_sq_natural X hX)
    (hint := integrable_partialSum_succ_sq (μ := μ) X hLp)
    (hf := fun i => ?_)
  have hle :=
    partialSum_succ_sq_le_condExp_partialSum_succ_sq_of_mean_zero
      (μ := μ) X hX hLp hindep hmean i
  have hnonneg :
      0 ≤ᵐ[μ]
        μ[(fun n ω => partialSum X (n + 1) ω ^ 2) (i + 1) | Filtration.natural X hX i] -
          (fun n ω => partialSum X (n + 1) ω ^ 2) i := by
    filter_upwards [hle] with ω hω
    exact sub_nonneg.mpr hω
  have hrewrite :
      μ[(fun n ω => partialSum X (n + 1) ω ^ 2) (i + 1) -
          (fun n ω => partialSum X (n + 1) ω ^ 2) i | Filtration.natural X hX i] =ᵐ[μ]
        μ[(fun n ω => partialSum X (n + 1) ω ^ 2) (i + 1) | Filtration.natural X hX i] -
          (fun n ω => partialSum X (n + 1) ω ^ 2) i := by
    refine (condExp_sub
        (integrable_partialSum_succ_sq (μ := μ) X hLp (i + 1))
        (integrable_partialSum_succ_sq (μ := μ) X hLp i)
        (Filtration.natural X hX i)).trans ?_
    exact (Filter.EventuallyEq.refl _ _).sub <|
      (condExp_of_stronglyMeasurable ((Filtration.natural X hX).le i)
        (stronglyAdapted_partialSum_succ_sq_natural X hX i)
        (integrable_partialSum_succ_sq (μ := μ) X hLp i)).eventuallyEq
  exact Filter.EventuallyLE.trans hnonneg hrewrite.symm.le

lemma smul_measure_partialSum_succ_sq_sup_ge_le_integral_partialSum_succ_sq_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0) (ε : NNReal) (n : ℕ) :
    ε • μ {ω | (ε : ℝ) ≤ (Finset.range (n + 1)).sup' (by simp)
      (fun k => partialSum X (k + 1) ω ^ 2)} ≤
      ENNReal.ofReal (∫ ω, partialSum X (n + 1) ω ^ 2 ∂μ) := by
  refine (MeasureTheory.maximal_ineq
      (μ := μ)
      (𝒢 := Filtration.natural X hX)
      (f := fun n ω => partialSum X (n + 1) ω ^ 2)
      (submartingale_partialSum_succ_sq_natural_of_mean_zero
        (μ := μ) X hX hLp hindep hmean)
      (partialSum_succ_sq_nonneg X)
      (ε := ε)
      n).trans ?_
  exact ENNReal.ofReal_le_ofReal <|
    setIntegral_le_integral
      (integrable_partialSum_succ_sq (μ := μ) X hLp n)
      (Filter.Eventually.of_forall fun ω => sq_nonneg (partialSum X (n + 1) ω))

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

lemma partialSumMax_succ_eq_sup_abs_partialSum_succ (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    partialSumMax X (n + 1) ω =
      (Finset.range (n + 1)).sup' (by simp) (fun k => |partialSum X (k + 1) ω|) := by
  apply le_antisymm
  · rw [partialSumMax, Finset.sup'_le_iff]
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have hnonneg :
          0 ≤ (Finset.range (n + 1)).sup' (by simp) (fun k => |partialSum X (k + 1) ω|) := by
        have hle := Finset.le_sup' (f := fun k => |partialSum X (k + 1) ω|) (by simp : 0 ∈ Finset.range (n + 1))
        exact le_trans (by simp) hle
      simpa [partialSum_zero] using hnonneg
    · rcases Nat.exists_eq_succ_of_ne_zero hk0.ne' with ⟨l, rfl⟩
      exact Finset.le_sup' (f := fun k => |partialSum X (k + 1) ω|)
        (by simpa using hk)
  · rw [Finset.sup'_le_iff]
    intro k hk
    exact abs_partialSum_le_partialSumMax X (n + 1) (k + 1) (by simpa using hk) ω

lemma sq_le_sup_partialSum_succ_sq_iff_le_partialSumMax_succ
    (X : ℕ → Ω → ℝ) (ε : NNReal) (n : ℕ) (ω : Ω) :
    (ε : ℝ) ^ 2 ≤ (Finset.range (n + 1)).sup' (by simp) (fun k => partialSum X (k + 1) ω ^ 2) ↔
      (ε : ℝ) ≤ partialSumMax X (n + 1) ω := by
  rw [partialSumMax_succ_eq_sup_abs_partialSum_succ]
  constructor
  · intro h
    rcases ((Finset.le_sup'_iff (H := by simp)
      (f := fun k => partialSum X (k + 1) ω ^ 2))).mp h with ⟨k, hk, hkε⟩
    have habs : (ε : ℝ) ≤ |partialSum X (k + 1) ω| := by
      have hkε' : (ε : ℝ) ^ 2 ≤ |partialSum X (k + 1) ω| ^ 2 := by
        simpa [sq_abs] using hkε
      exact (sq_le_sq₀ ε.2 (abs_nonneg _)).mp hkε'
    exact le_trans habs <| Finset.le_sup' (f := fun k => |partialSum X (k + 1) ω|) hk
  · intro h
    rcases ((Finset.le_sup'_iff (H := by simp)
      (f := fun k => |partialSum X (k + 1) ω|))).mp h with ⟨k, hk, hkε⟩
    have hsquare : (ε : ℝ) ^ 2 ≤ partialSum X (k + 1) ω ^ 2 := by
      have := (sq_le_sq₀ ε.2 (abs_nonneg (partialSum X (k + 1) ω))).2 hkε
      simpa [sq_abs] using this
    exact le_trans hsquare <| Finset.le_sup' (f := fun k => partialSum X (k + 1) ω ^ 2) hk

lemma event_sup_partialSum_succ_sq_ge_eq_event_partialSumMax_ge
    (X : ℕ → Ω → ℝ) (ε : NNReal) (n : ℕ) :
    {ω | (ε : ℝ) ^ 2 ≤ (Finset.range (n + 1)).sup' (by simp)
      (fun k => partialSum X (k + 1) ω ^ 2)} =
      {ω | (ε : ℝ) ≤ partialSumMax X (n + 1) ω} := by
  ext ω
  exact sq_le_sup_partialSum_succ_sq_iff_le_partialSumMax_succ X ε n ω

lemma smul_measure_partialSumMax_ge_le_integral_partialSum_succ_sq_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0) (ε : NNReal) (n : ℕ) :
    (ε ^ 2) • μ {ω | (ε : ℝ) ≤ partialSumMax X (n + 1) ω} ≤
      ENNReal.ofReal (∫ ω, partialSum X (n + 1) ω ^ 2 ∂μ) := by
  have hset :
      {ω | (((ε ^ 2 : NNReal) : ℝ)) ≤ (Finset.range (n + 1)).sup' (by simp)
        (fun k => partialSum X (k + 1) ω ^ 2)} =
        {ω | (ε : ℝ) ≤ partialSumMax X (n + 1) ω} := by
    ext ω
    change (ε : ℝ) ^ 2 ≤ (Finset.range (n + 1)).sup' (by simp)
      (fun k => partialSum X (k + 1) ω ^ 2) ↔
        (ε : ℝ) ≤ partialSumMax X (n + 1) ω
    exact sq_le_sup_partialSum_succ_sq_iff_le_partialSumMax_succ X ε n ω
  have hdoob :=
    smul_measure_partialSum_succ_sq_sup_ge_le_integral_partialSum_succ_sq_of_mean_zero
      (μ := μ) X hX hLp hindep hmean (ε := ε ^ 2) n
  rw [hset] at hdoob
  exact hdoob

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

lemma integral_partialSum_eq_sum_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (n : ℕ)
    (hX : ∀ k ∈ Finset.range n, MemLp (X k) 2 μ) :
    μ[partialSum X n] = ∑ k ∈ Finset.range n, μ[X k] := by
  simpa [partialSum] using
    (integral_finset_sum (μ := μ) (s := Finset.range n) (f := fun k => X k) fun k hk =>
      (hX k hk).integrable (by norm_num))

lemma integral_partialSum_eq_zero_of_forall_integral_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (n : ℕ)
    (hX : ∀ k ∈ Finset.range n, MemLp (X k) 2 μ)
    (hmean : ∀ k ∈ Finset.range n, μ[X k] = 0) :
    μ[partialSum X n] = 0 := by
  rw [integral_partialSum_eq_sum_integral (μ := μ) X n hX]
  exact Finset.sum_eq_zero fun k hk => hmean k hk

lemma integral_partialSum_sq_eq_variance_of_forall_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (n : ℕ)
    (hX : ∀ k ∈ Finset.range (n + 1), MemLp (X k) 2 μ)
    (hmean : ∀ k ∈ Finset.range (n + 1), μ[X k] = 0) :
    ∫ ω, partialSum X (n + 1) ω ^ 2 ∂μ = variance (partialSum X (n + 1)) μ := by
  rw [variance_eq_integral (partialSum_memLp (μ := μ) X (n + 1) hX).aemeasurable]
  rw [integral_partialSum_eq_zero_of_forall_integral_zero (μ := μ) X (n + 1) hX hmean]
  simp

lemma integral_partialSum_tail_eq_zero_of_forall_integral_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ k ∈ Finset.range n, MemLp (X (m + 1 + k)) 2 μ)
    (hmean : ∀ k ∈ Finset.range n, μ[X (m + 1 + k)] = 0) :
    μ[partialSum (fun j => X (m + 1 + j)) n] = 0 := by
  rw [integral_partialSum_eq_sum_integral (μ := μ) (X := fun j => X (m + 1 + j)) n hX]
  exact Finset.sum_eq_zero fun k hk => hmean k hk

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

lemma smul_measure_partialSumMax_ge_le_variance_partialSum_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0) (ε : NNReal) (n : ℕ) :
    (ε ^ 2) • μ {ω | (ε : ℝ) ≤ partialSumMax X (n + 1) ω} ≤
      ENNReal.ofReal (variance (partialSum X (n + 1)) μ) := by
  have hbound :=
    smul_measure_partialSumMax_ge_le_integral_partialSum_succ_sq_of_mean_zero
      (μ := μ) X hX hLp hindep hmean ε n
  have hEq :
      ∫ ω, partialSum X (n + 1) ω ^ 2 ∂μ = variance (partialSum X (n + 1)) μ := by
    exact integral_partialSum_sq_eq_variance_of_forall_mean_zero (μ := μ) X n
      (fun k hk => hLp k) (fun k hk => hmean k)
  have hEq' :
      ENNReal.ofReal (∫ ω, partialSum X (n + 1) ω ^ 2 ∂μ) =
        ENNReal.ofReal (variance (partialSum X (n + 1)) μ) := by
    rw [hEq]
  rw [hEq'] at hbound
  exact hbound

lemma smul_measure_partialSumMax_ge_le_sum_variance_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0) (ε : NNReal) (n : ℕ) :
    (ε ^ 2) • μ {ω | (ε : ℝ) ≤ partialSumMax X (n + 1) ω} ≤
      ENNReal.ofReal (∑ k ∈ Finset.range (n + 1), variance (X k) μ) := by
  have hbound :=
    smul_measure_partialSumMax_ge_le_variance_partialSum_of_mean_zero
      (μ := μ) X hX hLp hindep hmean ε n
  have hpair : Set.Pairwise ↑(Finset.range (n + 1)) fun i j => X i ⟂ᵢ[μ] X j := by
    intro i hi j hj hij
    exact hindep.indepFun hij
  have hvar :
      variance (partialSum X (n + 1)) μ =
        ∑ k ∈ Finset.range (n + 1), variance (X k) μ := by
    exact variance_partialSum_eq_sum_variance (μ := μ) X (n + 1) (fun k _ => hLp k) hpair
  rw [hvar] at hbound
  exact hbound

lemma variance_partialSum_tail_eq_sum_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ k ∈ Finset.range n, MemLp (X (m + 1 + k)) 2 μ)
    (hindep : Set.Pairwise ↑(Finset.range n) fun i j => X (m + 1 + i) ⟂ᵢ[μ] X (m + 1 + j)) :
    variance (partialSum (fun j => X (m + 1 + j)) n) μ =
      ∑ k ∈ Finset.range n, variance (X (m + 1 + k)) μ := by
  exact variance_partialSum_eq_sum_variance (μ := μ) (fun j => X (m + 1 + j)) n hX hindep

lemma measure_partialSum_tail_ge_le_sum_variance_div_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ k ∈ Finset.range n, MemLp (X (m + 1 + k)) 2 μ)
    (hindep : Set.Pairwise ↑(Finset.range n) fun i j => X (m + 1 + i) ⟂ᵢ[μ] X (m + 1 + j))
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |partialSum (fun j => X (m + 1 + j)) n ω - μ[partialSum (fun j => X (m + 1 + j)) n]|} ≤
      ENNReal.ofReal ((∑ k ∈ Finset.range n, variance (X (m + 1 + k)) μ) / ε ^ 2) := by
  refine (measure_partialSum_tail_ge_le_variance_div_sq (μ := μ) X m n hX hε).trans ?_
  rw [variance_partialSum_tail_eq_sum_variance (μ := μ) X m n hX hindep]

lemma measure_partialSum_tail_abs_ge_le_sum_variance_div_sq_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ k ∈ Finset.range n, MemLp (X (m + 1 + k)) 2 μ)
    (hindep : Set.Pairwise ↑(Finset.range n) fun i j => X (m + 1 + i) ⟂ᵢ[μ] X (m + 1 + j))
    (hmean : μ[partialSum (fun j => X (m + 1 + j)) n] = 0) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |partialSum (fun j => X (m + 1 + j)) n ω|} ≤
      ENNReal.ofReal ((∑ k ∈ Finset.range n, variance (X (m + 1 + k)) μ) / ε ^ 2) := by
  have hbound :=
    measure_partialSum_tail_ge_le_sum_variance_div_sq (μ := μ) X m n hX hindep hε
  rw [hmean] at hbound
  simpa using hbound

lemma measure_partialSum_tail_abs_ge_le_sum_variance_div_sq_of_forall_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ k ∈ Finset.range n, MemLp (X (m + 1 + k)) 2 μ)
    (hindep : Set.Pairwise ↑(Finset.range n) fun i j => X (m + 1 + i) ⟂ᵢ[μ] X (m + 1 + j))
    (hmean : ∀ k ∈ Finset.range n, μ[X (m + 1 + k)] = 0) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |partialSum (fun j => X (m + 1 + j)) n ω|} ≤
      ENNReal.ofReal ((∑ k ∈ Finset.range n, variance (X (m + 1 + k)) μ) / ε ^ 2) := by
  apply measure_partialSum_tail_abs_ge_le_sum_variance_div_sq_of_mean_zero
    (μ := μ) X m n hX hindep
  exact integral_partialSum_tail_eq_zero_of_forall_integral_zero (μ := μ) X m n hX hmean
  exact hε

lemma measure_partialSum_tail_abs_ge_le_sum_variance_div_sq_of_forall_mean_zero_of_mem_range
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m n k : ℕ)
    (hk : k ∈ Finset.range (n + 1))
    (hX : ∀ j ∈ Finset.range (n + 1), MemLp (X (m + 1 + j)) 2 μ)
    (hindep : Set.Pairwise ↑(Finset.range (n + 1))
      fun i j => X (m + 1 + i) ⟂ᵢ[μ] X (m + 1 + j))
    (hmean : ∀ j ∈ Finset.range (n + 1), μ[X (m + 1 + j)] = 0) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |partialSum (fun j => X (m + 1 + j)) k ω|} ≤
      ENNReal.ofReal ((∑ j ∈ Finset.range k, variance (X (m + 1 + j)) μ) / ε ^ 2) := by
  apply measure_partialSum_tail_abs_ge_le_sum_variance_div_sq_of_forall_mean_zero
    (μ := μ) X m k
  · intro j hj
    exact hX j <| Finset.mem_range.mpr <|
      Nat.lt_trans (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)
  · exact hindep.mono fun j hj =>
      Finset.mem_range.mpr <|
        Nat.lt_trans (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)
  · intro j hj
    exact hmean j <| Finset.mem_range.mpr <|
      Nat.lt_trans (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)
  · exact hε

lemma measure_event_two_mul_partialSumMax_tail_le_sum_variance_div_sq_of_forall_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ j ∈ Finset.range (n + 1), MemLp (X (m + 1 + j)) 2 μ)
    (hindep : Set.Pairwise ↑(Finset.range (n + 1))
      fun i j => X (m + 1 + i) ⟂ᵢ[μ] X (m + 1 + j))
    (hmean : ∀ j ∈ Finset.range (n + 1), μ[X (m + 1 + j)] = 0) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ 2 * partialSumMax (fun j => X (m + 1 + j)) n ω} ≤
      ∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal ((∑ j ∈ Finset.range k, variance (X (m + 1 + j)) μ) / (ε / 2) ^ 2) := by
  have hε2 : 0 < ε / 2 := by
    linarith
  refine (measure_event_two_mul_partialSumMax_tail_le_sum_sub' (μ := μ) X m n ε).trans ?_
  refine Finset.sum_le_sum fun k hk => ?_
  exact measure_partialSum_tail_abs_ge_le_sum_variance_div_sq_of_forall_mean_zero_of_mem_range
    (μ := μ) X m n k hk hX hindep hmean (ε := ε / 2) hε2

lemma measure_event_two_mul_partialSumMax_tail_le_mul_variance_div_sq_of_forall_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ j ∈ Finset.range (n + 1), MemLp (X (m + 1 + j)) 2 μ)
    (hindep : Set.Pairwise ↑(Finset.range (n + 1))
      fun i j => X (m + 1 + i) ⟂ᵢ[μ] X (m + 1 + j))
    (hmean : ∀ j ∈ Finset.range (n + 1), μ[X (m + 1 + j)] = 0) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ 2 * partialSumMax (fun j => X (m + 1 + j)) n ω} ≤
      (n + 1) * ENNReal.ofReal
        ((∑ j ∈ Finset.range (n + 1), variance (X (m + 1 + j)) μ) / (ε / 2) ^ 2) := by
  calc
    μ {ω | ε ≤ 2 * partialSumMax (fun j => X (m + 1 + j)) n ω} ≤
        ∑ k ∈ Finset.range (n + 1),
          ENNReal.ofReal ((∑ j ∈ Finset.range k, variance (X (m + 1 + j)) μ) / (ε / 2) ^ 2) := by
      exact measure_event_two_mul_partialSumMax_tail_le_sum_variance_div_sq_of_forall_mean_zero
        (μ := μ) X m n hX hindep hmean hε
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          ENNReal.ofReal
            ((∑ j ∈ Finset.range (n + 1), variance (X (m + 1 + j)) μ) / (ε / 2) ^ 2) := by
      refine Finset.sum_le_sum fun k hk => ?_
      apply ENNReal.ofReal_le_ofReal
      refine div_le_div_of_nonneg_right ?_ (sq_nonneg (ε / 2))
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (Nat.le_of_lt (Finset.mem_range.mp hk))) ?_
      intro j _ hj
      exact variance_nonneg (X (m + 1 + j)) μ
    _ = (n + 1) * ENNReal.ofReal
          ((∑ j ∈ Finset.range (n + 1), variance (X (m + 1 + j)) μ) / (ε / 2) ^ 2) := by
      simp

lemma div_sq_half_eq_four_mul_div_sq (a ε : ℝ) :
    a / (ε / 2) ^ 2 = 4 * a / ε ^ 2 := by
  by_cases hε : ε = 0
  · simp [hε]
  · field_simp [hε]
    ring

lemma measure_event_two_mul_partialSumMax_tail_le_mul_four_mul_variance_div_sq_of_forall_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ j ∈ Finset.range (n + 1), MemLp (X (m + 1 + j)) 2 μ)
    (hindep : Set.Pairwise ↑(Finset.range (n + 1))
      fun i j => X (m + 1 + i) ⟂ᵢ[μ] X (m + 1 + j))
    (hmean : ∀ j ∈ Finset.range (n + 1), μ[X (m + 1 + j)] = 0) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ 2 * partialSumMax (fun j => X (m + 1 + j)) n ω} ≤
      (n + 1) * ENNReal.ofReal
        (4 * (∑ j ∈ Finset.range (n + 1), variance (X (m + 1 + j)) μ) / ε ^ 2) := by
  simpa [div_sq_half_eq_four_mul_div_sq] using
    measure_event_two_mul_partialSumMax_tail_le_mul_variance_div_sq_of_forall_mean_zero
      (μ := μ) X m n hX hindep hmean hε

end Real

end Kolmogorov
