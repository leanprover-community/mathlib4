import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Filter.Ring
import Mathlib.Order.LiminfLimsup
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

lemma limsup_le_of_eventually_le_nat'
    {u : ℕ → ℝ} {a : ℝ}
    (hcu : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop u)
    (hbu : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u)
    (h : ∃ N : ℕ, ∀ n ≥ N, u n ≤ a) :
    Filter.limsup u Filter.atTop ≤ a := by
  rw [Filter.limsup_le_iff' (f := Filter.atTop) (u := u) (x := a) hcu hbu]
  intro y hy
  rcases h with ⟨N, hN⟩
  exact Filter.eventually_atTop.2 ⟨N, fun n hn => (hN n hn).trans (le_of_lt hy)⟩

lemma le_liminf_of_eventually_le_nat'
    {u : ℕ → ℝ} {a : ℝ}
    (hcu : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop u)
    (hbu : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop u)
    (h : ∃ N : ℕ, ∀ n ≥ N, a ≤ u n) :
    a ≤ Filter.liminf u Filter.atTop := by
  rw [Filter.le_liminf_iff' (f := Filter.atTop) (u := u) (x := a) hcu hbu]
  intro y hy
  rcases h with ⟨N, hN⟩
  exact Filter.eventually_atTop.2 ⟨N, fun n hn => (le_of_lt hy).trans (hN n hn)⟩

lemma le_liminf_of_monotone_nat'
    {u : ℕ → ℝ}
    (hcu : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop u)
    (hbu : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop u)
    (hmono : Monotone u) (n : ℕ) :
    u n ≤ Filter.liminf u Filter.atTop := by
  apply le_liminf_of_eventually_le_nat' hcu hbu
  exact ⟨n, fun k hk => hmono hk⟩

lemma limsup_sub_liminf_le_of_eventually_bounded_nat'
    {u : ℕ → ℝ} {a b : ℝ}
    (hcu : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop u)
    (hbu : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u)
    (hcl : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop u)
    (hbl : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop u)
    (h : ∃ N : ℕ, ∀ n ≥ N, a ≤ u n ∧ u n ≤ b) :
    Filter.limsup u Filter.atTop - Filter.liminf u Filter.atTop ≤ b - a := by
  have hsup : Filter.limsup u Filter.atTop ≤ b := by
    apply limsup_le_of_eventually_le_nat' hcu hbu
    rcases h with ⟨N, hN⟩
    exact ⟨N, fun n hn => (hN n hn).2⟩
  have hinf : a ≤ Filter.liminf u Filter.atTop := by
    apply le_liminf_of_eventually_le_nat' hcl hbl
    rcases h with ⟨N, hN⟩
    exact ⟨N, fun n hn => (hN n hn).1⟩
  linarith

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

/-- Any two tail partial sums differ by at most twice the maximal tail partial sum. -/
lemma abs_sub_partialSum_le_two_mul_partialSumMax_tail (X : ℕ → Ω → ℝ) (m n j k : ℕ)
    (hj : j ∈ Finset.range (n + 1)) (hk : k ∈ Finset.range (n + 1)) (ω : Ω) :
    |partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω|
      ≤ 2 * partialSumMax (fun l => X (m + 1 + l)) n ω := by
  have hj' := abs_sub_partialSum_le_partialSumMax_tail X m n j hj ω
  have hk' := abs_sub_partialSum_le_partialSumMax_tail X m n k hk ω
  calc
    |partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω|
      = |(partialSum X (m + j + 1) ω - partialSum X (m + 1) ω) +
          (partialSum X (m + 1) ω - partialSum X (m + k + 1) ω)| := by ring_nf
    _ ≤ |partialSum X (m + j + 1) ω - partialSum X (m + 1) ω| +
          |partialSum X (m + 1) ω - partialSum X (m + k + 1) ω| := by
        exact abs_add_le
          (partialSum X (m + j + 1) ω - partialSum X (m + 1) ω)
          (partialSum X (m + 1) ω - partialSum X (m + k + 1) ω)
    _ = |partialSum X (m + j + 1) ω - partialSum X (m + 1) ω| +
          |partialSum X (m + k + 1) ω - partialSum X (m + 1) ω| := by
        rw [abs_sub_comm (partialSum X (m + 1) ω) (partialSum X (m + k + 1) ω)]
    _ ≤ partialSumMax (fun l => X (m + 1 + l)) n ω +
          partialSumMax (fun l => X (m + 1 + l)) n ω := by
        exact add_le_add hj' hk'
    _ = 2 * partialSumMax (fun l => X (m + 1 + l)) n ω := by ring

/-- The maximal oscillation among the tail partial sums
`partialSum X (m + j + 1)` for `j ≤ n`. -/
def finiteTailOscillationMax (X : ℕ → Ω → ℝ) (m n : ℕ) : Ω → ℝ :=
  fun ω =>
    (Finset.range (n + 1)).sup' (by simp) fun j =>
      (Finset.range (n + 1)).sup' (by simp) fun k =>
        |partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω|

/-- The maximum of the finite tail window
`partialSum X (m + j + 1)` for `j ≤ n`. -/
def finiteTailSup (X : ℕ → Ω → ℝ) (m n : ℕ) : Ω → ℝ :=
  fun ω => (Finset.range (n + 1)).sup' (by simp) fun j => partialSum X (m + j + 1) ω

/-- The minimum of the finite tail window
`partialSum X (m + j + 1)` for `j ≤ n`. -/
def finiteTailInf (X : ℕ → Ω → ℝ) (m n : ℕ) : Ω → ℝ :=
  fun ω => (Finset.range (n + 1)).inf' (by simp) fun j => partialSum X (m + j + 1) ω

lemma le_finiteTailOscillationMax_iff (X : ℕ → Ω → ℝ) (m n : ℕ) (ε : ℝ) (ω : Ω) :
    ε ≤ finiteTailOscillationMax X m n ω ↔
      ∃ j ∈ Finset.range (n + 1), ∃ k ∈ Finset.range (n + 1),
        ε ≤ |partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω| := by
  simp [finiteTailOscillationMax, Finset.le_sup'_iff]

lemma finiteTailOscillationMax_nonneg (X : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) :
    0 ≤ finiteTailOscillationMax X m n ω := by
  exact (le_finiteTailOscillationMax_iff X m n 0 ω).2 ⟨0, by simp, 0, by simp, by simp⟩

lemma partialSum_le_finiteTailSup (X : ℕ → Ω → ℝ) (m n k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) (ω : Ω) :
    partialSum X (m + k + 1) ω ≤ finiteTailSup X m n ω := by
  exact Finset.le_sup' (f := fun j => partialSum X (m + j + 1) ω) hk

lemma finiteTailInf_le_partialSum (X : ℕ → Ω → ℝ) (m n k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) (ω : Ω) :
    finiteTailInf X m n ω ≤ partialSum X (m + k + 1) ω := by
  exact Finset.inf'_le (f := fun j => partialSum X (m + j + 1) ω) hk

lemma partialSum_mem_Icc_finiteTailInf_finiteTailSup (X : ℕ → Ω → ℝ) (m n k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) (ω : Ω) :
    partialSum X (m + k + 1) ω ∈ Set.Icc (finiteTailInf X m n ω) (finiteTailSup X m n ω) := by
  exact ⟨finiteTailInf_le_partialSum X m n k hk ω, partialSum_le_finiteTailSup X m n k hk ω⟩

lemma eventually_partialSum_le_finiteTailSup (X : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) :
    ∀ᶠ k in Filter.atTop, partialSum X (m + n + 1) ω ≤ finiteTailSup X m k ω := by
  refine Filter.eventually_atTop.2 ⟨n, ?_⟩
  intro k hk
  exact partialSum_le_finiteTailSup X m k n
    (Finset.mem_range.mpr <| Nat.lt_succ_of_le hk) ω

lemma eventually_finiteTailInf_le_partialSum (X : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) :
    ∀ᶠ k in Filter.atTop, finiteTailInf X m k ω ≤ partialSum X (m + n + 1) ω := by
  refine Filter.eventually_atTop.2 ⟨n, ?_⟩
  intro k hk
  exact finiteTailInf_le_partialSum X m k n
    (Finset.mem_range.mpr <| Nat.lt_succ_of_le hk) ω

lemma eventually_partialSum_mem_Icc_finiteTailInf_finiteTailSup
    (X : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) :
    ∀ᶠ k in Filter.atTop,
      partialSum X (m + n + 1) ω ∈ Set.Icc (finiteTailInf X m k ω) (finiteTailSup X m k ω) := by
  filter_upwards [eventually_finiteTailInf_le_partialSum X m n ω,
    eventually_partialSum_le_finiteTailSup X m n ω] with k hk₁ hk₂
  exact ⟨hk₁, hk₂⟩

lemma limsup_partialSum_tail_le_limsup_finiteTailSup
    (X : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω)
    (hcu : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun n => partialSum X (m + n + 1) ω))
    (hbu : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => finiteTailSup X m n ω)) :
    Filter.limsup (fun n => partialSum X (m + n + 1) ω) Filter.atTop ≤
      Filter.limsup (fun n => finiteTailSup X m n ω) Filter.atTop := by
  refine Filter.limsup_le_limsup (Filter.Eventually.of_forall ?_) hcu hbu
  intro n
  exact partialSum_le_finiteTailSup X m n n (by simp) ω

lemma liminf_finiteTailInf_le_liminf_partialSum_tail
    (X : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω)
    (hbu : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailInf X m n ω))
    (hcu : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun n => partialSum X (m + n + 1) ω)) :
    Filter.liminf (fun n => finiteTailInf X m n ω) Filter.atTop ≤
      Filter.liminf (fun n => partialSum X (m + n + 1) ω) Filter.atTop := by
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall ?_) hbu hcu
  intro n
  exact finiteTailInf_le_partialSum X m n n (by simp) ω

lemma limsup_sub_liminf_partialSum_tail_le_limsup_finiteTailSup_sub_liminf_finiteTailInf
    (X : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω)
    (hcu : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun n => partialSum X (m + n + 1) ω))
    (hbu : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => finiteTailSup X m n ω))
    (hbl : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailInf X m n ω))
    (hcl : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun n => partialSum X (m + n + 1) ω)) :
    Filter.limsup (fun n => partialSum X (m + n + 1) ω) Filter.atTop -
        Filter.liminf (fun n => partialSum X (m + n + 1) ω) Filter.atTop ≤
      Filter.limsup (fun n => finiteTailSup X m n ω) Filter.atTop -
        Filter.liminf (fun n => finiteTailInf X m n ω) Filter.atTop := by
  have hsup := limsup_partialSum_tail_le_limsup_finiteTailSup X m ω hcu hbu
  have hinf := liminf_finiteTailInf_le_liminf_partialSum_tail X m ω hbl hcl
  linarith

lemma finiteTailSup_mono (X : ℕ → Ω → ℝ) (m : ℕ) {n k : ℕ} (hnk : n ≤ k) (ω : Ω) :
    finiteTailSup X m n ω ≤ finiteTailSup X m k ω := by
  rw [finiteTailSup, Finset.sup'_le_iff]
  intro j hj
  exact partialSum_le_finiteTailSup X m k j
    (Finset.mem_range.mpr <|
      Nat.lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.succ_le_succ hnk)) ω

lemma finiteTailInf_anti (X : ℕ → Ω → ℝ) (m : ℕ) {n k : ℕ} (hnk : n ≤ k) (ω : Ω) :
    finiteTailInf X m k ω ≤ finiteTailInf X m n ω := by
  rw [finiteTailInf]
  refine Finset.le_inf' (s := Finset.range (n + 1)) (H := by simp)
    (f := fun j => partialSum X (m + j + 1) ω) ?_
  intro j hj
  exact finiteTailInf_le_partialSum X m k j
    (Finset.mem_range.mpr <|
      Nat.lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.succ_le_succ hnk)) ω

lemma finiteTailSup_sub_finiteTailInf_mono (X : ℕ → Ω → ℝ) (m : ℕ) {n k : ℕ}
    (hnk : n ≤ k) (ω : Ω) :
    finiteTailSup X m n ω - finiteTailInf X m n ω ≤
      (finiteTailSup X m k ω - finiteTailInf X m k ω) := by
  have hsup := finiteTailSup_mono X m hnk ω
  have hinf := finiteTailInf_anti X m hnk ω
  linarith

lemma finiteTailOscillationMax_mono (X : ℕ → Ω → ℝ) (m : ℕ) {n k : ℕ}
    (hnk : n ≤ k) (ω : Ω) :
    finiteTailOscillationMax X m n ω ≤ finiteTailOscillationMax X m k ω := by
  rw [finiteTailOscillationMax, Finset.sup'_le_iff]
  intro j hj
  rw [Finset.sup'_le_iff]
  intro l hl
  exact (le_finiteTailOscillationMax_iff X m k
    (|partialSum X (m + j + 1) ω - partialSum X (m + l + 1) ω|) ω).2
      ⟨j,
        Finset.mem_range.mpr <|
          Nat.lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.succ_le_succ hnk),
        l,
        Finset.mem_range.mpr <|
          Nat.lt_of_lt_of_le (Finset.mem_range.mp hl) (Nat.succ_le_succ hnk),
        le_rfl⟩

lemma finiteTailOscillationMax_le_liminf
    (X : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω)
    (hcu : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun k => finiteTailOscillationMax X m k ω))
    (hbu : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun k => finiteTailOscillationMax X m k ω)) :
    finiteTailOscillationMax X m n ω ≤
      Filter.liminf (fun k => finiteTailOscillationMax X m k ω) Filter.atTop := by
  exact le_liminf_of_monotone_nat' hcu hbu
    (fun a b hab => finiteTailOscillationMax_mono X m hab ω) n

lemma finiteTailSup_sub_finiteTailInf_le_finiteTailOscillationMax
    (X : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) :
    finiteTailSup X m n ω - finiteTailInf X m n ω ≤ finiteTailOscillationMax X m n ω := by
  obtain ⟨j, hj, hjEq⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (n + 1)) (H := by simp)
    (fun j => partialSum X (m + j + 1) ω)
  obtain ⟨k, hk, hkEq⟩ := Finset.exists_mem_eq_inf' (s := Finset.range (n + 1)) (H := by simp)
    (fun k => partialSum X (m + k + 1) ω)
  rw [finiteTailSup, finiteTailInf, hjEq, hkEq]
  refine (le_abs_self _).trans ?_
  exact (le_finiteTailOscillationMax_iff X m n
    (|partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω|) ω).2 ⟨j, hj, k, hk, le_rfl⟩

lemma finiteTailSup_sub_finiteTailInf_le_liminf_finiteTailOscillationMax
    (X : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω)
    (hcu : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun k => finiteTailOscillationMax X m k ω))
    (hbu : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun k => finiteTailOscillationMax X m k ω)) :
    finiteTailSup X m n ω - finiteTailInf X m n ω ≤
      Filter.liminf (fun k => finiteTailOscillationMax X m k ω) Filter.atTop := by
  exact (finiteTailSup_sub_finiteTailInf_le_finiteTailOscillationMax X m n ω).trans <|
    finiteTailOscillationMax_le_liminf X m n ω hcu hbu

lemma tendsto_finiteTailSup_ciSup
    (X : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω)
    (hbu : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => finiteTailSup X m n ω)) :
    Filter.Tendsto (fun n => finiteTailSup X m n ω) Filter.atTop
      (nhds (⨆ n : ℕ, finiteTailSup X m n ω)) := by
  refine tendsto_atTop_ciSup ?_ hbu.bddAbove_range
  intro n k hnk
  exact finiteTailSup_mono X m hnk ω

lemma tendsto_finiteTailInf_ciInf
    (X : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω)
    (hbl : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailInf X m n ω)) :
    Filter.Tendsto (fun n => finiteTailInf X m n ω) Filter.atTop
      (nhds (⨅ n : ℕ, finiteTailInf X m n ω)) := by
  refine tendsto_atTop_ciInf ?_ hbl.bddBelow_range
  intro n k hnk
  exact finiteTailInf_anti X m hnk ω

lemma limsup_finiteTailSup_eq_ciSup
    (X : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω)
    (hbu : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => finiteTailSup X m n ω)) :
    Filter.limsup (fun n => finiteTailSup X m n ω) Filter.atTop =
      ⨆ n : ℕ, finiteTailSup X m n ω := by
  exact (tendsto_finiteTailSup_ciSup X m ω hbu).limsup_eq

lemma liminf_finiteTailInf_eq_ciInf
    (X : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω)
    (hbl : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailInf X m n ω)) :
    Filter.liminf (fun n => finiteTailInf X m n ω) Filter.atTop =
      ⨅ n : ℕ, finiteTailInf X m n ω := by
  exact (tendsto_finiteTailInf_ciInf X m ω hbl).liminf_eq

lemma limsup_finiteTailSup_sub_liminf_finiteTailInf_eq_ciSup_sub_ciInf
    (X : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω)
    (hbu : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => finiteTailSup X m n ω))
    (hbl : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailInf X m n ω)) :
    Filter.limsup (fun n => finiteTailSup X m n ω) Filter.atTop -
        Filter.liminf (fun n => finiteTailInf X m n ω) Filter.atTop =
      (⨆ n : ℕ, finiteTailSup X m n ω) - (⨅ n : ℕ, finiteTailInf X m n ω) := by
  rw [limsup_finiteTailSup_eq_ciSup X m ω hbu, liminf_finiteTailInf_eq_ciInf X m ω hbl]

lemma ciSup_finiteTailSup_sub_ciInf_finiteTailInf_le_liminf_finiteTailOscillationMax
    (X : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω)
    (hbu : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => finiteTailSup X m n ω))
    (hbl : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailInf X m n ω))
    (hcu : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailOscillationMax X m n ω))
    (hbuOsc : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailOscillationMax X m n ω)) :
    (⨆ n : ℕ, finiteTailSup X m n ω) - (⨅ n : ℕ, finiteTailInf X m n ω) ≤
      Filter.liminf (fun n => finiteTailOscillationMax X m n ω) Filter.atTop := by
  let d : ℕ → ℝ := fun n => finiteTailSup X m n ω - finiteTailInf X m n ω
  have hd_nonneg : ∀ n, 0 ≤ d n := by
    intro n
    have hInf : finiteTailInf X m n ω ≤ partialSum X (m + 1) ω := by
      exact finiteTailInf_le_partialSum X m n 0 (by simp) ω
    have hSup : partialSum X (m + 1) ω ≤ finiteTailSup X m n ω := by
      exact partialSum_le_finiteTailSup X m n 0 (by simp) ω
    dsimp [d]
    linarith
  have hd_le : ∀ n, d n ≤ Filter.liminf (fun k => finiteTailOscillationMax X m k ω) Filter.atTop := by
    intro n
    simpa [d] using
      finiteTailSup_sub_finiteTailInf_le_liminf_finiteTailOscillationMax X m n ω hcu hbuOsc
  have hcu_d : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop d := by
    exact Filter.isCoboundedUnder_le_of_le Filter.atTop hd_nonneg
  have hbu_d : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop d := by
    exact Filter.isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall hd_le)
  have hlimsup_d :
      Filter.limsup d Filter.atTop ≤
        Filter.liminf (fun n => finiteTailOscillationMax X m n ω) Filter.atTop := by
    apply limsup_le_of_eventually_le_nat' hcu_d hbu_d
    exact ⟨0, fun n _ => hd_le n⟩
  have hd_tendsto :
      Filter.Tendsto d Filter.atTop
        (nhds ((⨆ n : ℕ, finiteTailSup X m n ω) - (⨅ n : ℕ, finiteTailInf X m n ω))) := by
    simpa [d] using (tendsto_finiteTailSup_ciSup X m ω hbu).sub
      (tendsto_finiteTailInf_ciInf X m ω hbl)
  have hd_eq :
      Filter.limsup d Filter.atTop =
        (⨆ n : ℕ, finiteTailSup X m n ω) - (⨅ n : ℕ, finiteTailInf X m n ω) := by
    exact hd_tendsto.limsup_eq
  simpa [hd_eq] using hlimsup_d

lemma limsup_sub_liminf_partialSum_tail_le_liminf_finiteTailOscillationMax
    (X : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω)
    (hcu : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun n => partialSum X (m + n + 1) ω))
    (hbu : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => finiteTailSup X m n ω))
    (hbl : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailInf X m n ω))
    (hcl : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun n => partialSum X (m + n + 1) ω))
    (hcuOsc : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailOscillationMax X m n ω))
    (hbuOsc : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailOscillationMax X m n ω)) :
    Filter.limsup (fun n => partialSum X (m + n + 1) ω) Filter.atTop -
        Filter.liminf (fun n => partialSum X (m + n + 1) ω) Filter.atTop ≤
      Filter.liminf (fun n => finiteTailOscillationMax X m n ω) Filter.atTop := by
  refine (limsup_sub_liminf_partialSum_tail_le_limsup_finiteTailSup_sub_liminf_finiteTailInf
      X m ω hcu hbu hbl hcl).trans ?_
  rw [limsup_finiteTailSup_sub_liminf_finiteTailInf_eq_ciSup_sub_ciInf X m ω hbu hbl]
  exact ciSup_finiteTailSup_sub_ciInf_finiteTailInf_le_liminf_finiteTailOscillationMax
    X m ω hbu hbl hcuOsc hbuOsc

lemma finiteTailOscillationMax_le_two_mul_partialSumMax_tail
    (X : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) :
    finiteTailOscillationMax X m n ω ≤ 2 * partialSumMax (fun l => X (m + 1 + l)) n ω := by
  rw [finiteTailOscillationMax, Finset.sup'_le_iff]
  intro j hj
  rw [Finset.sup'_le_iff]
  intro k hk
  exact abs_sub_partialSum_le_two_mul_partialSumMax_tail X m n j k hj hk ω

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

lemma tail_pair_event_subset_two_mul_partialSumMax_event (X : ℕ → Ω → ℝ) (m n j k : ℕ)
    (hj : j ∈ Finset.range (n + 1)) (hk : k ∈ Finset.range (n + 1)) (ε : ℝ) :
    {ω | ε ≤ |partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω|} ⊆
      {ω | ε ≤ 2 * partialSumMax (fun l => X (m + 1 + l)) n ω} := by
  intro ω hω
  exact le_trans hω (abs_sub_partialSum_le_two_mul_partialSumMax_tail X m n j k hj hk ω)

lemma finite_tail_oscillation_event_eq_biUnion (X : ℕ → Ω → ℝ) (m n : ℕ) (ε : ℝ) :
    {ω | ∃ j ∈ Finset.range (n + 1), ∃ k ∈ Finset.range (n + 1),
        ε ≤ |partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω|} =
      ⋃ j ∈ Finset.range (n + 1), ⋃ k ∈ Finset.range (n + 1),
        {ω | ε ≤ |partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω|} := by
  ext ω
  simp

lemma finite_tail_oscillation_event_subset_two_mul_partialSumMax_event
    (X : ℕ → Ω → ℝ) (m n : ℕ) (ε : ℝ) :
    {ω | ∃ j ∈ Finset.range (n + 1), ∃ k ∈ Finset.range (n + 1),
        ε ≤ |partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω|} ⊆
      {ω | ε ≤ 2 * partialSumMax (fun l => X (m + 1 + l)) n ω} := by
  intro ω hω
  rcases hω with ⟨j, hj, k, hk, hω⟩
  exact tail_pair_event_subset_two_mul_partialSumMax_event X m n j k hj hk ε hω

lemma finiteTailOscillationMax_event_eq (X : ℕ → Ω → ℝ) (m n : ℕ) (ε : ℝ) :
    {ω | ε ≤ finiteTailOscillationMax X m n ω} =
      {ω | ∃ j ∈ Finset.range (n + 1), ∃ k ∈ Finset.range (n + 1),
        ε ≤ |partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω|} := by
  ext ω
  exact le_finiteTailOscillationMax_iff X m n ε ω

lemma finiteTailOscillationMax_event_subset_two_mul_partialSumMax_event
    (X : ℕ → Ω → ℝ) (m n : ℕ) (ε : ℝ) :
    {ω | ε ≤ finiteTailOscillationMax X m n ω} ⊆
      {ω | ε ≤ 2 * partialSumMax (fun l => X (m + 1 + l)) n ω} := by
  intro ω hω
  exact le_trans hω (finiteTailOscillationMax_le_two_mul_partialSumMax_tail X m n ω)

lemma event_le_liminf_finiteTailOscillationMax_subset_iUnion
    (X : ℕ → Ω → ℝ) (m : ℕ) {η ε : ℝ} (hηε : η < ε) :
    {ω | ε ≤ Filter.liminf (fun n => finiteTailOscillationMax X m n ω) Filter.atTop} ⊆
      ⋃ n : ℕ, {ω | η ≤ finiteTailOscillationMax X m n ω} := by
  intro ω hω
  have hbuOsc : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailOscillationMax X m n ω) := by
    exact Filter.isBoundedUnder_of ⟨0, fun k => finiteTailOscillationMax_nonneg X m k ω⟩
  have hlt : ∀ᶠ n : ℕ in Filter.atTop, η < finiteTailOscillationMax X m n ω := by
    exact Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le hηε hω) hbuOsc
  simp only [Filter.eventually_atTop] at hlt
  rcases hlt with ⟨N, hN⟩
  refine Set.mem_iUnion.2 ⟨N, ?_⟩
  exact le_of_lt (hN N le_rfl)

lemma tail_oscillation_event_subset_iUnion_finiteTailOscillationMax_event
    (X : ℕ → Ω → ℝ) (m : ℕ) {η ε : ℝ} (hηε : η < ε)
    (hcu : ∀ ω, Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun n => partialSum X (m + n + 1) ω))
    (hbu : ∀ ω, Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => finiteTailSup X m n ω))
    (hbl : ∀ ω, Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailInf X m n ω))
    (hcl : ∀ ω, Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun n => partialSum X (m + n + 1) ω))
    (hcuOsc : ∀ ω, Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailOscillationMax X m n ω))
    (hbuOsc : ∀ ω, Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailOscillationMax X m n ω)) :
    {ω | ε ≤ Filter.limsup (fun n => partialSum X (m + n + 1) ω) Filter.atTop -
        Filter.liminf (fun n => partialSum X (m + n + 1) ω) Filter.atTop} ⊆
      ⋃ n : ℕ, {ω | η ≤ finiteTailOscillationMax X m n ω} := by
  intro ω hω
  have hliminf :
      ε ≤ Filter.liminf (fun n => finiteTailOscillationMax X m n ω) Filter.atTop := by
    exact hω.trans <|
      limsup_sub_liminf_partialSum_tail_le_liminf_finiteTailOscillationMax
        X m ω (hcu ω) (hbu ω) (hbl ω) (hcl ω) (hcuOsc ω) (hbuOsc ω)
  exact event_le_liminf_finiteTailOscillationMax_subset_iUnion X m hηε hliminf

lemma finiteTailSup_sub_finiteTailInf_event_subset_finiteTailOscillationMax_event
    (X : ℕ → Ω → ℝ) (m n : ℕ) (ε : ℝ) :
    {ω | ε ≤ finiteTailSup X m n ω - finiteTailInf X m n ω} ⊆
      {ω | ε ≤ finiteTailOscillationMax X m n ω} := by
  intro ω hω
  exact le_trans hω (finiteTailSup_sub_finiteTailInf_le_finiteTailOscillationMax X m n ω)

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

lemma measure_finite_tail_oscillation_event_le_measure_two_mul_partialSumMax_event
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ) (m n : ℕ) (ε : ℝ) :
    μ {ω | ∃ j ∈ Finset.range (n + 1), ∃ k ∈ Finset.range (n + 1),
      ε ≤ |partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω|} ≤
      μ {ω | ε ≤ 2 * partialSumMax (fun l => X (m + 1 + l)) n ω} := by
  exact measure_mono (finite_tail_oscillation_event_subset_two_mul_partialSumMax_event X m n ε)

lemma measure_finiteTailOscillationMax_event_le_measure_two_mul_partialSumMax_event
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ) (m n : ℕ) (ε : ℝ) :
    μ {ω | ε ≤ finiteTailOscillationMax X m n ω} ≤
      μ {ω | ε ≤ 2 * partialSumMax (fun l => X (m + 1 + l)) n ω} := by
  exact measure_mono (finiteTailOscillationMax_event_subset_two_mul_partialSumMax_event X m n ε)

lemma measure_finiteTailSup_sub_finiteTailInf_event_le_measure_finiteTailOscillationMax_event
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ) (m n : ℕ) (ε : ℝ) :
    μ {ω | ε ≤ finiteTailSup X m n ω - finiteTailInf X m n ω} ≤
      μ {ω | ε ≤ finiteTailOscillationMax X m n ω} := by
  exact measure_mono (finiteTailSup_sub_finiteTailInf_event_subset_finiteTailOscillationMax_event
    X m n ε)

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

lemma measure_partialSumMax_ge_le_variance_partialSum_div_sq_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    μ {ω | ε ≤ partialSumMax X (n + 1) ω} ≤
      ENNReal.ofReal (variance (partialSum X (n + 1)) μ / ε ^ 2) := by
  let ε' : NNReal := ⟨ε, hε.le⟩
  have hbound :=
    smul_measure_partialSumMax_ge_le_variance_partialSum_of_mean_zero
      (μ := μ) X hX hLp hindep hmean ε' n
  rw [ENNReal.smul_def, smul_eq_mul] at hbound
  have hdiv :
      μ {ω | ε ≤ partialSumMax X (n + 1) ω} ≤
        ENNReal.ofReal (variance (partialSum X (n + 1)) μ) / ((ε' : ENNReal) ^ 2) := by
    rw [ENNReal.le_div_iff_mul_le]
    · simpa [ε', mul_comm, mul_left_comm, mul_assoc] using hbound
    · left
      have hε' : (ε' : ENNReal) = ENNReal.ofReal ε := by
        simpa [ε'] using (ENNReal.ofReal_eq_coe_nnreal hε.le).symm
      rw [hε']
      simpa using (ENNReal.pow_ne_zero ((ENNReal.ofReal_ne_zero_iff).2 hε) 2)
    · right
      exact ENNReal.ofReal_ne_top
  refine hdiv.trans_eq ?_
  rw [show ((ε' : ENNReal) ^ 2) = ENNReal.ofReal (ε ^ 2) by
    have hε' : (ε' : ENNReal) = ENNReal.ofReal ε := by
      simpa [ε'] using (ENNReal.ofReal_eq_coe_nnreal hε.le).symm
    rw [hε']
    exact (ENNReal.ofReal_pow hε.le 2).symm]
  rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_ne_zero hε.ne.symm)]

/-- Kolmogorov's inequality in 0-indexed form:
`partialSum X (k + 1)` plays the role of `S_k` in the wiki statement. -/
theorem kolmogorov_inequality
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    μ {ω | ε ≤ (Finset.range (n + 1)).sup' (by simp)
      (fun k => |partialSum X (k + 1) ω|)} ≤
      ENNReal.ofReal (variance (partialSum X (n + 1)) μ / ε ^ 2) := by
  simpa [partialSumMax_succ_eq_sup_abs_partialSum_succ] using
    measure_partialSumMax_ge_le_variance_partialSum_div_sq_of_mean_zero
      (μ := μ) X hX hLp hindep hmean hε n

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

lemma measure_partialSumMax_ge_le_sum_variance_div_sq_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    μ {ω | ε ≤ partialSumMax X (n + 1) ω} ≤
      ENNReal.ofReal ((∑ k ∈ Finset.range (n + 1), variance (X k) μ) / ε ^ 2) := by
  let ε' : NNReal := ⟨ε, hε.le⟩
  have hbound :=
    smul_measure_partialSumMax_ge_le_sum_variance_of_mean_zero
      (μ := μ) X hX hLp hindep hmean ε' n
  rw [ENNReal.smul_def, smul_eq_mul] at hbound
  have hdiv :
      μ {ω | ε ≤ partialSumMax X (n + 1) ω} ≤
        (ENNReal.ofReal (∑ k ∈ Finset.range (n + 1), variance (X k) μ)) /
          ((ε' : ENNReal) ^ 2) := by
    rw [ENNReal.le_div_iff_mul_le]
    · simpa [ε', mul_comm, mul_left_comm, mul_assoc] using hbound
    · left
      have hε' : (ε' : ENNReal) = ENNReal.ofReal ε := by
        simpa [ε'] using (ENNReal.ofReal_eq_coe_nnreal hε.le).symm
      rw [hε']
      simpa using (ENNReal.pow_ne_zero ((ENNReal.ofReal_ne_zero_iff).2 hε) 2)
    · right
      exact ENNReal.ofReal_ne_top
  refine hdiv.trans_eq ?_
  rw [show ((ε' : ENNReal) ^ 2) = ENNReal.ofReal (ε ^ 2) by
    have hε' : (ε' : ENNReal) = ENNReal.ofReal ε := by
      simpa [ε'] using (ENNReal.ofReal_eq_coe_nnreal hε.le).symm
    rw [hε']
    exact (ENNReal.ofReal_pow hε.le 2).symm]
  rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_ne_zero hε.ne.symm)]

/-- Kolmogorov's inequality with the variance of the terminal partial sum rewritten
as the sum of the individual variances. This matches the usual independent mean-zero statement,
up to the repository's 0-indexing convention. -/
theorem kolmogorov_inequality_sum_variance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    μ {ω | ε ≤ (Finset.range (n + 1)).sup' (by simp)
      (fun k => |partialSum X (k + 1) ω|)} ≤
      ENNReal.ofReal ((∑ k ∈ Finset.range (n + 1), variance (X k) μ) / ε ^ 2) := by
  simpa [partialSumMax_succ_eq_sup_abs_partialSum_succ] using
    measure_partialSumMax_ge_le_sum_variance_div_sq_of_mean_zero
      (μ := μ) X hX hLp hindep hmean hε n

lemma measure_partialSumMax_tail_ge_le_sum_variance_div_sq_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ partialSumMax (fun j => X (m + 1 + j)) (n + 1) ω} ≤
      ENNReal.ofReal ((∑ j ∈ Finset.range (n + 1), variance (X (m + 1 + j)) μ) / ε ^ 2) := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    measure_partialSumMax_ge_le_sum_variance_div_sq_of_mean_zero
      (μ := μ) (X := fun j => X (m + 1 + j))
      (hX := fun j => hX (m + 1 + j))
      (hLp := fun j => hLp (m + 1 + j))
      (hindep := hindep.precomp (g := fun j => m + 1 + j) <| by
        intro a b hab
        exact Nat.add_left_cancel (n := m + 1) <| by
          simpa [Nat.add_assoc] using hab)
      (hmean := fun j => hmean (m + 1 + j))
      hε n

lemma measure_partialSumMax_tail_ge_le_sum_variance_div_sq_of_mean_zero'
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ partialSumMax (fun j => X (m + 1 + j)) n ω} ≤
      ENNReal.ofReal ((∑ j ∈ Finset.range n, variance (X (m + 1 + j)) μ) / ε ^ 2) := by
  cases n with
  | zero =>
      have hset : {ω | ε ≤ partialSumMax (fun j => X (m + 1 + j)) 0 ω} = (∅ : Set Ω) := by
        ext ω
        simp [partialSumMax, not_le_of_gt hε]
      rw [hset]
      simp
  | succ n =>
      simpa using
        measure_partialSumMax_tail_ge_le_sum_variance_div_sq_of_mean_zero
          (μ := μ) X m n hX hLp hindep hmean hε

lemma measure_event_two_mul_partialSumMax_tail_le_four_mul_variance_div_sq_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ 2 * partialSumMax (fun j => X (m + 1 + j)) n ω} ≤
      ENNReal.ofReal
        (4 * (∑ j ∈ Finset.range n, variance (X (m + 1 + j)) μ) / ε ^ 2) := by
  have hε2 : 0 < ε / 2 := by
    linarith
  rw [event_two_mul_partialSumMax_ge_eq]
  have hdiv :
      (∑ j ∈ Finset.range n, variance (X (m + 1 + j)) μ) / (ε / 2) ^ 2 =
        4 * (∑ j ∈ Finset.range n, variance (X (m + 1 + j)) μ) / ε ^ 2 := by
    by_cases hε0 : ε = 0
    · simp [hε0]
    · field_simp [hε0]
      ring
  simpa [hdiv] using
    measure_partialSumMax_tail_ge_le_sum_variance_div_sq_of_mean_zero'
      (μ := μ) X m n hX hLp hindep hmean (ε := ε / 2) hε2

lemma measure_finiteTailOscillationMax_event_le_four_mul_variance_div_sq_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ finiteTailOscillationMax X m n ω} ≤
      ENNReal.ofReal
        (4 * (∑ j ∈ Finset.range n, variance (X (m + 1 + j)) μ) / ε ^ 2) := by
  refine (measure_finiteTailOscillationMax_event_le_measure_two_mul_partialSumMax_event
      (μ := μ) X m n ε).trans ?_
  exact measure_event_two_mul_partialSumMax_tail_le_four_mul_variance_div_sq_of_mean_zero
    (μ := μ) X m n hX hLp hindep hmean hε

noncomputable def tailVarianceBound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (η : ℝ) (m : ℕ) : ENNReal :=
  ⨆ n : ℕ, ENNReal.ofReal (4 * (∑ j ∈ Finset.range n, variance (X (m + 1 + j)) μ) / η ^ 2)

lemma measure_tail_oscillation_event_le_iSup_four_mul_variance_div_sq_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m : ℕ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    {η ε : ℝ} (hη : 0 < η) (hηε : η < ε)
    (hcu : ∀ ω, Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun n => partialSum X (m + n + 1) ω))
    (hbu : ∀ ω, Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => finiteTailSup X m n ω))
    (hbl : ∀ ω, Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailInf X m n ω))
    (hcl : ∀ ω, Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun n => partialSum X (m + n + 1) ω))
    (hcuOsc : ∀ ω, Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailOscillationMax X m n ω))
    (hbuOsc : ∀ ω, Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => finiteTailOscillationMax X m n ω)) :
    μ {ω | ε ≤ Filter.limsup (fun n => partialSum X (m + n + 1) ω) Filter.atTop -
        Filter.liminf (fun n => partialSum X (m + n + 1) ω) Filter.atTop} ≤
      tailVarianceBound (μ := μ) X η m := by
  let s : ℕ → Set Ω := fun n => {ω | η ≤ finiteTailOscillationMax X m n ω}
  have hs_mono : Monotone s := by
    intro n k hnk ω hω
    exact le_trans hω (finiteTailOscillationMax_mono X m hnk ω)
  calc
    μ {ω | ε ≤ Filter.limsup (fun n => partialSum X (m + n + 1) ω) Filter.atTop -
        Filter.liminf (fun n => partialSum X (m + n + 1) ω) Filter.atTop} ≤
        μ (⋃ n : ℕ, s n) := by
      refine measure_mono ?_
      exact tail_oscillation_event_subset_iUnion_finiteTailOscillationMax_event
        X m hηε hcu hbu hbl hcl hcuOsc hbuOsc
    _ = ⨆ n : ℕ, μ (s n) := by
      exact hs_mono.measure_iUnion
    _ ≤ tailVarianceBound (μ := μ) X η m := by
      refine iSup_le fun n => ?_
      refine (measure_finiteTailOscillationMax_event_le_four_mul_variance_div_sq_of_mean_zero
          (μ := μ) X m n hX hLp hindep hmean (ε := η) hη).trans ?_
      exact le_iSup (fun n => ENNReal.ofReal
        (4 * (∑ j ∈ Finset.range n, variance (X (m + 1 + j)) μ) / η ^ 2)) n

lemma iSup_four_mul_variance_div_sq_le_ofReal_tsum_variance_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m : ℕ)
    (hvar : Summable (fun n => variance (X n) μ))
    {η : ℝ} (hη : 0 < η) :
    tailVarianceBound (μ := μ) X η m ≤
      ENNReal.ofReal (4 * (∑' j, variance (X (m + 1 + j)) μ) / η ^ 2) := by
  let v : ℕ → ℝ := fun n => variance (X n) μ
  have hvar_tail : Summable (fun j => variance (X (m + 1 + j)) μ) := by
    simpa [v, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ((_root_.summable_nat_add_iff (f := v) (m + 1)).2 hvar)
  refine iSup_le fun n => ?_
  apply ENNReal.ofReal_le_ofReal
  refine div_le_div_of_nonneg_right ?_ (sq_pos_of_pos hη).le
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact hvar_tail.sum_le_tsum (Finset.range n) fun j _ => variance_nonneg (X (m + 1 + j)) μ

lemma tendsto_iSup_four_mul_variance_div_sq_of_summable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hvar : Summable (fun n => variance (X n) μ))
    {η : ℝ} (hη : 0 < η) :
    Filter.Tendsto (fun m => tailVarianceBound (μ := μ) X η m) Filter.atTop (nhds 0) := by
  have htail :
      Filter.Tendsto (fun m => ∑' j, variance (X (m + 1 + j)) μ) Filter.atTop (nhds 0) := by
    convert ((_root_.tendsto_sum_nat_add (f := fun n => variance (X n) μ)).comp
      (Filter.tendsto_add_atTop_nat 1)) using 1
    ext m
    congr 1
    ext j
    simp [Nat.add_left_comm, Nat.add_comm]
  have hupper :
      Filter.Tendsto
        (fun m => ENNReal.ofReal (4 * (∑' j, variance (X (m + 1 + j)) μ) / η ^ 2))
        Filter.atTop (nhds 0) := by
    have hreal :
        Filter.Tendsto
          (fun m => 4 * (∑' j, variance (X (m + 1 + j)) μ) / η ^ 2)
          Filter.atTop (nhds 0) := by
      have hscaled : Filter.Tendsto
          (fun m => ((4 : ℝ) / η ^ 2) * (∑' j, variance (X (m + 1 + j)) μ))
          Filter.atTop (nhds (((4 : ℝ) / η ^ 2) * 0)) := by
        exact htail.const_mul ((4 : ℝ) / η ^ 2)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
    simpa [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun m => by exact bot_le) ?_
  intro m
  exact iSup_four_mul_variance_div_sq_le_ofReal_tsum_variance_tail (μ := μ) X m hvar hη

/-- The bad event that some two partial sums in the tail starting at `m + 1`
are at least `ε` apart. -/
def tailOscillationEvent (X : ℕ → Ω → ℝ) (m : ℕ) (ε : ℝ) : Set Ω :=
  {ω | ∃ j k, ε ≤ |partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω|}

lemma finiteTailOscillationMax_measurable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (m n : ℕ) (hX : ∀ k, Measurable (X k)) :
    Measurable (finiteTailOscillationMax X m n) := by
  simpa [finiteTailOscillationMax] using
    (Finset.measurable_range_sup'' (n := n)
      (f := fun j ω =>
        (Finset.range (n + 1)).sup' (by simp)
          (fun k => |partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω|))
      (fun j hj =>
        Finset.measurable_range_sup'' (n := n)
          (f := fun k ω =>
            |partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω|)
          (fun k hk =>
            continuous_abs.measurable.comp <|
              (partialSum_measurable X (m + j + 1) hX).sub
                (partialSum_measurable X (m + k + 1) hX))))

lemma measurableSet_finiteTailOscillationMax_event {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (m n : ℕ) (ε : ℝ) (hX : ∀ k, Measurable (X k)) :
    MeasurableSet {ω | ε ≤ finiteTailOscillationMax X m n ω} := by
  exact measurableSet_le measurable_const
    (finiteTailOscillationMax_measurable X m n hX)

lemma tailOscillationEvent_eq_iUnion_finiteTailOscillationMax_event
    (X : ℕ → Ω → ℝ) (m : ℕ) (ε : ℝ) :
    tailOscillationEvent X m ε = ⋃ n : ℕ, {ω | ε ≤ finiteTailOscillationMax X m n ω} := by
  ext ω
  constructor
  · rintro ⟨j, k, hω⟩
    refine Set.mem_iUnion.2 ⟨max j k, ?_⟩
    exact (le_finiteTailOscillationMax_iff X m (max j k) ε ω).2
      ⟨j, Finset.mem_range.mpr <| Nat.lt_succ_of_le <| le_max_left _ _,
        k, Finset.mem_range.mpr <| Nat.lt_succ_of_le <| le_max_right _ _, hω⟩
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
    rcases (le_finiteTailOscillationMax_iff X m n ε ω).1 hn with ⟨j, hj, k, hk, hjk⟩
    exact ⟨j, k, hjk⟩

lemma measurableSet_tailOscillationEvent {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (m : ℕ) (ε : ℝ) (hX : ∀ k, Measurable (X k)) :
    MeasurableSet (tailOscillationEvent X m ε) := by
  rw [tailOscillationEvent_eq_iUnion_finiteTailOscillationMax_event]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_finiteTailOscillationMax_event X m n ε hX

lemma measure_tailOscillationEvent_le_tailVarianceBound_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m : ℕ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    {ε : ℝ} (hε : 0 < ε) :
    μ (tailOscillationEvent X m ε) ≤ tailVarianceBound (μ := μ) X ε m := by
  let s : ℕ → Set Ω := fun n => {ω | ε ≤ finiteTailOscillationMax X m n ω}
  have hs_mono : Monotone s := by
    intro n k hnk ω hω
    exact le_trans hω (finiteTailOscillationMax_mono X m hnk ω)
  calc
    μ (tailOscillationEvent X m ε) = μ (⋃ n : ℕ, s n) := by
      rw [tailOscillationEvent_eq_iUnion_finiteTailOscillationMax_event]
    _ = ⨆ n : ℕ, μ (s n) := by
      exact hs_mono.measure_iUnion
    _ ≤ tailVarianceBound (μ := μ) X ε m := by
      refine iSup_le fun n => ?_
      refine (measure_finiteTailOscillationMax_event_le_four_mul_variance_div_sq_of_mean_zero
          (μ := μ) X m n hX hLp hindep hmean (ε := ε) hε).trans ?_
      exact le_iSup
        (fun n => ENNReal.ofReal
          (4 * (∑ j ∈ Finset.range n, variance (X (m + 1 + j)) μ) / ε ^ 2)) n

lemma tailOscillationEvent_antitone (X : ℕ → Ω → ℝ) (ε : ℝ) :
    Antitone (fun m => tailOscillationEvent X m ε) := by
  intro m n hmn ω hω
  rcases hω with ⟨j, k, hω⟩
  rcases Nat.exists_eq_add_of_le hmn with ⟨d, rfl⟩
  refine ⟨d + j, d + k, ?_⟩
  simpa [tailOscillationEvent, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hω

lemma measure_iInter_tailOscillationEvent_eq_zero_of_summable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    (hvar : Summable (fun n => variance (X n) μ))
    {ε : ℝ} (hε : 0 < ε) :
    μ (⋂ m : ℕ, tailOscillationEvent X m ε) = 0 := by
  let s : ℕ → Set Ω := fun m => tailOscillationEvent X m ε
  have hs_meas : ∀ m, NullMeasurableSet (s m) μ := by
    intro m
    exact (measurableSet_tailOscillationEvent X m ε (fun k => (hX k).measurable)).nullMeasurableSet
  have hs_anti : Antitone s := tailOscillationEvent_antitone X ε
  have hμ_tendsto :
      Filter.Tendsto (fun m => μ (s m)) Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_iSup_four_mul_variance_div_sq_of_summable (μ := μ) X hvar hε)
      (fun m => by exact bot_le) ?_
    intro m
    exact measure_tailOscillationEvent_le_tailVarianceBound_of_mean_zero
      (μ := μ) X m hX hLp hindep hmean hε
  have hμ_iInter :
      Filter.Tendsto (fun m => μ (s m)) Filter.atTop (nhds (μ (⋂ m : ℕ, s m))) := by
    refine tendsto_measure_iInter_atTop hs_meas hs_anti ?_
    exact ⟨0, measure_ne_top μ (s 0)⟩
  exact tendsto_nhds_unique hμ_iInter hμ_tendsto

lemma ae_eventually_pairwise_lt_of_summable_variance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    (hvar : Summable (fun n => variance (X n) μ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∃ N, ∀ j k,
      |partialSum X (N + j + 1) ω - partialSum X (N + k + 1) ω| < ε := by
  have hzero :
      μ (⋂ m : ℕ, tailOscillationEvent X m ε) = 0 :=
    measure_iInter_tailOscillationEvent_eq_zero_of_summable
      (μ := μ) X hX hLp hindep hmean hvar hε
  have hAE : ∀ᵐ ω ∂μ, ω ∉ ⋂ m : ℕ, tailOscillationEvent X m ε := by
    exact (measure_eq_zero_iff_ae_notMem).1 hzero
  filter_upwards [hAE] with ω hω
  simpa [tailOscillationEvent, not_exists, not_le] using hω

lemma ae_cauchySeq_partialSum_of_summable_variance_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    (hvar : Summable (fun n => variance (X n) μ)) :
    ∀ᵐ ω ∂μ, CauchySeq (fun n => partialSum X n ω) := by
  have hscales :
      ∀ n : ℕ, ∀ᵐ ω ∂μ, ∃ N, ∀ j k,
        |partialSum X (N + j + 1) ω - partialSum X (N + k + 1) ω| < 1 / (n + 1 : ℝ) := by
    intro n
    exact ae_eventually_pairwise_lt_of_summable_variance
      (μ := μ) X hX hLp hindep hmean hvar (show 0 < 1 / (n + 1 : ℝ) by positivity)
  have hAEall :
      ∀ᵐ ω ∂μ, ∀ n : ℕ, ∃ N, ∀ j k,
        |partialSum X (N + j + 1) ω - partialSum X (N + k + 1) ω| < 1 / (n + 1 : ℝ) :=
    (ae_all_iff.2 hscales)
  filter_upwards [hAEall] with ω hω
  refine Metric.cauchySeq_iff.2 ?_
  intro ε hε
  rcases exists_nat_one_div_lt hε with ⟨n, hn⟩
  rcases hω n with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro a ha b hb
  rcases Nat.exists_eq_add_of_le ha with ⟨j, rfl⟩
  rcases Nat.exists_eq_add_of_le hb with ⟨k, rfl⟩
  have hsmall : |partialSum X (N + j + 1) ω - partialSum X (N + k + 1) ω| < ε :=
    lt_trans (hN j k) hn
  simpa [Real.dist_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsmall

theorem ae_exists_tendsto_partialSum_of_summable_variance_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    (hvar : Summable (fun n => variance (X n) μ)) :
    ∀ᵐ ω ∂μ, ∃ x : ℝ, Filter.Tendsto (fun n => partialSum X n ω) Filter.atTop (nhds x) := by
  filter_upwards
    [ae_cauchySeq_partialSum_of_summable_variance_of_mean_zero
      (μ := μ) X hX hLp hindep hmean hvar] with ω hω
  exact cauchySeq_tendsto_of_complete hω

/-- The centered version of a sequence of real random variables. -/
noncomputable def centered {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun n ω => X n ω - μ[X n]

@[simp] lemma centered_apply {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    centered μ X n ω = X n ω - μ[X n] := rfl

lemma centered_stronglyMeasurable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hX : ∀ k, StronglyMeasurable (X k)) :
    ∀ k, StronglyMeasurable (centered μ X k) := by
  intro k
  exact (hX k).sub stronglyMeasurable_const

lemma centered_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (hLp : ∀ k, MemLp (X k) 2 μ) :
    ∀ k, MemLp (centered μ X k) 2 μ := by
  intro k
  exact (hLp k).sub (memLp_const (μ[X k]))

lemma centered_iIndepFun {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hindep : iIndepFun X μ) :
    iIndepFun (centered μ X) μ := by
  simpa [centered, Function.comp] using
    hindep.comp (fun k x => x - μ[X k]) (fun k => measurable_id.sub measurable_const)

lemma integral_centered_eq_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hLp : ∀ k, MemLp (X k) 2 μ) :
    ∀ k, μ[centered μ X k] = 0 := by
  intro k
  simp [centered]
  rw [integral_sub ((hLp k).integrable (by norm_num)) (integrable_const _)]
  simp [integral_const]

lemma variance_centered_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, StronglyMeasurable (X k)) :
    ∀ k, variance (centered μ X k) μ = variance (X k) μ := by
  intro k
  simpa [centered] using variance_sub_const (μ := μ) ((hX k).aestronglyMeasurable) (μ[X k])

lemma summable_variance_centered {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, StronglyMeasurable (X k))
    (hvar : Summable (fun n => variance (X n) μ)) :
    Summable (fun n => variance (centered μ X n) μ) := by
  refine hvar.congr ?_
  intro n
  exact (variance_centered_eq (μ := μ) X hX n).symm

lemma partialSum_centered_eq_sub_sum_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    partialSum (centered μ X) n ω =
      partialSum X n ω - ∑ i ∈ Finset.range n, μ[X i] := by
  calc
    partialSum (centered μ X) n ω = ∑ i ∈ Finset.range n, (X i ω - μ[X i]) := by
      simp [partialSum, centered]
    _ = (∑ i ∈ Finset.range n, X i ω) - ∑ i ∈ Finset.range n, μ[X i] := by
      rw [Finset.sum_sub_distrib]
    _ = partialSum X n ω - ∑ i ∈ Finset.range n, μ[X i] := by
      simp [partialSum]

lemma partialSum_eq_partialSum_centered_add_sum_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    partialSum X n ω =
      partialSum (centered μ X) n ω + ∑ i ∈ Finset.range n, μ[X i] := by
  rw [partialSum_centered_eq_sub_sum_integral (μ := μ) X n ω]
  ring

theorem ae_exists_tendsto_partialSum_of_summable_mean_of_summable_variance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ)
    (hmean : Summable (fun n => μ[X n]))
    (hvar : Summable (fun n => variance (X n) μ)) :
    ∀ᵐ ω ∂μ, ∃ x : ℝ, Filter.Tendsto (fun n => partialSum X n ω) Filter.atTop (nhds x) := by
  let Y : ℕ → Ω → ℝ := centered μ X
  have hYX : ∀ k, StronglyMeasurable (Y k) := centered_stronglyMeasurable (μ := μ) X hX
  have hYLp : ∀ k, MemLp (Y k) 2 μ := centered_memLp (μ := μ) X hLp
  have hYindep : iIndepFun Y μ := centered_iIndepFun (μ := μ) X hindep
  have hYmean : ∀ k, μ[Y k] = 0 := integral_centered_eq_zero (μ := μ) X hLp
  have hYvar : Summable (fun n => variance (Y n) μ) :=
    summable_variance_centered (μ := μ) X hX hvar
  have hmean_tendsto :
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, μ[X i]) Filter.atTop
        (nhds (∑' i, μ[X i])) :=
    hmean.hasSum.tendsto_sum_nat
  filter_upwards
    [ae_exists_tendsto_partialSum_of_summable_variance_of_mean_zero
      (μ := μ) Y hYX hYLp hYindep hYmean hYvar] with ω hω
  rcases hω with ⟨x, hx⟩
  refine ⟨x + ∑' i, μ[X i], ?_⟩
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) (hx.add hmean_tendsto)
  have hEq := partialSum_eq_partialSum_centered_add_sum_integral (μ := μ) X n ω
  simpa [Y] using hEq

theorem kolmogorov_two_series
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ)
    (hmean : Summable (fun n => μ[X n]))
    (hvar : Summable (fun n => variance (X n) μ)) :
    ∀ᵐ ω ∂μ, ∃ x : ℝ, Filter.Tendsto (fun n => partialSum X n ω) Filter.atTop (nhds x) :=
  ae_exists_tendsto_partialSum_of_summable_mean_of_summable_variance
    (μ := μ) X hX hLp hindep hmean hvar

lemma measure_finite_tail_oscillation_event_le_four_mul_variance_div_sq_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ∃ j ∈ Finset.range (n + 1), ∃ k ∈ Finset.range (n + 1),
      ε ≤ |partialSum X (m + j + 1) ω - partialSum X (m + k + 1) ω|} ≤
      ENNReal.ofReal
        (4 * (∑ j ∈ Finset.range n, variance (X (m + 1 + j)) μ) / ε ^ 2) := by
  refine (measure_finite_tail_oscillation_event_le_measure_two_mul_partialSumMax_event
      (μ := μ) X m n ε).trans ?_
  exact measure_event_two_mul_partialSumMax_tail_le_four_mul_variance_div_sq_of_mean_zero
    (μ := μ) X m n hX hLp hindep hmean hε

lemma measure_finiteTailSup_sub_finiteTailInf_event_le_four_mul_variance_div_sq_of_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (m n : ℕ)
    (hX : ∀ k, StronglyMeasurable (X k)) (hLp : ∀ k, MemLp (X k) 2 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ k, μ[X k] = 0)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ finiteTailSup X m n ω - finiteTailInf X m n ω} ≤
      ENNReal.ofReal
        (4 * (∑ j ∈ Finset.range n, variance (X (m + 1 + j)) μ) / ε ^ 2) := by
  refine (measure_finiteTailSup_sub_finiteTailInf_event_le_measure_finiteTailOscillationMax_event
      (μ := μ) X m n ε).trans ?_
  exact measure_finiteTailOscillationMax_event_le_four_mul_variance_div_sq_of_mean_zero
    (μ := μ) X m n hX hLp hindep hmean hε

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
