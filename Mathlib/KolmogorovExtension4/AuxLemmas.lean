import Mathlib.MeasureTheory.OuterMeasure.Basic

open Finset Set Filter

open scoped BigOperators ENNReal NNReal Topology

theorem bInter_diff_bUnion_subset {ι α : Type _} (A B : ι → Set α) (s : Set ι) :
    ((⋂ i ∈ s, A i) \ ⋃ i ∈ s, B i) ⊆ ⋂ i ∈ s, A i \ B i := by
  intro x
  simp only [mem_diff, mem_iInter, mem_iUnion, exists_prop, not_exists, not_and, and_imp]
  intro h1 h2 i hi
  exact ⟨h1 i hi, h2 i hi⟩

theorem Finset.sum_image_le {ι α β : Type _} [DecidableEq α] [OrderedSemiring β] (J : Finset ι)
    (g : ι → α) (f : α → β) (hf : ∀ u ∈ J.image g, 0 ≤ f u) :
    ∑ u in J.image g, f u ≤ ∑ u in J, f (g u) := by
  rw [sum_comp f g]
  refine sum_le_sum fun a hag ↦ ?_
  let hag' := hag
  rw [Finset.mem_image] at hag'
  obtain ⟨i, hi, hig⟩ := hag'
  suffices 1 ≤ (J.filter (fun j ↦ g j = a)).card by
    conv_lhs => rw [← one_smul ℕ (f a)]
    simp_rw [nsmul_eq_mul]
    exact mul_le_mul (Nat.mono_cast this) le_rfl (hf a hag) (Nat.cast_nonneg _)
  rw [Nat.succ_le_iff, card_pos]
  refine ⟨i, ?_⟩
  rw [mem_filter]
  exact ⟨hi, hig⟩

theorem partialSups_eq_sUnion_image {α : Type _} [DecidableEq (Set α)] (f : ℕ → Set α) (n : ℕ) :
    partialSups f n = ⋃₀ ↑(Finset.image f (range (n + 1))) := by
  ext1 s
  simp only [partialSups_eq_biSup, iSup_eq_iUnion, Set.mem_sUnion, mem_iUnion, exists_prop, mem_coe,
  Finset.mem_image, Finset.mem_range, exists_exists_and_eq_and, Nat.lt_succ_iff]

theorem monotone_partialSups {α : Type _} [SemilatticeSup α] (f : ℕ → α) :
    Monotone fun n ↦ partialSups f n := fun n _ hnm ↦
  partialSups_le f n _ fun _ hm'n ↦ le_partialSups_of_le _ (hm'n.trans hnm)

/-- todo: this has to be somewhere in mathlib -/
theorem Set.bUnion_le_succ {α : Type _} (s : ℕ → Set α) (n : ℕ) :
    (⋃ i ≤ n.succ, s i) = (⋃ i ≤ n, s i) ∪ s n.succ := by
  simp_rw [← Nat.lt_succ_iff];
  exact Set.biUnion_lt_succ s (n + 1)

theorem Set.bInter_le_succ {α : Type _} (s : ℕ → Set α) (n : ℕ) :
    (⋂ i ≤ n.succ, s i) = (⋂ i ≤ n, s i) ∩ s n.succ := by
  simp_rw [← Nat.lt_succ_iff];
  exact Set.biInter_lt_succ s (n + 1)

theorem ENNReal.tendsto_atTop_zero_const_sub_iff (f : ℕ → ℝ≥0∞) (a : ℝ≥0∞) (ha : a ≠ ∞)
    (hfa : ∀ n, f n ≤ a) :
    Tendsto (fun n ↦ a - f n) atTop (𝓝 0) ↔ Tendsto (fun n ↦ f n) atTop (𝓝 a) := by
  rw [ENNReal.tendsto_atTop_zero, ENNReal.tendsto_atTop ha]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩ <;> obtain ⟨N, hN⟩ := h ε hε
  · refine ⟨N, fun n hn ↦ ⟨?_, (hfa n).trans (le_add_right le_rfl)⟩⟩
    specialize hN n hn
    rw [tsub_le_iff_right] at hN ⊢
    rwa [add_comm]
  · refine ⟨N, fun n hn ↦ ?_⟩
    have hN_left := (hN n hn).1
    rw [tsub_le_iff_right] at hN_left ⊢
    rwa [add_comm]

section Accumulate

variable {α : Type _}

theorem MeasurableSet.accumulate {_ : MeasurableSpace α} {s : ℕ → Set α}
    (hs : ∀ n, MeasurableSet (s n)) (n : ℕ) : MeasurableSet (Set.Accumulate s n) :=
  MeasurableSet.biUnion (Set.to_countable _) fun n _ ↦ hs n

theorem Set.disjoint_accumulate {s : ℕ → Set α} (hs : Pairwise (Disjoint on s)) {i j : ℕ}
    (hij : i < j) : Disjoint (Set.Accumulate s i) (s j) := by
  rw [Set.accumulate_def]
  induction' i with i hi
  · simp only [Nat.zero_eq, nonpos_iff_eq_zero, iUnion_iUnion_eq_left]
    exact hs hij.ne
  · rw [Set.bUnion_le_succ s i]
    exact Disjoint.union_left (hi ((Nat.lt_succ_self i).trans hij)) (hs hij.ne)

theorem Set.accumulate_succ (s : ℕ → Set α) (n : ℕ) :
    Set.Accumulate s (n + 1) = Set.Accumulate s n ∪ s (n + 1) :=
  Set.bUnion_le_succ s n

end Accumulate

namespace NNReal

theorem isOpen_Ico_zero {b : NNReal} : IsOpen (Set.Ico 0 b) := by
  rw [← bot_eq_zero, Ico_bot];
  exact isOpen_Iio

/-- Given some x > 0, there is a sequence of positive reals summing to x. -/
theorem exists_seq_pos_summable_eq (x : ℝ≥0) (hx : 0 < x) :
    ∃ f : ℕ → ℝ≥0, (∀ n, 0 < f n) ∧ Summable f ∧ ∑' n, f n = x := by
  use fun n : ℕ ↦ x / 2 / 2 ^ n
  constructor
  · intro n
    positivity
  have h : ∑' n : ℕ, x / 2 / 2 ^ n = x := by
    rw [← NNReal.eq_iff, NNReal.coe_tsum]
    push_cast [(· ∘ ·), NNReal.coe_div]
    rw [tsum_geometric_two' (x : ℝ)]
  refine ⟨?_, h⟩
  by_contra h1
  obtain h2 := tsum_eq_zero_of_not_summable h1
  rw [h] at h2
  apply hx.ne
  rw [h2]

/-- Given some x > 0, there is a sequence of positive reals summing to something less than x.
This is needed in several lemmas in measure theory. -/
theorem exists_seq_pos_summable_lt (x : ℝ≥0) (hx : 0 < x) :
    ∃ f : ℕ → ℝ≥0, (∀ n, 0 < f n) ∧ Summable f ∧ ∑' n, f n < x := by
  cases' NNReal.exists_seq_pos_summable_eq (x / 2) (half_pos hx) with f hf
  refine ⟨f, hf.1, ?_, ?_⟩
  · rcases hf with ⟨_, hf2, _⟩
    exact hf2
  · rcases hf with ⟨_, _, hf3⟩
    rw [hf3]
    exact NNReal.half_lt_self (ne_of_gt hx)

end NNReal

namespace ENNReal

/-- Given some x > 0, there is a sequence of positive reals summing to x. -/
theorem exists_seq_pos_eq (x : ℝ≥0∞) (hx : 0 < x) :
    ∃ f : ℕ → ℝ≥0∞, (∀ n, 0 < f n) ∧ ∑' n, f n = x := by
  by_cases hx_top : x = ∞
  · use fun _ ↦ ∞
    simp only [forall_const, ENNReal.tsum_top, hx_top, and_self]
    simp
  suffices ∃ f : ℕ → ℝ≥0, (∀ n, 0 < f n) ∧ Summable f ∧ ∑' n, f n = x.toNNReal by
    obtain ⟨f, hf_pos, hf_sum, hf_eq⟩ := this
    refine ⟨fun n ↦ f n, ?_, ?_⟩
    · exact fun n ↦ ENNReal.coe_pos.mpr (hf_pos n)
    · simp only
      rw [← ENNReal.coe_tsum hf_sum, hf_eq, coe_toNNReal hx_top]
  exact NNReal.exists_seq_pos_summable_eq x.toNNReal (toNNReal_pos hx.ne' hx_top)

/-- Given some x > 0, there is a sequence of positive reals summing to something less than x.
This is needed in several lemmas in measure theory. -/
theorem exists_seq_pos_lt (x : ℝ≥0∞) (hx : 0 < x) :
    ∃ f : ℕ → ℝ≥0∞, (∀ n, 0 < f n) ∧ ∑' n, f n < x := by
  by_cases hx_top : x = ∞
  · obtain ⟨f, hf_pos, hf_eq⟩ : ∃ f : ℕ → ℝ≥0∞, (∀ n, 0 < f n) ∧ ∑' n, f n = 1 :=
      exists_seq_pos_eq 1 zero_lt_one
    refine ⟨f, hf_pos, ?_⟩
    simp only [hf_eq, hx_top, one_lt_top]
  have hx_half : 0 < x / 2 := by simp only [div_pos_iff, ne_eq, hx.ne', not_false_eq_true,
    two_ne_top, and_self]
  obtain ⟨f, hf⟩ := ENNReal.exists_seq_pos_eq (x / 2) hx_half
  refine ⟨f, hf.1, ?_⟩
  rcases hf with ⟨_, hf3⟩
  rw [hf3]
  exact ENNReal.half_lt_self hx.ne' hx_top

end ENNReal
