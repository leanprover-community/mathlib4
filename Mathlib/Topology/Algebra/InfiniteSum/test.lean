import Mathlib



open Real

lemma Complex.log_of_summable {f : ℕ → ℂ} (hf : Summable f) :
    Summable (fun n : ℕ => Complex.log (1 + f n)) := by
  have hff := Summable.const_smul ((3 : ℝ) / 2) (summable_norm_iff.mpr hf)
  have := Metric.tendsto_atTop.mp (Summable.tendsto_atTop_zero ((summable_norm_iff.mpr hf)))
  apply Summable.of_norm_bounded_eventually_nat (fun n => (3/2) * Complex.abs (f n)) hff
  simp only [smul_eq_mul, gt_iff_lt, ge_iff_le, dist_zero_right, Real.norm_eq_abs, Complex.abs_abs,
    Complex.norm_eq_abs, eventually_atTop] at *
  obtain ⟨n, hn⟩ := this (1/2) (one_half_pos)
  exact Exists.intro n fun m hm ↦ norm_log_one_add_half_le_self (LT.lt.le (hn m hm))

lemma Real.log_of_summable {f : ℕ → ℝ} (hf : Summable f) :
    Summable (fun n : ℕ => Real.log (1 + |f n|)) := by
  apply Summable.of_norm_bounded_eventually_nat (fun n => |(f n)|)
    (by apply summable_norm_iff.mpr hf)
  simp only [gt_iff_lt, ge_iff_le, norm_eq_abs, dist_zero_right, _root_.abs_abs,
    eventually_atTop]
  obtain ⟨n, _⟩ := Metric.tendsto_atTop.mp
    (Summable.tendsto_atTop_zero ((summable_norm_iff.mpr hf))) (1/2) (one_half_pos)
  use n
  intro m _
  have ht : 0  < 1 + |f m| := by
    rw [add_comm]
    apply add_pos_of_nonneg_of_pos (abs_nonneg _)  Real.zero_lt_one
  have := Real.log_le_sub_one_of_pos ht
  simp only [add_sub_cancel_left] at this
  apply le_trans _ this
  have habs : |Real.log (1 + |f m|)| = Real.log (1 + |f m|) := by
    rw [abs_eq_self]
    apply Real.log_nonneg
    simp only [le_add_iff_nonneg_right, abs_nonneg]
  rw [habs]

lemma Complex.summable_multipliable_one_add (f : ℕ → ℂ) (hf : Summable f)
    (hff : ∀ n : ℕ, 1 + f n  ≠ 0) : Multipliable (fun n : ℕ => (1 + f n)) := by
  have := log_of_summable hf
  simp_rw [Summable, HasSum] at this
  obtain ⟨a, ha⟩ := this
  have := Filter.Tendsto.cexp ha
  have h1 : (fun n : Finset ℕ ↦ cexp (∑ x ∈ n, Complex.log (1 + f x))) =
     (fun n : Finset ℕ ↦ (∏ x ∈ n,  (1 + f x))) := by
    ext y
    rw [Complex.exp_sum]
    congr
    ext r
    rw [Complex.exp_log]
    apply hff r
  rw [h1] at this
  refine ⟨exp a, this⟩

lemma Real.summable_multipliable_one_add (f : ℕ → ℝ) (hf : Summable f) :
    Multipliable (fun n : ℕ => (1 + |f n|)) := by
  have := log_of_summable hf
  simp_rw [Summable, HasSum] at this
  obtain ⟨a, ha⟩ := this
  have := Filter.Tendsto.rexp ha
  have h1 : (fun n : Finset ℕ ↦ rexp (∑ x ∈ n, Real.log (1 + |f x|))) =
     (fun n : Finset ℕ ↦ (∏ x ∈ n, (1 + |f x|))) := by
    ext y
    rw [Real.exp_sum]
    congr
    ext r
    rw [Real.exp_log]
    apply add_pos_of_pos_of_nonneg
    exact Real.zero_lt_one
    apply abs_nonneg
  rw [h1] at this
  refine ⟨exp a, this⟩
