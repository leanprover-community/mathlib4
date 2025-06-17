import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.MoveAdd
import Mathlib.Tactic.Rify

noncomputable def reprReal (x : ℝ) (b : ℕ) [NeZero b] : ℕ → Fin b :=
  fun i ↦ Fin.ofNat _ <| ⌊x * b^(i + 1)⌋₊ % b

noncomputable def ofDigitsTerm {b : ℕ} [NeZero b] (digits : ℕ → Fin b) : ℕ → ℝ :=
  fun i ↦ (digits i) * (b⁻¹ : ℝ)^(i + 1)

theorem ofDigitsTerm_nonneg {b : ℕ} [NeZero b] {digits : ℕ → Fin b} {n : ℕ} :
    0 ≤ ofDigitsTerm digits n := by
  simp [ofDigitsTerm]
  positivity

theorem ofDigitsTerm_le {b : ℕ} [NeZero b] {digits : ℕ → Fin b} {n : ℕ} (hb : 0 < b) :
    ofDigitsTerm digits n ≤ (b - 1) * (b⁻¹ : ℝ)^(n + 1) := by
  simp [ofDigitsTerm]
  gcongr
  rw [← Nat.cast_pred hb]
  norm_cast
  omega

theorem ofDigitsTerm_Summable {b : ℕ} [inst : NeZero b] {digits : ℕ → Fin b} :
    Summable (ofDigitsTerm digits) := by
  by_cases hb : b = 1
  · subst hb
    have : ofDigitsTerm digits = 0 := by
      ext i
      simp [ofDigitsTerm]
    simp [this]
    eta_expand
    simp [summable_const_iff]
  replace hb : 1 < b := by
    cases inst
    omega
  have h1 := summable_geometric_of_lt_one (r := (b⁻¹ : ℝ)) (by simp)
    (by rify at hb; exact inv_lt_one_of_one_lt₀ hb)
  apply Summable.mul_left (a := (b : ℝ)) at h1
  replace h1 : Summable fun i ↦ b * (b : ℝ)⁻¹ ^ (i + 1) := by
    simp_rw [pow_succ', ← mul_assoc, mul_comm (b : ℝ), mul_assoc]
    exact Summable.mul_left _ h1
  apply Summable.of_nonneg_of_le _ _ h1
  · intros
    exact ofDigitsTerm_nonneg
  intro i
  -- todo: refactor with above
  simp [ofDigitsTerm]
  gcongr
  simp

noncomputable def ofDigits {b : ℕ} [NeZero b] (digits : ℕ → Fin b) : ℝ :=
  ∑' n, ofDigitsTerm digits n

theorem ofDigits_nonneg {b : ℕ} [NeZero b] {digits : ℕ → Fin b} : 0 ≤ ofDigits digits := by
  simp [ofDigits]
  apply tsum_nonneg
  intro i
  exact ofDigitsTerm_nonneg

theorem ofDigits_le_one {b : ℕ} [inst_neZero : NeZero b] {digits : ℕ → Fin b}  :
    ofDigits digits ≤ 1 := by
  by_cases hb : ¬(1 < b)
  · interval_cases b
    · simp at inst_neZero
    simp [ofDigits, ofDigitsTerm]
  push_neg at hb
  have hb_inv_nonneg : 0 ≤ (b⁻¹ : ℝ) := by simp
  have hb_inv_lt_one : (b⁻¹ : ℝ) < 1 := by
    rify at hb
    exact inv_lt_one_of_one_lt₀ hb
  simp [ofDigits]
  let g (i : ℕ) : ℝ := (1 - (b⁻¹ : ℝ)) * (b⁻¹ : ℝ)^i
  have hg_summable : Summable g := by
    apply Summable.mul_left
    apply summable_geometric_of_lt_one (by simp)
      (by rify at hb; exact inv_lt_one_of_one_lt₀ hb)
  convert Summable.tsum_mono (ofDigitsTerm_Summable) hg_summable _
  · simp [g, tsum_mul_left, ← inv_pow]
    rw [tsum_geometric_of_lt_one hb_inv_nonneg hb_inv_lt_one, mul_inv_cancel₀]
    linarith
  · intro i
    simp [g]
    convert ofDigitsTerm_le (by linarith) using 1
    rw [pow_succ, inv_pow]
    move_mul [((b : ℝ)^i)⁻¹]
    congr
    rw [sub_mul, mul_inv_cancel₀]
    · simp
    · rify at hb
      linarith

theorem ofDigits_partail_sum_eq {b : ℕ} [NeZero b] (a : ℕ → Fin b) (n : ℕ) :
    ofDigits a = (∑ i ∈ Finset.range n, ofDigitsTerm a i) +
      ((b : ℝ)^n)⁻¹ * ofDigits (fun i ↦ a (i + n)) := by
  simp [ofDigits]
  rw [← Summable.sum_add_tsum_nat_add n ofDigitsTerm_Summable,
    ← Summable.tsum_mul_left _ ofDigitsTerm_Summable]
  congr
  ext i
  simp [ofDigitsTerm]
  ring

theorem ofDigits_close {b : ℕ} [NeZero b] {x y : ℕ → Fin b} {n : ℕ} (hxy : ∀ i < n, x i = y i) :
    |ofDigits x - ofDigits y| ≤ ((b : ℝ)^n)⁻¹ := by
  rw [ofDigits_partail_sum_eq x n, ofDigits_partail_sum_eq y n]
  have : ∑ i ∈ Finset.range n, ofDigitsTerm x i = ∑ i ∈ Finset.range n, ofDigitsTerm y i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp at hi
    simp [ofDigitsTerm, hxy i hi]
  simp [this]
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  apply mul_le_of_le_one_right (by positivity)
  rw [abs_le']
  constructor <;> linarith [ofDigits_nonneg (digits := fun i ↦ x (i + n)),
    ofDigits_nonneg (digits := fun i ↦ y (i + n)), ofDigits_le_one (digits := fun i ↦ x (i + n)),
    ofDigits_le_one (digits := fun i ↦ y (i + n))]

lemma ofDigits_reprReal_partial_sum_eq {x : ℝ} {b : ℕ} [inst : NeZero b] (hb : 1 < b)
    (hx : x ∈ Set.Ico 0 1) {n : ℕ} :
    b^n * ∑ i ∈ Finset.range n, ofDigitsTerm (reprReal x b) i = ⌊b^n * x⌋₊ := by
  induction n with
  | zero =>
    simp
    simp at hx
    norm_cast
    symm
    rw [Nat.floor_eq_zero]
    exact hx.right
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, pow_succ', mul_assoc, ih]
    simp only [ofDigitsTerm, reprReal]
    rw [show x * (b : ℝ) ^ (n + 1) = b * (b^n * x) by ring]
    conv => rhs; rw [mul_assoc]
    set y := (b : ℝ) ^ n * x
    ring_nf
    move_mul [← (b : ℝ)⁻¹]
    have hb_zero : (b : ℝ) ≠ 0 := by
      obtain ⟨h⟩ := inst
      simpa using h
    simp [inv_mul_cancel₀ (hb_zero)]
    move_mul [← ((b : ℝ)^n)⁻¹]
    rw [inv_mul_cancel₀ (by positivity)]
    simp
    norm_cast
    have : ⌊y⌋₊ = ⌊b * y⌋₊ / b := by
      symm
      apply Nat.mul_floor_div_eq_floor
      omega
    rw [this]
    conv => rhs; rw [← Nat.mod_add_div ⌊(b : ℝ) * y⌋₊ b]

lemma ofDigits_reprReal_partial_sum_ge {x : ℝ} {b : ℕ} [NeZero b] (hb : 1 < b)
    (hx : x ∈ Set.Ico 0 1) {n : ℕ} :
    x - (b⁻¹ : ℝ)^n ≤ ∑ i ∈ Finset.range n, ofDigitsTerm (reprReal x b) i := by
  have := ofDigits_reprReal_partial_sum_eq hb hx (n := n)
  have h_le := Nat.lt_floor_add_one (b^n * x)
  rw [← this] at h_le
  rw [← mul_le_mul_left (show 0 < (b : ℝ)^n by positivity)]
  rw [mul_sub, inv_pow, mul_inv_cancel₀ (by positivity)]
  linarith

lemma ofDigits_reprReal_partial_sum_le {x : ℝ} {b : ℕ} [NeZero b] (hb : 1 < b) {n : ℕ}
    (hx : x ∈ Set.Ico 0 1) :
    ∑ i ∈ Finset.range n, ofDigitsTerm (reprReal x b) i ≤ x := by
  have := ofDigits_reprReal_partial_sum_eq hb hx (n := n)
  have h_le := Nat.floor_le (a := b^n * x) (by simp at hx; apply mul_nonneg _ hx.left; positivity)
  rw [← this, mul_le_mul_iff_of_pos_left (by positivity)] at h_le
  exact h_le

theorem ofDigits_HasSum (x : ℝ) (b : ℕ) [NeZero b] (hb : 1 < b) (hx : x ∈ Set.Ico 0 1) :
    HasSum (ofDigitsTerm (reprReal x b)) x := by
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  swap
  · conv => arg 1; ext i; simp; rw [abs_of_nonneg (by simp [ofDigitsTerm]; positivity)]
    exact ofDigitsTerm_Summable
  rw [← tendsto_sub_nhds_zero_iff]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n ↦ -(b⁻¹ : ℝ)^n) (h := 0)
  · rw [show (0 : ℝ) = -0 by simp]
    apply Filter.Tendsto.neg
    apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    rw [abs_of_nonneg (by positivity)]
    rify at hb
    exact inv_lt_one_of_one_lt₀ hb
  · apply tendsto_const_nhds
  · intro n
    simp
    have := ofDigits_reprReal_partial_sum_ge hb hx (n := n)
    simp at this
    linarith
  · intro n
    simp
    exact ofDigits_reprReal_partial_sum_le hb hx

theorem reprReal_ofDigits (b : ℕ) [NeZero b] (x : ℝ) (hb : 1 < b) (hx : x ∈ Set.Ico 0 1) :
    ofDigits (reprReal x b) = x := by
  simp [ofDigits]
  rw [← Summable.hasSum_iff]
  · exact ofDigits_HasSum x b hb hx
  · exact ofDigitsTerm_Summable

#min_imports
