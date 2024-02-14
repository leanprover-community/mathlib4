/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Geometry.Euclidean.Triangle

/-!
# Abel's limit theorem

If a real or complex power series for a function has radius of convergence 1 and the series is only
known to converge conditionally at 1, Abel's limit theorem gives the value at 1 as the limit of the
function at 1 from the left. "Left" for complex numbers means within a fixed cone opening to the
left with angle less than `π`.

## Main theorems

* `Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzCone`:
  Abel's limit theorem for complex power series.
* `Real.tendsto_tsum_powerSeries_nhdsWithin_lt`: Abel's limit theorem for real power series.

## References

* https://planetmath.org/proofofabelslimittheorem
* https://en.wikipedia.org/wiki/Abel%27s_theorem
-/


open Filter Finset

open scoped BigOperators Topology

namespace Complex

section StolzSet

/-- The Stolz set for a given `M`, roughly teardrop-shaped with the tip at 1 but tending to the
open unit disc as `M` tends to infinity. -/
def stolzSet (M : ℝ) : Set ℂ := {z | ‖z‖ < 1 ∧ ‖1 - z‖ < M * (1 - ‖z‖)}

variable {M : ℝ}

theorem stolzSet_empty (hM : M ≤ 1) : stolzSet M = ∅ := by
  ext z
  rw [stolzSet, Set.mem_setOf, Set.mem_empty_iff_false, iff_false, not_and, not_lt, ← sub_pos]
  intro zn
  calc
    _ ≤ 1 * (1 - ‖z‖) := mul_le_mul_of_nonneg_right hM zn.le
    _ = ‖(1 : ℂ)‖ - ‖z‖ := by rw [one_mul, norm_one]
    _ ≤ _ := norm_sub_norm_le _ _

theorem nhdsWithin_lt_le_nhdsWithin_stolzSet (hM : 1 < M) :
    (𝓝[<] 1).map ofReal' ≤ 𝓝[stolzSet M] 1 := by
  rw [← tendsto_id']
  refine' tendsto_map' <| tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ofReal'
    (tendsto_nhdsWithin_of_tendsto_nhds <| ofRealCLM.continuous.tendsto' 1 1 rfl) _
  simp only [eventually_iff, norm_eq_abs, abs_ofReal, abs_lt, mem_nhdsWithin]
  refine' ⟨Set.Ioo 0 2, isOpen_Ioo, by norm_num, fun x hx ↦ _⟩
  simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio] at hx
  simp only [Set.mem_setOf_eq, stolzSet, ← ofReal_one, ← ofReal_sub, norm_eq_abs, abs_ofReal,
    abs_of_pos hx.1.1, abs_of_pos <| sub_pos.mpr hx.2]
  exact ⟨hx.2, lt_mul_left (sub_pos.mpr hx.2) hM⟩

open InnerProductGeometry in
theorem stolzSet_polar' (hM : 1 < M) : stolzSet M =
    {z | ‖z‖ < 1 ∧ ‖1 - z‖ < 2 * M ^ 2 / (M ^ 2 - 1) * (Real.cos (1 - z).arg - 1 / M)} := by
  ext z
  rw [stolzSet, Set.mem_setOf_eq, Set.mem_setOf_eq, ← div_lt_iff' (by positivity), lt_tsub_comm,
    and_congr_right_iff]
  intro hz
  have hnz : 0 < ‖1 - z‖ := by
    contrapose! hz
    rw [norm_le_zero_iff, sub_eq_zero] at hz
    rw [← hz, norm_one]
  have q : ‖z‖ < 1 - ‖1 - z‖ / M ↔ ‖z‖ ^ 2 < (1 - ‖1 - z‖ / M) ^ 2 := by
    constructor <;> intro h
    · rw [sq, sq]
      exact (mul_self_lt_mul_self_iff (norm_nonneg z) ((norm_nonneg z).trans h.le)).mp h
    · rw [sq_lt_sq, abs_norm, lt_abs] at h
      cases' h with c c
      · exact c
      · nth_rw 1 [neg_sub, lt_sub_iff_add_lt', ← norm_one (α := ℂ)] at c
        have : ‖1 - z‖ / M ≤ ‖1 - z‖ := by nth_rw 2 [← div_one ‖_‖]; gcongr
        replace c := c.trans_le this
        rw [← not_le] at c
        exact absurd (norm_sub_le _ _) c
  have r := norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle 1 (1 - z)
  nth_rw 1 [q, show z = 1 - (1 - z) by ring]
  rw [sq, r, sub_sq, norm_one, one_pow, mul_one, mul_one,
    show _ + _ - _ = ‖1 - z‖ * (‖1 - z‖ - 2 * Real.cos (angle 1 (1 - z))) + 1 by ring,
    show 1 - _ + _ = ‖1 - z‖ * (‖1 - z‖ / M ^ 2 - 2 / M) + 1 by ring, add_lt_add_iff_right,
    mul_lt_mul_left hnz, sub_lt_sub_iff, add_comm (_ / M ^ 2), ← sub_lt_sub_iff,
    ← mul_lt_mul_left (show 0 < M ^ 2 by positivity), mul_sub, mul_div_cancel' _ (by positivity),
    show M ^ 2 * ‖1 - z‖ - ‖1 - z‖ = ‖1 - z‖ * (M ^ 2 - 1) by ring, ← lt_div_iff (by nlinarith),
    show M ^ 2 * _ / _ = 2 * M ^ 2 / (M ^ 2 - 1) * (Real.cos (angle 1 (1 - z)) - 1 / M) by ring]
  congr! 3
  rw [cos_angle, cos_arg (by simp_all)]
  simp

open InnerProductGeometry in
theorem stolzSet_polar (hM : 1 < M) : stolzSet M =
    {z | z ≠ 1 ∧ ‖1 - z‖ < 2 * M ^ 2 / (M ^ 2 - 1) * (Real.cos (1 - z).arg - 1 / M)} := by
  rw [stolzSet_polar' hM]
  ext z
  simp only [Set.mem_setOf_eq]
  constructor <;> (intro ⟨b, l⟩; refine' ⟨_, l⟩)
  · contrapose! b
    rw [b, norm_one]
  · have : ‖1 - z‖ < 2 * Real.cos (1 - z).arg := by
      have p1 : 0 < M ^ 2 - 1 := by nlinarith
      have cnn : 0 ≤ Real.cos (1 - z).arg := by
        by_contra! h
        have p2 : Real.cos (arg (1 - z)) - 1 / M < 0 := by
          rw [sub_neg]
          exact h.trans (by positivity)
        have p3 :=
          l.trans (mul_neg_of_pos_of_neg (show 0 < 2 * M ^ 2 / (M ^ 2 - 1) by positivity) p2)
        rw [← not_le] at p3
        exact absurd (norm_nonneg _) p3
      calc
        ‖1 - z‖ < 2 * M ^ 2 / (M ^ 2 - 1) * (Real.cos (1 - z).arg - 1 / M) := l
        _ ≤ 2 * M ^ 2 / (M ^ 2 - 1) * (Real.cos (1 - z).arg - Real.cos (1 - z).arg * 1 / M) := by
          gcongr; rw [mul_one]; exact Real.cos_le_one _
        _ = 2 * Real.cos (1 - z).arg * (M / (M + 1)) := by
          rw [mul_div_assoc _ 1, ← mul_one_sub, show _ * (_ * _) =
            2 * Real.cos (1 - z).arg * (M * (M * (1 - 1 / M)) / ((M + 1) * (M - 1))) by ring,
            mul_one_sub, mul_one_div_cancel (by positivity), mul_div_mul_right _ _ (by linarith)]
        _ ≤ _ := by
          nth_rw 2 [← mul_one (2 * _)]
          gcongr
          rw [div_le_iff (by positivity)]
          linarith
    have r := norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle 1 (1 - z)
    have hnz : 0 < ‖1 - z‖ := by
      contrapose! b
      rw [norm_le_zero_iff, sub_eq_zero] at b
      exact b.symm
    have s : Real.cos (1 - z).arg = Real.cos (angle 1 (1 - z)) := by
      rw [cos_angle, cos_arg (by simp_all)]
      simp
    rw [sub_sub_cancel, norm_one, mul_one, mul_one, ← s] at r
    rw [← mul_lt_mul_left hnz, ← add_lt_add_iff_left 1, ← sub_lt_iff_lt_add,
      mul_comm 2, ← mul_assoc, ← mul_rotate, ← r] at this
    rwa [mul_self_lt_mul_self_iff (norm_nonneg _) zero_le_one, one_mul]

/-- The cone around 1 with angle `2θ`. -/
def stolzCone (θ : ℝ) : Set ℂ := {z | ‖1 - z‖ ≠ 0 ∧ |arg (1 - z)| < θ}

variable {θ : ℝ}

theorem stolzCone_empty (hθ : θ ≤ 0) : stolzCone θ = ∅ := by
  ext z
  rw [stolzCone, Set.mem_setOf, Set.mem_empty_iff_false, iff_false, and_comm, not_and]
  intro h
  exact absurd (h.trans_le hθ) (by simp)

open Real in
theorem nhdsWithin_stolzCone_le_nhdsWithin_stolzSet (hθ : θ < π / 2) (hM : (Real.cos θ)⁻¹ < M) :
    𝓝[stolzCone θ] 1 ≤ 𝓝[stolzSet M] 1 := by
  cases' le_or_lt θ 0 with hl hl
  · rw [stolzCone_empty hl]; simp
  rw [nhdsWithin_le_iff, Metric.mem_nhdsWithin_iff]
  have cpos : 0 < Real.cos θ := cos_pos_of_mem_Ioo ⟨by linarith, hθ⟩
  have one_lt_M : 1 < M := (one_le_inv cpos (cos_le_one θ)).trans_lt hM
  rw [stolzSet_polar one_lt_M]
  have p1 : 0 < M ^ 2 - 1 := by nlinarith
  have p2 : 0 < Real.cos θ - 1 / M := by rw [sub_pos, one_div_lt (by positivity) cpos]; simpa
  use 2 * M ^ 2 / (M ^ 2 - 1) * (Real.cos θ - 1 / M), by positivity
  intro z
  rw [Set.mem_inter_iff]
  intro ⟨m1, m2⟩
  rw [mem_ball_iff_norm'] at m1
  rw [stolzCone] at m2
  rw [Set.mem_setOf_eq] at m2 ⊢
  constructor
  · replace m2 := m2.1
    contrapose! m2
    simp [m2]
  · apply m1.trans _
    gcongr
    rw [← cos_abs (arg _)]
    exact cos_lt_cos_of_nonneg_of_le_pi_div_two (abs_nonneg _) hθ.le m2.2

end StolzSet

variable {f : ℕ → ℂ} {l : ℂ}

/-- Auxiliary lemma for Abel's limit theorem. The difference between the sum `l` at 1 and the
power series's value at a point `z` away from 1 can be rewritten as `1 - z` times a power series
whose coefficients are tail sums of `l`. -/
lemma abel_aux (h : Tendsto (fun n ↦ ∑ i in range n, f i) atTop (𝓝 l)) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun n ↦ (1 - z) * ∑ i in range n, (l - ∑ j in range (i + 1), f j) * z ^ i)
      atTop (𝓝 (l - ∑' n, f n * z ^ n)) := by
  let s := fun n ↦ ∑ i in range n, f i
  have k := h.sub (summable_powerSeries_of_norm_lt_one h.cauchySeq hz).hasSum.tendsto_sum_nat
  simp_rw [← sum_sub_distrib, ← mul_one_sub, ← geom_sum_mul_neg, ← mul_assoc, ← sum_mul,
    mul_comm, mul_sum _ _ (f _), range_eq_Ico, ← sum_Ico_Ico_comm', ← range_eq_Ico,
    ← sum_mul] at k
  conv at k =>
    enter [1, n]
    rw [sum_congr (g := fun j ↦ (∑ k in range n, f k - ∑ k in range (j + 1), f k) * z ^ j)
      rfl (fun j hj ↦ by congr 1; exact sum_Ico_eq_sub _ (mem_range.mp hj))]
  suffices : Tendsto (fun n ↦ (l - s n) * ∑ i in range n, z ^ i) atTop (𝓝 0)
  · simp_rw [mul_sum] at this
    replace this := (this.const_mul (1 - z)).add k
    conv at this =>
      enter [1, n]
      rw [← mul_add, ← sum_add_distrib]
      enter [2, 2, i]
      rw [← add_mul, sub_add_sub_cancel]
    rwa [mul_zero, zero_add] at this
  rw [← zero_mul (-1 / (z - 1))]
  apply Tendsto.mul
  · simpa only [neg_zero, neg_sub] using (tendsto_sub_nhds_zero_iff.mpr h).neg
  · conv =>
      enter [1, n]
      rw [geom_sum_eq (by contrapose! hz; simp [hz]), sub_div, sub_eq_add_neg, ← neg_div]
    rw [← zero_add (-1 / (z - 1)), ← zero_div (z - 1)]
    apply Tendsto.add (Tendsto.div_const (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz) (z - 1))
    simp only [zero_div, zero_add, tendsto_const_nhds_iff]

/-- **Abel's limit theorem**. Given a power series converging at 1, the corresponding function
is continuous at 1 when approaching 1 within a fixed Stolz set. -/
theorem tendsto_tsum_powerSeries_nhdsWithin_stolzSet
    (h : Tendsto (fun n ↦ ∑ i in range n, f i) atTop (𝓝 l)) {M : ℝ} :
    Tendsto (fun z ↦ ∑' n, f n * z ^ n) (𝓝[stolzSet M] 1) (𝓝 l) := by
  -- If `M ≤ 1` the Stolz set is empty and the statement is trivial
  cases' le_or_lt M 1 with hM hM
  · simp_rw [stolzSet_empty hM, nhdsWithin_empty, tendsto_bot]
  -- Abbreviations
  let s := fun n ↦ ∑ i in range n, f i
  let g := fun z ↦ ∑' n, f n * z ^ n
  have hm := Metric.tendsto_atTop.mp h
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [dist_eq_norm] at hm ⊢
  -- Introduce the "challenge" `ε`
  intro ε εpos
  -- First bound, handles the tail
  obtain ⟨B₁, hB₁⟩ := hm (ε / 4 / M) (by positivity)
  -- Second bound, handles the head
  let F := ∑ i in range B₁, ‖l - s (i + 1)‖
  have Fnonneg : 0 ≤ F := sum_nonneg (fun _ _ ↦ by positivity)
  use ε / 4 / (F + 1), by positivity
  intro z ⟨zn, zm⟩ zd
  have p := abel_aux h zn
  simp_rw [Metric.tendsto_atTop, dist_eq_norm, norm_sub_rev] at p
  -- Third bound, regarding the distance between `l - g z` and the rearranged sum
  obtain ⟨B₂, hB₂⟩ := p (ε / 2) (by positivity)
  clear hm p
  replace hB₂ := hB₂ (max B₁ B₂) (by simp)
  suffices : ‖(1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ < ε / 2
  · calc
      _ = ‖l - g z‖ := by rw [norm_sub_rev]
      _ = ‖l - g z - (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i +
          (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by rw [sub_add_cancel _]
      _ ≤ ‖l - g z - (1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ +
          ‖(1 - z) * ∑ i in range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hB₂ this
      _ = _ := add_halves ε
  -- We break the rearranged sum along `B₁`
  calc
    _ = ‖(1 - z) * ∑ i in range B₁, (l - s (i + 1)) * z ^ i +
        (1 - z) * ∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by
      rw [← mul_add, sum_range_add_sum_Ico _ (le_max_left B₁ B₂)]
    _ ≤ ‖(1 - z) * ∑ i in range B₁, (l - s (i + 1)) * z ^ i‖ +
        ‖(1 - z) * ∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := norm_add_le _ _
    _ = ‖1 - z‖ * ‖∑ i in range B₁, (l - s (i + 1)) * z ^ i‖ +
        ‖1 - z‖ * ‖∑ i in Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ * ‖z‖ ^ i +
        ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ‖l - s (i + 1)‖ * ‖z‖ ^ i := by
      gcongr <;> simp_rw [← norm_pow, ← norm_mul, norm_sum_le]
  -- then prove that the two pieces are each less than `ε / 4`
  have S₁ : ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ * ‖z‖ ^ i < ε / 4 :=
    calc
      _ ≤ ‖1 - z‖ * ∑ i in range B₁, ‖l - s (i + 1)‖ := by
        gcongr; nth_rw 3 [← mul_one ‖_‖]
        gcongr; exact pow_le_one _ (norm_nonneg _) zn.le
      _ ≤ ‖1 - z‖ * (F + 1) := by gcongr; linarith only
      _ < _ := by rwa [norm_sub_rev, lt_div_iff (by positivity)] at zd
  have S₂ : ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ‖l - s (i + 1)‖ * ‖z‖ ^ i < ε / 4 :=
    calc
      _ ≤ ‖1 - z‖ * ∑ i in Ico B₁ (max B₁ B₂), ε / 4 / M * ‖z‖ ^ i := by
        gcongr with i hi
        have := hB₁ (i + 1) (by linarith only [(mem_Ico.mp hi).1])
        rw [norm_sub_rev] at this
        exact this.le
      _ = ‖1 - z‖ * (ε / 4 / M) * ∑ i in Ico B₁ (max B₁ B₂), ‖z‖ ^ i := by
        rw [← mul_sum, ← mul_assoc]
      _ ≤ ‖1 - z‖ * (ε / 4 / M) * ∑' i, ‖z‖ ^ i := by
        gcongr
        exact sum_le_tsum _ (fun _ _ ↦ by positivity)
          (summable_geometric_of_lt_one (by positivity) zn)
      _ = ‖1 - z‖ * (ε / 4 / M) / (1 - ‖z‖) := by
        rw [tsum_geometric_of_lt_one (by positivity) zn, ← div_eq_mul_inv]
      _ < M * (1 - ‖z‖) * (ε / 4 / M) / (1 - ‖z‖) := by gcongr; linarith only [zn]
      _ = _ := by
        rw [← mul_rotate, mul_div_cancel _ (by linarith only [zn]),
          div_mul_cancel _ (by linarith only [hM])]
  convert add_lt_add S₁ S₂ using 1
  linarith only

open Real in
/-- **Abel's limit theorem**. Given a power series converging at 1, the corresponding function
is continuous at 1 when approaching 1 within a fixed cone opening to the left with angle `< π`. -/
theorem tendsto_tsum_powerSeries_nhdsWithin_stolzCone
    (h : Tendsto (fun n ↦ ∑ i in range n, f i) atTop (𝓝 l)) {θ : ℝ} (hθ : θ < π / 2) :
    Tendsto (fun z ↦ ∑' n, f n * z ^ n) (𝓝[stolzCone θ] 1) (𝓝 l) :=
  (tendsto_tsum_powerSeries_nhdsWithin_stolzSet (M := (Real.cos θ)⁻¹ + 1) h).mono_left
    (nhdsWithin_stolzCone_le_nhdsWithin_stolzSet hθ (lt_add_one _))

theorem tendsto_tsum_powerSeries_nhdsWithin_lt
    (h : Tendsto (fun n ↦ ∑ i in range n, f i) atTop (𝓝 l)) :
    Tendsto (fun z ↦ ∑' n, f n * z ^ n) ((𝓝[<] 1).map ofReal') (𝓝 l) :=
  (tendsto_tsum_powerSeries_nhdsWithin_stolzSet (M := 2) h).mono_left
    (nhdsWithin_lt_le_nhdsWithin_stolzSet one_lt_two)

end Complex

namespace Real

open Complex

variable {f : ℕ → ℝ} {l : ℝ}

/-- **Abel's limit theorem**. Given a real power series converging at 1, the corresponding function
is continuous at 1 when approaching 1 from the left. -/
theorem tendsto_tsum_powerSeries_nhdsWithin_lt
    (h : Tendsto (fun n ↦ ∑ i in range n, f i) atTop (𝓝 l)) :
    Tendsto (fun x ↦ ∑' n, f n * x ^ n) (𝓝[<] 1) (𝓝 l) := by
  have m : (𝓝 l).map ofReal' ≤ 𝓝 ↑l := ofRealCLM.continuous.tendsto l
  replace h := (tendsto_map.comp h).mono_right m
  rw [Function.comp_def] at h
  push_cast at h
  replace h := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt h
  rw [tendsto_map'_iff] at h
  rw [Metric.tendsto_nhdsWithin_nhds] at h ⊢
  convert h
  simp_rw [Function.comp_apply, dist_eq_norm]
  norm_cast
  rw [norm_real]

end Real
