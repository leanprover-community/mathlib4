/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Sébastien Gouëzel, Yury Kudryashov, Dylan MacKenzie, Patrick Massot
-/
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Order.Filter.AtTopBot.ModEq
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.NoncommRing

/-!
# A collection of specific limit computations

This file contains important specific limit computations in (semi-)normed groups/rings/spaces, as
well as such computations in `ℝ` when the natural proof passes through a fact about normed spaces.
-/

noncomputable section

open Set Function Filter Finset Metric Asymptotics Topology Nat NNReal ENNReal

variable {α : Type*}

theorem tendsto_natCast_atTop_cobounded
    [NormedRing α] [NormSMulClass ℤ α] [Nontrivial α] :
    Tendsto Nat.cast atTop (Bornology.cobounded α) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa [norm_natCast_eq_mul_norm_one] using tendsto_natCast_atTop_atTop
    |>.atTop_mul_const (norm_pos_iff.mpr one_ne_zero)

theorem tendsto_intCast_atBot_sup_atTop_cobounded
    [NormedRing α] [NormSMulClass ℤ α] [Nontrivial α] :
    Tendsto Int.cast (atBot ⊔ atTop) (Bornology.cobounded α) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa [norm_intCast_eq_abs_mul_norm_one] using tendsto_intCast_atTop_atTop
    |>.comp (tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop)
    |>.atTop_mul_const (norm_pos_iff.mpr one_ne_zero)

theorem tendsto_intCast_atBot_cobounded
    [NormedRing α] [NormSMulClass ℤ α] [Nontrivial α] :
    Tendsto Int.cast atBot (Bornology.cobounded α) :=
  tendsto_intCast_atBot_sup_atTop_cobounded.mono_left le_sup_left

theorem tendsto_intCast_atTop_cobounded
    [NormedRing α] [NormSMulClass ℤ α] [Nontrivial α] :
    Tendsto Int.cast atTop (Bornology.cobounded α) :=
  tendsto_intCast_atBot_sup_atTop_cobounded.mono_left le_sup_right

/-! ### Powers -/

theorem isLittleO_pow_pow_of_lt_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ < r₂) :
    (fun n : ℕ ↦ r₁ ^ n) =o[atTop] fun n ↦ r₂ ^ n :=
  have H : 0 < r₂ := h₁.trans_lt h₂
  (isLittleO_of_tendsto fun _ hn ↦ False.elim <| H.ne' <| pow_eq_zero hn) <|
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg h₁ (h₁.trans h₂.le)) ((div_lt_one H).2 h₂)).congr fun _ ↦ div_pow _ _ _

theorem isBigO_pow_pow_of_le_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ ≤ r₂) :
    (fun n : ℕ ↦ r₁ ^ n) =O[atTop] fun n ↦ r₂ ^ n :=
  h₂.eq_or_lt.elim (fun h ↦ h ▸ isBigO_refl _ _) fun h ↦ (isLittleO_pow_pow_of_lt_left h₁ h).isBigO

theorem isLittleO_pow_pow_of_abs_lt_left {r₁ r₂ : ℝ} (h : |r₁| < |r₂|) :
    (fun n : ℕ ↦ r₁ ^ n) =o[atTop] fun n ↦ r₂ ^ n := by
  refine (IsLittleO.of_norm_left ?_).of_norm_right
  exact (isLittleO_pow_pow_of_lt_left (abs_nonneg r₁) h).congr (pow_abs r₁) (pow_abs r₂)

open List in
/-- Various statements equivalent to the fact that `f n` grows exponentially slower than `R ^ n`.

* 0: $f n = o(a ^ n)$ for some $-R < a < R$;
* 1: $f n = o(a ^ n)$ for some $0 < a < R$;
* 2: $f n = O(a ^ n)$ for some $-R < a < R$;
* 3: $f n = O(a ^ n)$ for some $0 < a < R$;
* 4: there exist `a < R` and `C` such that one of `C` and `R` is positive and $|f n| ≤ Ca^n$
  for all `n`;
* 5: there exists `0 < a < R` and a positive `C` such that $|f n| ≤ Ca^n$ for all `n`;
* 6: there exists `a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`;
* 7: there exists `0 < a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`.

NB: For backwards compatibility, if you add more items to the list, please append them at the end of
the list. -/
theorem TFAE_exists_lt_isLittleO_pow (f : ℕ → ℝ) (R : ℝ) :
    TFAE
      [∃ a ∈ Ioo (-R) R, f =o[atTop] (a ^ ·), ∃ a ∈ Ioo 0 R, f =o[atTop] (a ^ ·),
        ∃ a ∈ Ioo (-R) R, f =O[atTop] (a ^ ·), ∃ a ∈ Ioo 0 R, f =O[atTop] (a ^ ·),
        ∃ a < R, ∃ C : ℝ, (0 < C ∨ 0 < R) ∧ ∀ n, |f n| ≤ C * a ^ n,
        ∃ a ∈ Ioo 0 R, ∃ C > 0, ∀ n, |f n| ≤ C * a ^ n, ∃ a < R, ∀ᶠ n in atTop, |f n| ≤ a ^ n,
        ∃ a ∈ Ioo 0 R, ∀ᶠ n in atTop, |f n| ≤ a ^ n] := by
  have A : Ico 0 R ⊆ Ioo (-R) R :=
    fun x hx ↦ ⟨(neg_lt_zero.2 (hx.1.trans_lt hx.2)).trans_le hx.1, hx.2⟩
  have B : Ioo 0 R ⊆ Ioo (-R) R := Subset.trans Ioo_subset_Ico_self A
  -- First we prove that 1-4 are equivalent using 2 → 3 → 4, 1 → 3, and 2 → 1
  tfae_have 1 → 3 := fun ⟨a, ha, H⟩ ↦ ⟨a, ha, H.isBigO⟩
  tfae_have 2 → 1 := fun ⟨a, ha, H⟩ ↦ ⟨a, B ha, H⟩
  tfae_have 3 → 2
  | ⟨a, ha, H⟩ => by
    rcases exists_between (abs_lt.2 ha) with ⟨b, hab, hbR⟩
    exact ⟨b, ⟨(abs_nonneg a).trans_lt hab, hbR⟩,
      H.trans_isLittleO (isLittleO_pow_pow_of_abs_lt_left (hab.trans_le (le_abs_self b)))⟩
  tfae_have 2 → 4 := fun ⟨a, ha, H⟩ ↦ ⟨a, ha, H.isBigO⟩
  tfae_have 4 → 3 := fun ⟨a, ha, H⟩ ↦ ⟨a, B ha, H⟩
  -- Add 5 and 6 using 4 → 6 → 5 → 3
  tfae_have 4 → 6
  | ⟨a, ha, H⟩ => by
    rcases bound_of_isBigO_nat_atTop H with ⟨C, hC₀, hC⟩
    refine ⟨a, ha, C, hC₀, fun n ↦ ?_⟩
    simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg ha.1.le] using hC (pow_ne_zero n ha.1.ne')
  tfae_have 6 → 5 := fun ⟨a, ha, C, H₀, H⟩ ↦ ⟨a, ha.2, C, Or.inl H₀, H⟩
  tfae_have 5 → 3
  | ⟨a, ha, C, h₀, H⟩ => by
    rcases sign_cases_of_C_mul_pow_nonneg fun n ↦ (abs_nonneg _).trans (H n) with (rfl | ⟨hC₀, ha₀⟩)
    · obtain rfl : f = 0 := by
        ext n
        simpa using H n
      simp only [lt_irrefl, false_or] at h₀
      exact ⟨0, ⟨neg_lt_zero.2 h₀, h₀⟩, isBigO_zero _ _⟩
    exact ⟨a, A ⟨ha₀, ha⟩,
      isBigO_of_le' _ fun n ↦ (H n).trans <| mul_le_mul_of_nonneg_left (le_abs_self _) hC₀.le⟩
  -- Add 7 and 8 using 2 → 8 → 7 → 3
  tfae_have 2 → 8
  | ⟨a, ha, H⟩ => by
    refine ⟨a, ha, (H.def zero_lt_one).mono fun n hn ↦ ?_⟩
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_pow, abs_of_pos ha.1] at hn
  tfae_have 8 → 7 := fun ⟨a, ha, H⟩ ↦ ⟨a, ha.2, H⟩
  tfae_have 7 → 3
  | ⟨a, ha, H⟩ => by
    refine ⟨a, A ⟨?_, ha⟩, .of_norm_eventuallyLE H⟩
    exact nonneg_of_eventually_pow_nonneg (H.mono fun n ↦ (abs_nonneg _).trans)
  tfae_finish

/-- For any natural `k` and a real `r > 1` we have `n ^ k = o(r ^ n)` as `n → ∞`. -/
theorem isLittleO_pow_const_const_pow_of_one_lt {R : Type*} [NormedRing R] (k : ℕ) {r : ℝ}
    (hr : 1 < r) : (fun n ↦ (n : R) ^ k : ℕ → R) =o[atTop] fun n ↦ r ^ n := by
  have : Tendsto (fun x : ℝ ↦ x ^ k) (𝓝[>] 1) (𝓝 1) :=
    ((continuous_id.pow k).tendsto' (1 : ℝ) 1 (one_pow _)).mono_left inf_le_left
  obtain ⟨r' : ℝ, hr' : r' ^ k < r, h1 : 1 < r'⟩ :=
    ((this.eventually (gt_mem_nhds hr)).and self_mem_nhdsWithin).exists
  have h0 : 0 ≤ r' := zero_le_one.trans h1.le
  suffices (fun n ↦ (n : R) ^ k : ℕ → R) =O[atTop] fun n : ℕ ↦ (r' ^ k) ^ n from
    this.trans_isLittleO (isLittleO_pow_pow_of_lt_left (pow_nonneg h0 _) hr')
  conv in (r' ^ _) ^ _ => rw [← pow_mul, mul_comm, pow_mul]
  suffices ∀ n : ℕ, ‖(n : R)‖ ≤ (r' - 1)⁻¹ * ‖(1 : R)‖ * ‖r' ^ n‖ from
    (isBigO_of_le' _ this).pow _
  intro n
  rw [mul_right_comm]
  refine n.norm_cast_le.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  simpa [_root_.div_eq_inv_mul, Real.norm_eq_abs, abs_of_nonneg h0] using n.cast_le_pow_div_sub h1

/-- For a real `r > 1` we have `n = o(r ^ n)` as `n → ∞`. -/
theorem isLittleO_coe_const_pow_of_one_lt {R : Type*} [NormedRing R] {r : ℝ} (hr : 1 < r) :
    ((↑) : ℕ → R) =o[atTop] fun n ↦ r ^ n := by
  simpa only [pow_one] using @isLittleO_pow_const_const_pow_of_one_lt R _ 1 _ hr

/-- If `‖r₁‖ < r₂`, then for any natural `k` we have `n ^ k r₁ ^ n = o (r₂ ^ n)` as `n → ∞`. -/
theorem isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt {R : Type*} [NormedRing R] (k : ℕ)
    {r₁ : R} {r₂ : ℝ} (h : ‖r₁‖ < r₂) :
    (fun n ↦ (n : R) ^ k * r₁ ^ n : ℕ → R) =o[atTop] fun n ↦ r₂ ^ n := by
  by_cases h0 : r₁ = 0
  · refine (isLittleO_zero _ _).congr' (mem_atTop_sets.2 <| ⟨1, fun n hn ↦ ?_⟩) EventuallyEq.rfl
    simp [zero_pow (one_le_iff_ne_zero.1 hn), h0]
  rw [← Ne, ← norm_pos_iff] at h0
  have A : (fun n ↦ (n : R) ^ k : ℕ → R) =o[atTop] fun n ↦ (r₂ / ‖r₁‖) ^ n :=
    isLittleO_pow_const_const_pow_of_one_lt k ((one_lt_div h0).2 h)
  suffices (fun n ↦ r₁ ^ n) =O[atTop] fun n ↦ ‖r₁‖ ^ n by
    simpa [div_mul_cancel₀ _ (pow_pos h0 _).ne', div_pow] using A.mul_isBigO this
  exact .of_norm_eventuallyLE <| eventually_norm_pow_le r₁

theorem tendsto_pow_const_div_const_pow_of_one_lt (k : ℕ) {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n ↦ (n : ℝ) ^ k / r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  (isLittleO_pow_const_const_pow_of_one_lt k hr).tendsto_div_nhds_zero

/-- If `|r| < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`. -/
theorem tendsto_pow_const_mul_const_pow_of_abs_lt_one (k : ℕ) {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun n ↦ (n : ℝ) ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  by_cases h0 : r = 0
  · exact tendsto_const_nhds.congr'
      (mem_atTop_sets.2 ⟨1, fun n hn ↦ by simp [zero_lt_one.trans_le hn |>.ne', h0]⟩)
  have hr' : 1 < |r|⁻¹ := (one_lt_inv₀ (abs_pos.2 h0)).2 hr
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [div_eq_mul_inv] using tendsto_pow_const_div_const_pow_of_one_lt k hr'

/-- For `k ≠ 0` and a constant `r` the function `r / n ^ k` tends to zero. -/
lemma tendsto_const_div_pow (r : ℝ) (k : ℕ) (hk : k ≠ 0) :
    Tendsto (fun n : ℕ => r / n ^ k) atTop (𝓝 0) := by
  simpa using Filter.Tendsto.const_div_atTop (tendsto_natCast_atTop_atTop (R := ℝ).comp
    (tendsto_pow_atTop hk) ) r

/-- If `0 ≤ r < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`.
This is a specialized version of `tendsto_pow_const_mul_const_pow_of_abs_lt_one`, singled out
for ease of application. -/
theorem tendsto_pow_const_mul_const_pow_of_lt_one (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n ↦ (n : ℝ) ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  tendsto_pow_const_mul_const_pow_of_abs_lt_one k (abs_lt.2 ⟨neg_one_lt_zero.trans_le hr, h'r⟩)

/-- If `|r| < 1`, then `n * r ^ n` tends to zero. -/
theorem tendsto_self_mul_const_pow_of_abs_lt_one {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun n ↦ n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr

/-- If `0 ≤ r < 1`, then `n * r ^ n` tends to zero. This is a specialized version of
`tendsto_self_mul_const_pow_of_abs_lt_one`, singled out for ease of application. -/
theorem tendsto_self_mul_const_pow_of_lt_one {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n ↦ n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_lt_one 1 hr h'r

/-- In a normed ring, the powers of an element x with `‖x‖ < 1` tend to zero. -/
theorem tendsto_pow_atTop_nhds_zero_of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R}
    (h : ‖x‖ < 1) :
    Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_pow_le x)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h

theorem tendsto_pow_atTop_nhds_zero_of_abs_lt_one {r : ℝ} (h : |r| < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one h

lemma tendsto_pow_atTop_nhds_zero_iff_norm_lt_one {R : Type*} [SeminormedRing R] [NormMulClass R]
    {x : R} : Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) ↔ ‖x‖ < 1 := by
  -- this proof is slightly fiddly since `‖x ^ n‖ = ‖x‖ ^ n` might not hold for `n = 0`
  refine ⟨?_, tendsto_pow_atTop_nhds_zero_of_norm_lt_one⟩
  rw [← abs_of_nonneg (norm_nonneg _), ← tendsto_pow_atTop_nhds_zero_iff,
    tendsto_zero_iff_norm_tendsto_zero]
  apply Tendsto.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn IH => simp [pow_succ, IH]

/-! ### Geometric series -/

/-- A normed ring has summable geometric series if, for all `ξ` of norm `< 1`, the geometric series
`∑ ξ ^ n` converges. This holds both in complete normed rings and in normed fields, providing a
convenient abstraction of these two classes to avoid repeating the same proofs. -/
class HasSummableGeomSeries (K : Type*) [NormedRing K] : Prop where
  summable_geometric_of_norm_lt_one : ∀ (ξ : K), ‖ξ‖ < 1 → Summable (fun n ↦ ξ ^ n)

lemma summable_geometric_of_norm_lt_one {K : Type*} [NormedRing K] [HasSummableGeomSeries K]
    {x : K} (h : ‖x‖ < 1) : Summable (fun n ↦ x ^ n) :=
  HasSummableGeomSeries.summable_geometric_of_norm_lt_one x h

instance {R : Type*} [NormedRing R] [CompleteSpace R] : HasSummableGeomSeries R := by
  constructor
  intro x hx
  have h1 : Summable fun n : ℕ ↦ ‖x‖ ^ n := summable_geometric_of_lt_one (norm_nonneg _) hx
  exact h1.of_norm_bounded_eventually_nat (eventually_norm_pow_le x)

section HasSummableGeometricSeries

variable {R : Type*} [NormedRing R]

open NormedSpace

/-- Bound for the sum of a geometric series in a normed ring. This formula does not assume that the
normed ring satisfies the axiom `‖1‖ = 1`. -/
theorem tsum_geometric_le_of_norm_lt_one (x : R) (h : ‖x‖ < 1) :
    ‖∑' n : ℕ, x ^ n‖ ≤ ‖(1 : R)‖ - 1 + (1 - ‖x‖)⁻¹ := by
  by_cases hx : Summable (fun n ↦ x ^ n)
  · rw [hx.tsum_eq_zero_add]
    simp only [_root_.pow_zero]
    refine le_trans (norm_add_le _ _) ?_
    have : ‖∑' b : ℕ, (fun n ↦ x ^ (n + 1)) b‖ ≤ (1 - ‖x‖)⁻¹ - 1 := by
      refine tsum_of_norm_bounded ?_ fun b ↦ norm_pow_le' _ (Nat.succ_pos b)
      convert (hasSum_nat_add_iff' 1).mpr (hasSum_geometric_of_lt_one (norm_nonneg x) h)
      simp
    linarith
  · simp [tsum_eq_zero_of_not_summable hx]
    nontriviality R
    have : 1 ≤ ‖(1 : R)‖ := one_le_norm_one R
    have : 0 ≤ (1 - ‖x‖) ⁻¹ := inv_nonneg.2 (by linarith)
    linarith

variable [HasSummableGeomSeries R]

theorem geom_series_mul_neg (x : R) (h : ‖x‖ < 1) : (∑' i : ℕ, x ^ i) * (1 - x) = 1 := by
  have := (summable_geometric_of_norm_lt_one h).hasSum.mul_right (1 - x)
  refine tendsto_nhds_unique this.tendsto_sum_nat ?_
  have : Tendsto (fun n : ℕ ↦ 1 - x ^ n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_norm_lt_one h)
  convert← this
  rw [← geom_sum_mul_neg, Finset.sum_mul]

theorem mul_neg_geom_series (x : R) (h : ‖x‖ < 1) : (1 - x) * ∑' i : ℕ, x ^ i = 1 := by
  have := (summable_geometric_of_norm_lt_one h).hasSum.mul_left (1 - x)
  refine tendsto_nhds_unique this.tendsto_sum_nat ?_
  have : Tendsto (fun n : ℕ ↦ 1 - x ^ n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_norm_lt_one h)
  convert← this
  rw [← mul_neg_geom_sum, Finset.mul_sum]

theorem geom_series_succ (x : R) (h : ‖x‖ < 1) : ∑' i : ℕ, x ^ (i + 1) = ∑' i : ℕ, x ^ i - 1 := by
  rw [eq_sub_iff_add_eq, (summable_geometric_of_norm_lt_one h).tsum_eq_zero_add,
    pow_zero, add_comm]

theorem geom_series_mul_shift (x : R) (h : ‖x‖ < 1) :
    x * ∑' i : ℕ, x ^ i = ∑' i : ℕ, x ^ (i + 1) := by
  simp_rw [← (summable_geometric_of_norm_lt_one h).tsum_mul_left, ← _root_.pow_succ']

theorem geom_series_mul_one_add (x : R) (h : ‖x‖ < 1) :
    (1 + x) * ∑' i : ℕ, x ^ i = 2 * ∑' i : ℕ, x ^ i - 1 := by
  rw [add_mul, one_mul, geom_series_mul_shift x h, geom_series_succ x h, two_mul, add_sub_assoc]

/-- In a normed ring with summable geometric series, a perturbation of `1` by an element `t`
of distance less than `1` from `1` is a unit.  Here we construct its `Units` structure. -/
@[simps val]
def Units.oneSub (t : R) (h : ‖t‖ < 1) : Rˣ where
  val := 1 - t
  inv := ∑' n : ℕ, t ^ n
  val_inv := mul_neg_geom_series t h
  inv_val := geom_series_mul_neg t h

theorem geom_series_eq_inverse (x : R) (h : ‖x‖ < 1) :
    ∑' i, x ^ i = Ring.inverse (1 - x) := by
  change (Units.oneSub x h) ⁻¹ = Ring.inverse (1 - x)
  rw [← Ring.inverse_unit]
  rfl

theorem hasSum_geom_series_inverse (x : R) (h : ‖x‖ < 1) :
    HasSum (fun i ↦ x ^ i) (Ring.inverse (1 - x)) := by
  convert (summable_geometric_of_norm_lt_one h).hasSum
  exact (geom_series_eq_inverse x h).symm

lemma isUnit_one_sub_of_norm_lt_one {x : R} (h : ‖x‖ < 1) : IsUnit (1 - x) :=
  ⟨Units.oneSub x h, rfl⟩

end HasSummableGeometricSeries

section Geometric

variable {K : Type*} [NormedDivisionRing K] {ξ : K}

theorem hasSum_geometric_of_norm_lt_one (h : ‖ξ‖ < 1) : HasSum (fun n : ℕ ↦ ξ ^ n) (1 - ξ)⁻¹ := by
  have xi_ne_one : ξ ≠ 1 := by
    contrapose! h
    simp [h]
  have A : Tendsto (fun n ↦ (ξ ^ n - 1) * (ξ - 1)⁻¹) atTop (𝓝 ((0 - 1) * (ξ - 1)⁻¹)) :=
    ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one h).sub tendsto_const_nhds).mul tendsto_const_nhds
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  · simpa [geom_sum_eq, xi_ne_one, neg_inv, div_eq_mul_inv] using A
  · simp [norm_pow, summable_geometric_of_lt_one (norm_nonneg _) h]

instance : HasSummableGeomSeries K :=
  ⟨fun _ h ↦ (hasSum_geometric_of_norm_lt_one h).summable⟩

theorem tsum_geometric_of_norm_lt_one (h : ‖ξ‖ < 1) : ∑' n : ℕ, ξ ^ n = (1 - ξ)⁻¹ :=
  (hasSum_geometric_of_norm_lt_one h).tsum_eq

theorem hasSum_geometric_of_abs_lt_one {r : ℝ} (h : |r| < 1) :
    HasSum (fun n : ℕ ↦ r ^ n) (1 - r)⁻¹ :=
  hasSum_geometric_of_norm_lt_one h

theorem summable_geometric_of_abs_lt_one {r : ℝ} (h : |r| < 1) : Summable fun n : ℕ ↦ r ^ n :=
  summable_geometric_of_norm_lt_one h

theorem tsum_geometric_of_abs_lt_one {r : ℝ} (h : |r| < 1) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  tsum_geometric_of_norm_lt_one h

/-- A geometric series in a normed field is summable iff the norm of the common ratio is less than
one. -/
@[simp]
theorem summable_geometric_iff_norm_lt_one : (Summable fun n : ℕ ↦ ξ ^ n) ↔ ‖ξ‖ < 1 := by
  refine ⟨fun h ↦ ?_, summable_geometric_of_norm_lt_one⟩
  obtain ⟨k : ℕ, hk : dist (ξ ^ k) 0 < 1⟩ :=
    (h.tendsto_cofinite_zero.eventually (ball_mem_nhds _ zero_lt_one)).exists
  simp only [norm_pow, dist_zero_right] at hk
  rw [← one_pow k] at hk
  exact lt_of_pow_lt_pow_left₀ _ zero_le_one hk

end Geometric

section MulGeometric

variable {R : Type*} [NormedRing R] {𝕜 : Type*} [NormedDivisionRing 𝕜]

theorem summable_norm_mul_geometric_of_norm_lt_one {k : ℕ} {r : R}
    (hr : ‖r‖ < 1) {u : ℕ → ℕ} (hu : (fun n ↦ (u n : ℝ)) =O[atTop] (fun n ↦ (↑(n ^ k) : ℝ))) :
    Summable fun n : ℕ ↦ ‖(u n * r ^ n : R)‖ := by
  rcases exists_between hr with ⟨r', hrr', h⟩
  rw [← norm_norm] at hrr'
  apply summable_of_isBigO_nat (summable_geometric_of_lt_one ((norm_nonneg _).trans hrr'.le) h)
  calc
  fun n ↦ ‖↑(u n) * r ^ n‖
  _ =O[atTop] fun n ↦ u n * ‖r‖ ^ n := by
      apply (IsBigOWith.of_bound (c := ‖(1 : R)‖) ?_).isBigO
      filter_upwards [eventually_norm_pow_le r] with n hn
      simp only [norm_mul, Real.norm_eq_abs, abs_cast, norm_pow, abs_norm]
      apply (norm_mul_le _ _).trans
      have : ‖(u n : R)‖ * ‖r ^ n‖ ≤ (u n * ‖(1 : R)‖) * ‖r‖ ^ n := by
        gcongr; exact norm_cast_le (u n)
      exact this.trans (le_of_eq (by ring))
  _ =O[atTop] fun n ↦ ↑(n ^ k) * ‖r‖ ^ n := hu.mul (isBigO_refl _ _)
  _ =O[atTop] fun n ↦ r' ^ n := by
      simp only [cast_pow]
      exact (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt k hrr').isBigO

theorem summable_norm_pow_mul_geometric_of_norm_lt_one (k : ℕ) {r : R}
    (hr : ‖r‖ < 1) : Summable fun n : ℕ ↦ ‖((n : R) ^ k * r ^ n : R)‖ := by
  simp only [← cast_pow]
  exact summable_norm_mul_geometric_of_norm_lt_one (k := k) (u := fun n ↦ n ^ k) hr
    (isBigO_refl _ _)

theorem summable_norm_geometric_of_norm_lt_one {r : R}
    (hr : ‖r‖ < 1) : Summable fun n : ℕ ↦ ‖(r ^ n : R)‖ := by
  simpa using summable_norm_pow_mul_geometric_of_norm_lt_one 0 hr

variable [HasSummableGeomSeries R]

lemma hasSum_choose_mul_geometric_of_norm_lt_one'
    (k : ℕ) {r : R} (hr : ‖r‖ < 1) :
    HasSum (fun n ↦ (n + k).choose k * r ^ n) (Ring.inverse (1 - r) ^ (k + 1)) := by
  induction k with
  | zero => simpa using hasSum_geom_series_inverse r hr
  | succ k ih =>
      have I1 : Summable (fun (n : ℕ) ↦ ‖(n + k).choose k * r ^ n‖) := by
        apply summable_norm_mul_geometric_of_norm_lt_one (k := k) hr
        apply isBigO_iff.2 ⟨2 ^ k, ?_⟩
        filter_upwards [Ioi_mem_atTop k] with n (hn : k < n)
        simp only [Real.norm_eq_abs, abs_cast, cast_pow, norm_pow]
        norm_cast
        calc (n + k).choose k
          _ ≤ (2 * n).choose k := choose_le_choose k (by omega)
          _ ≤ (2 * n) ^ k := Nat.choose_le_pow _ _
          _ = 2 ^ k * n ^ k := Nat.mul_pow 2 n k
      convert hasSum_sum_range_mul_of_summable_norm' I1 ih.summable
        (summable_norm_geometric_of_norm_lt_one hr) (summable_geometric_of_norm_lt_one hr) with n
      · have : ∑ i ∈ Finset.range (n + 1), ↑((i + k).choose k) * r ^ i * r ^ (n - i) =
            ∑ i ∈ Finset.range (n + 1), ↑((i + k).choose k) * r ^ n := by
          apply Finset.sum_congr rfl (fun i hi ↦ ?_)
          simp only [Finset.mem_range] at hi
          rw [mul_assoc, ← pow_add, show i + (n - i) = n by omega]
        simp [this, ← sum_mul, ← Nat.cast_sum, sum_range_add_choose n k, add_assoc]
      · rw [ih.tsum_eq, (hasSum_geom_series_inverse r hr).tsum_eq, pow_succ]

lemma summable_choose_mul_geometric_of_norm_lt_one (k : ℕ) {r : R} (hr : ‖r‖ < 1) :
    Summable (fun n ↦ (n + k).choose k * r ^ n) :=
  (hasSum_choose_mul_geometric_of_norm_lt_one' k hr).summable

lemma tsum_choose_mul_geometric_of_norm_lt_one' (k : ℕ) {r : R} (hr : ‖r‖ < 1) :
    ∑' n, (n + k).choose k * r ^ n = (Ring.inverse (1 - r)) ^ (k + 1) :=
  (hasSum_choose_mul_geometric_of_norm_lt_one' k hr).tsum_eq

lemma hasSum_choose_mul_geometric_of_norm_lt_one
    (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    HasSum (fun n ↦ (n + k).choose k * r ^ n) (1 / (1 - r) ^ (k + 1)) := by
  convert hasSum_choose_mul_geometric_of_norm_lt_one' k hr
  simp

lemma tsum_choose_mul_geometric_of_norm_lt_one (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' n, (n + k).choose k * r ^ n = 1/ (1 - r) ^ (k + 1) :=
  (hasSum_choose_mul_geometric_of_norm_lt_one k hr).tsum_eq

lemma summable_descFactorial_mul_geometric_of_norm_lt_one (k : ℕ) {r : R} (hr : ‖r‖ < 1) :
    Summable (fun n ↦ (n + k).descFactorial k * r ^ n) := by
  convert (summable_choose_mul_geometric_of_norm_lt_one k hr).mul_left (k.factorial : R)
    using 2 with n
  simp [← mul_assoc, descFactorial_eq_factorial_mul_choose (n + k) k]

open Polynomial in
theorem summable_pow_mul_geometric_of_norm_lt_one (k : ℕ) {r : R} (hr : ‖r‖ < 1) :
    Summable (fun n ↦ (n : R) ^ k * r ^ n : ℕ → R) := by
  refine Nat.strong_induction_on k fun k hk => ?_
  obtain ⟨a, ha⟩ : ∃ (a : ℕ → ℕ), ∀ n, (n + k).descFactorial k
      = n ^ k + ∑ i ∈ range k, a i * n ^ i := by
    let P : Polynomial ℕ := (ascPochhammer ℕ k).comp (Polynomial.X + C 1)
    refine ⟨fun i ↦ P.coeff i, fun n ↦ ?_⟩
    have mP : Monic P := Monic.comp_X_add_C (monic_ascPochhammer ℕ k) _
    have dP : P.natDegree = k := by
      simp only [P, natDegree_comp, ascPochhammer_natDegree, mul_one, natDegree_X_add_C]
    have A : (n + k).descFactorial k = P.eval n := by
      have : n + 1 + k - 1 = n + k := by omega
      simp [P, ascPochhammer_nat_eq_descFactorial, this]
    conv_lhs => rw [A, mP.as_sum, dP]
    simp [eval_finset_sum]
  have : Summable (fun n ↦ (n + k).descFactorial k * r ^ n
      - ∑ i ∈ range k, a i * n ^ (i : ℕ) * r ^ n) := by
    apply (summable_descFactorial_mul_geometric_of_norm_lt_one k hr).sub
    apply summable_sum (fun i hi ↦ ?_)
    simp_rw [mul_assoc]
    simp only [Finset.mem_range] at hi
    exact (hk _ hi).mul_left _
  convert this using 1
  ext n
  simp [ha n, add_mul, sum_mul]

/-- If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `HasSum` version in a general ring
with summable geometric series. For a version in a field, using division instead of `Ring.inverse`,
see `hasSum_coe_mul_geometric_of_norm_lt_one`. -/
theorem hasSum_coe_mul_geometric_of_norm_lt_one'
    {x : R} (h : ‖x‖ < 1) :
    HasSum (fun n ↦ n * x ^ n : ℕ → R) (x * (Ring.inverse (1 - x)) ^ 2) := by
  have A : HasSum (fun (n : ℕ) ↦ (n + 1) * x ^ n) (Ring.inverse (1 - x) ^ 2) := by
    convert hasSum_choose_mul_geometric_of_norm_lt_one' 1 h with n
    simp
  have B : HasSum (fun (n : ℕ) ↦ x ^ n) (Ring.inverse (1 - x)) := hasSum_geom_series_inverse x h
  convert A.sub B using 1
  · ext n
    simp [add_mul]
  · symm
    calc Ring.inverse (1 - x) ^ 2 - Ring.inverse (1 - x)
    _ = Ring.inverse (1 - x) ^ 2 - ((1 - x) * Ring.inverse (1 - x)) * Ring.inverse (1 - x) := by
      simp [Ring.mul_inverse_cancel (1 - x) (isUnit_one_sub_of_norm_lt_one h)]
    _ = x * Ring.inverse (1 - x) ^ 2 := by noncomm_ring

/-- If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, version in a general ring with
summable geometric series. For a version in a field, using division instead of `Ring.inverse`,
see `tsum_coe_mul_geometric_of_norm_lt_one`. -/
theorem tsum_coe_mul_geometric_of_norm_lt_one'
    {r : 𝕜} (hr : ‖r‖ < 1) : (∑' n : ℕ, n * r ^ n : 𝕜) = r * Ring.inverse (1 - r) ^ 2 :=
  (hasSum_coe_mul_geometric_of_norm_lt_one' hr).tsum_eq

/-- If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `HasSum` version. -/
theorem hasSum_coe_mul_geometric_of_norm_lt_one {r : 𝕜} (hr : ‖r‖ < 1) :
    HasSum (fun n ↦ n * r ^ n : ℕ → 𝕜) (r / (1 - r) ^ 2) := by
  convert hasSum_coe_mul_geometric_of_norm_lt_one' hr using 1
  simp [div_eq_mul_inv]

/-- If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`. -/
theorem tsum_coe_mul_geometric_of_norm_lt_one {r : 𝕜} (hr : ‖r‖ < 1) :
    (∑' n : ℕ, n * r ^ n : 𝕜) = r / (1 - r) ^ 2 :=
  (hasSum_coe_mul_geometric_of_norm_lt_one hr).tsum_eq

end MulGeometric

section SummableLeGeometric

variable [SeminormedAddCommGroup α] {r C : ℝ} {f : ℕ → α}

nonrec theorem SeminormedAddCommGroup.cauchySeq_of_le_geometric {C : ℝ} {r : ℝ} (hr : r < 1)
    {u : ℕ → α} (h : ∀ n, ‖u n - u (n + 1)‖ ≤ C * r ^ n) : CauchySeq u :=
  cauchySeq_of_le_geometric r C hr (by simpa [dist_eq_norm] using h)

theorem dist_partial_sum_le_of_le_geometric (hf : ∀ n, ‖f n‖ ≤ C * r ^ n) (n : ℕ) :
    dist (∑ i ∈ range n, f i) (∑ i ∈ range (n + 1), f i) ≤ C * r ^ n := by
  rw [sum_range_succ, dist_eq_norm, ← norm_neg, neg_sub, add_sub_cancel_left]
  exact hf n

/-- If `‖f n‖ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` form a
Cauchy sequence. This lemma does not assume `0 ≤ r` or `0 ≤ C`. -/
theorem cauchySeq_finset_of_geometric_bound (hr : r < 1) (hf : ∀ n, ‖f n‖ ≤ C * r ^ n) :
    CauchySeq fun s : Finset ℕ ↦ ∑ x ∈ s, f x :=
  cauchySeq_finset_of_norm_bounded
    (aux_hasSum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf)).summable hf

/-- If `‖f n‖ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` are within
distance `C * r ^ n / (1 - r)` of the sum of the series. This lemma does not assume `0 ≤ r` or
`0 ≤ C`. -/
theorem norm_sub_le_of_geometric_bound_of_hasSum (hr : r < 1) (hf : ∀ n, ‖f n‖ ≤ C * r ^ n) {a : α}
    (ha : HasSum f a) (n : ℕ) : ‖(∑ x ∈ Finset.range n, f x) - a‖ ≤ C * r ^ n / (1 - r) := by
  rw [← dist_eq_norm]
  apply dist_le_of_le_geometric_of_tendsto r C hr (dist_partial_sum_le_of_le_geometric hf)
  exact ha.tendsto_sum_nat

@[simp]
theorem dist_partial_sum (u : ℕ → α) (n : ℕ) :
    dist (∑ k ∈ range (n + 1), u k) (∑ k ∈ range n, u k) = ‖u n‖ := by
  simp [dist_eq_norm, sum_range_succ]

@[simp]
theorem dist_partial_sum' (u : ℕ → α) (n : ℕ) :
    dist (∑ k ∈ range n, u k) (∑ k ∈ range (n + 1), u k) = ‖u n‖ := by
  simp [dist_eq_norm', sum_range_succ]

theorem cauchy_series_of_le_geometric {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1)
    (h : ∀ n, ‖u n‖ ≤ C * r ^ n) : CauchySeq fun n ↦ ∑ k ∈ range n, u k :=
  cauchySeq_of_le_geometric r C hr (by simp [h])

theorem NormedAddCommGroup.cauchy_series_of_le_geometric' {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1)
    (h : ∀ n, ‖u n‖ ≤ C * r ^ n) : CauchySeq fun n ↦ ∑ k ∈ range (n + 1), u k :=
  (cauchy_series_of_le_geometric hr h).comp_tendsto <| tendsto_add_atTop_nat 1

theorem NormedAddCommGroup.cauchy_series_of_le_geometric'' {C : ℝ} {u : ℕ → α} {N : ℕ} {r : ℝ}
    (hr₀ : 0 < r) (hr₁ : r < 1) (h : ∀ n ≥ N, ‖u n‖ ≤ C * r ^ n) :
    CauchySeq fun n ↦ ∑ k ∈ range (n + 1), u k := by
  set v : ℕ → α := fun n ↦ if n < N then 0 else u n
  have hC : 0 ≤ C :=
    (mul_nonneg_iff_of_pos_right <| pow_pos hr₀ N).mp ((norm_nonneg _).trans <| h N <| le_refl N)
  have : ∀ n ≥ N, u n = v n := by
    intro n hn
    simp [v, if_neg (not_lt.mpr hn)]
  apply cauchySeq_sum_of_eventually_eq this
    (NormedAddCommGroup.cauchy_series_of_le_geometric' hr₁ _)
  · exact C
  intro n
  simp only [v]
  split_ifs with H
  · rw [norm_zero]
    exact mul_nonneg hC (pow_nonneg hr₀.le _)
  · push_neg at H
    exact h _ H

/-- The term norms of any convergent series are bounded by a constant. -/
lemma exists_norm_le_of_cauchySeq (h : CauchySeq fun n ↦ ∑ k ∈ range n, f k) :
    ∃ C, ∀ n, ‖f n‖ ≤ C := by
  obtain ⟨b, ⟨_, key, _⟩⟩ := cauchySeq_iff_le_tendsto_0.mp h
  refine ⟨b 0, fun n ↦ ?_⟩
  simpa only [dist_partial_sum'] using key n (n + 1) 0 (_root_.zero_le _) (_root_.zero_le _)

end SummableLeGeometric

/-! ### Summability tests based on comparison with geometric series -/

theorem summable_of_ratio_norm_eventually_le {α : Type*} [SeminormedAddCommGroup α]
    [CompleteSpace α] {f : ℕ → α} {r : ℝ} (hr₁ : r < 1)
    (h : ∀ᶠ n in atTop, ‖f (n + 1)‖ ≤ r * ‖f n‖) : Summable f := by
  by_cases hr₀ : 0 ≤ r
  · rw [eventually_atTop] at h
    rcases h with ⟨N, hN⟩
    rw [← @summable_nat_add_iff α _ _ _ _ N]
    refine .of_norm_bounded (g := fun n ↦ ‖f N‖ * r ^ n)
      (Summable.mul_left _ <| summable_geometric_of_lt_one hr₀ hr₁) fun n ↦ ?_
    simp only
    conv_rhs => rw [mul_comm, ← zero_add N]
    refine le_geom (u := fun n ↦ ‖f (n + N)‖) hr₀ n fun i _ ↦ ?_
    convert hN (i + N) (N.le_add_left i) using 3
    ac_rfl
  · push_neg at hr₀
    refine .of_norm_bounded_eventually_nat summable_zero ?_
    filter_upwards [h] with _ hn
    by_contra! h
    exact not_lt.mpr (norm_nonneg _) (lt_of_le_of_lt hn <| mul_neg_of_neg_of_pos hr₀ h)

theorem summable_of_ratio_test_tendsto_lt_one {α : Type*} [NormedAddCommGroup α] [CompleteSpace α]
    {f : ℕ → α} {l : ℝ} (hl₁ : l < 1) (hf : ∀ᶠ n in atTop, f n ≠ 0)
    (h : Tendsto (fun n ↦ ‖f (n + 1)‖ / ‖f n‖) atTop (𝓝 l)) : Summable f := by
  rcases exists_between hl₁ with ⟨r, hr₀, hr₁⟩
  refine summable_of_ratio_norm_eventually_le hr₁ ?_
  filter_upwards [h.eventually_le_const hr₀, hf] with _ _ h₁
  rwa [← div_le_iff₀ (norm_pos_iff.mpr h₁)]

theorem not_summable_of_ratio_norm_eventually_ge {α : Type*} [SeminormedAddCommGroup α] {f : ℕ → α}
    {r : ℝ} (hr : 1 < r) (hf : ∃ᶠ n in atTop, ‖f n‖ ≠ 0)
    (h : ∀ᶠ n in atTop, r * ‖f n‖ ≤ ‖f (n + 1)‖) : ¬Summable f := by
  rw [eventually_atTop] at h
  rcases h with ⟨N₀, hN₀⟩
  rw [frequently_atTop] at hf
  rcases hf N₀ with ⟨N, hNN₀ : N₀ ≤ N, hN⟩
  rw [← @summable_nat_add_iff α _ _ _ _ N]
  refine mt Summable.tendsto_atTop_zero
    fun h' ↦ not_tendsto_atTop_of_tendsto_nhds (tendsto_norm_zero.comp h') ?_
  convert tendsto_atTop_of_geom_le _ hr _
  · refine lt_of_le_of_ne (norm_nonneg _) ?_
    intro h''
    specialize hN₀ N hNN₀
    simp only [comp_apply, zero_add] at h''
    exact hN h''.symm
  · grind

theorem not_summable_of_ratio_test_tendsto_gt_one {α : Type*} [SeminormedAddCommGroup α]
    {f : ℕ → α} {l : ℝ} (hl : 1 < l) (h : Tendsto (fun n ↦ ‖f (n + 1)‖ / ‖f n‖) atTop (𝓝 l)) :
    ¬Summable f := by
  have key : ∀ᶠ n in atTop, ‖f n‖ ≠ 0 := by
    filter_upwards [h.eventually_const_le hl] with _ hn hc
    rw [hc, _root_.div_zero] at hn
    linarith
  rcases exists_between hl with ⟨r, hr₀, hr₁⟩
  refine not_summable_of_ratio_norm_eventually_ge hr₀ key.frequently ?_
  filter_upwards [h.eventually_const_le hr₁, key] with _ _ h₁
  rwa [← le_div_iff₀ (lt_of_le_of_ne (norm_nonneg _) h₁.symm)]

section NormedDivisionRing

variable [NormedDivisionRing α] [CompleteSpace α] {f : ℕ → α}

/-- If a power series converges at `w`, it converges absolutely at all `z` of smaller norm. -/
theorem summable_powerSeries_of_norm_lt {w z : α}
    (h : CauchySeq fun n ↦ ∑ i ∈ range n, f i * w ^ i) (hz : ‖z‖ < ‖w‖) :
    Summable fun n ↦ f n * z ^ n := by
  have hw : 0 < ‖w‖ := (norm_nonneg z).trans_lt hz
  obtain ⟨C, hC⟩ := exists_norm_le_of_cauchySeq h
  rw [summable_iff_cauchySeq_finset]
  refine cauchySeq_finset_of_geometric_bound (r := ‖z‖ / ‖w‖) (C := C) ((div_lt_one hw).mpr hz)
    (fun n ↦ ?_)
  rw [norm_mul, norm_pow, div_pow, ← mul_comm_div]
  conv at hC => enter [n]; rw [norm_mul, norm_pow, ← _root_.le_div_iff₀ (by positivity)]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (norm_nonneg z) n)

/-- If a power series converges at 1, it converges absolutely at all `z` of smaller norm. -/
theorem summable_powerSeries_of_norm_lt_one {z : α}
    (h : CauchySeq fun n ↦ ∑ i ∈ range n, f i) (hz : ‖z‖ < 1) :
    Summable fun n ↦ f n * z ^ n :=
  summable_powerSeries_of_norm_lt (w := 1) (by simp [h]) (by simp [hz])

end NormedDivisionRing

section

/-! ### Dirichlet and alternating series tests -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {b : ℝ} {f : ℕ → ℝ} {z : ℕ → E}

/-- **Dirichlet's test** for monotone sequences. -/
theorem Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) (hgb : ∀ n, ‖∑ i ∈ range n, z i‖ ≤ b) :
    CauchySeq fun n ↦ ∑ i ∈ range n, f i • z i := by
  rw [← cauchySeq_shift 1]
  simp_rw [Finset.sum_range_by_parts _ _ (Nat.succ _), sub_eq_add_neg, Nat.succ_sub_succ_eq_sub,
    tsub_zero]
  apply (NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hf0
    ⟨b, eventually_map.mpr <| Eventually.of_forall fun n ↦ hgb <| n + 1⟩).cauchySeq.add
  refine CauchySeq.neg ?_
  refine cauchySeq_range_of_norm_bounded ?_
    (fun n ↦ ?_ : ∀ n, ‖(f (n + 1) + -f n) • (Finset.range (n + 1)).sum z‖ ≤ b * |f (n + 1) - f n|)
  · simp_rw [abs_of_nonneg (sub_nonneg_of_le (hfa (Nat.le_succ _))), ← mul_sum]
    apply Real.uniformContinuous_const_mul.comp_cauchySeq
    simp_rw [sum_range_sub, sub_eq_add_neg]
    exact (Tendsto.cauchySeq hf0).add_const
  · rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hgb _) (abs_nonneg _)

/-- **Dirichlet's test** for antitone sequences. -/
theorem Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) (hzb : ∀ n, ‖∑ i ∈ range n, z i‖ ≤ b) :
    CauchySeq fun n ↦ ∑ i ∈ range n, f i • z i := by
  have hfa' : Monotone fun n ↦ -f n := fun _ _ hab ↦ neg_le_neg <| hfa hab
  have hf0' : Tendsto (fun n ↦ -f n) atTop (𝓝 0) := by
    convert hf0.neg
    norm_num
  convert (hfa'.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0' hzb).neg
  simp

theorem norm_sum_neg_one_pow_le (n : ℕ) : ‖∑ i ∈ range n, (-1 : ℝ) ^ i‖ ≤ 1 := by
  rw [neg_one_geom_sum]
  split_ifs <;> norm_num

/-- The **alternating series test** for monotone sequences.
See also `Monotone.tendsto_alternating_series_of_tendsto_zero`. -/
theorem Monotone.cauchySeq_alternating_series_of_tendsto_zero (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) : CauchySeq fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

/-- The **alternating series test** for monotone sequences. -/
theorem Monotone.tendsto_alternating_series_of_tendsto_zero (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete <| hfa.cauchySeq_alternating_series_of_tendsto_zero hf0

/-- The **alternating series test** for antitone sequences.
See also `Antitone.tendsto_alternating_series_of_tendsto_zero`. -/
theorem Antitone.cauchySeq_alternating_series_of_tendsto_zero (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) : CauchySeq fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

/-- The **alternating series test** for antitone sequences. -/
theorem Antitone.tendsto_alternating_series_of_tendsto_zero (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete <| hfa.cauchySeq_alternating_series_of_tendsto_zero hf0

end

/-! ### Partial sum bounds on alternating convergent series -/

section

variable {E : Type*} [Ring E] [PartialOrder E] [IsOrderedRing E]
  [TopologicalSpace E] [OrderClosedTopology E]
  {l : E} {f : ℕ → E}

/-- Partial sums of an alternating monotone series with an even number of terms provide
upper bounds on the limit. -/
theorem Monotone.tendsto_le_alternating_series
    (hfl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfm : Monotone f) (k : ℕ) : l ≤ ∑ i ∈ range (2 * k), (-1) ^ i * f i := by
  have ha : Antitone (fun n ↦ ∑ i ∈ range (2 * n), (-1) ^ i * f i) := by
    refine antitone_nat_of_succ_le (fun n ↦ ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, one_mul,
      ← sub_eq_add_neg, sub_le_iff_le_add]
    gcongr
    exact hfm (by omega)
  exact ha.le_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n ↦ by dsimp; omega) tendsto_id)) _

/-- Partial sums of an alternating monotone series with an odd number of terms provide
lower bounds on the limit. -/
theorem Monotone.alternating_series_le_tendsto
    (hfl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfm : Monotone f) (k : ℕ) : ∑ i ∈ range (2 * k + 1), (-1) ^ i * f i ≤ l := by
  have hm : Monotone (fun n ↦ ∑ i ∈ range (2 * n + 1), (-1) ^ i * f i) := by
    refine monotone_nat_of_le_succ (fun n ↦ ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      sum_range_succ _ (2 * n + 1 + 1), sum_range_succ _ (2 * n + 1)]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, neg_neg, one_mul,
      ← sub_eq_add_neg, sub_add_eq_add_sub, le_sub_iff_add_le]
    gcongr
    exact hfm (by omega)
  exact hm.ge_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n ↦ by dsimp; omega) tendsto_id)) _

/-- Partial sums of an alternating antitone series with an even number of terms provide
lower bounds on the limit. -/
theorem Antitone.alternating_series_le_tendsto
    (hfl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfa : Antitone f) (k : ℕ) : ∑ i ∈ range (2 * k), (-1) ^ i * f i ≤ l := by
  have hm : Monotone (fun n ↦ ∑ i ∈ range (2 * n), (-1) ^ i * f i) := by
    refine monotone_nat_of_le_succ (fun n ↦ ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, one_mul,
      ← sub_eq_add_neg, le_sub_iff_add_le]
    gcongr
    exact hfa (by omega)
  exact hm.ge_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n ↦ by dsimp; omega) tendsto_id)) _

/-- Partial sums of an alternating antitone series with an odd number of terms provide
upper bounds on the limit. -/
theorem Antitone.tendsto_le_alternating_series
    (hfl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfa : Antitone f) (k : ℕ) : l ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * f i := by
  have ha : Antitone (fun n ↦ ∑ i ∈ range (2 * n + 1), (-1) ^ i * f i) := by
    refine antitone_nat_of_succ_le (fun n ↦ ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, neg_neg, one_mul,
      ← sub_eq_add_neg, sub_add_eq_add_sub, sub_le_iff_le_add]
    gcongr
    exact hfa (by omega)
  exact ha.le_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n ↦ by dsimp; omega) tendsto_id)) _

end

/-!
### Factorial
-/

/-- The series `∑' n, x ^ n / n!` is summable of any `x : ℝ`. See also `expSeries_div_summable`
for a version that also works in `ℂ`, and `NormedSpace.expSeries_summable'` for a version
that works in any normed algebra over `ℝ` or `ℂ`. -/
theorem Real.summable_pow_div_factorial (x : ℝ) : Summable (fun n ↦ x ^ n / n ! : ℕ → ℝ) := by
  -- We start with trivial estimates
  have A : (0 : ℝ) < ⌊‖x‖⌋₊ + 1 := zero_lt_one.trans_le (by simp)
  have B : ‖x‖ / (⌊‖x‖⌋₊ + 1) < 1 := (div_lt_one A).2 (Nat.lt_floor_add_one _)
  -- Then we apply the ratio test. The estimate works for `n ≥ ⌊‖x‖⌋₊`.
  suffices ∀ n ≥ ⌊‖x‖⌋₊, ‖x ^ (n + 1) / (n + 1)!‖ ≤ ‖x‖ / (⌊‖x‖⌋₊ + 1) * ‖x ^ n / ↑n !‖ from
    summable_of_ratio_norm_eventually_le B (eventually_atTop.2 ⟨⌊‖x‖⌋₊, this⟩)
  -- Finally, we prove the upper estimate
  intro n hn
  calc
    ‖x ^ (n + 1) / (n + 1)!‖ = ‖x‖ / (n + 1) * ‖x ^ n / (n !)‖ := by
      rw [_root_.pow_succ', Nat.factorial_succ, Nat.cast_mul, ← _root_.div_mul_div_comm, norm_mul,
        norm_div, Real.norm_natCast, Nat.cast_succ]
    _ ≤ ‖x‖ / (⌊‖x‖⌋₊ + 1) * ‖x ^ n / (n !)‖ := by gcongr

section

/-! Limits when `f x * g x` is bounded or convergent and `f` tends to the `cobounded` filter. -/

open Bornology

variable {R K : Type*}

lemma tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded [NormedAddGroup K]
    [NormedAddGroup R] [SMulWithZero K R] [NoZeroSMulDivisors K R] [NormSMulClass K R]
    {f : α → K} {g : α → R} {l : Filter α}
    (hmul : IsBoundedUnder (· ≤ ·) l fun x ↦ ‖f x • g x‖)
    (hf : Tendsto f l (cobounded K)) :
    Tendsto g l (𝓝 0) := by
  obtain ⟨c, hc⟩ := hmul.eventually_le
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.mpr fun ε hε0 ↦ ?_
  filter_upwards [hc, hasBasis_cobounded_norm.tendsto_right_iff.mp hf (c / ε) trivial,
    hf.eventually_ne_cobounded 0] with x hfgc hεf hf0
  rcases eq_or_lt_of_le ((norm_nonneg _).trans hfgc) with rfl | hc0
  · simpa [(smul_eq_zero_iff_right hf0).mp (norm_le_zero_iff.mp hfgc)] using hε0.le
  calc
    _ = ‖g x‖ := by simp
    _ ≤ c / ‖f x‖ := by rwa [norm_smul, ← le_div_iff₀' (by positivity)] at hfgc
    _ ≤ c / (c / ε) := by gcongr
    _ = ε := div_div_cancel₀ hc0.ne'

section

variable [NormedRing K] [NormedAddCommGroup R]
variable [Module K R] [NoZeroSMulDivisors K R] [NormSMulClass K R]

lemma tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder
    {f₁ f₂ : α → K} {g : α → R} {t : R} {l : Filter α}
    (hmul : Tendsto (fun x ↦ f₁ x • g x) l (𝓝 t))
    (hf₁ : Tendsto f₁ l (cobounded K))
    (hbdd : IsBoundedUnder (· ≤ ·) l fun x ↦ ‖f₁ x - f₂ x‖) :
    Tendsto (fun x ↦ f₂ x • g x) l (𝓝 t) := by
  apply hmul.congr_dist
  dsimp
  simp_rw [dist_eq_norm, ← sub_smul, norm_smul]
  apply isBoundedUnder_le_mul_tendsto_zero
  · change IsBoundedUnder _ _ fun _ ↦ _
    simpa using hbdd
  · rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded hmul.norm.isBoundedUnder_le hf₁

-- The use case in mind for this is when `K = ℝ`, and `R = ℝ` or `ℂ`
lemma tendsto_smul_comp_nat_floor_of_tendsto_nsmul [NormSMulClass ℤ K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorSemiring K] [HasSolidNorm K] {g : ℕ → R} {t : R}
    (hg : Tendsto (fun n : ℕ ↦ n • g n) atTop (𝓝 t)) :
    Tendsto (fun x : K ↦ x • g ⌊x⌋₊) atTop (𝓝 t) := by
  replace hg : Tendsto (fun n : ℕ ↦ (n : K) • g n) atTop (𝓝 t) := mod_cast hg
  apply tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder
    (hg.comp tendsto_nat_floor_atTop)
  · exact tendsto_natCast_atTop_cobounded.comp tendsto_nat_floor_atTop
  · apply isBoundedUnder_of_eventually_le (a := ‖(1 : K)‖)
    apply Eventually.mono _ (fun x h ↦ norm_le_norm_of_abs_le_abs h)
    simpa using ⟨0, fun _ h ↦ mod_cast Nat.abs_floor_sub_le h⟩

end

lemma tendsto_smul_comp_nat_floor_of_tendsto_mul [NormedRing K] [NormedRing R]
    [Module K R] [NoZeroSMulDivisors K R] [NormSMulClass K R] [NormSMulClass ℤ K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorSemiring K] [HasSolidNorm K] {g : ℕ → R} {t : R}
    (hg : Tendsto (fun n : ℕ ↦ (n : R) * g n) atTop (𝓝 t)) :
    Tendsto (fun x : K ↦ x • g ⌊x⌋₊) atTop (𝓝 t) :=
  tendsto_smul_comp_nat_floor_of_tendsto_nsmul (by simpa only [nsmul_eq_mul] using hg)

end
