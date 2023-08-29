/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Liouville.Residual
import Mathlib.NumberTheory.Liouville.LiouvilleWith
import Mathlib.Analysis.PSeries

#align_import number_theory.liouville.measure from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Volume of the set of Liouville numbers

In this file we prove that the set of Liouville numbers with exponent (irrationality measure)
strictly greater than two is a set of Lebesgue measure zero, see
`volume_iUnion_setOf_liouvilleWith`.

Since this set is a residual set, we show that the filters `residual` and `volume.ae` are disjoint.
These filters correspond to two common notions of genericity on `ℝ`: residual sets and sets of full
measure. The fact that the filters are disjoint means that two mutually exclusive properties can be
“generic” at the same time (in the sense of different “genericity” filters).

## Tags

Liouville number, Lebesgue measure, residual, generic property
-/

open scoped Filter BigOperators ENNReal Topology NNReal

open Filter Set Metric MeasureTheory Real

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

theorem setOf_liouvilleWith_subset_aux :
    { x : ℝ | ∃ p > 2, LiouvilleWith p x } ⊆
      ⋃ m : ℤ, (· + (m : ℝ)) ⁻¹' ⋃ n > (0 : ℕ),
        { x : ℝ | ∃ᶠ b : ℕ in atTop, ∃ a ∈ Finset.Icc (0 : ℤ) b,
          |x - (a : ℤ) / b| < 1 / (b : ℝ) ^ (2 + 1 / n : ℝ) } := by
  rintro x ⟨p, hp, hxp⟩
  -- ⊢ x ∈ ⋃ (m : ℤ), (fun x => x + ↑m) ⁻¹' ⋃ (n : ℕ) (_ : n > 0), {x | ∃ᶠ (b : ℕ)  …
  rcases exists_nat_one_div_lt (sub_pos.2 hp) with ⟨n, hn⟩
  -- ⊢ x ∈ ⋃ (m : ℤ), (fun x => x + ↑m) ⁻¹' ⋃ (n : ℕ) (_ : n > 0), {x | ∃ᶠ (b : ℕ)  …
  rw [lt_sub_iff_add_lt'] at hn
  -- ⊢ x ∈ ⋃ (m : ℤ), (fun x => x + ↑m) ⁻¹' ⋃ (n : ℕ) (_ : n > 0), {x | ∃ᶠ (b : ℕ)  …
  suffices ∀ y : ℝ, LiouvilleWith p y → y ∈ Ico (0 : ℝ) 1 → ∃ᶠ b : ℕ in atTop,
      ∃ a ∈ Finset.Icc (0 : ℤ) b, |y - a / b| < 1 / (b : ℝ) ^ (2 + 1 / (n + 1 : ℕ) : ℝ) by
    simp only [mem_iUnion, mem_preimage]
    have hx : x + ↑(-⌊x⌋) ∈ Ico (0 : ℝ) 1 := by
      simp only [Int.floor_le, Int.lt_floor_add_one, add_neg_lt_iff_le_add', zero_add, and_self_iff,
        mem_Ico, Int.cast_neg, le_add_neg_iff_add_le]
    refine' ⟨-⌊x⌋, n + 1, n.succ_pos, this _ (hxp.add_int _) hx⟩
  clear hxp x; intro x hxp hx01
  -- ⊢ ∀ (y : ℝ), LiouvilleWith p y → y ∈ Ico 0 1 → ∃ᶠ (b : ℕ) in atTop, ∃ a, a ∈ F …
               -- ⊢ ∃ᶠ (b : ℕ) in atTop, ∃ a, a ∈ Finset.Icc 0 ↑b ∧ |x - ↑a / ↑b| < 1 / ↑b ^ (2  …
  refine' ((hxp.frequently_lt_rpow_neg hn).and_eventually (eventually_ge_atTop 1)).mono _
  -- ⊢ ∀ (x_1 : ℕ), (∃ m, x ≠ ↑m / ↑x_1 ∧ |x - ↑m / ↑x_1| < ↑x_1 ^ (-(2 + 1 / (↑n + …
  rintro b ⟨⟨a, -, hlt⟩, hb⟩
  -- ⊢ ∃ a, a ∈ Finset.Icc 0 ↑b ∧ |x - ↑a / ↑b| < 1 / ↑b ^ (2 + 1 / ↑(n + 1))
  rw [rpow_neg b.cast_nonneg, ← one_div, ← Nat.cast_succ] at hlt
  -- ⊢ ∃ a, a ∈ Finset.Icc 0 ↑b ∧ |x - ↑a / ↑b| < 1 / ↑b ^ (2 + 1 / ↑(n + 1))
  refine' ⟨a, _, hlt⟩
  -- ⊢ a ∈ Finset.Icc 0 ↑b
  replace hb : (1 : ℝ) ≤ b; exact Nat.one_le_cast.2 hb
  -- ⊢ 1 ≤ ↑b
                            -- ⊢ a ∈ Finset.Icc 0 ↑b
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans_le hb
  -- ⊢ a ∈ Finset.Icc 0 ↑b
  replace hlt : |x - a / b| < 1 / b
  -- ⊢ |x - ↑a / ↑b| < 1 / ↑b
  · refine' hlt.trans_le (one_div_le_one_div_of_le hb0 _)
    -- ⊢ ↑b ≤ ↑b ^ (2 + 1 / ↑(Nat.succ n))
    calc
      (b : ℝ) = (b : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
      _ ≤ (b : ℝ) ^ (2 + 1 / (n + 1 : ℕ) : ℝ) :=
        rpow_le_rpow_of_exponent_le hb (one_le_two.trans ?_)
    simpa using n.cast_add_one_pos.le
    -- 🎉 no goals
  rw [sub_div' _ _ _ hb0.ne', abs_div, abs_of_pos hb0, div_lt_div_right hb0, abs_sub_lt_iff,
    sub_lt_iff_lt_add, sub_lt_iff_lt_add, ← sub_lt_iff_lt_add'] at hlt
  rw [Finset.mem_Icc, ← Int.lt_add_one_iff, ← Int.lt_add_one_iff, ← neg_lt_iff_pos_add, add_comm, ←
    @Int.cast_lt ℝ, ← @Int.cast_lt ℝ]
  push_cast
  -- ⊢ -1 < ↑a ∧ ↑a < 1 + ↑b
  refine' ⟨lt_of_le_of_lt _ hlt.1, hlt.2.trans_le _⟩
  -- ⊢ -1 ≤ x * ↑b - 1
  · simp only [mul_nonneg hx01.left b.cast_nonneg, neg_le_sub_iff_le_add, le_add_iff_nonneg_left]
    -- 🎉 no goals
  · rw [add_le_add_iff_left]
    -- ⊢ x * ↑b ≤ ↑b
    exact mul_le_of_le_one_left hb0.le hx01.2.le
    -- 🎉 no goals
#align set_of_liouville_with_subset_aux setOf_liouvilleWith_subset_aux

/-- The set of numbers satisfying the Liouville condition with some exponent `p > 2` has Lebesgue
measure zero. -/
@[simp]
theorem volume_iUnion_setOf_liouvilleWith :
    volume (⋃ (p : ℝ) (_hp : 2 < p), { x : ℝ | LiouvilleWith p x }) = 0 := by
  simp only [← setOf_exists, exists_prop]
  -- ⊢ ↑↑volume {x | ∃ i, 2 < i ∧ LiouvilleWith i x} = 0
  refine' measure_mono_null setOf_liouvilleWith_subset_aux _
  -- ⊢ ↑↑volume (⋃ (m : ℤ), (fun x => x + ↑m) ⁻¹' ⋃ (n : ℕ) (_ : n > 0), {x | ∃ᶠ (b …
  rw [measure_iUnion_null_iff]; intro m; rw [measure_preimage_add_right]; clear m
  -- ⊢ ∀ (i : ℤ), ↑↑volume ((fun x => x + ↑i) ⁻¹' ⋃ (n : ℕ) (_ : n > 0), {x | ∃ᶠ (b …
                                -- ⊢ ↑↑volume ((fun x => x + ↑m) ⁻¹' ⋃ (n : ℕ) (_ : n > 0), {x | ∃ᶠ (b : ℕ) in at …
                                         -- ⊢ ↑↑volume (⋃ (n : ℕ) (_ : n > 0), {x | ∃ᶠ (b : ℕ) in atTop, ∃ a, a ∈ Finset.I …
                                                                          -- ⊢ ↑↑volume (⋃ (n : ℕ) (_ : n > 0), {x | ∃ᶠ (b : ℕ) in atTop, ∃ a, a ∈ Finset.I …
  refine' (measure_biUnion_null_iff <| to_countable _).2 fun n (hn : 1 ≤ n) => _
  -- ⊢ ↑↑volume {x | ∃ᶠ (b : ℕ) in atTop, ∃ a, a ∈ Finset.Icc 0 ↑b ∧ |x - ↑a / ↑b|  …
  generalize hr : (2 + 1 / n : ℝ) = r
  -- ⊢ ↑↑volume {x | ∃ᶠ (b : ℕ) in atTop, ∃ a, a ∈ Finset.Icc 0 ↑b ∧ |x - ↑a / ↑b|  …
  replace hr : 2 < r; · simp [← hr, zero_lt_one.trans_le hn]
  -- ⊢ 2 < r
                        -- 🎉 no goals
  clear hn n
  -- ⊢ ↑↑volume {x | ∃ᶠ (b : ℕ) in atTop, ∃ a, a ∈ Finset.Icc 0 ↑b ∧ |x - ↑a / ↑b|  …
  refine' measure_setOf_frequently_eq_zero _
  -- ⊢ ∑' (i : ℕ), ↑↑volume {x | ∃ a, a ∈ Finset.Icc 0 ↑i ∧ |x - ↑a / ↑i| < 1 / ↑i  …
  simp only [setOf_exists, ← exists_prop, ← Real.dist_eq, ← mem_ball, setOf_mem_eq]
  -- ⊢ ∑' (i : ℕ), ↑↑volume (⋃ (i_1 : ℤ) (_ : i_1 ∈ Finset.Icc 0 ↑i), ball (↑i_1 /  …
  set B : ℤ → ℕ → Set ℝ := fun a b => ball (a / b) (1 / (b : ℝ) ^ r)
  -- ⊢ ∑' (i : ℕ), ↑↑volume (⋃ (i_1 : ℤ) (_ : i_1 ∈ Finset.Icc 0 ↑i), ball (↑i_1 /  …
  have hB : ∀ a b, volume (B a b) = ↑((2 : ℝ≥0) / (b : ℝ≥0) ^ r) := fun a b ↦ by
    rw [Real.volume_ball, mul_one_div, ← NNReal.coe_two, ← NNReal.coe_nat_cast, ← NNReal.coe_rpow,
      ← NNReal.coe_div, ENNReal.ofReal_coe_nnreal]
  have : ∀ b : ℕ, volume (⋃ a ∈ Finset.Icc (0 : ℤ) b, B a b) ≤
      ↑(2 * ((b : ℝ≥0) ^ (1 - r) + (b : ℝ≥0) ^ (-r))) := fun b ↦
    calc
      volume (⋃ a ∈ Finset.Icc (0 : ℤ) b, B a b) ≤ ∑ a in Finset.Icc (0 : ℤ) b, volume (B a b) :=
        measure_biUnion_finset_le _ _
      _ = ↑((b + 1) * (2 / (b : ℝ≥0) ^ r)) := by
        simp only [hB, Int.card_Icc, Finset.sum_const, nsmul_eq_mul, sub_zero, ← Int.ofNat_succ,
          Int.toNat_coe_nat, ← Nat.cast_succ, ENNReal.coe_mul, ENNReal.coe_nat]
      _ = _ := by
        have : 1 - r ≠ 0 := by linarith
        rw [ENNReal.coe_eq_coe]
        simp [add_mul, div_eq_mul_inv, NNReal.rpow_neg, NNReal.rpow_sub' _ this, mul_add,
          mul_left_comm]
  refine' ne_top_of_le_ne_top (ENNReal.tsum_coe_ne_top_iff_summable.2 _) (ENNReal.tsum_le_tsum this)
  -- ⊢ Summable fun a => 2 * (↑a ^ (1 - r) + ↑a ^ (-r))
  refine' (Summable.add _ _).mul_left _ <;> simp only [NNReal.summable_rpow] <;> linarith
  -- ⊢ Summable fun a => ↑a ^ (1 - r)
                                            -- ⊢ 1 - r < -1
                                            -- ⊢ -r < -1
                                                                                 -- 🎉 no goals
                                                                                 -- 🎉 no goals
#align volume_Union_set_of_liouville_with volume_iUnion_setOf_liouvilleWith

theorem ae_not_liouvilleWith : ∀ᵐ x, ∀ p > (2 : ℝ), ¬LiouvilleWith p x := by
  simpa only [ae_iff, not_forall, Classical.not_not, setOf_exists] using
    volume_iUnion_setOf_liouvilleWith
#align ae_not_liouville_with ae_not_liouvilleWith

theorem ae_not_liouville : ∀ᵐ x, ¬Liouville x :=
  ae_not_liouvilleWith.mono fun x h₁ h₂ => h₁ 3 (by norm_num) (h₂.liouvilleWith 3)
                                                    -- 🎉 no goals
#align ae_not_liouville ae_not_liouville

/-- The set of Liouville numbers has Lebesgue measure zero. -/
@[simp]
theorem volume_setOf_liouville : volume { x : ℝ | Liouville x } = 0 := by
  simpa only [ae_iff, Classical.not_not] using ae_not_liouville
  -- 🎉 no goals
#align volume_set_of_liouville volume_setOf_liouville

/-- The filters `residual ℝ` and `volume.ae` are disjoint. This means that there exists a residual
set of Lebesgue measure zero (e.g., the set of Liouville numbers). -/
theorem Real.disjoint_residual_ae : Disjoint (residual ℝ) volume.ae :=
  disjoint_of_disjoint_of_mem disjoint_compl_right eventually_residual_liouville ae_not_liouville
#align real.disjoint_residual_ae Real.disjoint_residual_ae
