/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Instances.ENNReal

#align_import analysis.normed.field.infinite_sum from "leanprover-community/mathlib"@"008205aa645b3f194c1da47025c5f110c8406eab"

/-! # Multiplying two infinite sums in a normed ring

In this file, we prove various results about `(∑' x : ι, f x) * (∑' y : ι', g y)` in a normed
ring. There are similar results proven in `Mathlib.Topology.Algebra.InfiniteSum` (e.g
`tsum_mul_tsum`), but in a normed ring we get summability results which aren't true in general.

We first establish results about arbitrary index types, `ι` and `ι'`, and then we specialize to
`ι = ι' = ℕ` to prove the Cauchy product formula
(see `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`).
-/


variable {R : Type*} {ι : Type*} {ι' : Type*} [NormedRing R]

open scoped Classical
open BigOperators

open Finset

/-! ### Arbitrary index types -/

theorem not_summable_iff_tendsto_nat_atTop_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    ¬Summable f ↔ Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop atTop := by
  lift f to ℕ → ℝ≥0 using hf
  exact mod_cast NNReal.not_summable_iff_tendsto_nat_atTop
#align not_summable_iff_tendsto_nat_at_top_of_nonneg not_summable_iff_tendsto_nat_atTop_of_nonneg

theorem summable_iff_not_tendsto_nat_atTop_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    Summable f ↔ ¬Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop atTop := by
  rw [← not_iff_not, Classical.not_not, not_summable_iff_tendsto_nat_atTop_of_nonneg hf]
#align summable_iff_not_tendsto_nat_at_top_of_nonneg summable_iff_not_tendsto_nat_atTop_of_nonneg

theorem summable_sigma_of_nonneg {β : α → Type*} {f : (Σ x, β x) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    Summable f ↔ (∀ x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑' y, f ⟨x, y⟩ := by
  lift f to (Σx, β x) → ℝ≥0 using hf
  exact mod_cast NNReal.summable_sigma
#align summable_sigma_of_nonneg summable_sigma_of_nonneg

lemma summable_partition {κ ι: Type*} {f : ι → ℝ} (hf : 0 ≤ f) {s : κ → Set ι}
    (hs : ∀ i, ∃! j, i ∈ s j) : Summable f ↔
      (∀ j, Summable fun i : s j ↦ f i) ∧ Summable fun j ↦ ∑' i : s j, f i := by
  rw [← (Set.sigmaEquiv s hs).summable_iff, summable_sigma_of_nonneg]
  simp only [Set.sigmaEquiv, Equiv.coe_fn_mk, Function.comp_apply]
  exact fun _ ↦ hf _

theorem summable_prod_of_nonneg {f : (α × β) → ℝ} (hf : 0 ≤ f) :
    Summable f ↔ (∀ x, Summable fun y ↦ f (x, y)) ∧ Summable fun x ↦ ∑' y, f (x, y) :=
  (Equiv.sigmaEquivProd _ _).summable_iff.symm.trans <| summable_sigma_of_nonneg fun _ ↦ hf _

theorem summable_of_sum_le {ι : Type*} {f : ι → ℝ} {c : ℝ} (hf : 0 ≤ f)
    (h : ∀ u : Finset ι, ∑ x in u, f x ≤ c) : Summable f :=
  ⟨⨆ u : Finset ι, ∑ x in u, f x,
    tendsto_atTop_ciSup (Finset.sum_mono_set_of_nonneg hf) ⟨c, fun _ ⟨u, hu⟩ => hu ▸ h u⟩⟩
#align summable_of_sum_le summable_of_sum_le

theorem summable_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∀ n, ∑ i in Finset.range n, f i ≤ c) : Summable f := by
  refine (summable_iff_not_tendsto_nat_atTop_of_nonneg hf).2 fun H => ?_
  rcases exists_lt_of_tendsto_atTop H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))
#align summable_of_sum_range_le summable_of_sum_range_le

theorem Real.tsum_le_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∀ n, ∑ i in Finset.range n, f i ≤ c) : ∑' n, f n ≤ c :=
  _root_.tsum_le_of_sum_range_le (summable_of_sum_range_le hf h) h
#align real.tsum_le_of_sum_range_le Real.tsum_le_of_sum_range_le

/-- If a sequence `f` with non-negative terms is dominated by a sequence `g` with summable
series and at least one term of `f` is strictly smaller than the corresponding term in `g`,
then the series of `f` is strictly smaller than the series of `g`. -/
theorem tsum_lt_tsum_of_nonneg {i : ℕ} {f g : ℕ → ℝ} (h0 : ∀ b : ℕ, 0 ≤ f b)
    (h : ∀ b : ℕ, f b ≤ g b) (hi : f i < g i) (hg : Summable g) : ∑' n, f n < ∑' n, g n :=
  tsum_lt_tsum h hi (.of_nonneg_of_le h0 h hg) hg
#align tsum_lt_tsum_of_nonneg tsum_lt_tsum_of_nonneg


theorem Summable.mul_of_nonneg {f : ι → ℝ} {g : ι' → ℝ} (hf : Summable f) (hg : Summable g)
    (hf' : 0 ≤ f) (hg' : 0 ≤ g) : Summable fun x : ι × ι' => f x.1 * g x.2 :=
  (summable_prod_of_nonneg fun _ ↦ mul_nonneg (hf' _) (hg' _)).2 ⟨fun x ↦ hg.mul_left (f x),
    by simpa only [hg.tsum_mul_left _] using hf.mul_right (∑' x, g x)⟩
#align summable.mul_of_nonneg Summable.mul_of_nonneg

theorem Summable.mul_norm {f : ι → R} {g : ι' → R} (hf : Summable fun x => ‖f x‖)
    (hg : Summable fun x => ‖g x‖) : Summable fun x : ι × ι' => ‖f x.1 * g x.2‖ :=
  .of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun x => norm_mul_le (f x.1) (g x.2))
    (hf.mul_of_nonneg hg (fun x => norm_nonneg <| f x) fun x => norm_nonneg <| g x : _)
#align summable.mul_norm Summable.mul_norm

theorem summable_mul_of_summable_norm [CompleteSpace R] {f : ι → R} {g : ι' → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    Summable fun x : ι × ι' => f x.1 * g x.2 :=
  (hf.mul_norm hg).of_norm
#align summable_mul_of_summable_norm summable_mul_of_summable_norm

/-- Product of two infinites sums indexed by arbitrary types.
    See also `tsum_mul_tsum` if `f` and `g` are *not* absolutely summable. -/
theorem tsum_mul_tsum_of_summable_norm [CompleteSpace R] {f : ι → R} {g : ι' → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × ι', f z.1 * g z.2 :=
  tsum_mul_tsum hf.of_norm hg.of_norm (summable_mul_of_summable_norm hf hg)
#align tsum_mul_tsum_of_summable_norm tsum_mul_tsum_of_summable_norm

/-! ### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`, where the `n`-th term is a sum over
`Finset.range (n+1)` involving `Nat` subtraction.
In order to avoid `Nat` subtraction, we also provide
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`Finset` `Finset.antidiagonal n`. -/


section Nat

open Finset.Nat

theorem summable_norm_sum_mul_antidiagonal_of_summable_norm {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    Summable fun n => ‖∑ kl in antidiagonal n, f kl.1 * g kl.2‖ := by
  have :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (Summable.mul_of_nonneg hf hg (fun _ => norm_nonneg _) fun _ => norm_nonneg _)
  refine this.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n ↦ ?_)
  calc
    ‖∑ kl in antidiagonal n, f kl.1 * g kl.2‖ ≤ ∑ kl in antidiagonal n, ‖f kl.1 * g kl.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ kl in antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖ := by gcongr; apply norm_mul_le
#align summable_norm_sum_mul_antidiagonal_of_summable_norm summable_norm_sum_mul_antidiagonal_of_summable_norm

/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
    expressed by summing on `Finset.antidiagonal`.
    See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal` if `f` and `g` are
    *not* absolutely summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [CompleteSpace R] {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl in antidiagonal n, f kl.1 * g kl.2 :=
  tsum_mul_tsum_eq_tsum_sum_antidiagonal hf.of_norm hg.of_norm (summable_mul_of_summable_norm hf hg)
#align tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm

theorem summable_norm_sum_mul_range_of_summable_norm {f g : ℕ → R} (hf : Summable fun x => ‖f x‖)
    (hg : Summable fun x => ‖g x‖) : Summable fun n => ‖∑ k in range (n + 1), f k * g (n - k)‖ := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
#align summable_norm_sum_mul_range_of_summable_norm summable_norm_sum_mul_range_of_summable_norm

/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
    expressed by summing on `Finset.range`.
    See also `tsum_mul_tsum_eq_tsum_sum_range` if `f` and `g` are
    *not* absolutely summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm [CompleteSpace R] {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k in range (n + 1), f k * g (n - k) := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
#align tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm

end Nat
