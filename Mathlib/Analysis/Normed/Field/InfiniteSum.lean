/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

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

open BigOperators Classical

open Finset

/-! ### Arbitrary index types -/

theorem Summable.mul_of_nonneg {f : ι → ℝ} {g : ι' → ℝ} (hf : Summable f) (hg : Summable g)
    (hf' : 0 ≤ f) (hg' : 0 ≤ g) : Summable fun x : ι × ι' => f x.1 * g x.2 :=
  (summable_prod_of_nonneg <| fun _ ↦ mul_nonneg (hf' _) (hg' _)).2 ⟨fun x ↦ hg.mul_left (f x),
    by simpa only [hg.tsum_mul_left _] using hf.mul_right (∑' x, g x)⟩
       -- 🎉 no goals
#align summable.mul_of_nonneg Summable.mul_of_nonneg

theorem Summable.mul_norm {f : ι → R} {g : ι' → R} (hf : Summable fun x => ‖f x‖)
    (hg : Summable fun x => ‖g x‖) : Summable fun x : ι × ι' => ‖f x.1 * g x.2‖ :=
  summable_of_nonneg_of_le (fun x => norm_nonneg (f x.1 * g x.2))
    (fun x => norm_mul_le (f x.1) (g x.2))
    (hf.mul_of_nonneg hg (fun x => norm_nonneg <| f x) fun x => norm_nonneg <| g x : _)
#align summable.mul_norm Summable.mul_norm

theorem summable_mul_of_summable_norm [CompleteSpace R] {f : ι → R} {g : ι' → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    Summable fun x : ι × ι' => f x.1 * g x.2 :=
  summable_of_summable_norm (hf.mul_norm hg)
#align summable_mul_of_summable_norm summable_mul_of_summable_norm

/-- Product of two infinites sums indexed by arbitrary types.
    See also `tsum_mul_tsum` if `f` and `g` are *not* absolutely summable. -/
theorem tsum_mul_tsum_of_summable_norm [CompleteSpace R] {f : ι → R} {g : ι' → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × ι', f z.1 * g z.2 :=
  tsum_mul_tsum (summable_of_summable_norm hf) (summable_of_summable_norm hg)
    (summable_mul_of_summable_norm hf hg)
#align tsum_mul_tsum_of_summable_norm tsum_mul_tsum_of_summable_norm

/-! ### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`, where the `n`-th term is a sum over
`Finset.range (n+1)` involving `Nat` subtraction.
In order to avoid `Nat` subtraction, we also provide
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`Finset` `Finset.Nat.antidiagonal n`. -/


section Nat

open Finset.Nat

theorem summable_norm_sum_mul_antidiagonal_of_summable_norm {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    Summable fun n => ‖∑ kl in antidiagonal n, f kl.1 * g kl.2‖ := by
  have :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (Summable.mul_of_nonneg hf hg (fun _ => norm_nonneg _) fun _ => norm_nonneg _)
  refine' summable_of_nonneg_of_le (fun _ => norm_nonneg _) _ this
  -- ⊢ ∀ (b : ℕ), ‖∑ kl in antidiagonal b, f kl.fst * g kl.snd‖ ≤ ∑ kl in antidiago …
  intro n
  -- ⊢ ‖∑ kl in antidiagonal n, f kl.fst * g kl.snd‖ ≤ ∑ kl in antidiagonal n, ‖f k …
  calc
    ‖∑ kl in antidiagonal n, f kl.1 * g kl.2‖ ≤ ∑ kl in antidiagonal n, ‖f kl.1 * g kl.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ kl in antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖ := by gcongr; apply norm_mul_le
#align summable_norm_sum_mul_antidiagonal_of_summable_norm summable_norm_sum_mul_antidiagonal_of_summable_norm

/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
    expressed by summing on `Finset.Nat.antidiagonal`.
    See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal` if `f` and `g` are
    *not* absolutely summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [CompleteSpace R] {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl in antidiagonal n, f kl.1 * g kl.2 :=
  tsum_mul_tsum_eq_tsum_sum_antidiagonal (summable_of_summable_norm hf)
    (summable_of_summable_norm hg) (summable_mul_of_summable_norm hf hg)
#align tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm

theorem summable_norm_sum_mul_range_of_summable_norm {f g : ℕ → R} (hf : Summable fun x => ‖f x‖)
    (hg : Summable fun x => ‖g x‖) : Summable fun n => ‖∑ k in range (n + 1), f k * g (n - k)‖ := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  -- ⊢ Summable fun n => ‖∑ ij in antidiagonal n, f ij.fst * g ij.snd‖
  exact summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  -- 🎉 no goals
#align summable_norm_sum_mul_range_of_summable_norm summable_norm_sum_mul_range_of_summable_norm

/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
    expressed by summing on `Finset.range`.
    See also `tsum_mul_tsum_eq_tsum_sum_range` if `f` and `g` are
    *not* absolutely summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm [CompleteSpace R] {f g : ℕ → R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k in range (n + 1), f k * g (n - k) := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  -- ⊢ (∑' (n : ℕ), f n) * ∑' (n : ℕ), g n = ∑' (n : ℕ), ∑ ij in antidiagonal n, f  …
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  -- 🎉 no goals
#align tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm

end Nat
