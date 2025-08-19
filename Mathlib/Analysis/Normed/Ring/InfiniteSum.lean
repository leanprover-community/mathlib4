/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Ring.Lemmas

/-! # Multiplying two infinite sums in a normed ring

In this file, we prove various results about `(∑' x : ι, f x) * (∑' y : ι', g y)` in a normed
ring. There are similar results proven in `Mathlib/Topology/Algebra/InfiniteSum.lean` (e.g
`tsum_mul_tsum`), but in a normed ring we get summability results which aren't true in general.

We first establish results about arbitrary index types, `ι` and `ι'`, and then we specialize to
`ι = ι' = ℕ` to prove the Cauchy product formula
(see `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`).
-/


variable {R : Type*} {ι : Type*} {ι' : Type*} [NormedRing R]

open scoped Topology

open Finset Filter

/-! ### Arbitrary index types -/

theorem Summable.mul_of_nonneg {f : ι → ℝ} {g : ι' → ℝ} (hf : Summable f) (hg : Summable g)
    (hf' : 0 ≤ f) (hg' : 0 ≤ g) : Summable fun x : ι × ι' ↦ f x.1 * g x.2 :=
  (summable_prod_of_nonneg fun _ ↦ mul_nonneg (hf' _) (hg' _)).2 ⟨fun x ↦ hg.mul_left (f x),
    by simpa only [hg.tsum_mul_left _] using hf.mul_right (∑' x, g x)⟩

theorem Summable.mul_norm {f : ι → R} {g : ι' → R} (hf : Summable fun x ↦ ‖f x‖)
    (hg : Summable fun x ↦ ‖g x‖) : Summable fun x : ι × ι' ↦ ‖f x.1 * g x.2‖ :=
  .of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun x ↦ norm_mul_le (f x.1) (g x.2))
    (hf.mul_of_nonneg hg (fun x ↦ norm_nonneg <| f x) fun x ↦ norm_nonneg <| g x :)

theorem summable_mul_of_summable_norm [CompleteSpace R] {f : ι → R} {g : ι' → R}
    (hf : Summable fun x ↦ ‖f x‖) (hg : Summable fun x ↦ ‖g x‖) :
    Summable fun x : ι × ι' ↦ f x.1 * g x.2 :=
  (hf.mul_norm hg).of_norm

theorem summable_mul_of_summable_norm' {f : ι → R} {g : ι' → R}
    (hf : Summable fun x ↦ ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x ↦ ‖g x‖) (h'g : Summable g) :
    Summable fun x : ι × ι' ↦ f x.1 * g x.2 := by
  classical
  suffices HasSum (fun x : ι × ι' ↦ f x.1 * g x.2) ((∑' i, f i) * (∑' j, g j)) from this.summable
  let s : Finset ι × Finset ι' → Finset (ι × ι') := fun p ↦ p.1 ×ˢ p.2
  apply hasSum_of_subseq_of_summable (hf.mul_norm hg) tendsto_finset_prod_atTop
  rw [← prod_atTop_atTop_eq]
  have := Tendsto.prodMap h'f.hasSum h'g.hasSum
  rw [← nhds_prod_eq] at this
  convert ((continuous_mul (M := R)).continuousAt
      (x := (∑' (i : ι), f i, ∑' (j : ι'), g j))).tendsto.comp this with p
  simp [sum_product, ← mul_sum, ← sum_mul]

/-- Product of two infinite sums indexed by arbitrary types.
See also `tsum_mul_tsum` if `f` and `g` are *not* absolutely summable, and
`tsum_mul_tsum_of_summable_norm'` when the space is not complete. -/
theorem tsum_mul_tsum_of_summable_norm [CompleteSpace R] {f : ι → R} {g : ι' → R}
    (hf : Summable fun x ↦ ‖f x‖) (hg : Summable fun x ↦ ‖g x‖) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × ι', f z.1 * g z.2 :=
  hf.of_norm.tsum_mul_tsum hg.of_norm (summable_mul_of_summable_norm hf hg)

theorem tsum_mul_tsum_of_summable_norm' {f : ι → R} {g : ι' → R}
    (hf : Summable fun x ↦ ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x ↦ ‖g x‖) (h'g : Summable g) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × ι', f z.1 * g z.2 :=
  h'f.tsum_mul_tsum h'g (summable_mul_of_summable_norm' hf h'f hg h'g)

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
    (hf : Summable fun x ↦ ‖f x‖) (hg : Summable fun x ↦ ‖g x‖) :
    Summable fun n ↦ ‖∑ kl ∈ antidiagonal n, f kl.1 * g kl.2‖ := by
  have :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (Summable.mul_of_nonneg hf hg (fun _ ↦ norm_nonneg _) fun _ ↦ norm_nonneg _)
  refine this.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
  calc
    ‖∑ kl ∈ antidiagonal n, f kl.1 * g kl.2‖ ≤ ∑ kl ∈ antidiagonal n, ‖f kl.1 * g kl.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ kl ∈ antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖ := by gcongr; apply norm_mul_le

theorem summable_sum_mul_antidiagonal_of_summable_norm' {f g : ℕ → R}
    (hf : Summable fun x ↦ ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x ↦ ‖g x‖) (h'g : Summable g) :
    Summable fun n ↦ ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 :=
  summable_sum_mul_antidiagonal_of_summable_mul (summable_mul_of_summable_norm' hf h'f hg h'g)

/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
expressed by summing on `Finset.antidiagonal`.
See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal` if `f` and `g` are
*not* absolutely summable, and `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm'`
when the space is not complete. -/
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [CompleteSpace R] {f g : ℕ → R}
    (hf : Summable fun x ↦ ‖f x‖) (hg : Summable fun x ↦ ‖g x‖) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 :=
  hf.of_norm.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg.of_norm (summable_mul_of_summable_norm hf hg)

theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm' {f g : ℕ → R}
    (hf : Summable fun x ↦ ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x ↦ ‖g x‖) (h'g : Summable g) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 :=
  h'f.tsum_mul_tsum_eq_tsum_sum_antidiagonal  h'g (summable_mul_of_summable_norm' hf h'f hg h'g)

theorem summable_norm_sum_mul_range_of_summable_norm {f g : ℕ → R} (hf : Summable fun x ↦ ‖f x‖)
    (hg : Summable fun x ↦ ‖g x‖) : Summable fun n ↦ ‖∑ k ∈ range (n + 1), f k * g (n - k)‖ := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k * g l]
  exact summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg

theorem summable_sum_mul_range_of_summable_norm' {f g : ℕ → R}
    (hf : Summable fun x ↦ ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x ↦ ‖g x‖) (h'g : Summable g) :
    Summable fun n ↦ ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k * g l]
  exact summable_sum_mul_antidiagonal_of_summable_norm' hf h'f hg h'g

/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
expressed by summing on `Finset.range`.
See also `tsum_mul_tsum_eq_tsum_sum_range` if `f` and `g` are
not* absolutely summable, and `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm'` when the
space is not complete. -/
theorem tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm [CompleteSpace R] {f g : ℕ → R}
    (hf : Summable fun x ↦ ‖f x‖) (hg : Summable fun x ↦ ‖g x‖) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg

theorem hasSum_sum_range_mul_of_summable_norm [CompleteSpace R] {f g : ℕ → R}
    (hf : Summable fun x ↦ ‖f x‖) (hg : Summable fun x ↦ ‖g x‖) :
    HasSum (fun n ↦ ∑ k ∈ range (n + 1), f k * g (n - k)) ((∑' n, f n) * ∑' n, g n) := by
  convert (summable_norm_sum_mul_range_of_summable_norm hf hg).of_norm.hasSum
  exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg

theorem tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm' {f g : ℕ → R}
    (hf : Summable fun x ↦ ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x ↦ ‖g x‖) (h'g : Summable g) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm' hf h'f hg h'g

theorem hasSum_sum_range_mul_of_summable_norm' {f g : ℕ → R}
    (hf : Summable fun x ↦ ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x ↦ ‖g x‖) (h'g : Summable g) :
    HasSum (fun n ↦ ∑ k ∈ range (n + 1), f k * g (n - k)) ((∑' n, f n) * ∑' n, g n) := by
  convert (summable_sum_mul_range_of_summable_norm' hf h'f hg h'g).hasSum
  exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm' hf h'f hg h'g

end Nat

lemma summable_of_absolute_convergence_real {f : ℕ → ℝ} :
    (∃ r, Tendsto (fun n ↦ ∑ i ∈ range n, |f i|) atTop (𝓝 r)) → Summable f
  | ⟨r, hr⟩ => by
    refine .of_norm ⟨r, (hasSum_iff_tendsto_nat_of_nonneg ?_ _).2 ?_⟩
    · exact fun i ↦ norm_nonneg _
    · simpa only using hr
