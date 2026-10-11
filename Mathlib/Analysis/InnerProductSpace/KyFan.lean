/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues

import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Ky Fan's inequality for singular values

For linear maps `u v : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, the sum of
the `n` largest singular values is subadditive:
`∑ j < n, s_j(u + v) ≤ ∑ j < n, s_j(u) + ∑ j < n, s_j(v)`.

## Main statements

* `sum_norm_inner_sq_le_norm_sq_of_orthogonal`: Bessel's inequality for a finite family of
  pairwise orthogonal vectors of norm at most `1`.
* `LinearMap.norm_sum_inner_le_sum_singularValues`: Ky Fan's maximum principle: for pairwise
  orthogonal families `(x_i)` in `E` and `(y_i)` in `F` of vectors of norm at most `1`, indexed by
  a finite set with at most `n` elements, `‖∑ i, ⟪y_i, T x_i⟫‖ ≤ ∑ j < n, s_j(T)`.
* `LinearMap.sum_singularValues_add_le`: Ky Fan's inequality.
* `LinearMap.sum_powersetCard_two_prod_singularValues_add_le`: the same for the second elementary
  symmetric function `σ₂` of the `n` largest singular values:
  `σ₂(u + v) ≤ σ₂(u) + (∑ j < n, s_j(u)) (∑ j < n, s_j(v)) + σ₂(v)`. The proof works with
  `2 × 2` minors of the compressions `⟪y_i, T x_j⟫` instead of the second exterior power.

## References

* [K. Fan, *Maximum properties and inequalities for the eigenvalues of completely continuous
  operators*][fan1951]: the maximum principle is the case `m = 1` of Theorem 1 (inequality (8)),
  and Ky Fan's inequality is inequality (20) in the proof of Theorem 5
* [R. Bhatia, *Matrix Analysis*][bhatia1997]

## Tags

singular values, Ky Fan
-/

public section

open Finset Module InnerProductSpace
open scoped ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **Bessel's inequality** for a finite family of pairwise orthogonal vectors of norm at most
`1`. See `Orthonormal.sum_inner_products_le` for orthonormal families. -/
theorem sum_norm_inner_sq_le_norm_sq_of_orthogonal {ι : Type*} (s : Finset ι) {y : ι → E}
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪y i, y j⟫ = 0) (hle : ∀ i ∈ s, ‖y i‖ ≤ 1)
    (z : E) : ∑ i ∈ s, ‖⟪y i, z⟫‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  set c : ι → 𝕜 := fun i ↦ ⟪y i, z⟫ with hc
  set p : E := ∑ i ∈ s, c i • y i with hp
  set S : ℝ := ∑ i ∈ s, ‖c i‖ ^ 2 with hS
  have hS0 : 0 ≤ S := sum_nonneg fun i _ ↦ by positivity
  have hpz : ⟪p, z⟫ = (S : 𝕜) := by
    rw [hp, sum_inner, hS]
    push_cast
    refine sum_congr rfl fun i _ ↦ ?_
    rw [inner_smul_left, hc, RCLike.conj_mul]
  have hyp (i) (hi : i ∈ s) : ⟪y i, p⟫ = c i * ⟪y i, y i⟫ := by
    rw [hp, inner_sum, sum_eq_single i]
    · rw [inner_smul_right]
    · intro j hj hji
      rw [inner_smul_right, horth i hi j hj (Ne.symm hji), mul_zero]
    · intro h
      exact absurd hi h
  have hpp : ‖p‖ ^ 2 ≤ S := by
    have h1 : ‖p‖ ^ 2 = ∑ i ∈ s, ‖c i‖ ^ 2 * ‖y i‖ ^ 2 := by
      rw [← @inner_self_eq_norm_sq 𝕜, hp, sum_inner, map_sum]
      refine sum_congr rfl fun i hi ↦ ?_
      rw [inner_smul_left, ← hp, hyp i hi, ← mul_assoc, RCLike.conj_mul,
        inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [h1, hS]
    refine sum_le_sum fun i hi ↦ ?_
    have : ‖y i‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hle i hi)
    nlinarith [sq_nonneg ‖c i‖]
  have hSle : S ≤ ‖p‖ * ‖z‖ := by
    have := norm_inner_le_norm (𝕜 := 𝕜) p z
    rwa [hpz, RCLike.norm_ofReal, abs_of_nonneg hS0] at this
  rcases hS0.eq_or_lt with h | h
  · rw [← h]
    positivity
  · by_contra hcon
    rw [not_le] at hcon
    have : S ^ 2 ≤ S * ‖z‖ ^ 2 :=
      calc S ^ 2 ≤ (‖p‖ * ‖z‖) ^ 2 := by gcongr
        _ = ‖p‖ ^ 2 * ‖z‖ ^ 2 := by ring
        _ ≤ S * ‖z‖ ^ 2 := by gcongr
    nlinarith

/-- For `s` antitone and nonnegative, and weights `0 ≤ c j ≤ 1` of total mass at most `n`, the
weighted sum `∑ j, s j * c j` is at most the sum of the `n` largest values of `s`. -/
private theorem sum_mul_le_sum_range {d : ℕ} (s : ℕ → ℝ) (hs : Antitone s)
    (hs0 : ∀ j, 0 ≤ s j) (c : Fin d → ℝ) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1) {n : ℕ}
    (hcn : ∑ j, c j ≤ n) : ∑ j : Fin d, s j * c j ≤ ∑ j ∈ range n, s j := by
  classical
  have key (j : Fin d) : s j * c j ≤ (if (j : ℕ) < n then s j else 0)
      + s n * (c j - if (j : ℕ) < n then 1 else 0) := by
    split_ifs with hj
    · have := hs hj.le
      nlinarith [hc1 j]
    · have := hs (not_lt.mp hj)
      nlinarith [hc0 j]
  have hcard : ∑ j : Fin d, c j ≤ ∑ j : Fin d, (if (j : ℕ) < n then (1 : ℝ) else 0) := by
    rw [sum_boole, Fin.card_filter_val_lt]
    rcases le_total d n with h | h
    · rw [min_eq_left h]
      calc ∑ j, c j ≤ ∑ _j : Fin d, (1 : ℝ) := sum_le_sum fun j _ ↦ hc1 j
        _ = d := by simp
    · rw [min_eq_right h]
      exact hcn
  have hfin : ∑ j : Fin d, (if (j : ℕ) < n then s j else 0) ≤ ∑ j ∈ range n, s j := by
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ if k < n then s k else 0) d, ← sum_filter]
    refine sum_le_sum_of_subset_of_nonneg (fun k hk ↦ ?_) fun k _ _ ↦ hs0 k
    simp only [mem_filter, mem_range] at hk ⊢
    exact hk.2
  calc ∑ j : Fin d, s j * c j ≤ ∑ j : Fin d, ((if (j : ℕ) < n then s j else 0)
        + s n * (c j - if (j : ℕ) < n then 1 else 0)) := sum_le_sum fun j _ ↦ key j
    _ = ∑ j : Fin d, (if (j : ℕ) < n then s j else 0)
        + s n * (∑ j : Fin d, c j - ∑ j : Fin d, (if (j : ℕ) < n then (1 : ℝ) else 0)) := by
          rw [sum_add_distrib, ← mul_sum, sum_sub_distrib]
    _ ≤ ∑ j ∈ range n, s j + s n * 0 :=
          add_le_add hfin (mul_le_mul_of_nonneg_left (by linarith) (hs0 n))
    _ = _ := by ring

/-! ### The second elementary symmetric function -/

/-- Lagrange's inequality: `∑_{i,j ∈ S} |a_i b_j - a_j b_i|² ≤ 2 (∑ |a_i|²)(∑ |b_i|²)`. -/
private theorem sum_sum_norm_sub_sq_le {ι : Type*} (S : Finset ι) (a b : ι → 𝕜) :
    ∑ i ∈ S, ∑ j ∈ S, ‖a i * b j - a j * b i‖ ^ 2 ≤
      2 * (∑ i ∈ S, ‖a i‖ ^ 2) * ∑ i ∈ S, ‖b i‖ ^ 2 := by
  set z : ι → 𝕜 := fun i ↦ conj (a i) * b i with hz
  have key : ∀ i j, ‖a i * b j - a j * b i‖ ^ 2 =
      (‖a i‖ ^ 2 * ‖b j‖ ^ 2 + ‖a j‖ ^ 2 * ‖b i‖ ^ 2) - 2 * RCLike.re (z i * conj (z j)) := by
    intro i j
    rw [@norm_sub_sq 𝕜, RCLike.inner_apply', norm_mul, norm_mul]
    have : conj (a i * b j) * (a j * b i) = z i * conj (z j) := by
      simp only [hz, map_mul, RCLike.conj_conj]; ring
    rw [this]; ring
  have h2 : ∑ i ∈ S, ∑ j ∈ S, RCLike.re (z i * conj (z j)) = ‖∑ i ∈ S, z i‖ ^ 2 := by
    have h : (∑ i ∈ S, z i) * conj (∑ i ∈ S, z i) = ∑ i ∈ S, ∑ j ∈ S, z i * conj (z j) := by
      rw [map_sum, sum_mul_sum]
    rw [RCLike.mul_conj] at h
    have h' := congrArg RCLike.re h
    rw [← RCLike.ofReal_pow, RCLike.ofReal_re] at h'
    rw [h']
    simp only [map_sum]
  have h3 : ∑ i ∈ S, ∑ j ∈ S, (‖a i‖ ^ 2 * ‖b j‖ ^ 2 + ‖a j‖ ^ 2 * ‖b i‖ ^ 2) =
      2 * (∑ i ∈ S, ‖a i‖ ^ 2) * ∑ i ∈ S, ‖b i‖ ^ 2 := by
    simp only [sum_add_distrib]
    rw [sum_comm (f := fun i j ↦ ‖a j‖ ^ 2 * ‖b i‖ ^ 2), mul_assoc, sum_mul_sum]
    ring
  calc ∑ i ∈ S, ∑ j ∈ S, ‖a i * b j - a j * b i‖ ^ 2
      = ∑ i ∈ S, ∑ j ∈ S, (‖a i‖ ^ 2 * ‖b j‖ ^ 2 + ‖a j‖ ^ 2 * ‖b i‖ ^ 2)
        - 2 * ∑ i ∈ S, ∑ j ∈ S, RCLike.re (z i * conj (z j)) := by
        simp only [key, sum_sub_distrib, mul_sum]
    _ ≤ _ := by rw [h3, h2]; nlinarith [sq_nonneg ‖∑ i ∈ S, z i‖]

/-- `2 e_2(f_0, …, f_{n-1}) = (∑ f_i)² - ∑ f_i²`. -/
private theorem two_mul_sum_powersetCard_two (f : ℕ → ℝ) (n : ℕ) :
    2 * ∑ t ∈ (range n).powersetCard 2, ∏ i ∈ t, f i =
      (∑ i ∈ range n, f i) ^ 2 - ∑ i ∈ range n, f i ^ 2 := by
  induction n with
  | zero => rw [range_zero, powersetCard_eq_empty.mpr (by simp)]; simp
  | succ n ih =>
    have hn : n ∉ range n := notMem_range_self
    rw [range_add_one, powersetCard_succ_insert hn, sum_union, sum_image, sum_insert hn,
      sum_insert hn, mul_add, ih, powersetCard_one, sum_map]
    · have : ∑ x ∈ range n, ∏ i ∈ insert n ({x} : Finset ℕ), f i = f n * ∑ i ∈ range n, f i := by
        rw [mul_sum]
        refine sum_congr rfl fun x hx ↦ ?_
        rw [prod_insert (by simpa using (ne_of_gt (mem_range.mp hx))), prod_singleton]
      simp only [Function.Embedding.coeFn_mk] at this ⊢
      rw [this]; ring
    · intro t ht t' ht' h
      have h1 : n ∉ t := fun h ↦ hn ((mem_powersetCard.mp ht).1 h)
      have h2 : n ∉ t' := fun h ↦ hn ((mem_powersetCard.mp ht').1 h)
      rw [← erase_insert h1, ← erase_insert h2, h]
    · rw [disjoint_left]
      intro t ht ht'
      obtain ⟨t', _, rfl⟩ := mem_image.mp ht'
      exact hn ((mem_powersetCard.mp ht).1 (mem_insert_self _ _))

/-- The weight lemma for `σ²`. Let `s ≥ 0` and `θ ≥ 0` with `s_k ≥ θ` on a finite set `G` and
`s_k ≤ θ` off `G`. Let `(α_{kl})` be symmetric with entries in `[0,1]` and zero diagonal, and
`p_k ∈ [0,1]` with `∑ p_k ≤ |G|` and row sums `∑_l α_{kl} ≤ (|G| - 1) p_k`. Then
`∑_{k,l} α_{kl} s_k s_l ≤ (∑_{k ∈ G} s_k)² - ∑_{k ∈ G} s_k²`. -/
private theorem sum_sum_mul_le_of_weights {κ : Type*} [Fintype κ] (G : Finset κ)
    (s : κ → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) (hs0 : ∀ k, 0 ≤ s k) (hG : ∀ k ∈ G, θ ≤ s k)
    (hGc : ∀ k ∉ G, s k ≤ θ) (α : κ → κ → ℝ) (p : κ → ℝ) (hα0 : ∀ k l, 0 ≤ α k l)
    (hα1 : ∀ k l, α k l ≤ 1) (hdiag : ∀ k, α k k = 0) (hsymm : ∀ k l, α k l = α l k)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1) (hrow : ∀ k, ∑ l, α k l ≤ ((#G : ℝ) - 1) * p k)
    (hp : ∑ k, p k ≤ #G) :
    ∑ k, ∑ l, α k l * (s k * s l) ≤ (∑ k ∈ G, s k) ^ 2 - ∑ k ∈ G, s k ^ 2 := by
  classical
  set g : ℝ := (#G : ℝ) with hg
  set m : κ → ℝ := fun k ↦ min (s k) θ with hm
  set d : κ → ℝ := fun k ↦ s k - m k with hd
  have hm0 : ∀ k, 0 ≤ m k := fun k ↦ le_min (hs0 k) hθ
  have hmθ : ∀ k, m k ≤ θ := fun k ↦ min_le_right _ _
  have hd0 : ∀ k, 0 ≤ d k := fun k ↦ sub_nonneg.mpr (min_le_left _ _)
  have hdG : ∀ k ∉ G, d k = 0 := fun k hk ↦ by
    simp only [hd, hm, min_eq_left (hGc k hk), sub_self]
  have hmG : ∀ k ∈ G, m k = θ := fun k hk ↦ min_eq_right (hG k hk)
  have hsd : ∀ k, s k = m k + d k := fun k ↦ by simp only [hd]; ring
  set D : ℝ := ∑ k ∈ G, d k with hD
  have hDu : ∑ k, d k = D := (sum_subset (subset_univ G) fun k _ hk ↦ hdG k hk).symm
  have hd2u : ∑ k, d k ^ 2 = ∑ k ∈ G, d k ^ 2 :=
    (sum_subset (subset_univ G) fun k _ hk ↦ by rw [hdG k hk]; ring).symm
  -- the three bounds
  have hcol : ∀ l, ∑ k, α k l ≤ (g - 1) * p l := fun l ↦ by
    simpa only [hsymm _ l] using hrow l
  have hdp : ∀ l, d l * ((g - 1) * p l) ≤ d l * (g - 1) := fun l ↦ by
    by_cases hl : l ∈ G
    · have : (1 : ℝ) ≤ g := by rw [hg]; exact_mod_cast card_pos.mpr ⟨l, hl⟩
      have := hd0 l; have := hp1 l
      nlinarith [mul_nonneg (hd0 l) (sub_nonneg.mpr this)]
    · rw [hdG l hl]; ring_nf; rfl
  have hgp : (g - 1) * ∑ k, p k ≤ (g - 1) * g := by
    rcases Nat.eq_zero_or_pos #G with h0 | h0
    · have hg0 : g = 0 := by rw [hg, h0]; simp
      have : 0 ≤ ∑ k, p k := sum_nonneg fun k _ ↦ hp0 k
      rw [hg0]; linarith [hp, hg0]
    · have : (1 : ℝ) ≤ g := by rw [hg]; exact_mod_cast h0
      exact mul_le_mul_of_nonneg_left hp (by linarith)
  have b1 : ∑ k, ∑ l, α k l * (m k * m l) ≤ θ ^ 2 * ((g - 1) * g) := by
    calc ∑ k, ∑ l, α k l * (m k * m l) ≤ ∑ k, ∑ l, α k l * θ ^ 2 := by
          refine sum_le_sum fun k _ ↦ sum_le_sum fun l _ ↦ ?_
          refine mul_le_mul_of_nonneg_left ?_ (hα0 k l)
          rw [sq]; exact mul_le_mul (hmθ k) (hmθ l) (hm0 l) hθ
      _ = θ ^ 2 * ∑ k, ∑ l, α k l := by rw [mul_sum]; simp only [← sum_mul, mul_comm]
      _ ≤ θ ^ 2 * ((g - 1) * ∑ k, p k) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg θ)
          rw [mul_sum]; exact sum_le_sum fun k _ ↦ hrow k
      _ ≤ _ := mul_le_mul_of_nonneg_left hgp (sq_nonneg θ)
  have b2 : ∑ k, ∑ l, α k l * (m k * d l) ≤ θ * ((g - 1) * D) := by
    calc ∑ k, ∑ l, α k l * (m k * d l) ≤ ∑ k, ∑ l, α k l * (θ * d l) := by
          refine sum_le_sum fun k _ ↦ sum_le_sum fun l _ ↦ ?_
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hmθ k) (hd0 l)) (hα0 k l)
      _ = θ * ∑ l, d l * ∑ k, α k l := by
          rw [sum_comm, mul_sum]
          refine sum_congr rfl fun l _ ↦ ?_
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun k _ ↦ ?_
          ring
      _ ≤ θ * ∑ l, d l * (g - 1) := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun l _ ↦ ?_) hθ
          exact (mul_le_mul_of_nonneg_left (hcol l) (hd0 l)).trans (hdp l)
      _ = _ := by rw [← sum_mul, hDu]; ring
  have b3 : ∑ k, ∑ l, α k l * (d k * m l) ≤ θ * ((g - 1) * D) := by
    calc ∑ k, ∑ l, α k l * (d k * m l) ≤ ∑ k, ∑ l, α k l * (d k * θ) := by
          refine sum_le_sum fun k _ ↦ sum_le_sum fun l _ ↦ ?_
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hmθ l) (hd0 k)) (hα0 k l)
      _ = θ * ∑ k, d k * ∑ l, α k l := by
          rw [mul_sum]
          refine sum_congr rfl fun k _ ↦ ?_
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun l _ ↦ ?_
          ring
      _ ≤ θ * ∑ k, d k * (g - 1) := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun k _ ↦ ?_) hθ
          exact (mul_le_mul_of_nonneg_left (hrow k) (hd0 k)).trans (hdp k)
      _ = _ := by rw [← sum_mul, hDu]; ring
  have b4 : ∑ k, ∑ l, α k l * (d k * d l) ≤ D ^ 2 - ∑ k ∈ G, d k ^ 2 := by
    calc ∑ k, ∑ l, α k l * (d k * d l)
        ≤ ∑ k, ∑ l, (d k * d l - if k = l then d k * d l else 0) := by
          refine sum_le_sum fun k _ ↦ sum_le_sum fun l _ ↦ ?_
          split_ifs with h
          · rw [h, hdiag]; simp
          · have := mul_nonneg (hd0 k) (hd0 l)
            nlinarith [hα1 k l]
      _ = _ := by
          simp only [sum_sub_distrib, sum_ite_eq, mem_univ, ite_true]
          rw [← sum_mul_sum, hDu, ← hd2u]
          simp only [sq]
  have hsG : ∑ k ∈ G, s k = g * θ + D := by
    rw [sum_congr rfl fun k hk ↦ (show s k = θ + d k by rw [hsd, hmG k hk]), sum_add_distrib,
      sum_const, nsmul_eq_mul]
  have hs2G : ∑ k ∈ G, s k ^ 2 = g * θ ^ 2 + 2 * θ * D + ∑ k ∈ G, d k ^ 2 := by
    rw [sum_congr rfl fun k hk ↦ (show s k ^ 2 = θ ^ 2 + 2 * θ * d k + d k ^ 2 by
      rw [hsd, hmG k hk]; ring), sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul,
      ← mul_sum]
  calc ∑ k, ∑ l, α k l * (s k * s l)
      = ∑ k, ∑ l, α k l * (m k * m l) + ∑ k, ∑ l, α k l * (m k * d l)
        + ∑ k, ∑ l, α k l * (d k * m l) + ∑ k, ∑ l, α k l * (d k * d l) := by
        simp only [← sum_add_distrib]
        refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
        rw [hsd k, hsd l]; ring
    _ ≤ θ ^ 2 * ((g - 1) * g) + θ * ((g - 1) * D) + θ * ((g - 1) * D)
        + (D ^ 2 - ∑ k ∈ G, d k ^ 2) := by linarith
    _ = _ := by rw [hsG, hs2G]; ring

section Frames

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The `2 × 2` minor `⟪g_k, h_i⟫⟪g'_l, h_j⟫ - ⟪g_k, h_j⟫⟪g'_l, h_i⟫`, that is
`⟪g_k ∧ g'_l, h_i ∧ h_j⟫` up to conjugation. -/
private def minor2 {κ ι : Type*} (g g' : κ → H) (h : ι → H) (k l : κ) (i j : ι) : 𝕜 :=
  ⟪g k, h i⟫ * ⟪g' l, h j⟫ - ⟪g k, h j⟫ * ⟪g' l, h i⟫

/-- `Λ_{kl} = ∑_{i,j ∈ S} |minor2 g g' h k l i j|²`. -/
private def lam {κ ι : Type*} (g g' : κ → H) (h : ι → H) (S : Finset ι) (k l : κ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, ‖(minor2 g g' h k l i j : 𝕜)‖ ^ 2

/-- `p_k = ∑_{i ∈ S} |⟪g_k, h_i⟫|²`. -/
private def wt {κ ι : Type*} (g : κ → H) (h : ι → H) (S : Finset ι) (k : κ) : ℝ :=
  ∑ i ∈ S, ‖⟪g k, h i⟫‖ ^ 2

private theorem lam_nonneg {κ ι : Type*} (g g' : κ → H) (h : ι → H) (S : Finset ι) (k l : κ) :
    0 ≤ lam (𝕜 := 𝕜) g g' h S k l :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ by positivity

private theorem wt_nonneg {κ ι : Type*} (g : κ → H) (h : ι → H) (S : Finset ι) (k : κ) :
    0 ≤ wt (𝕜 := 𝕜) g h S k :=
  sum_nonneg fun _ _ ↦ by positivity

private theorem lam_le {κ ι : Type*} (g g' : κ → H) (h : ι → H) (S : Finset ι) (k l : κ) :
    lam (𝕜 := 𝕜) g g' h S k l ≤ 2 * wt (𝕜 := 𝕜) g h S k * wt (𝕜 := 𝕜) g' h S l :=
  sum_sum_norm_sub_sq_le S (fun i ↦ ⟪g k, h i⟫) (fun i ↦ ⟪g' l, h i⟫)

private theorem lam_self {κ ι : Type*} (g : κ → H) (h : ι → H) (S : Finset ι) (k : κ) :
    lam (𝕜 := 𝕜) g g h S k k = 0 := by
  simp [lam, minor2, mul_comm]

private theorem lam_symm {κ ι : Type*} (g : κ → H) (h : ι → H) (S : Finset ι) (k l : κ) :
    lam (𝕜 := 𝕜) g g h S k l = lam (𝕜 := 𝕜) g g h S l k := by
  unfold lam
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  rw [← norm_neg (minor2 g g h l k i j)]
  congr 2
  simp only [minor2]; ring

private theorem wt_le_one {ι : Type*} (S : Finset ι) (h : ι → H)
    (hh : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪h i, h j⟫ = 0) (hh1 : ∀ i ∈ S, ‖h i‖ ≤ 1)
    {κ : Type*} (g : κ → H) (hg1 : ∀ k, ‖g k‖ ≤ 1) (k : κ) :
    wt (𝕜 := 𝕜) g h S k ≤ 1 := by
  have := sum_norm_inner_sq_le_norm_sq_of_orthogonal (𝕜 := 𝕜) S hh hh1 (g k)
  have h2 : ‖g k‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hg1 k)
  unfold wt
  simp only [norm_inner_symm (g k)]
  linarith

private theorem sum_wt_le {ι : Type*} (S : Finset ι) (h : ι → H) (hh1 : ∀ i ∈ S, ‖h i‖ ≤ 1)
    {κ : Type*} [Fintype κ] (g : κ → H)
    (hg : ∀ k l, k ≠ l → ⟪g k, g l⟫ = 0) (hg1 : ∀ k, ‖g k‖ ≤ 1) :
    ∑ k, wt (𝕜 := 𝕜) g h S k ≤ #S := by
  unfold wt
  rw [sum_comm]
  calc ∑ i ∈ S, ∑ k, ‖⟪g k, h i⟫‖ ^ 2 ≤ ∑ _i ∈ S, (1 : ℝ) := by
        refine sum_le_sum fun i hi ↦ ?_
        have := sum_norm_inner_sq_le_norm_sq_of_orthogonal univ (fun k _ l _ hkl ↦ hg k l hkl)
          (fun k _ ↦ hg1 k) (h i)
        have h3 : ‖h i‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hh1 i hi)
        linarith
    _ = #S := by simp

/-- Row sums of `Λ`: `∑_l Λ_{kl} ≤ 2 (|S| - 1) p_k`, by Bessel's inequality in the index `l`. -/
private theorem sum_lam_le {ι : Type*} (S : Finset ι) (h : ι → H)
    (hh : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪h i, h j⟫ = 0) (hh1 : ∀ i ∈ S, ‖h i‖ ≤ 1)
    {κ : Type*} [Fintype κ] (g : κ → H)
    (hg : ∀ k l, k ≠ l → ⟪g k, g l⟫ = 0) (hg1 : ∀ k, ‖g k‖ ≤ 1) (k : κ) :
    ∑ l, lam (𝕜 := 𝕜) g g h S k l ≤ 2 * ((#S : ℝ) - 1) * wt (𝕜 := 𝕜) g h S k := by
  classical
  unfold lam
  set c : ι → 𝕜 := fun i ↦ ⟪g k, h i⟫ with hc
  have hz : ∀ l i j, minor2 g g h k l i j = ⟪g l, c i • h j - c j • h i⟫ := by
    intro l i j
    simp only [minor2, inner_sub_right, inner_smul_right, hc]
  have hij : ∀ i ∈ S, ∀ j ∈ S, ∑ l, ‖(minor2 g g h k l i j : 𝕜)‖ ^ 2 ≤
      ‖c i‖ ^ 2 + ‖c j‖ ^ 2 - (if i = j then 2 * ‖c i‖ ^ 2 else 0) := by
    intro i hi j hj
    simp only [hz]
    refine (sum_norm_inner_sq_le_norm_sq_of_orthogonal univ (fun k _ l _ hkl ↦ hg k l hkl)
      (fun k _ ↦ hg1 k) _).trans ?_
    split_ifs with h0
    · subst h0; simp; linarith
    · rw [@norm_sub_sq 𝕜, inner_smul_left, inner_smul_right, hh j hj i hi (Ne.symm h0),
        mul_zero, mul_zero, map_zero, mul_zero, sub_zero, norm_smul, norm_smul]
      have := hh1 i hi; have := hh1 j hj
      have h1 : ‖h j‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hh1 j hj)
      have h2 : ‖h i‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hh1 i hi)
      rw [mul_pow, mul_pow]
      nlinarith [sq_nonneg ‖c i‖, sq_nonneg ‖c j‖]
  rw [sum_comm]
  calc ∑ i ∈ S, ∑ l, ∑ j ∈ S, ‖(minor2 g g h k l i j : 𝕜)‖ ^ 2
      = ∑ i ∈ S, ∑ j ∈ S, ∑ l, ‖(minor2 g g h k l i j : 𝕜)‖ ^ 2 :=
        sum_congr rfl fun i _ ↦ sum_comm
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, (‖c i‖ ^ 2 + ‖c j‖ ^ 2 - (if i = j then 2 * ‖c i‖ ^ 2 else 0)) :=
        sum_le_sum fun i hi ↦ sum_le_sum fun j hj ↦ hij i hi j hj
    _ = ∑ i ∈ S, ((#S : ℝ) * ‖c i‖ ^ 2 + ∑ j ∈ S, ‖c j‖ ^ 2 - 2 * ‖c i‖ ^ 2) := by
        refine sum_congr rfl fun i hi ↦ ?_
        rw [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
        simp only [sum_ite_eq, hi, ite_true]
    _ = _ := by
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, ← mul_sum]
        simp only [wt, hc]
        ring

/-- The weight lemma applied to `α_{kl} = Λ_{kl} / 2` and `p_k = wt g h S k`. -/
private theorem sum_lam_mul_le {ι : Type*} (S : Finset ι) (h : ι → H)
    (hh : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪h i, h j⟫ = 0) (hh1 : ∀ i ∈ S, ‖h i‖ ≤ 1)
    {κ : Type*} [Fintype κ] (g : κ → H)
    (hg : ∀ k l, k ≠ l → ⟪g k, g l⟫ = 0) (hg1 : ∀ k, ‖g k‖ ≤ 1) (G : Finset κ)
    (s : κ → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) (hs0 : ∀ k, 0 ≤ s k) (hG : ∀ k ∈ G, θ ≤ s k)
    (hGc : ∀ k ∉ G, s k ≤ θ) (hSG : #S ≤ #G) :
    ∑ k, ∑ l, lam (𝕜 := 𝕜) g g h S k l / 2 * (s k * s l) ≤
      (∑ k ∈ G, s k) ^ 2 - ∑ k ∈ G, s k ^ 2 := by
  have hSG' : ((#S : ℕ) : ℝ) ≤ #G := by exact_mod_cast hSG
  have hp1 := wt_le_one S h hh hh1 g hg1
  have hp0 := wt_nonneg (𝕜 := 𝕜) g h S
  refine sum_sum_mul_le_of_weights G s hθ hs0 hG hGc (fun k l ↦ lam (𝕜 := 𝕜) g g h S k l / 2)
    (wt (𝕜 := 𝕜) g h S) (fun k l ↦ by have := lam_nonneg (𝕜 := 𝕜) g g h S k l; positivity)
    (fun k l ↦ ?_) (fun k ↦ by simp [lam_self]) (fun k l ↦ by rw [lam_symm]) hp0 hp1
    (fun k ↦ ?_) ((sum_wt_le S h hh1 g hg hg1).trans hSG')
  · have := lam_le (𝕜 := 𝕜) g g h S k l
    have := mul_le_mul (hp1 k) (hp1 l) (hp0 l) zero_le_one
    linarith
  · have := sum_lam_le S h hh hh1 g hg hg1 k
    rw [← sum_div]
    have := hp0 k
    nlinarith

end Frames

/-- The algebraic identity behind `Λ²`: for `A_{ij} = ∑_k s_k P_{ik} Q_{kj}` and
`C_{ij} = ∑_l t_l P'_{il} Q'_{lj}`, twice the sum of the mixed principal `2 × 2` minors is
`∑_{k,l} s_k t_l ∑_{i,j} (P_{ik} P'_{jl} - P_{jk} P'_{il}) (Q_{ki} Q'_{lj} - Q_{kj} Q'_{li})`
(Cauchy–Binet for `2 × 2` minors). -/
private theorem two_mul_sum_minor {R ι κ : Type*} [CommRing R] [Fintype κ] (S : Finset ι)
    (s t : κ → R) (P P' : ι → κ → R) (Q Q' : κ → ι → R) :
    2 * ∑ i ∈ S, ∑ j ∈ S, ((∑ k, s k * P i k * Q k i) * (∑ l, t l * P' j l * Q' l j) -
        (∑ k, s k * P i k * Q k j) * (∑ l, t l * P' j l * Q' l i)) =
      ∑ k, ∑ l, s k * t l * ∑ i ∈ S, ∑ j ∈ S,
        (P i k * P' j l - P j k * P' i l) * (Q k i * Q' l j - Q k j * Q' l i) := by
  set f1 : κ → κ → ι → ι → R := fun k l i j ↦ P i k * Q k i * (P' j l * Q' l j) with hf1
  set f2 : κ → κ → ι → ι → R := fun k l i j ↦ P i k * Q k j * (P' j l * Q' l i) with hf2
  have hin : ∀ k l, ∑ i ∈ S, ∑ j ∈ S,
      (P i k * P' j l - P j k * P' i l) * (Q k i * Q' l j - Q k j * Q' l i) =
        2 * ∑ i ∈ S, ∑ j ∈ S, (f1 k l i j - f2 k l i j) := by
    intro k l
    have e : ∀ i j, (P i k * P' j l - P j k * P' i l) * (Q k i * Q' l j - Q k j * Q' l i) =
        (f1 k l i j - f2 k l i j) + (f1 k l j i - f2 k l j i) := by
      intro i j; simp only [hf1, hf2]; ring
    simp only [e, sum_add_distrib]
    rw [sum_comm (f := fun i j ↦ f1 k l j i - f2 k l j i)]
    ring
  have hout : ∀ i j, (∑ k, s k * P i k * Q k i) * (∑ l, t l * P' j l * Q' l j) -
      (∑ k, s k * P i k * Q k j) * (∑ l, t l * P' j l * Q' l i) =
        ∑ k, ∑ l, s k * t l * (f1 k l i j - f2 k l i j) := by
    intro i j
    rw [sum_mul_sum, sum_mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun l _ ↦ ?_
    simp only [hf1, hf2]; ring
  simp only [hout, hin]
  simp only [mul_sum]
  calc _ = ∑ i ∈ S, ∑ k, ∑ j ∈ S, ∑ l, 2 * (s k * t l * (f1 k l i j - f2 k l i j)) :=
        sum_congr rfl fun i _ ↦ sum_comm
    _ = ∑ k, ∑ i ∈ S, ∑ j ∈ S, ∑ l, 2 * (s k * t l * (f1 k l i j - f2 k l i j)) := sum_comm
    _ = ∑ k, ∑ i ∈ S, ∑ l, ∑ j ∈ S, 2 * (s k * t l * (f1 k l i j - f2 k l i j)) :=
        sum_congr rfl fun k _ ↦ sum_congr rfl fun i _ ↦ sum_comm
    _ = ∑ k, ∑ l, ∑ i ∈ S, ∑ j ∈ S, 2 * (s k * t l * (f1 k l i j - f2 k l i j)) :=
        sum_congr rfl fun k _ ↦ sum_comm
    _ = _ := by
        refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ =>
          sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
        ring


namespace LinearMap

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- An orthonormal basis of `E` made of eigenvectors of `T† T`, in the order of decreasing
eigenvalues `s_j(T) ^ 2`. -/
private noncomputable def rightSingularBasis (T : E →ₗ[𝕜] F) :
    OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

private theorem inner_apply_rightSingularBasis (T : E →ₗ[𝕜] F) (j k : Fin (finrank 𝕜 E)) :
    ⟪T (rightSingularBasis T j), T (rightSingularBasis T k)⟫ =
      ((T.singularValues k ^ 2 : ℝ) : 𝕜) * ⟪rightSingularBasis T j, rightSingularBasis T k⟫ := by
  rw [← adjoint_inner_right, ← comp_apply (adjoint T) T, rightSingularBasis,
    IsSymmetric.apply_eigenvectorBasis, inner_smul_right, T.sq_singularValues_fin rfl]

private theorem norm_apply_rightSingularBasis (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) :
    ‖T (rightSingularBasis T j)‖ = T.singularValues j := by
  have h := inner_apply_rightSingularBasis T j j
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    (rightSingularBasis T).orthonormal.1 j] at h
  simp only [RCLike.ofReal_one, one_pow, mul_one] at h
  norm_cast at h
  exact (sq_eq_sq₀ (norm_nonneg _) (T.singularValues_nonneg _)).mp h

/-- The vectors `s_j(T)⁻¹ • T e_j`, where `(e_j)` is `rightSingularBasis T` (zero when
`s_j(T) = 0`). -/
private noncomputable def leftSingularVec (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) : F :=
  (((T.singularValues j)⁻¹ : ℝ) : 𝕜) • T (rightSingularBasis T j)

private theorem apply_rightSingularBasis (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) :
    T (rightSingularBasis T j) = ((T.singularValues j : ℝ) : 𝕜) • leftSingularVec T j := by
  rcases eq_or_ne (T.singularValues j) 0 with h | h
  · have h0 : T (rightSingularBasis T j) = 0 := by
      rw [← norm_eq_zero, norm_apply_rightSingularBasis, h]
    rw [h0, h, RCLike.ofReal_zero, zero_smul]
  · rw [leftSingularVec, smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ h, RCLike.ofReal_one,
      one_smul]

private theorem inner_leftSingularVec_of_ne (T : E →ₗ[𝕜] F) {j k : Fin (finrank 𝕜 E)}
    (h : j ≠ k) : ⟪leftSingularVec T j, leftSingularVec T k⟫ = 0 := by
  rw [leftSingularVec, leftSingularVec, inner_smul_left, inner_smul_right,
    inner_apply_rightSingularBasis, (rightSingularBasis T).orthonormal.2 h, mul_zero, mul_zero,
    mul_zero]

private theorem norm_leftSingularVec_le (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) :
    ‖leftSingularVec T j‖ ≤ 1 := by
  rw [leftSingularVec, norm_smul, norm_apply_rightSingularBasis, RCLike.norm_ofReal, abs_inv,
    abs_of_nonneg (T.singularValues_nonneg _)]
  rcases eq_or_ne (T.singularValues j) 0 with h | h
  · simp [h]
  · rw [inv_mul_cancel₀ h]

private theorem inner_leftSingularVec_apply (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) :
    ⟪leftSingularVec T j, T (rightSingularBasis T j)⟫ = ((T.singularValues j : ℝ) : 𝕜) := by
  rw [leftSingularVec, inner_smul_left, inner_self_eq_norm_sq_to_K, norm_apply_rightSingularBasis,
    RCLike.conj_ofReal]
  rcases eq_or_ne (T.singularValues j) 0 with h | h
  · simp [h]
  · rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, sq, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- **Ky Fan's maximum principle.** For families `(x_i)` in `E` and `(y_i)` in `F`, indexed by
a finite set with at most `n` elements, each pairwise orthogonal and made of vectors of norm at
most `1`, `‖∑ i, ⟪y_i, T x_i⟫‖` is at most the sum of the `n` largest singular values of `T`. -/
theorem norm_sum_inner_le_sum_singularValues {ι : Type*} (s : Finset ι) {x : ι → E}
    {y : ι → F} (hx : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪x i, x j⟫ = 0) (hx1 : ∀ i ∈ s, ‖x i‖ ≤ 1)
    (hy : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪y i, y j⟫ = 0) (hy1 : ∀ i ∈ s, ‖y i‖ ≤ 1)
    (T : E →ₗ[𝕜] F) {n : ℕ} (hn : #s ≤ n) :
    ‖∑ i ∈ s, ⟪y i, T (x i)⟫‖ ≤ ∑ j ∈ Finset.range n, T.singularValues j := by
  set e := rightSingularBasis T
  set f := leftSingularVec T
  have hexp : ∑ i ∈ s, ⟪y i, T (x i)⟫ =
      ∑ j, ∑ i ∈ s, ⟪e j, x i⟫ * (((T.singularValues j : ℝ) : 𝕜) * ⟪y i, f j⟫) := by
    rw [sum_comm]
    refine sum_congr rfl fun i _ ↦ ?_
    calc ⟪y i, T (x i)⟫ = ⟪y i, T (∑ j, ⟪e j, x i⟫ • e j)⟫ := by rw [e.sum_repr']
      _ = _ := by
          rw [map_sum, inner_sum]
          refine sum_congr rfl fun j _ ↦ ?_
          rw [map_smul, inner_smul_right, apply_rightSingularBasis, inner_smul_right]
  have hbound : ‖∑ i ∈ s, ⟪y i, T (x i)⟫‖ ≤ ∑ j : Fin (finrank 𝕜 E), T.singularValues j *
      ((∑ i ∈ s, ‖⟪x i, e j⟫‖ ^ 2 + ∑ i ∈ s, ‖⟪y i, f j⟫‖ ^ 2) / 2) := by
    rw [hexp]
    refine (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ ?_)
    refine (norm_sum_le _ _).trans ?_
    rw [← sum_add_distrib, sum_div, mul_sum]
    refine sum_le_sum fun i _ ↦ ?_
    rw [norm_mul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (T.singularValues_nonneg _),
      norm_inner_symm (e j) (x i)]
    have hσ := T.singularValues_nonneg j
    nlinarith [mul_nonneg hσ (sq_nonneg (‖⟪x i, e j⟫‖ - ‖⟪y i, f j⟫‖))]
  have ha1 (j) : ∑ i ∈ s, ‖⟪x i, e j⟫‖ ^ 2 ≤ 1 := by
    have := sum_norm_inner_sq_le_norm_sq_of_orthogonal s hx hx1 (e j)
    rwa [e.orthonormal.1 j, one_pow] at this
  have hb1 (j) : ∑ i ∈ s, ‖⟪y i, f j⟫‖ ^ 2 ≤ 1 := by
    have := sum_norm_inner_sq_le_norm_sq_of_orthogonal s hy hy1 (f j)
    have h2 : ‖f j‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_leftSingularVec_le T j)
    linarith
  have ha : ∑ j, ∑ i ∈ s, ‖⟪x i, e j⟫‖ ^ 2 ≤ #s := by
    rw [sum_comm]
    calc ∑ i ∈ s, ∑ j, ‖⟪x i, e j⟫‖ ^ 2 ≤ ∑ _i ∈ s, (1 : ℝ) := by
          refine sum_le_sum fun i hi ↦ ?_
          have h1 := sum_norm_inner_sq_le_norm_sq_of_orthogonal univ
            (fun j _ k _ h ↦ e.orthonormal.2 h) (fun j _ ↦ (e.orthonormal.1 j).le) (x i)
          have h1' : ∑ j, ‖⟪x i, e j⟫‖ ^ 2 = ∑ j, ‖⟪e j, x i⟫‖ ^ 2 :=
            sum_congr rfl fun j _ ↦ by rw [norm_inner_symm]
          have h3 : ‖x i‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hx1 i hi)
          linarith
      _ = #s := by simp
  have hb : ∑ j, ∑ i ∈ s, ‖⟪y i, f j⟫‖ ^ 2 ≤ #s := by
    rw [sum_comm]
    calc ∑ i ∈ s, ∑ j, ‖⟪y i, f j⟫‖ ^ 2 ≤ ∑ _i ∈ s, (1 : ℝ) := by
          refine sum_le_sum fun i hi ↦ ?_
          have h1 := sum_norm_inner_sq_le_norm_sq_of_orthogonal univ
            (fun j _ k _ h ↦ inner_leftSingularVec_of_ne T h)
            (fun j _ ↦ norm_leftSingularVec_le T j) (y i)
          have h1' : ∑ j, ‖⟪y i, f j⟫‖ ^ 2 = ∑ j, ‖⟪f j, y i⟫‖ ^ 2 :=
            sum_congr rfl fun j _ ↦ by rw [norm_inner_symm]
          have h3 : ‖y i‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hy1 i hi)
          linarith
      _ = #s := by simp
  refine hbound.trans (sum_mul_le_sum_range T.singularValues T.singularValues_antitone
    T.singularValues_nonneg
    (fun j ↦ (∑ i ∈ s, ‖⟪x i, e j⟫‖ ^ 2 + ∑ i ∈ s, ‖⟪y i, f j⟫‖ ^ 2) / 2)
    (fun j ↦ by positivity) (fun j ↦ by linarith [ha1 j, hb1 j]) ?_)
  rw [← sum_div, sum_add_distrib]
  have : (#s : ℝ) ≤ n := by exact_mod_cast hn
  linarith

private theorem sum_range_singularValues_eq (T : E →ₗ[𝕜] F) (n : ℕ) :
    ∑ j ∈ Finset.range n, T.singularValues j =
      ∑ j ∈ univ.filter (fun j : Fin (finrank 𝕜 E) ↦ (j : ℕ) < n), T.singularValues j := by
  rw [sum_filter, Fin.sum_univ_eq_sum_range (fun k ↦ if k < n then T.singularValues k else 0),
    ← sum_filter]
  symm
  apply sum_subset
  · intro k hk
    simp only [mem_filter, Finset.mem_range] at hk ⊢
    exact hk.2
  · intro k hk hk'
    simp only [mem_filter, Finset.mem_range, not_and, not_lt] at hk hk'
    exact T.singularValues_of_finrank_le (not_lt.mp fun h ↦ (not_lt.mpr (hk' h)) hk)

/-- **Ky Fan's inequality**: the sum of the `n` largest singular values is subadditive. -/
theorem sum_singularValues_add_le (u v : E →ₗ[𝕜] F) (n : ℕ) :
    ∑ j ∈ Finset.range n, (u + v).singularValues j ≤
      ∑ j ∈ Finset.range n, u.singularValues j + ∑ j ∈ Finset.range n, v.singularValues j := by
  set e := rightSingularBasis (u + v)
  set f := leftSingularVec (u + v)
  set S := univ.filter (fun j : Fin (finrank 𝕜 E) ↦ (j : ℕ) < n)
  have hSn : #S ≤ n := by
    rw [Fin.card_filter_val_lt]
    exact min_le_right _ _
  rw [sum_range_singularValues_eq]
  have key : ((∑ j ∈ S, (u + v).singularValues j : ℝ) : 𝕜) =
      ∑ j ∈ S, ⟪f j, u (e j)⟫ + ∑ j ∈ S, ⟪f j, v (e j)⟫ := by
    rw [← sum_add_distrib, RCLike.ofReal_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [← inner_add_right, ← add_apply, inner_leftSingularVec_apply]
  have hxo : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪e i, e j⟫ = 0 := fun i _ j _ h ↦ e.orthonormal.2 h
  have hx1 : ∀ i ∈ S, ‖e i‖ ≤ 1 := fun i _ ↦ (e.orthonormal.1 i).le
  have hyo : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪f i, f j⟫ = 0 :=
    fun i _ j _ h ↦ inner_leftSingularVec_of_ne (u + v) h
  have hy1 : ∀ i ∈ S, ‖f i‖ ≤ 1 := fun i _ ↦ norm_leftSingularVec_le (u + v) i
  calc ∑ j ∈ S, (u + v).singularValues j
      = ‖((∑ j ∈ S, (u + v).singularValues j : ℝ) : 𝕜)‖ := by
        rw [RCLike.norm_ofReal,
          abs_of_nonneg (sum_nonneg fun j _ ↦ (u + v).singularValues_nonneg _)]
    _ ≤ ‖∑ j ∈ S, ⟪f j, u (e j)⟫‖ + ‖∑ j ∈ S, ⟪f j, v (e j)⟫‖ := by
        rw [key]
        exact norm_add_le _ _
    _ ≤ _ := add_le_add (norm_sum_inner_le_sum_singularValues S hxo hx1 hyo hy1 u hSn)
        (norm_sum_inner_le_sum_singularValues S hxo hx1 hyo hy1 v hSn)


/-- The singular value expansion `⟪y, T x⟫ = ∑_k s_k(T) ⟪y, f_k⟫ ⟪e_k, x⟫`. -/
private theorem inner_apply_eq_sum (T : E →ₗ[𝕜] F) (x : E) (y : F) :
    ⟪y, T x⟫ = ∑ k : Fin (finrank 𝕜 E), ((T.singularValues k : ℝ) : 𝕜) * conj ⟪leftSingularVec T k,
        y⟫ *
      ⟪rightSingularBasis T k, x⟫ := by
  calc ⟪y, T x⟫ = ⟪y, T (∑ k : Fin (finrank 𝕜 E), ⟪rightSingularBasis T k,
      x⟫ • rightSingularBasis T k)⟫ := by
        rw [(rightSingularBasis T).sum_repr']
    _ = _ := by
        rw [map_sum, inner_sum]
        refine sum_congr rfl fun k _ ↦ ?_
        rw [map_smul, inner_smul_right, apply_rightSingularBasis, inner_smul_right, inner_conj_symm]
        ring

/-- The sum over ordered pairs `i, j ∈ S` of the mixed principal `2 × 2` minors of the
compressions `(⟪y_i, T x_j⟫)` and `(⟪y_i, T' x_j⟫)`; for `T = T'` it is twice the second
elementary symmetric function of the eigenvalues of the compression. -/
private def bform {ι : Type*} (S : Finset ι) (x : ι → E) (y : ι → F) (T T' : E →ₗ[𝕜] F) : 𝕜 :=
  ∑ i ∈ S, ∑ j ∈ S,
    (⟪y i, T (x i)⟫ * ⟪y j, T' (x j)⟫ - ⟪y i, T (x j)⟫ * ⟪y j, T' (x i)⟫)

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
private theorem bform_add {ι : Type*} (S : Finset ι) (x : ι → E) (y : ι → F) (u v : E →ₗ[𝕜] F) :
    bform S x y (u + v) (u + v) =
      bform S x y u u + bform S x y u v + bform S x y v u + bform S x y v v := by
  simp only [bform, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only [LinearMap.add_apply, inner_add_right]
  ring

/-- `|bform| ≤ ¼ ∑_{k,l} s_k(T) s_l(T') (Λ^f_{kl} + Λ^e_{kl})`, from the Cauchy–Binet identity
and `|ab| ≤ (|a|² + |b|²)/2`. -/
private theorem norm_bform_le {ι : Type*} (S : Finset ι) (x : ι → E) (y : ι → F)
    (T T' : E →ₗ[𝕜] F) :
    ‖bform S x y T T'‖ ≤ (1 / 4) * ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E),
        T.singularValues k * T'.singularValues l *
      (lam (𝕜 := 𝕜) (leftSingularVec T) (leftSingularVec T') y S k l +
        lam (𝕜 := 𝕜) (rightSingularBasis T) (rightSingularBasis T') x S k l) := by
  have h2 : (2 : 𝕜) * bform S x y T T' = ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E),
      ((T.singularValues k : ℝ) : 𝕜) *
      ((T'.singularValues l : ℝ) : 𝕜) * ∑ i ∈ S, ∑ j ∈ S,
        conj (minor2 (leftSingularVec T) (leftSingularVec T') y k l i j) * minor2
            (rightSingularBasis T) (rightSingularBasis T') x k l i j := by
    have := two_mul_sum_minor S (fun k : Fin (finrank 𝕜 E) ↦ ((T.singularValues k : ℝ) : 𝕜))
      (fun l : Fin (finrank 𝕜 E) ↦ ((T'.singularValues l : ℝ) : 𝕜))
      (fun i (k : Fin (finrank 𝕜 E)) ↦ conj ⟪leftSingularVec T k, y i⟫)
      (fun i (l : Fin (finrank 𝕜 E)) ↦ conj ⟪leftSingularVec T' l, y i⟫)
      (fun (k : Fin (finrank 𝕜 E)) j ↦ ⟪rightSingularBasis T k, x j⟫)
      (fun (l : Fin (finrank 𝕜 E)) j ↦ ⟪rightSingularBasis T' l, x j⟫)
    rw [bform]
    simp only [inner_apply_eq_sum T, inner_apply_eq_sum T']
    refine this.trans ?_
    refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
    congr 1
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    simp only [minor2, map_sub, map_mul]
  have hb : ‖(2 : 𝕜) * bform S x y T T'‖ ≤ ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E),
      T.singularValues k * T'.singularValues l *
      ((lam (𝕜 := 𝕜) (leftSingularVec T) (leftSingularVec T') y S k l +
        lam (𝕜 := 𝕜) (rightSingularBasis T) (rightSingularBasis T') x S k l) / 2) := by
    rw [h2]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k _ =>
      (norm_sum_le _ _).trans (sum_le_sum fun l _ ↦ ?_))
    rw [norm_mul, norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal,
      abs_of_nonneg (T.singularValues_nonneg _), abs_of_nonneg (T'.singularValues_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (T.singularValues_nonneg _) (T'.singularValues_nonneg _))
    unfold lam
    rw [← sum_add_distrib, sum_div]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i _ ↦ ?_)
    rw [← sum_add_distrib, sum_div]
    refine (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ ?_)
    rw [norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖(minor2 (leftSingularVec T) (leftSingularVec T') y k l i j : 𝕜)‖ -
      ‖(minor2 (rightSingularBasis T) (rightSingularBasis T') x k l i j : 𝕜)‖)]
  have e : ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), T.singularValues k *
      T'.singularValues l *
      ((lam (𝕜 := 𝕜) (leftSingularVec T) (leftSingularVec T') y S k l +
        lam (𝕜 := 𝕜) (rightSingularBasis T) (rightSingularBasis T') x S k l) / 2) =
      2 * ((1 / 4) * ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), T.singularValues k *
          T'.singularValues l *
      (lam (𝕜 := 𝕜) (leftSingularVec T) (leftSingularVec T') y S k l +
        lam (𝕜 := 𝕜) (rightSingularBasis T) (rightSingularBasis T') x S k l)) := by
    rw [← mul_assoc, mul_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun l _ ↦ ?_
    ring
  rw [norm_mul, RCLike.norm_two, e] at hb
  linarith

/-- The mixed term: `|bform S x y T T'| ≤ (∑_{j<n} s_j(T)) (∑_{j<n} s_j(T'))` when `|S| ≤ n`. -/
private theorem norm_bform_le_mul {ι : Type*} (S : Finset ι) (x : ι → E) (y : ι → F)
    (hx : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪x i, x j⟫ = 0) (hx1 : ∀ i ∈ S, ‖x i‖ ≤ 1)
    (hy : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪y i, y j⟫ = 0) (hy1 : ∀ i ∈ S, ‖y i‖ ≤ 1)
    (T T' : E →ₗ[𝕜] F) {n : ℕ} (hn : #S ≤ n) :
    ‖bform S x y T T'‖ ≤
      (∑ j ∈ Finset.range n, T.singularValues j) * ∑ j ∈ Finset.range n, T'.singularValues j := by
  have hKF : ∀ (T : E →ₗ[𝕜] F) (c : Fin (finrank 𝕜 E) → ℝ), (∀ k, 0 ≤ c k) → (∀ k, c k ≤ 1) →
      ∑ k : Fin (finrank 𝕜 E), c k ≤ #S → ∑ k : Fin (finrank 𝕜 E), T.singularValues k * c k ≤
          ∑ j ∈ Finset.range n, T.singularValues j :=
    fun T c h0 h1 hs ↦ sum_mul_le_sum_range T.singularValues T.singularValues_antitone
      T.singularValues_nonneg c h0 h1 (hs.trans (by exact_mod_cast hn))
  have hfo : ∀ T : E →ₗ[𝕜] F, ∀ k l, k ≠ l → ⟪leftSingularVec T k, leftSingularVec T l⟫ = 0 :=
    fun T k l h ↦ inner_leftSingularVec_of_ne T h
  have heo : ∀ T : E →ₗ[𝕜] F, ∀ k l, k ≠ l → ⟪rightSingularBasis T k, rightSingularBasis T l⟫ = 0 :=
    fun T k l h ↦ (rightSingularBasis T).orthonormal.2 h
  have he1 : ∀ T : E →ₗ[𝕜] F, ∀ k, ‖rightSingularBasis T k‖ ≤ 1 :=
    fun T k ↦ ((rightSingularBasis T).orthonormal.1 k).le
  have Aq : ∀ T : E →ₗ[𝕜] F, ∑ k : Fin (finrank 𝕜 E), T.singularValues k * wt (𝕜 := 𝕜)
      (leftSingularVec T) y S k ≤
      ∑ j ∈ Finset.range n, T.singularValues j := fun T =>
    hKF T _ (wt_nonneg _ _ _) (wt_le_one S y hy hy1 _ (norm_leftSingularVec_le T))
      (sum_wt_le S y hy1 _ (hfo T) (norm_leftSingularVec_le T))
  have Ap : ∀ T : E →ₗ[𝕜] F, ∑ k : Fin (finrank 𝕜 E), T.singularValues k * wt (𝕜 := 𝕜)
      (rightSingularBasis T) x S k ≤
      ∑ j ∈ Finset.range n, T.singularValues j := fun T =>
    hKF T _ (wt_nonneg _ _ _) (wt_le_one S x hx hx1 _ (he1 T))
      (sum_wt_le S x hx1 _ (heo T) (he1 T))
  have N : ∀ (T : E →ₗ[𝕜] F) (c : Fin (finrank 𝕜 E) → ℝ), (∀ k, 0 ≤ c k) →
      0 ≤ ∑ k : Fin (finrank 𝕜 E), T.singularValues k * c k :=
    fun T c h ↦ sum_nonneg fun k _ ↦ mul_nonneg (T.singularValues_nonneg _) (h k)
  have K0 : ∀ T : E →ₗ[𝕜] F, 0 ≤ ∑ j ∈ Finset.range n, T.singularValues j :=
    fun T ↦ sum_nonneg fun j _ ↦ T.singularValues_nonneg j
  calc ‖bform S x y T T'‖
      ≤ (1 / 4) * ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), T.singularValues k *
          T'.singularValues l *
        (lam (𝕜 := 𝕜) (leftSingularVec T) (leftSingularVec T') y S k l +
          lam (𝕜 := 𝕜) (rightSingularBasis T) (rightSingularBasis T') x S k l) :=
              norm_bform_le S x y T T'
    _ ≤ (1 / 4) * ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), T.singularValues k *
        T'.singularValues l *
        (2 * wt (𝕜 := 𝕜) (leftSingularVec T) y S k * wt (𝕜 := 𝕜) (leftSingularVec T') y S l +
          2 * wt (𝕜 := 𝕜) (rightSingularBasis T) x S k * wt (𝕜 := 𝕜)
              (rightSingularBasis T') x S l) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun k _ ↦ sum_le_sum fun l _ ↦ ?_)
          (by norm_num)
        exact mul_le_mul_of_nonneg_left (add_le_add (lam_le _ _ _ _ _ _) (lam_le _ _ _ _ _ _))
          (mul_nonneg (T.singularValues_nonneg _) (T'.singularValues_nonneg _))
    _ = (1 / 2) * ((∑ k : Fin (finrank 𝕜 E), T.singularValues k * wt (𝕜 := 𝕜)
        (leftSingularVec T) y S k) *
          (∑ l : Fin (finrank 𝕜 E), T'.singularValues l * wt (𝕜 := 𝕜) (leftSingularVec T') y S l) +
        (∑ k : Fin (finrank 𝕜 E), T.singularValues k * wt (𝕜 := 𝕜) (rightSingularBasis T) x S k) *
          (∑ l : Fin (finrank 𝕜 E), T'.singularValues l * wt (𝕜 := 𝕜)
              (rightSingularBasis T') x S l)) := by
        rw [sum_mul_sum, sum_mul_sum, ← sum_add_distrib, mul_sum, mul_sum]
        refine sum_congr rfl fun k _ ↦ ?_
        rw [← sum_add_distrib, mul_sum, mul_sum]
        refine sum_congr rfl fun l _ ↦ ?_
        ring
    _ ≤ (1 / 2) * ((∑ j ∈ Finset.range n, T.singularValues j) * (∑ j ∈ Finset.range n,
        T'.singularValues j) +
        (∑ j ∈ Finset.range n, T.singularValues j) * (∑ j ∈ Finset.range n, T'.singularValues j)) :=
            by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
        · exact mul_le_mul (Aq T) (Aq T') (N T' _ (wt_nonneg _ _ _)) (K0 T)
        · exact mul_le_mul (Ap T) (Ap T') (N T' _ (wt_nonneg _ _ _)) (K0 T)
    _ = _ := by ring

/-- **The pure term**: `|bform S x y T T| ≤ (∑_{k∈G} s_k)² - ∑_{k∈G} s_k²` for a set `G` of
indices cut off by a threshold `θ` and `|S| ≤ |G|`. -/
private theorem norm_bform_self_le {ι : Type*} (S : Finset ι) (x : ι → E) (y : ι → F)
    (hx : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪x i, x j⟫ = 0) (hx1 : ∀ i ∈ S, ‖x i‖ ≤ 1)
    (hy : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪y i, y j⟫ = 0) (hy1 : ∀ i ∈ S, ‖y i‖ ≤ 1)
    (T : E →ₗ[𝕜] F) (G : Finset (Fin (finrank 𝕜 E))) {θ : ℝ}
    (hθ : 0 ≤ θ) (hG : ∀ k ∈ G, θ ≤ T.singularValues k)
    (hGc : ∀ k ∉ G, T.singularValues k ≤ θ) (hSG : #S ≤ #G) :
    ‖bform S x y T T‖ ≤ (∑ k ∈ G, T.singularValues k) ^ 2 - ∑ k ∈ G, T.singularValues k ^ 2 := by
  have Bf := sum_lam_mul_le S y hy hy1 (leftSingularVec T)
      (fun k l h ↦ inner_leftSingularVec_of_ne T h)
    (norm_leftSingularVec_le T) G (fun k ↦ T.singularValues k) hθ
        (fun k ↦ T.singularValues_nonneg _)
    hG hGc hSG
  have Be := sum_lam_mul_le S x hx hx1 (rightSingularBasis T) (fun k l h ↦
      (rightSingularBasis T).orthonormal.2 h)
    (fun k ↦ ((rightSingularBasis T).orthonormal.1 k).le) G (fun k ↦ T.singularValues k) hθ
    (fun k ↦ T.singularValues_nonneg _) hG hGc hSG
  have e : (1 / 4) * ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), T.singularValues k *
      T.singularValues l *
      (lam (𝕜 := 𝕜) (leftSingularVec T) (leftSingularVec T) y S k l + lam (𝕜 := 𝕜)
          (rightSingularBasis T) (rightSingularBasis T) x S k l) =
      (1 / 2) * (∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), lam (𝕜 := 𝕜) (leftSingularVec T)
          (leftSingularVec T) y S k l / 2 *
        (T.singularValues k * T.singularValues l) +
        ∑ k : Fin (finrank 𝕜 E), ∑ l : Fin (finrank 𝕜 E), lam (𝕜 := 𝕜) (rightSingularBasis T)
            (rightSingularBasis T) x S k l / 2 *
        (T.singularValues k * T.singularValues l)) := by
    rw [← sum_add_distrib, mul_sum, mul_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [← sum_add_distrib, mul_sum, mul_sum]
    refine sum_congr rfl fun l _ ↦ ?_
    ring
  have := norm_bform_le S x y T T
  rw [e] at this
  linarith


/-- A sum over `Finset.range n` of a function vanishing from `d` on is a sum over
`{j : Fin d | j < n}`. -/
private theorem sum_range_eq_sum_filter (d : ℕ) (f : ℕ → ℝ) (hf : ∀ k, d ≤ k → f k = 0) (n : ℕ) :
    ∑ j ∈ Finset.range n, f j = ∑ j ∈ univ.filter (fun j : Fin d ↦ (j : ℕ) < n), f j := by
  have h1 : ∑ j : Fin d, (if (j : ℕ) < n then f j else 0) =
      ∑ k ∈ Finset.range d, (if k < n then f k else 0) :=
    Fin.sum_univ_eq_sum_range (fun k ↦ if k < n then f k else 0) _
  rw [sum_filter, h1, ← sum_filter]
  symm
  apply sum_subset
  · intro k hk
    simp only [mem_filter, Finset.mem_range] at hk ⊢
    exact hk.2
  · intro k hk hk'
    simp only [mem_filter, Finset.mem_range, not_and, not_lt] at hk hk'
    exact hf k (not_lt.mp fun h ↦ (not_lt.mpr (hk' h)) hk)

/-- The second elementary symmetric function of the `n` largest singular values of `T`. -/
private noncomputable def sigmaTwo (n : ℕ) (T : E →ₗ[𝕜] F) : ℝ :=
  ∑ t ∈ (Finset.range n).powersetCard 2, ∏ i ∈ t, T.singularValues i

/-- `2 σ₂(T) = (∑_{k<n} s_k)² - ∑_{k<n} s_k²`, the sums over the indices `k < dim E`. -/
private theorem two_mul_sigma_two (T : E →ₗ[𝕜] F) (n : ℕ) :
    2 * sigmaTwo n T =
      (∑ k ∈ univ.filter (fun j : Fin (finrank 𝕜 E) ↦ (j : ℕ) < n), T.singularValues k) ^ 2 -
        ∑ k ∈ univ.filter (fun j : Fin (finrank 𝕜 E) ↦ (j : ℕ) < n), T.singularValues k ^ 2 := by
  rw [sigmaTwo, two_mul_sum_powersetCard_two,
    sum_range_eq_sum_filter _ _ (fun k hk ↦ T.singularValues_of_finrank_le hk) n,
    sum_range_eq_sum_filter _ (fun k ↦ T.singularValues k ^ 2)
      (fun k hk ↦ by simp [T.singularValues_of_finrank_le hk]) n]

/-- For `w` and its own singular vectors, `bform` is `2 σ₂(w)`. -/
private theorem bform_rightSingularBasis (w : E →ₗ[𝕜] F) (n : ℕ) :
    bform (univ.filter (fun j : Fin (finrank 𝕜 E) ↦ (j : ℕ) < n)) (rightSingularBasis w)
        (leftSingularVec w) w w =
      ((2 * sigmaTwo n w : ℝ) : 𝕜) := by
  have hij : ∀ i j, ⟪leftSingularVec w i, w (rightSingularBasis w j)⟫ =
      if i = j then ((w.singularValues i : ℝ) : 𝕜) else 0 := by
    intro i j
    split_ifs with h
    · subst h; exact inner_leftSingularVec_apply w i
    · rw [apply_rightSingularBasis, inner_smul_right, inner_leftSingularVec_of_ne w h, mul_zero]
  rw [two_mul_sigma_two, bform]
  set G := univ.filter (fun j : Fin (finrank 𝕜 E) ↦ (j : ℕ) < n)
  have e : ∀ i j, ⟪leftSingularVec w i, w (rightSingularBasis w i)⟫ * ⟪leftSingularVec w j, w
      (rightSingularBasis w j)⟫ -
      ⟪leftSingularVec w i, w (rightSingularBasis w j)⟫ * ⟪leftSingularVec w j, w
          (rightSingularBasis w i)⟫ =
      ((w.singularValues i * w.singularValues j -
        if i = j then w.singularValues i ^ 2 else 0 : ℝ) : 𝕜) := by
    intro i j
    simp only [hij, ite_true]
    by_cases h : i = j
    · subst h; simp; ring
    · simp [h, Ne.symm h]
  have hr : ∑ i ∈ G, ∑ j ∈ G, (w.singularValues i * w.singularValues j -
      if i = j then w.singularValues i ^ 2 else 0) =
      (∑ k ∈ G, w.singularValues k) ^ 2 - ∑ k ∈ G, w.singularValues k ^ 2 := by
    simp only [sum_sub_distrib]
    rw [sq, sum_mul_sum]
    congr 1
    refine sum_congr rfl fun i hi ↦ ?_
    simp only [sum_ite_eq, hi, ite_true]
  simp only [e]
  rw [← hr]
  simp only [RCLike.ofReal_sum]

/-- `σ₂(u + v) ≤ σ₂(u) + (∑_{j<n} s_j(u)) (∑_{j<n} s_j(v)) + σ₂(v)`. -/
private theorem sigma_two_add_le (u v : E →ₗ[𝕜] F) (n : ℕ) :
    sigmaTwo n (u + v) ≤ sigmaTwo n u + (∑ j ∈ Finset.range n, u.singularValues j) *
        ∑ j ∈ Finset.range n, v.singularValues j + sigmaTwo n v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ∀ T : E →ₗ[𝕜] F, sigmaTwo 0 T = 0 := fun T ↦ by
      rw [sigmaTwo, Finset.range_zero, powersetCard_eq_empty.mpr (by simp), sum_empty]
    simp [h0]
  obtain ⟨G, hG⟩ : ∃ G : Finset (Fin (finrank 𝕜 E)), G = univ.filter (fun j : Fin (finrank 𝕜 E) ↦
      (j : ℕ) < n) :=
    ⟨_, rfl⟩
  have hGn : #G ≤ n := by rw [hG, Fin.card_filter_val_lt]; exact min_le_right _ _
  have hord1 : ∀ T : E →ₗ[𝕜] F, ∀ k ∈ G, T.singularValues (n - 1) ≤ T.singularValues k :=
    fun T k hk ↦ T.singularValues_antitone (by rw [hG, mem_filter] at hk; omega)
  have hord2 : ∀ T : E →ₗ[𝕜] F, ∀ k ∉ G, T.singularValues k ≤ T.singularValues (n - 1) :=
    fun T k hk ↦ T.singularValues_antitone (by
      rw [hG, mem_filter, not_and, not_lt] at hk; have := hk (mem_univ _); omega)
  have hσ : ∀ T : E →ₗ[𝕜] F, 2 * sigmaTwo n T =
      (∑ k ∈ G, T.singularValues k) ^ 2 - ∑ k ∈ G, T.singularValues k ^ 2 := fun T ↦ by
    rw [hG]; exact two_mul_sigma_two T n
  have hbw : bform G (rightSingularBasis (u + v)) (leftSingularVec (u + v)) (u + v) (u + v) =
      ((2 * sigmaTwo n (u + v) : ℝ) : 𝕜) := by rw [hG]; exact bform_rightSingularBasis _ n
  have hx : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → ⟪rightSingularBasis (u + v) i, rightSingularBasis (u + v) j⟫ =
      0 :=
    fun i _ j _ h ↦ (rightSingularBasis (u + v)).orthonormal.2 h
  have hx1 : ∀ i ∈ G, ‖rightSingularBasis (u + v) i‖ ≤ 1 := fun i _ ↦ ((rightSingularBasis (u +
      v)).orthonormal.1 i).le
  have hy : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → ⟪leftSingularVec (u + v) i, leftSingularVec (u + v) j⟫ = 0 :=
    fun i _ j _ h ↦ inner_leftSingularVec_of_ne (u + v) h
  have hy1 : ∀ i ∈ G, ‖leftSingularVec (u + v) i‖ ≤ 1 := fun i _ ↦ norm_leftSingularVec_le (u + v) i
  have Buu := norm_bform_self_le G _ _ hx hx1 hy hy1 u G (u.singularValues_nonneg _)
    (hord1 u) (hord2 u) le_rfl
  have Bvv := norm_bform_self_le G _ _ hx hx1 hy hy1 v G (v.singularValues_nonneg _)
    (hord1 v) (hord2 v) le_rfl
  have Buv := norm_bform_le_mul G _ _ hx hx1 hy hy1 u v hGn
  have Bvu := norm_bform_le_mul G _ _ hx hx1 hy hy1 v u hGn
  rw [← hσ] at Buu Bvv
  have hw := bform_add G (rightSingularBasis (u + v)) (leftSingularVec (u + v)) u v
  rw [hbw] at hw
  have h0 : 0 ≤ sigmaTwo n (u + v) :=
    sum_nonneg fun _ _ ↦ prod_nonneg fun i _ ↦ (u + v).singularValues_nonneg i
  have hn2 : 2 * sigmaTwo n (u + v) = ‖((2 * sigmaTwo n (u + v) : ℝ) : 𝕜)‖ := by
    rw [RCLike.norm_ofReal, abs_of_nonneg (by linarith)]
  rw [hw] at hn2
  set x := rightSingularBasis (u + v)
  set y := leftSingularVec (u + v)
  have t1 := norm_add_le (bform G x y u u + bform G x y u v + bform G x y v u) (bform G x y v v)
  have t2 := norm_add_le (bform G x y u u + bform G x y u v) (bform G x y v u)
  have t3 := norm_add_le (bform G x y u u) (bform G x y u v)
  linarith
/-- Writing `σ₂(T)` for the second elementary symmetric function of the `n` largest singular
values of `T`, `σ₂(u + v) ≤ σ₂(u) + (∑ j < n, s_j(u)) (∑ j < n, s_j(v)) + σ₂(v)`.
Ky Fan's inequality `sum_singularValues_add_le` is the analogous statement for the first
elementary symmetric function. -/
theorem sum_powersetCard_two_prod_singularValues_add_le (u v : E →ₗ[𝕜] F) (n : ℕ) :
    ∑ t ∈ (Finset.range n).powersetCard 2, ∏ i ∈ t, (u + v).singularValues i ≤
      ∑ t ∈ (Finset.range n).powersetCard 2, ∏ i ∈ t, u.singularValues i +
        (∑ j ∈ Finset.range n, u.singularValues j) * ∑ j ∈ Finset.range n, v.singularValues j +
        ∑ t ∈ (Finset.range n).powersetCard 2, ∏ i ∈ t, v.singularValues i :=
  sigma_two_add_le u v n

end LinearMap
