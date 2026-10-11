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

end LinearMap
