/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Dominance

/-!
# Spectral dominance for primitive matrices

Phase alignment and triangle-equality arguments showing that eigenvalues of primitive
non-negative matrices at the Perron modulus are exactly the Perron root.

## Main results

* `spectral_dominance_of_primitive`: if `‖μ‖` equals the Perron root, then `μ` is the Perron root.
* `spectral_dominance_of_primitive'`: every other eigenvalue has strictly smaller modulus.

## Implementation notes

The proof uses a positive matrix power from primitivity to force global phase alignment of a
complex eigenvector, then identifies the eigenvalue with the real Perron root.

## References

* [E. Seneta, *Non-negative Matrices and Markov Chains*][seneta2006]

## Tags

Perron–Frobenius theorem, primitive matrix, spectral dominance
-/

@[expose] public section

namespace Matrix
open CollatzWielandt Classical Complex

variable {n : Type*} {A : Matrix n n ℝ} [Fintype n] [Nonempty n] [DecidableEq n]


omit [Nonempty n] [DecidableEq n] in
/-- Triangle equality when `‖μ‖` equals the Perron root. -/
lemma triangle_equality_of_norm_eq_perron_root
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    {r : ℝ} (h_norm_eq_r : ‖μ‖ = r)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = r • (fun i => ‖x i‖)) :
    ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖ := by
  intro i
  let x_abs := fun i => ‖x i‖
  calc
    ‖∑ j, (A i j : ℂ) * x j‖ = ‖((A.map (algebraMap ℝ ℂ)) *ᵥ x) i‖ := by simp; rfl
    _ = ‖(μ • x) i‖ := by rw [hx_eig]
    _ = ‖μ‖ * ‖x i‖ := by simp
    _ = r * x_abs i := by rw [h_norm_eq_r];
    _ = (r • x_abs) i := by simp [smul_eq_mul]
    _ = (A *ᵥ x_abs) i := by rw [h_x_abs_eig]
    _ = ∑ j, A i j * x_abs j := by simp [mulVec_apply]
    _ = ∑ j, ‖(A i j : ℂ) * x j‖ := by
        simp_rw [x_abs, norm_mul, norm_ofReal, abs_of_nonneg (hA_nonneg _ _)]

/-- `(A *ᵥ |x|) i` is positive when `|x|` is a Perron eigenvector. -/
lemma mulVec_x_abs_pos_of_irreducible {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    {x_abs : n → ℝ} (h_x_abs_nonneg : ∀ i, 0 ≤ x_abs i)
    (h_x_abs_eig : A *ᵥ x_abs = (perronRoot_alt A) • x_abs)
    (hx_abs_ne_zero : x_abs ≠ 0) (i : n) :
    0 < (A *ᵥ x_abs) i := by
  have h_x_abs_pos : ∀ k, 0 < x_abs k :=
    eigenvector_is_positive_of_irreducible hA_irred h_x_abs_eig h_x_abs_nonneg hx_abs_ne_zero
  have h_r_pos : 0 < perronRoot_alt A := by
    obtain ⟨i₀, j₀, hAij_pos⟩ := Matrix.Irreducible.exists_pos_entry (A := A) hA_irred
    have h_sum_pos : 0 < ∑ k, A i₀ k * x_abs k := by
      apply sum_pos_of_mem
      · intro k _
        exact mul_nonneg (hA_irred.nonneg i₀ k) (h_x_abs_pos k).le
      · exact Finset.mem_univ j₀
      · exact mul_pos hAij_pos (h_x_abs_pos j₀)
    have h_eq : (A *ᵥ x_abs) i₀ = (perronRoot_alt A) * x_abs i₀ := by
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun h_x_abs_eig i₀
    have : 0 < (perronRoot_alt A) * x_abs i₀ := by
      exact lt_of_lt_of_eq h_sum_pos h_eq
    exact pos_of_mul_pos_left this (h_x_abs_pos i₀).le
  have h_eq_i : (A *ᵥ x_abs) i = (perronRoot_alt A) * x_abs i := by
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun h_x_abs_eig i
  have : 0 < (perronRoot_alt A) * x_abs i :=
    mul_pos h_r_pos (h_x_abs_pos i)
  simpa [h_eq_i] using this

/-- Triangle equality forces a non-zero row sum. -/
lemma sum_s_ne_zero_of_triangle_eq {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℂ} (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot_alt A) • (fun i => ‖x i‖))
    (hx_ne_zero : x ≠ 0) (i : n) :
    (∑ j, (A i j : ℂ) * x j) ≠ 0 := by
  let x_abs := fun i => ‖x i‖
  have hx_abs_ne_zero : x_abs ≠ 0 := by
    contrapose! hx_ne_zero; ext i; exact norm_eq_zero.mp (congr_fun hx_ne_zero i)
  intro hs_zero
  have h_norm_s_zero : ‖∑ j, (A i j : ℂ) * x j‖ = 0 := by rw [hs_zero]; exact norm_zero
  have h_sum_norm_zero : ∑ j, ‖(A i j : ℂ) * x j‖ = 0 := h_triangle_eq i ▸ h_norm_s_zero
  have h_sum_A_x_abs_zero : ∑ j, A i j * x_abs j = 0 := by
    simpa [norm_mul, norm_ofReal, abs_of_nonneg (hA_nonneg _ _)] using h_sum_norm_zero
  have h_Ax_abs_i_zero : (A *ᵥ x_abs) i = 0 := by simpa [mulVec_apply]
  have h_pos := mulVec_x_abs_pos_of_irreducible hA_irred (fun _ => norm_nonneg _) h_x_abs_eig
      hx_abs_ne_zero i
  exact h_pos.ne' h_Ax_abs_i_zero

omit [Fintype n] [Nonempty n] [DecidableEq n] in
/-- A positive entry gives a non-zero term. -/
lemma term_ne_zero_of_pos_entry {A : Matrix n n ℝ} {x : n → ℂ}
    {i j : n} (hAij_pos : 0 < A i j) (hxj_ne_zero : x j ≠ 0) :
    (A i j : ℂ) * x j ≠ 0 :=
  mul_ne_zero (ofReal_ne_zero.mpr hAij_pos.ne') hxj_ne_zero

/-- Positive entries in the same row share the phase of `x`. -/
lemma aligned_neighbors_of_triangle_eq {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot_alt A) • (fun i => ‖x i‖)) :
    ∀ k l m, 0 < A k l → 0 < A k m → x l / ↑‖x l‖ = x m / ↑‖x m‖ := by
  let x_abs := fun i => ‖x i‖
  have hx_abs_nonneg : ∀ i, 0 ≤ x_abs i := fun i => norm_nonneg _
  have hx_abs_ne_zero : x_abs ≠ 0 := by
    contrapose! hx_ne_zero; ext i; exact norm_eq_zero.mp (congr_fun hx_ne_zero i)
  have h_x_abs_pos : ∀ k, 0 < x_abs k :=
    eigenvector_is_positive_of_irreducible hA_irred h_x_abs_eig hx_abs_nonneg hx_abs_ne_zero
  intro k l m hAkl_pos hAkm_pos
  let z l' := (A k l' : ℂ) * x l'
  let s := ∑ l', z l'
  have hs_ne_zero : s ≠ 0 :=
    sum_s_ne_zero_of_triangle_eq hA_irred hA_nonneg h_triangle_eq h_x_abs_eig hx_ne_zero k
  have h_aligned_with_sum : ∀ l', z l' ≠ 0 → z l' / ↑‖z l'‖ = s / ↑‖s‖ := fun l' hz =>
    Complex.aligned_of_triangle_eq rfl (h_triangle_eq k) hs_ne_zero l' (by simp) hz
  have h_zl_ne_zero : z l ≠ 0 := by
    apply term_ne_zero_of_pos_entry hAkl_pos
    exact norm_pos_iff.mp (h_x_abs_pos l)
  have h_zm_ne_zero : z m ≠ 0 := by
    apply term_ne_zero_of_pos_entry hAkm_pos
    exact norm_pos_iff.mp (h_x_abs_pos m)
  have h_align_l := h_aligned_with_sum l h_zl_ne_zero
  have h_align_m := h_aligned_with_sum m h_zm_ne_zero
  have h_xl_aligned : x l / ↑‖x l‖ = z l / ↑‖z l‖ := by
    exact (Complex.aligned_of_mul_of_real_pos hAkl_pos rfl (norm_pos_iff.mp (h_x_abs_pos l))).symm
  have h_xm_aligned : x m / ↑‖x m‖ = z m / ↑‖z m‖ := by
    exact (Complex.aligned_of_mul_of_real_pos hAkm_pos rfl (norm_pos_iff.mp (h_x_abs_pos m))).symm
  rw [h_xl_aligned, h_xm_aligned, h_align_l, h_align_m]

lemma aligned_term_of_triangle_eq {ι : Type*} {s : Finset ι} {v : ι → ℂ}
    (h_sum : ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖)
    {j : ι} (h_j : j ∈ s) (h_vj_ne_zero : v j ≠ 0) :
    let sum := ∑ i ∈ s, v i
    v j / ↑‖v j‖ = sum / ↑‖sum‖ := by
  intro sum
  have h_sum_ne_zero : sum ≠ 0 := by
    intro h_sum_zero
    have h_norm_sum : ‖sum‖ = 0 := by rw [h_sum_zero, norm_zero]
    have h_sum_norms : ∑ i ∈ s, ‖v i‖ = 0 := by rw [← h_sum, h_norm_sum]
    have h_all_zero : ∀ i ∈ s, ‖v i‖ = 0 := by
      intro i hi
      have h_single_nonneg : 0 ≤ ‖v i‖ := norm_nonneg (v i)
      have h_sum_ge_single : ‖v i‖ ≤ ∑ j ∈ s, ‖v j‖ :=
        Finset.single_le_sum (fun _ _ => norm_nonneg _) hi
      rw [h_sum_norms] at h_sum_ge_single
      exact le_antisymm h_sum_ge_single h_single_nonneg
    have h_vj_zero : ‖v j‖ = 0 := h_all_zero j h_j
    exact h_vj_ne_zero (norm_eq_zero.mp h_vj_zero)
  have h_aligned := Complex.aligned_of_triangle_eq rfl h_sum h_sum_ne_zero j h_j h_vj_ne_zero
  exact h_aligned

/-- `|x|` is strictly positive for a primitive matrix eigenpair at the Perron root. -/
lemma eigenvector_norm_pos_of_primitive_and_norm_eq_perron_root
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} (_ : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)))
    (_ : ‖μ‖ = perronRoot_alt A)
    {x : n → ℂ} (hx_ne_zero : x ≠ 0) (_ : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot_alt A) • (fun i => ‖x i‖)) :
    ∀ i, 0 < ‖x i‖ := by
  have h_x_abs_ne_zero : (fun j => ‖x j‖) ≠ 0 := by
    contrapose! hx_ne_zero
    ext j
    exact norm_eq_zero.mp (congr_fun hx_ne_zero j)
  have h_x_abs_nonneg : ∀ j, 0 ≤ ‖x j‖ := fun j => norm_nonneg _
  have h_r_pos : 0 < perronRoot_alt A := by
    obtain ⟨r', _, hr'_pos, hv_pos, h_eig'⟩ := exists_positive_eigenvector_of_primitive hA_prim hA_nonneg
    exact hr'_pos.trans <| (eigenvalue_is_perron_root_of_positive_eigenvector
      (IsPrimitive.isIrreducible hA_prim) hA_nonneg hr'_pos hv_pos h_eig').symm
  exact eigenvector_of_primitive_is_positive hA_prim h_r_pos h_x_abs_eig h_x_abs_nonneg h_x_abs_ne_zero

omit [Nonempty n] in
/-- `‖((A ^ k) *ᵥ x) m‖ = r ^ k * ‖x m‖` when `‖μ‖ = r`. -/
lemma norm_matrix_power_vec_eq_perron_power_norm
    {A : Matrix n n ℝ} {μ : ℂ} {x : n → ℂ}
    (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_norm_eq_r : ‖μ‖ = perronRoot_alt A)
    (k : ℕ) (m : n) :
    ‖(((A ^ k).map (algebraMap ℝ ℂ)) *ᵥ x) m‖ = (perronRoot_alt A) ^ k * ‖x m‖ := by
  have h_k_power : ((A ^ k).map (algebraMap ℝ ℂ)) *ᵥ x = (μ ^ k) • x :=
    pow_eigenvector_of_eigenvector' hx_eig k
  have h_component : ((μ ^ k) • x) m = (μ ^ k) * x m := by simp [Pi.smul_apply]
  calc ‖(((A ^ k).map (algebraMap ℝ ℂ)) *ᵥ x) m‖
    = ‖((μ ^ k) • x) m‖ := by rw [h_k_power]
    _ = ‖(μ ^ k) * x m‖ := by rw [h_component]
    _ = ‖μ ^ k‖ * ‖x m‖ := by rw [norm_mul]
    _ = ‖μ‖ ^ k * ‖x m‖ := by rw [norm_pow]
    _ = (perronRoot_alt A) ^ k * ‖x m‖ := by rw [h_norm_eq_r]

omit [Nonempty n] in
/-- Triangle equality holds for a positive primitive matrix power. -/
lemma triangle_equality_for_primitive_power
    {A : Matrix n n ℝ} (_ : IsPrimitive A)
    {μ : ℂ} {x : n → ℂ}
    (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) = (perronRoot_alt A) • (fun i ↦ ‖x i‖))
    (h_norm_eq_r : ‖μ‖ = perronRoot_alt A)
    (m : n) (k : ℕ) (hAk_pos : ∀ i j, 0 < (A ^ k) i j) :
    ‖∑ l, ((A ^ k) m l : ℂ) * x l‖ = ∑ l, ‖((A ^ k) m l : ℂ) * x l‖ := by
  have h_left : ‖∑ l, ((A ^ k) m l : ℂ) * x l‖ = (perronRoot_alt A) ^ k * ‖x m‖ := by
    have h_eq : ‖∑ l, ((A ^ k) m l : ℂ) * x l‖ = ‖(((A ^ k).map (algebraMap ℝ ℂ)) *ᵥ x) m‖ := by
      simp_all only [coe_algebraMap]
      rfl
    rw [h_eq]
    exact norm_matrix_power_vec_eq_perron_power_norm hx_eig h_norm_eq_r k m
  have h_right : ∑ l, ‖((A ^ k) m l : ℂ) * x l‖ = (perronRoot_alt A) ^ k * ‖x m‖ :=
    sum_component_norms_eq_perron_power_norm h_x_abs_eig k m hAk_pos
  rw [h_left, h_right]

omit [Nonempty n] in
/-- A positive matrix entry aligns the phase of its term. -/
lemma component_phase_alignment
    {A : Matrix n n ℝ} {x : n → ℂ} {k : ℕ} {m i : n}
    (hAk_pos : 0 < (A ^ k) m i)
    (hx_abs_pos : 0 < ‖x i‖) :
    x i / ‖x i‖ = ((A ^ k) m i : ℂ) * x i / ‖((A ^ k) m i : ℂ) * x i‖ := by
  have h_ne : x i ≠ 0 := norm_pos_iff.mp hx_abs_pos
  exact (Complex.aligned_of_mul_of_real_pos hAk_pos rfl h_ne).symm

/-- All components of a primitive eigenvector share the same phase. -/
lemma entries_share_phase_of_primitive
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A)
    {μ : ℂ} {x : n → ℂ}
    (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) =
                     (perronRoot_alt A) • (fun i ↦ ‖x i‖))
    (h_norm_eq_r : ‖μ‖ = perronRoot_alt A)
    (hx_abs_pos : ∀ i, 0 < ‖x i‖) :
    ∀ i j : n, x i / ‖x i‖ = x j / ‖x j‖ := by
  classical
  obtain ⟨k, _hk_pos, hAk_pos⟩ := hA_prim.2
  intro i j
  let m := Classical.arbitrary n
  have tri := triangle_equality_for_primitive_power
              hA_prim hx_eig h_x_abs_eig h_norm_eq_r m k hAk_pos
  have align_i :=
    aligned_term_of_triangle_eq tri (Finset.mem_univ i)
      (term_ne_zero_of_pos_entry (hAk_pos m i) (norm_pos_iff.mp (hx_abs_pos i)))
  have align_j :=
    aligned_term_of_triangle_eq tri (Finset.mem_univ j)
      (term_ne_zero_of_pos_entry (hAk_pos m j) (norm_pos_iff.mp (hx_abs_pos j)))
  have phase_i := component_phase_alignment (hAk_pos m i) (hx_abs_pos i)
  have phase_j := component_phase_alignment (hAk_pos m j) (hx_abs_pos j)
  trans ((A ^ k) m i : ℂ) * x i / ‖((A ^ k) m i : ℂ) * x i‖
  · exact phase_i
  trans (∑ l, ((A ^ k) m l : ℂ) * x l) / ‖∑ l, ((A ^ k) m l : ℂ) * x l‖
  · exact align_i
  trans ((A ^ k) m j : ℂ) * x j / ‖((A ^ k) m j : ℂ) * x j‖
  · exact align_j.symm
  · exact phase_j.symm

lemma eigenvector_phase_aligned_of_primitive
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A) (_ : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} (h_norm_eq_r : ‖μ‖ = perronRoot_alt A)
    {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) = (perronRoot_alt A) • (fun i ↦ ‖x i‖))
    (hx_abs_pos : ∀ i, 0 < ‖x i‖) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ x = fun i ↦ c * ‖x i‖ := by
  let i₀ : n := Classical.arbitrary _
  let c   : ℂ := x i₀ / ‖x i₀‖
  have hc_norm : ‖c‖ = 1 := by
    have h_pos : 0 < ‖x i₀‖ := hx_abs_pos i₀
    simp [c, h_pos.ne']
  have h_same_phase : ∀ j : n, x j / ‖x j‖ = c := by
    intro j
    simp_rw [c]
    exact entries_share_phase_of_primitive hA_prim hx_eig h_x_abs_eig h_norm_eq_r hx_abs_pos j i₀
  refine ⟨c, hc_norm, ?_⟩
  funext j
  have hnorm_ne_zero : ‖x j‖ ≠ 0 := (hx_abs_pos j).ne'
  calc
    x j = (x j / ‖x j‖) * ‖x j‖ := by field_simp [hnorm_ne_zero]
    _ = c * ‖x j‖ := by rw [h_same_phase j]

omit [Nonempty n] [DecidableEq n] in
/--
If an eigenvector `x` is phase‐aligned, i.e. `x i = c * ‖x i‖` for every `i`,
then its eigenvalue `μ` is real and coincides with the eigenvalue `r`
of the real vector `‖x‖`.
-/
lemma eigenvalue_eq_of_phase_aligned
    {A : Matrix n n ℝ} {μ : ℂ} {c : ℂ} (hc_norm : ‖c‖ = 1)
    {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_phase : ∀ i, x i = c * ‖x i‖)
    {r : ℝ} (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) = r • (fun i ↦ ‖x i‖))
    {i : n} (hx_abs_pos_i : 0 < ‖x i‖) :
    μ = r := by
  have hc_ne_zero : c ≠ 0 := by
    intro hc
    have : (‖(0 : ℂ)‖ : ℝ) = 1 := by
      rw [hc, norm_zero] at hc_norm
      aesop
    norm_num at this
  set x_abs : n → ℂ := fun j ↦ (‖x j‖ : ℂ) with hx_abs_def
  have hx_repr : x = fun j ↦ c * x_abs j := by
    funext j
    rw [h_phase j, hx_abs_def]
  have h_factored :
      c • ((A.map (algebraMap ℝ ℂ)) *ᵥ x_abs) = c • (μ • x_abs) := by
    have : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x := hx_eig
    rw [hx_repr] at this
    have h_left : (A.map (algebraMap ℝ ℂ)) *ᵥ (fun j ↦ c * x_abs j) =
                  c • ((A.map (algebraMap ℝ ℂ)) *ᵥ x_abs) := by
      rw [← mulVec_smul]; rw [hx_abs_def]; simp; rfl
    have h_right : μ • (fun j ↦ c * x_abs j) = c • (μ • x_abs) := by
      ext j
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [h_left, h_right] at this
    exact this
  have h_cancelled :
      (A.map (algebraMap ℝ ℂ)) *ᵥ x_abs = μ • x_abs := by
    have := congrArg (fun v : n → ℂ ↦ c⁻¹ • v) h_factored
    simp only at this
    have h_left : c⁻¹ • (c • ((A.map (algebraMap ℝ ℂ)) *ᵥ x_abs)) = (A.map (algebraMap ℝ ℂ)) *ᵥ x_abs := by
      rw [smul_smul, inv_mul_cancel₀ hc_ne_zero, one_smul]
    have h_right : c⁻¹ • (c • (μ • x_abs)) = μ • x_abs := by
      rw [smul_smul, ← smul_smul]
      have : c⁻¹ * c * μ = μ := by
        rw [mul_assoc]; rw [propext (inv_mul_eq_iff_eq_mul₀ hc_ne_zero)]
      rw [propext (inv_smul_eq_iff₀ hc_ne_zero)]
    rw [h_left, h_right] at this
    exact this
  have h_real :
      (A *ᵥ fun j ↦ ‖x j‖) i = r * ‖x i‖ := by
    rw [h_x_abs_eig]
    simp only [Pi.smul_apply, smul_eq_mul]
  have h_real_C :
      ((A.map (algebraMap ℝ ℂ)) *ᵥ x_abs) i = (r : ℂ) * x_abs i := by
    have h_sum : (A.map (algebraMap ℝ ℂ)) *ᵥ x_abs =
                fun j ↦ ∑ k, (A j k : ℂ) * (‖x k‖ : ℂ) := by
      ext j
      rfl
    have h_real_sum : (A *ᵥ fun j ↦ ‖x j‖) i =
                     ∑ k, A i k * ‖x k‖ := by
      rfl
    calc ((A.map (algebraMap ℝ ℂ)) *ᵥ x_abs) i
        = ∑ k, (A i k : ℂ) * (‖x k‖ : ℂ) := by rw [h_sum]
      _ = (∑ k, A i k * ‖x k‖ : ℂ) := by
          simp only
      _ = ((A *ᵥ fun j ↦ ‖x j‖) i : ℂ) := by
          rw [h_real_sum]; simp
      _ = (r * ‖x i‖ : ℂ) := by rw [h_real]; simp
      _ = (r : ℂ) * (‖x i‖ : ℂ) := by simp only
      _ = (r : ℂ) * x_abs i := by rw [hx_abs_def]
  have h_key : (r : ℂ) * x_abs i = μ * x_abs i := by
    rw [← h_real_C]
    have := congr_fun h_cancelled i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact this
  have h_norm_ne_zero : x_abs i ≠ 0 := by
    rw [hx_abs_def]
    exact Complex.ofReal_ne_zero.mpr hx_abs_pos_i.ne'
  have h_final : (r : ℂ) = μ := by
    apply (mul_right_cancel₀ h_norm_ne_zero)
    exact h_key
  exact h_final.symm

theorem spectral_dominance_of_primitive {A : Matrix n n ℝ} (hA_prim : IsPrimitive A)
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {μ : ℂ} (h_is_eigenvalue : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)))
    (h_norm_eq_r : ‖μ‖ = perronRoot_alt A) : μ = perronRoot_alt A := by
  let B := A.map (algebraMap ℝ ℂ)
  obtain ⟨x, hx_ne_zero, hx_eig⟩ := Module.End.exists_eigenvector_of_mem_spectrum <| by
    rwa [spectrum_toLin']
  have h_subinv := by
    simpa [h_norm_eq_r] using eigenvalue_abs_subinvariant hA_nonneg hx_eig
  have h_x_abs_eig := subinvariant_equality_implies_eigenvector
    (IsPrimitive.isIrreducible hA_prim) hA_nonneg (fun _ => norm_nonneg _) (by
      intro h; exact hx_ne_zero <| funext fun i => norm_eq_zero.mp (congrFun h i))
    h_subinv
  have hx_abs_pos := eigenvector_norm_pos_of_primitive_and_norm_eq_perron_root hA_prim hA_nonneg
    h_is_eigenvalue h_norm_eq_r hx_ne_zero hx_eig h_x_abs_eig
  obtain ⟨c, hc_norm, h_phase⟩ := eigenvector_phase_aligned_of_primitive hA_prim hA_nonneg h_norm_eq_r
    hx_eig h_x_abs_eig hx_abs_pos
  exact eigenvalue_eq_of_phase_aligned hc_norm hx_eig (fun i => congrFun h_phase i) h_x_abs_eig
    (hx_abs_pos (Classical.arbitrary n))

/--
Spectral Dominance for Primitive Matrices
(Seneta 1.1 (c)).
If `A` is primitive with Perron root `r`, every eigenvalue `μ ≠ r`
satisfies `‖μ‖ < r`.
-/
theorem spectral_dominance_of_primitive' (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (μ : ℂ) (h_is_eigenvalue : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)))
    (h_ne_perron : μ ≠ perronRoot_alt A) : ‖μ‖ < perronRoot_alt A := by
  rcases lt_or_eq_of_le <| eigenvalue_abs_le_perron_root (IsPrimitive.isIrreducible hA_prim)
    hA_nonneg h_is_eigenvalue with h_lt | h_eq
  · exact h_lt
  · exact (h_ne_perron <| spectral_dominance_of_primitive hA_prim hA_nonneg h_is_eigenvalue h_eq).elim

end Matrix
