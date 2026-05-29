/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
public import Mathlib.Analysis.CStarAlgebra.PerronFrobenius

/-!
# Spectral dominance for irreducible matrices

Sub-invariance, Perron root bounds, and absolute eigenvalue estimates for irreducible
non-negative real matrices.

## Main results

* `eigenvalue_abs_subinvariant`: a complex eigenpair yields a sub-invariant absolute-value vector.
* `eigenvalue_abs_le_perron_root`: every eigenvalue has modulus at most the Perron root.
* `perron_root_is_eigenvalue` and `perron_root_is_spectral_radius`: the Perron root is a real
  eigenvalue and equals the spectral radius.

## Implementation notes

Complex eigenvectors are treated through alignment and norm lemmas from
`Mathlib.Analysis.CStarAlgebra.PerronFrobenius`.

## References

* [E. Seneta, *Non-negative Matrices and Markov Chains*][seneta2006]

## Tags

Perron–Frobenius theorem, irreducible matrix, spectral radius, Collatz–Wielandt
-/

@[expose] public section

namespace Matrix
open CollatzWielandt

open Quiver
open Matrix Classical Complex

variable {n : Type*} {A : Matrix n n ℝ}

/-- If a property `P` holds for at least one vertex `i₀` and propagates along the edges
of an irreducible matrix's graph (`P i ∧ A i j > 0 → P j`), then `P` holds for all vertices. -/
lemma IsIrreducible.eq_univ_of_propagate (hA_irred : A.IsIrreducible) (P : n → Prop)
  (h₀ : ∃ i₀, P i₀) (hstep : ∀ i j, P i → 0 < A i j → P j) :
  ∀ i, P i := by
  by_contra hP
  push Not at hP
  set S : Set n := {i | P i}
  have hS' : S ≠ Set.univ := by
    intro hSu
    obtain ⟨j, hj⟩ := hP
    exact hj (by
      have : j ∈ S := by simpa [hSu.symm] using (Set.mem_univ j)
      simpa [S] using this)
  obtain ⟨i, hiS, j, hjS, hij⟩ :=
    Irreducible.exists_edge_out (A := A) hA_irred S h₀ hS'
  exact hjS (by simpa [S] using (hstep i j (by simpa [S] using hiS) hij))

variable {n : Type*} [Fintype n]
variable {A : Matrix n n ℝ}

/-- For an irreducible, non-negative matrix `A`, if `v` is an eigenvector for an eigenvalue `μ`,
then the vector `w` of absolute values of `v` satisfies the inequality `|μ| • w ≤ A *ᵥ w`.
This is a key step in the Perron-Frobenius theorem. -/
lemma abs_eigenvector_inequality (hA_nonneg : ∀ i j, 0 ≤ A i j)
  {μ : ℝ} {v : n → ℝ} (h_eig : A *ᵥ v = μ • v) :
  let w := fun i ↦ |v i|; |μ| • w ≤ A *ᵥ w := by
  intro w i
  calc (|μ| • w) i = |μ| * |v i| := ?_
    _ = |μ * v i| := ?_
    _ = |(μ • v) i| := ?_
    _ = |(A *ᵥ v) i| := ?_
    _ = |∑ j, A i j * v j| := ?_
    _ ≤ ∑ j, |A i j * v j| := ?_
    _ = ∑ j, (A i j) * |v j| := ?_
    _ = (A *ᵥ w) i := ?_
  · simp [w, Pi.smul_apply, smul_eq_mul]
  · simp
  · simp [Pi.smul_apply, smul_eq_mul]
  · simp [h_eig, Pi.smul_apply, smul_eq_mul]
  · simp [mulVec_apply]
  · simpa using
    (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j => A i j * v j))
  ·classical
   refine Finset.sum_congr rfl ?_
   intro j _
   simp [abs_mul, abs_of_nonneg (hA_nonneg i j)]
  · simp [w, mulVec_apply]

/--
If the triangle equality holds for the complex eigenvector equation `A * x = lam * x`,
then the vector of norms `‖x‖` is a real eigenvector of `A` with eigenvalue `‖lam‖`.
-/
lemma norm_eigenvector_is_eigenvector_of_triangle_eq (hA_nonneg : ∀ i j, 0 ≤ A i j)
  {lam : ℂ} {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = lam • x)
  (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖) :
  A *ᵥ (fun i => ‖x i‖) = (‖lam‖ : ℝ) • (fun i => ‖x i‖) := by
  funext i
  calc (A *ᵥ fun i => ‖x i‖) i = ∑ j, A i j * ‖x j‖ := ?_
       _   = ∑ j, ‖(A i j : ℂ)‖ * ‖x j‖ := ?_
       _   = ∑ j, ‖(A i j : ℂ) * x j‖ := ?_
       _   = ‖∑ j, (A i j : ℂ) * x j‖ := ?_
       _   = ‖((A.map (algebraMap ℝ ℂ)) *ᵥ x) i‖ := ?_
       _   = ‖(lam • x) i‖ := ?_
       _   = ‖lam * x i‖ := ?_
       _   = ‖lam‖ * ‖x i‖ := ?_
       _   = ((‖lam‖ : ℝ) • fun i => ‖x i‖) i := ?_
  · simp [mulVec_apply]
  · simp_rw [Complex.norm_ofReal, abs_of_nonneg (hA_nonneg _ _)]
  · simp_rw [norm_mul]
  · exact (h_triangle_eq i).symm
  · simp; rfl
  · rw [hx_eig]
  · rw [Pi.smul_apply]; rfl
  · rw [norm_mul]
  · simp [smul_eq_mul]

/--
If equality holds in the triangle inequality for `∑ z_j`, then all non-zero `z_j`
are aligned with the sum.
-/
lemma aligned_of_all_nonneg_re_im {i : n} {x : n → ℂ}
    (h_sum_eq : ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖) :
    ∀ j, (A i j : ℂ) * x j ≠ 0 →
      ∃ c : ℝ, 0 ≤ c ∧ (A i j : ℂ) * x j = c • ∑ k, (A i k : ℂ) * x k := by
  let z : n → ℂ := fun j => (A i j : ℂ) * x j
  let s : ℂ     := ∑ j, z j
  have h_z_sum : ‖s‖ = ∑ j, ‖z j‖ := by
    simpa [z, s] using h_sum_eq
  intro j hz_ne_zero
  have hs_ne_zero : s ≠ 0 := by
    intro hs
    have hsum : (∑ k, ‖z k‖) = 0 := by
      calc
        (∑ k, ‖z k‖) = ‖s‖ := by simpa using h_z_sum.symm
        _ = 0 := by simpa [hs] using (norm_zero : ‖(0 : ℂ)‖ = 0)
    have hzj_norm0 : ‖z j‖ = 0 := by
      have hnonneg : ∀ k, 0 ≤ ‖z k‖ := fun _ => norm_nonneg _
      exact
        (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun k _ => hnonneg k)).1 hsum
          j (by simp)
    exact hz_ne_zero (by
      have : z j = 0 := norm_eq_zero.mp hzj_norm0
      simpa [z] using this)
  have h_align :=
    Complex.each_term_is_nonneg_real_multiple_of_sum_of_triangle_eq (s := Finset.univ)
      (v := z) (u := s) (by simp [s]) (by simpa [s] using h_z_sum) hs_ne_zero
  rcases h_align j (by simp) with ⟨c, hc_nonneg, hcz⟩
  have hcz' : z j = (c : ℂ) * s := hcz
  have hcz_smul : z j = c • s := by simpa [smul_eq_mul] using hcz'
  refine ⟨c, hc_nonneg, ?_⟩
  simpa [z, s] using hcz_smul

/-- For a non-negative matrix `A`, if the row sums are all
equal to `lambda`, then `lambda` is an eigenvalue with the all-ones vector as its eigenvector. -/
lemma row_sum_eigenvalue {lambda : ℝ} (h_row_sums : ∀ i, ∑ j, A i j = lambda) :
    A *ᵥ (1 : n → ℝ) = lambda • (1 : n → ℝ) := by
  ext i; simp [mulVec_apply, h_row_sums i, smul_eq_mul]

/-- If the dot product of a non-negative vector `v` and a strictly positive vector `w` is zero,
    then `v` must be the zero vector. -/
lemma eq_zero_of_dotProduct_eq_zero_of_nonneg_of_pos {v w : n → ℝ}
    (hv_nonneg : ∀ i, 0 ≤ v i) (hw_pos : ∀ i, 0 < w i) (h_dot : v ⬝ᵥ w = 0) : v = 0 := by
  rw [dotProduct] at h_dot
  have h_terms_nonneg : ∀ i, 0 ≤ v i * w i := by
    intro i
    exact mul_nonneg (hv_nonneg i) (hw_pos i).le
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h_terms_nonneg i)] at h_dot
  funext i
  have hi_zero : v i * w i = 0 := h_dot i (Finset.mem_univ i)
  rw [mul_eq_zero] at hi_zero
  exact hi_zero.resolve_right (hw_pos i).ne'

/--
If a scalar `μ` is in the spectrum of a complex matrix `A`, then there exists a non-zero
eigenvector `x` for that eigenvalue.
-/
theorem exists_eigenvector_of_mem_spectrum {A' : Matrix n n ℝ} {μ : ℂ}
    (h : μ ∈ spectrum ℂ (A'.map (algebraMap ℝ ℂ))) :
    ∃ x, x ≠ 0 ∧ (A'.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x := by
  have h_spec : μ ∈ spectrum ℂ (toLin' (A'.map (algebraMap ℝ ℂ))) := by
    rwa [spectrum_toLin']
  obtain ⟨x, hx_ne_zero, hx_eig⟩ := Module.End.exists_eigenvector_of_mem_spectrum h_spec
  refine ⟨x, hx_ne_zero, by aesop⟩

/- If `v` is an eigenvector of `A` with eigenvalue `r`, then `v` is an eigenvector of `A^m`
with eigenvalue `r^m`.
-/
lemma pow_eigenvector_of_eigenvector {R : Type*} [DecidableEq n] [CommSemiring R]
  {A : Matrix n n R} {r : R} {v : n → R} (h_eig : A *ᵥ v = r • v) (m : ℕ) :
  (A ^ m) *ᵥ v = (r ^ m) • v := by
  induction m with
  | zero => simp [pow_zero]
  | succ m ih =>
    calc (A ^ m.succ) *ᵥ v = (A ^ m * A) *ᵥ v := by simp [pow_succ]
      _ = A ^ m *ᵥ (A *ᵥ v) := by rw [Matrix.mulVec_mulVec]
      _ = A ^ m *ᵥ (r • v) := by rw [h_eig]
      _ = r • (A ^ m *ᵥ v) := by rw [mulVec_smul]
      _ = r • (r ^ m • v) := by rw [ih]
      _ = r ^ (m + 1) • v := by simp [pow_succ', smul_smul]

lemma sum_component_norms_eq_perron_power_norm [DecidableEq n] -- [CommSemiring R]
      {A : Matrix n n ℝ} {x : n → ℂ}
      (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) = (perronRoot_alt A) • (fun i ↦ ‖x i‖))
      (k : ℕ) (m : n) (hAk_pos : ∀ i j, 0 < (A ^ k) i j) :
      ∑ l, ‖((A ^ k) m l : ℂ) * x l‖ = (perronRoot_alt A) ^ k * ‖x m‖ := by
  have h_pow_eig : (A ^ k) *ᵥ (fun i ↦ ‖x i‖) = (perronRoot_alt A) ^ k • (fun i ↦ ‖x i‖) :=
  pow_eigenvector_of_eigenvector h_x_abs_eig k
  calc ∑ l, ‖((A ^ k) m l : ℂ) * x l‖ = ∑ l, |(A ^ k) m l| * ‖x l‖ := ?_
    _ = ∑ l, (A ^ k) m l * ‖x l‖ := ?_
    _ = ((A ^ k) *ᵥ (fun i ↦ ‖x i‖)) m := ?_
    _ = ((perronRoot_alt A) ^ k • (fun i ↦ ‖x i‖)) m := ?_
    _ = (perronRoot_alt A) ^ k * ‖x m‖ := ?_
  · simp_rw [norm_mul, Complex.norm_ofReal]
  · simp_rw [abs_of_pos (hAk_pos m _)]
  · simp [mulVec_apply]
  · simpa using congrArg (fun v => v m) h_pow_eig
  · simp [Pi.smul_apply, smul_eq_mul]

/--
If `x` is a complex eigenvector of a real matrix `A` with eigenvalue `μ`, then `x` is an
eigenvector of `A^m` with eigenvalue `μ^m`. This is the complex version of the lemma.
-/
lemma pow_eigenvector_of_eigenvector' [DecidableEq n] {A : Matrix n n ℝ} {μ : ℂ} {x : n → ℂ}
    (h_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x) (m : ℕ) :
    ((A ^ m).map (algebraMap ℝ ℂ)) *ᵥ x = (μ ^ m) • x := by
  induction m with
  | zero =>
    simp [pow_zero, Matrix.map_one, one_mulVec, one_smul]
  | succ m ih =>
    calc ((A ^ (m + 1)).map (algebraMap ℝ ℂ)) *ᵥ x
        = ((A * A ^ m).map (algebraMap ℝ ℂ)) *ᵥ x := by rw [pow_succ']
      _ = ((A.map (algebraMap ℝ ℂ)) * ((A ^ m).map (algebraMap ℝ ℂ))) *ᵥ x := by rw [Matrix.map_mul]
      _ = (A.map (algebraMap ℝ ℂ)) *ᵥ (((A ^ m).map (algebraMap ℝ ℂ)) *ᵥ x) := by rw [Matrix.mulVec_mulVec]
      _ = (A.map (algebraMap ℝ ℂ)) *ᵥ ((μ ^ m) • x) := by rw [ih]
      _ = (μ ^ m) • ((A.map (algebraMap ℝ ℂ)) *ᵥ x) := by rw [mulVec_smul]
      _ = (μ ^ m) • (μ • x) := by rw [h_eig]
      _ = ((μ ^ m) * μ) • x := by rw [smul_smul]
      _ = (μ ^ (m + 1)) • x := by simp [pow_succ', mul_comm]

/--
For an eigenvalue μ of a nonnegative matrix A with eigenvector x,
the absolute value |μ| satisfies the sub-invariant relation: |μ|⋅|x| ≤ A⋅|x|.
This is the fundamental inequality in spectral analysis of nonnegative matrices.
-/
theorem eigenvalue_abs_subinvariant
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x) :
    (‖μ‖ : ℝ) • (fun i => ‖x i‖) ≤ A *ᵥ (fun i => ‖x i‖) := by
  intro i
  calc
    (‖μ‖ : ℝ) * ‖x i‖ = ‖μ * x i‖ := by rw [← norm_mul]
    _ = ‖(μ • x) i‖ := by simp [Pi.smul_apply]
    _ = ‖((A.map (algebraMap ℝ ℂ)) *ᵥ x) i‖ := by rw [← hx_eig]
    _ = ‖∑ j, (A i j : ℂ) * x j‖ := by simp; rfl
    _ ≤ ∑ j, ‖(A i j : ℂ) * x j‖ := by apply norm_sum_le
    _ = ∑ j, A i j * ‖x j‖ := by
      simp only [Complex.norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hA_nonneg _ _)]
    _ = (A *ᵥ fun i => ‖x i‖) i := by simp [mulVec_apply]

variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
variable {A : Matrix n n ℝ}

/--
Under the conditions of the main theorem, the eigenvalue `lamda` must be non-zero.
-/
lemma eigenvalue_ne_zero_of_irreducible
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    {lam : ℂ} {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (‖lam‖ : ℝ) • (fun i => ‖x i‖)) :
    lam ≠ 0 := by
  intro h_lam_zero
  have h_norm_lam_zero : ‖lam‖ = 0 := by rwa [norm_eq_zero]
  have h_eig_zero_smul : A *ᵥ (fun i => ‖x i‖) = (0 : ℝ) • (fun i => ‖x i‖) := by
    rw [h_norm_lam_zero] at h_x_abs_eig
    exact h_x_abs_eig
  have h_eig_zero : A *ᵥ (fun i => ‖x i‖) = 0 := by
    simpa [zero_smul] using h_eig_zero_smul
  have h_x_abs_nonneg : ∀ i, 0 ≤ ‖x i‖ := fun i => norm_nonneg _
  have h_x_abs_ne_zero : (fun i => ‖x i‖) ≠ 0 := by
    contrapose! hx_ne_zero
    ext i
    exact norm_eq_zero.mp (congr_fun hx_ne_zero i)
  have h_x_abs_pos : ∀ i, 0 < ‖x i‖ :=
    eigenvector_is_positive_of_irreducible hA_irred h_eig_zero_smul h_x_abs_nonneg h_x_abs_ne_zero
  obtain ⟨i, j, hAij_pos⟩ := Matrix.Irreducible.exists_pos_entry (A := A) hA_irred
  have h_sum : (A *ᵥ (fun k => ‖x k‖)) i = 0 := by rw [h_eig_zero]; rfl
  rw [mulVec_apply] at h_sum
  have h_sum_pos : 0 < ∑ k, A i k * ‖x k‖ := by
    apply sum_pos_of_mem
    · intro k _
      exact mul_nonneg (hA_irred.nonneg i k) (h_x_abs_nonneg k)
    · exact Finset.mem_univ j
    · exact mul_pos hAij_pos (h_x_abs_pos j)
  exact h_sum_pos.ne' h_sum

theorem eigenvalue_is_perron_root_of_positive_eigenvector {r : ℝ} {v : n → ℝ}
    (_ : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) (hr_pos : 0 < r) (hv_pos : ∀ i, 0 < v i)
    (h_eig : A *ᵥ v = r • v) : r = perronRoot_alt A := by
  have h_ge : perronRoot_alt A ≤ r :=
    eigenvalue_is_ub_of_positive_eigenvector hA_nonneg hr_pos hv_pos h_eig
  have h_le : r ≤ perronRoot_alt A := by
    rw [← eq_eigenvalue_of_positive_eigenvector hv_pos h_eig]
    have hv_nonneg : ∀ i, 0 ≤ v i := fun i => (hv_pos i).le
    have hv_ne_zero : v ≠ 0 := by
      intro h0
      have : 0 < v (Classical.arbitrary n) := hv_pos (Classical.arbitrary n)
      rw [h0] at this
      exact lt_irrefl 0 this
    apply le_csSup (CollatzWielandt.bddAbove A hA_nonneg)
    exact Set.mem_image_of_mem _ ⟨hv_nonneg, hv_ne_zero⟩
  exact le_antisymm h_le h_ge

theorem perronRoot_transpose_eq (A : Matrix n n ℝ) (hA_irred : A.IsIrreducible) :
    perronRoot_alt A = perronRoot_alt Aᵀ := by
  obtain ⟨r, v, hr_pos, hv_pos, hv_eig⟩ := exists_positive_eigenvector_of_irreducible hA_irred
  have hr_eq_perron : r = perronRoot_alt A := eigenvalue_is_perron_root_of_positive_eigenvector
      hA_irred hA_irred.nonneg hr_pos hv_pos hv_eig
  obtain ⟨r', u, hr'_pos, hu_pos, hu_eig_T⟩ := exists_positive_eigenvector_of_irreducible
      (Matrix.IsIrreducible.transpose hA_irred)
  have hr'_eq_perron : r' = perronRoot_alt Aᵀ :=
    eigenvalue_is_perron_root_of_positive_eigenvector (Matrix.IsIrreducible.transpose hA_irred)
      (fun i j => hA_irred.nonneg j i) hr'_pos hu_pos hu_eig_T
  have hu_eig_left : u ᵥ* A = r' • u := by simpa [vecMul_eq_mulVec_transpose] using hu_eig_T
  have hv_nonneg : ∀ i, 0 ≤ v i := fun i ↦ (hv_pos i).le
  have hv_ne_zero : v ≠ 0 := by
    intro hv
    exact (ne_of_gt (hv_pos (Classical.arbitrary n))) (by simp [hv])
  have h_dot_pos : 0 < u ⬝ᵥ v := dotProduct_pos_of_pos_of_nonneg_ne_zero hu_pos hv_nonneg hv_ne_zero
  have h1 : u ⬝ᵥ (A *ᵥ v) = r * (u ⬝ᵥ v) := by simp [hv_eig, dotProduct_smul, smul_eq_mul]
  have h2 : (u ᵥ* A) ⬝ᵥ v = r' * (u ⬝ᵥ v) := by
    simp [hu_eig_left, smul_dotProduct, smul_eq_mul]
  have h_eq : r * (u ⬝ᵥ v) = r' * (u ⬝ᵥ v) := by
    calc
      r * (u ⬝ᵥ v) = u ⬝ᵥ (A *ᵥ v) := (h1.symm)
      _             = (u ᵥ* A) ⬝ᵥ v := by
                        simpa using dotProduct_mulVec u A v
      _             = r' * (u ⬝ᵥ v) := h2
  have hr_eq_r' : r = r' := by
    subst hr_eq_perron hr'_eq_perron
    simp_all only [ne_eq, dotProduct_smul, smul_eq_mul, smul_dotProduct, mul_eq_mul_right_iff]
    cases h_eq with
    | inl h => simp_all only
    | inr h_1 => simp_all only [lt_self_iff_false]
  calc
    perronRoot_alt A   = r   := by symm; simpa using hr_eq_perron
    _                  = r'  := hr_eq_r'
    _                  = perronRoot_alt Aᵀ := hr'_eq_perron

/--
If for a non-negative, irreducible matrix `A`, there exists
a non-negative, non-zero vector `y` and a positive scalar `s` such that `A *ᵥ y ≤ s • y`,
then the Perron root of `A` is at most `s`.
-/
lemma perron_root_le_of_subinvariant (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {s : ℝ} (_ : 0 < s) {y : n → ℝ} (hy_nonneg : ∀ i, 0 ≤ y i) (hy_ne_zero : y ≠ 0)
    (h_subinv : A *ᵥ y ≤ s • y) : perronRoot_alt A ≤ s := by
  let A_T := Aᵀ
  have hAT_irred : A_T.IsIrreducible := Matrix.IsIrreducible.transpose hA_irred
  have hAT_nonneg : ∀ i j, 0 ≤ A_T i j := by simp [A_T]; exact fun i j ↦ hA_nonneg j i
  obtain ⟨r, u, hr_pos, hu_pos, hu_eig⟩ :=
    exists_positive_eigenvector_of_irreducible hAT_irred
  have h_r_eq_perron : r = perronRoot_alt A := by
    calc
      r = perronRoot_alt Aᵀ := eigenvalue_is_perron_root_of_positive_eigenvector
        hAT_irred hAT_nonneg hr_pos hu_pos hu_eig
      _ = perronRoot_alt A  := by rw [← perronRoot_transpose_eq A hA_irred]
  have h_u_left_eig : u ᵥ* A = r • u := by
    rwa [vecMul_eq_mulVec_transpose]
  have h_dot_le : u ⬝ᵥ (A *ᵥ y) ≤ u ⬝ᵥ (s • y) :=
    dotProduct_le_dotProduct_of_nonneg_left' (fun i => (hu_pos i).le) h_subinv
  rw [dotProduct_mulVec, h_u_left_eig, dotProduct_smul_left, dotProduct_smul] at h_dot_le
  have h_dot_pos : 0 < u ⬝ᵥ y := dotProduct_pos_of_pos_of_nonneg_ne_zero hu_pos hy_nonneg hy_ne_zero
  have h_r_le_s : r ≤ s := by
    have h_mul_le : r * (u ⬝ᵥ y) ≤ s * (u ⬝ᵥ y) := h_dot_le
    exact le_of_mul_le_mul_right h_mul_le h_dot_pos
  rwa [h_r_eq_perron] at h_r_le_s

/-- If equality holds in the subinvariance inequality `r • v ≤ A *ᵥ v` for the Perron root `r`,
    then `v` must be an eigenvector. -/
lemma subinvariant_equality_implies_eigenvector
    (hA_irred : A.IsIrreducible)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {v : n → ℝ} (_ : ∀ i, 0 ≤ v i) (_ : v ≠ 0)
    (h_subinv : perronRoot_alt A • v ≤ A *ᵥ v) :
    A *ᵥ v = perronRoot_alt A • v := by
  let r := perronRoot_alt A
  let z := A *ᵥ v - r • v
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_nonneg, z]
    exact h_subinv i
  by_cases hz_zero : z = 0
  · simp only [sub_eq_zero, z] at hz_zero
    exact hz_zero
  · obtain ⟨r_T, u, hr_T_pos, hu_pos, hu_eig⟩ :=
      exists_positive_eigenvector_of_irreducible (Matrix.IsIrreducible.transpose hA_irred)
    have h_u_left_eig : u ᵥ* A = r_T • u := by
      rwa [vecMul_eq_mulVec_transpose]
    have h_rT_eq_r : r_T = r := by
      calc
        r_T = perronRoot_alt Aᵀ :=
          eigenvalue_is_perron_root_of_positive_eigenvector
            (Matrix.IsIrreducible.transpose hA_irred)
            (fun i j ↦ hA_nonneg j i) hr_T_pos hu_pos hu_eig
        _   = perronRoot_alt A   := (perronRoot_transpose_eq A hA_irred).symm
        _   = r                 := rfl
    have h_dot_z : u ⬝ᵥ z = 0 := by
      rw [dotProduct_sub, dotProduct_mulVec, h_u_left_eig, h_rT_eq_r, dotProduct_smul_left,
        dotProduct_smul, smul_eq_mul, sub_self]
    have h_z_is_zero' := eq_zero_of_dotProduct_eq_zero_of_nonneg_of_pos hz_nonneg hu_pos
      (by rw [dotProduct_comm]; exact h_dot_z)
    contradiction

/--
The value of the Collatz-Wielandt function for any non-negative, non-zero vector
is less than or equal to the Perron root.
-/
lemma collatzWielandtFn_le_perronRoot_alt (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    collatzWielandtFn A x ≤ perronRoot_alt A :=
  le_csSup (CollatzWielandt.bddAbove A hA_nonneg) <|
    Set.mem_image_of_mem _ ⟨hx_nonneg, hx_ne_zero⟩

/--
Any eigenvalue μ of a nonnegative irreducible matrix A has absolute value
at most equal to the Perron root.
-/
theorem eigenvalue_abs_le_perron_root
    {A : Matrix n n ℝ} (_ : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} (h_is_eigenvalue : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) :
    ‖μ‖ ≤ perronRoot_alt A := by
  let B := A.map (algebraMap ℝ ℂ)
  have h_spec : μ ∈ spectrum ℂ (toLin' B) := by rwa [spectrum_toLin']
  rcases Module.End.exists_eigenvector_of_mem_spectrum h_spec with ⟨x, hx_ne_zero, hx_eig_lin⟩
  have hx_eig : B *ᵥ x = μ • x := by rwa [toLin'_apply] at hx_eig_lin
  let x_abs := fun i => ‖x i‖
  have hx_abs_nonneg : ∀ i, 0 ≤ x_abs i := fun i => norm_nonneg _
  have hx_abs_ne_zero : x_abs ≠ 0 := by
    contrapose! hx_ne_zero
    ext i
    exact norm_eq_zero.mp (congr_fun hx_ne_zero i)
  have h_subinv : (‖μ‖ : ℝ) • x_abs ≤ A *ᵥ x_abs :=
    eigenvalue_abs_subinvariant hA_nonneg hx_eig
  have h_le_collatz : (‖μ‖ : ℝ) ≤ collatzWielandtFn A x_abs :=
    le_of_subinvariant hA_nonneg hx_abs_nonneg hx_abs_ne_zero h_subinv
  have h_le_perron : collatzWielandtFn A x_abs ≤ perronRoot_alt A :=
    collatzWielandtFn_le_perronRoot_alt hA_nonneg hx_abs_nonneg hx_abs_ne_zero
  exact le_trans h_le_collatz h_le_perron

/-- For an irreducible, non-negative matrix, the Perron root (defined as the Collatz-Wielandt
supremum) is equal to the unique positive eigenvalue `r` from the existence theorem. -/
lemma perron_root_eq_positive_eigenvalue (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    ∃ r v, 0 < r ∧ (∀ i, 0 < v i) ∧ A *ᵥ v = r • v ∧ perronRoot_alt A = r := by
  obtain ⟨r, v, hr_pos, hv_pos, h_eig⟩ := exists_positive_eigenvector_of_irreducible hA_irred
  exact ⟨r, v, hr_pos, hv_pos, h_eig, le_antisymm
    (eigenvalue_is_ub_of_positive_eigenvector hA_nonneg hr_pos hv_pos h_eig)
    (eigenvalue_le_perron_root_of_positive_eigenvector hA_nonneg hr_pos hv_pos h_eig)⟩

/--
If a matrix `A` has an eigenvector `v` for an eigenvalue `μ`, then `μ` is in the spectrum of `A`.
This is a direct consequence of the definition of an eigenvalue and the spectrum.
-/
lemma mem_spectrum_of_hasEigenvector {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {f : V →ₗ[K] V} {μ : K} {v : V} (h : Module.End.HasEigenvector f μ v) :
    μ ∈ spectrum K f := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  exact Module.End.hasEigenvalue_of_hasEigenvector h

lemma mem_spectrum_of_eigenvalue
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n K} {μ : K} {v : n → K}
    (hv_ne_zero : v ≠ 0) (h_eig : A *ᵥ v = μ • v) :
    μ ∈ spectrum K A := by
  let f := toLin' A
  have h_eig_f : f v = μ • v := by
    simpa [toLin'_apply, f] using h_eig
  have h_has_eigvec : Module.End.HasEigenvector f μ v :=
    ⟨by
      rwa [← Module.End.mem_eigenspace_iff] at h_eig_f,
      hv_ne_zero⟩
  have h_mem_f : μ ∈ spectrum K f :=
    mem_spectrum_of_hasEigenvector h_has_eigvec
  simpa [f, spectrum_toLin'] using h_mem_f

/-- The Perron root of an irreducible, non-negative matrix is an eigenvalue. -/
theorem perron_root_is_eigenvalue (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    perronRoot_alt A ∈ spectrum ℝ A := by
  obtain ⟨r', v, _, hv_pos, h_eig, h_eq⟩ := perron_root_eq_positive_eigenvalue hA_irred hA_nonneg
  have hv_ne_0 : v ≠ 0 := fun h => by
    have := hv_pos (Classical.arbitrary n)
    rw [h] at this
    exact lt_irrefl 0 this
  rw [h_eq]
  exact mem_spectrum_of_eigenvalue hv_ne_0 h_eig

/-- Perron-Frobenius Theorem (Dominance): The Perron root of an irreducible, non-negative
matrix is an eigenvalue and its modulus is greater than or equal to the modulus of any other
eigenvalue. It is the spectral radius. -/
theorem perron_root_is_spectral_radius (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    let r := perronRoot_alt A
    r ∈ spectrum ℝ A ∧ ∀ μ ∈ spectrum ℝ A, |μ| ≤ r := by
  constructor
  · exact perron_root_is_eigenvalue hA_irred hA_nonneg
  · intro μ hμ
    have hμ_complex : (μ : ℂ) ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := by
      have hμ_lin : μ ∈ spectrum ℝ (toLin' A) := by
        simpa [spectrum_toLin'] using hμ
      obtain ⟨v, hv_ne_zero, hv_eig⟩ :=
        Module.End.exists_eigenvector_of_mem_spectrum hμ_lin
      let v_complex : n → ℂ := fun i => (v i : ℂ)
      have hvc_ne_zero : v_complex ≠ 0 := by
        intro h
        have : v = 0 := by
          ext i
          have : (v i : ℂ) = 0 := congr_fun h i
          exact_mod_cast this
        exact hv_ne_zero this
      have hv_eig_vec : A *ᵥ v = μ • v := by
        simpa [toLin'_apply] using hv_eig
      have hvc_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ v_complex = (μ : ℂ) • v_complex := by
        ext i
        have h_eq : (A *ᵥ v) i = μ * v i := by
          simpa using congr_fun hv_eig_vec i
        simpa [v_complex, smul_eq_mul, mulVec, dotProduct, map_apply] using
          congrArg (fun x : ℝ => (x : ℂ)) h_eq
      exact mem_spectrum_of_eigenvalue hvc_ne_zero hvc_eig
    have h_bound := eigenvalue_abs_le_perron_root hA_irred hA_nonneg hμ_complex
    rwa [Complex.norm_ofReal] at h_bound

end Matrix
