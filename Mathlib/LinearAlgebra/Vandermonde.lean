/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Peter Nelson
-/
import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Vandermonde matrix

This file defines the `vandermonde` matrix and gives its determinant.
For each `CommRing R`, and function `v : Fin n → R` the matrix `vandermonde v`
is defined to be `Fin n` by `Fin n` matrix `V` whose `i`th row is `[1, (v i), (v i)^2, ...]`.
This matrix has determinant equal to the product of `v i - v j` over all unordered pairs `i,j`,
and therefore is nonsingular if and only if `v` is injective.

`vandermonde v` is a special case of two more general matrices we also define.
For a type `α` and functions `v w : α → R`, we write `rectVandermonde v w n` for
the `α × Fin n` matrix with `i`th row `[(w i) ^ (n-1), (v i) * (w i)^(n-2), ..., (v i)^(n-1)]`.
`projVandermonde v w = rectVandermonde v w n` is the square matrix case, where `α = Fin n`.
The determinant of `projVandermonde v w` is the product of `v j * w i - v i * w j`,
taken over all pairs `i,j` with `i < j`, which gives a similar characterization of
when it it nonsingular. Since `vandermonde v w = projVandermonde v 1`,
we can derive most of the API for the former in terms of the latter.

These extensions of Vandermonde matrices arise in the study of complete arcs in finite geometry,
coding theory, and representations of uniform matroids over finite fields.

## Main definitions

* `vandermonde v`: a square matrix with the `i, j`th entry equal to `v i ^ j`.
* `rectVandermonde v w n`: an `α × Fin n` matrix whose
  `i, j`-th entry is `(v i) ^ j * (w i) ^ (n-1-j)`.
* `projVandermonde v w`: a square matrix whose `i, j`-th entry is `(v i) ^ j * (w i) ^ (n-1-j)`.

## Main results

* `det_vandermonde`: `det (vandermonde v)` is the product of `v j - v i`, where
  `(i, j)` ranges over the set of pairs with `i < j`.
* `det_projVandermonde`: `det (projVandermonde v w)` is the product of `v j * w i - v i * w j`,
  taken over all pairs with `i < j`.

## Implementation notes

We derive the `det_vandermonde` formula from `det_projVandermonde`,
which is proved using an induction argument involving row operations and division.
To circumvent issues with non-invertible elements while still maintaining the generality of rings,
we first prove it for fields using the private lemma `det_projVandermonde_of_field`,
and then use an algebraic workaround to generalize to the ring case,
stating the strictly more general form as `det_projVandermonde`.

## TODO

Characterize when `rectVandermonde v w n` has linearly independent rows.
-/

variable {R K : Type*} [CommRing R] [Field K] {n : ℕ}

open Equiv Finset

open Matrix Fin

namespace Matrix

/-- A matrix with rows all having the form `[b^(n-1), a * b^(n-2), ..., a ^ (n-1)]` -/
def rectVandermonde {α : Type*} (v w : α → R) (n : ℕ) : Matrix α (Fin n) R :=
  .of fun i j ↦ (v i) ^ j.1 * (w i) ^ j.rev.1

/-- A square matrix with rows all having the form `[b^(n-1), a * b^(n-2), ..., a ^ (n-1)]` -/
def projVandermonde (v w : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  rectVandermonde v w n

/-- `vandermonde v` is the square matrix with `i`th row equal to `1, v i, v i ^ 2, v i ^ 3, ...`. -/
def vandermonde (v : Fin n → R) : Matrix (Fin n) (Fin n) R := .of fun i j ↦ (v i) ^ j.1

lemma vandermonde_eq_projVandermonde (v : Fin n → R) : vandermonde v = projVandermonde v 1 := by
  simp [projVandermonde, rectVandermonde, vandermonde]

/-- We don't mark this as `@[simp]` because the RHS is not simp-nf,
and simplifying the RHS gives a bothersome `Nat` subtraction. -/
theorem projVandermonde_apply {v w : Fin n → R} {i j : Fin n} :
    projVandermonde v w i j = (v i) ^ j.1 * (w i) ^ j.rev.1 := rfl

theorem rectVandermonde_apply {α : Type*} {v w : α → R} {i : α} {j : Fin n} :
    rectVandermonde v w n i j = (v i) ^ j.1 * (w i) ^ j.rev.1 := rfl

@[simp]
theorem vandermonde_apply (v : Fin n → R) (i j) : vandermonde v i j = v i ^ (j : ℕ) := rfl

@[simp]
theorem vandermonde_cons (v0 : R) (v : Fin n → R) :
    vandermonde (Fin.cons v0 v : Fin n.succ → R) =
      Fin.cons (fun (j : Fin n.succ) => v0 ^ (j : ℕ)) fun i => Fin.cons 1
      fun j => v i * vandermonde v i j := by
  ext i j
  refine Fin.cases (by simp) (fun i => ?_) i
  refine Fin.cases (by simp) (fun j => ?_) j
  simp [pow_succ']

theorem vandermonde_succ (v : Fin n.succ → R) :
    vandermonde v = .of
      Fin.cons (fun (j : Fin n.succ) => v 0 ^ (j : ℕ)) fun i =>
        Fin.cons 1 fun j => v i.succ * vandermonde (Fin.tail v) i j := by
  conv_lhs => rw [← Fin.cons_self_tail v, vandermonde_cons]
  rfl

theorem vandermonde_mul_vandermonde_transpose (v w : Fin n → R) (i j) :
    (vandermonde v * (vandermonde w)ᵀ) i j = ∑ k : Fin n, (v i * w j) ^ (k : ℕ) := by
  simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, mul_pow]

theorem vandermonde_transpose_mul_vandermonde (v : Fin n → R) (i j) :
    ((vandermonde v)ᵀ * vandermonde v) i j = ∑ k : Fin n, v k ^ (i + j : ℕ) := by
  simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_add]

theorem rectVandermonde_apply_zero_right {α : Type*} {v w : α → R} {i : α} (hw : w i = 0) :
    rectVandermonde v w (n + 1) i = Pi.single (Fin.last n) ((v i) ^ n) := by
  ext j
  obtain rfl | hlt := j.le_last.eq_or_lt
  · simp [rectVandermonde_apply]
  rw [rectVandermonde_apply, Pi.single_eq_of_ne hlt.ne, hw, zero_pow, mul_zero]
  simpa [Nat.sub_eq_zero_iff_le] using hlt

theorem projVandermonde_apply_of_ne_zero
    {v w : Fin (n + 1) → K} {i j : Fin (n + 1)} (hw : w i ≠ 0) :
    projVandermonde v w i j = (v i) ^ j.1 * (w i) ^ n / (w i) ^ j.1 := by
  rw [projVandermonde_apply, eq_div_iff (by simp [hw]), mul_assoc, ← pow_add, rev_add_cast]

theorem projVandermonde_apply_zero_right {v w : Fin (n + 1) → R} {i : Fin (n + 1)} (hw : w i = 0) :
    projVandermonde v w i = Pi.single (Fin.last n) ((v i) ^ n)  := by
  ext j
  obtain rfl | hlt := j.le_last.eq_or_lt
  · simp [projVandermonde_apply]
  rw [projVandermonde_apply, Pi.single_eq_of_ne hlt.ne, hw, zero_pow, mul_zero]
  simpa [Nat.sub_eq_zero_iff_le] using hlt

theorem projVandermonde_comp {v w : Fin n → R} (f : Fin n → Fin n) :
    projVandermonde (v ∘ f) (w ∘ f) = (projVandermonde v w).submatrix f id := rfl

theorem projVandermonde_map {R' : Type*} [CommRing R'] (φ : R →+* R') (v w : Fin n → R) :
    projVandermonde (fun i ↦ φ (v i)) (fun i ↦ φ (w i)) = φ.mapMatrix (projVandermonde v w) := by
  ext i j
  simp [projVandermonde_apply]

private theorem det_projVandermonde_of_field (v w : Fin n → K) :
    (projVandermonde v w).det = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j * w i - v i * w j) := by
  induction n with
  | zero => simp
  | succ n ih =>
  /- We can assume not all `w i` are zero, and therefore that `w 0 ≠ 0`,
  since otherwise we can swap row `0` with another nonzero row. -/
  wlog h0 : w 0 ≠ 0 generalizing v w with aux
  · obtain h0' | ⟨i₀, hi₀ : w i₀ ≠ 0⟩ := forall_or_exists_not (w · = 0)
    · obtain rfl | hne := eq_or_ne n 0
      · simp [projVandermonde_apply]
      rw [det_eq_zero_of_column_eq_zero 0 (fun i ↦ by simpa [projVandermonde_apply, h0']),
        Finset.prod_sigma', Finset.prod_eq_zero (i := ⟨0, Fin.last n⟩) (by simpa) (by simp [h0'])]
    rw [← mul_right_inj' (a := ((Equiv.swap 0 i₀).sign : K))
      (by simp [show 0 ≠ i₀ by rintro rfl; contradiction]), ← det_permute, ← projVandermonde_comp,
      aux _ _ (by simpa), ← (Equiv.swap 0 i₀).prod_Ioi_comp_eq_sign_mul_prod (by simp)]
    rfl
  /- Let `W` be obtained from the matrix by subtracting `r = (v 0) / (w 0)` times each column
  from the next column, starting from the penultimate column. This doesn't change the determinant.-/
  set r := v 0 / w 0 with hr
  set W : Matrix (Fin (n + 1)) (Fin (n + 1)) K := .of fun i ↦ (cons (projVandermonde v w i 0)
    (fun j ↦ projVandermonde v w i j.succ - r * projVandermonde v w i j.castSucc))
  -- deleting the first row and column of `W` gives a row-scaling of a Vandermonde matrix.
  have hW_eq : (W.submatrix succ succ) = .of fun i j ↦ (v (succ i) - r * w (succ i)) *
      projVandermonde (v ∘ succ) (w ∘ succ) i j := by
    ext i j
    simp only [projVandermonde_apply, val_zero, rev_zero, val_last, val_succ,
      coe_castSucc, submatrix_apply, Function.comp_apply, rev_succ,
      W, r, rev_castSucc]
    simp
    ring
  /- The first row of `W` is `[(w 0)^n, 0, ..., 0]` - take a cofactor expansion along this row,
  and apply induction. -/
  rw [det_eq_of_forall_col_eq_smul_add_pred (B := W) (c := fun _ ↦ r) (by simp [W])
    (fun i j ↦ by simp [W, r, projVandermonde_apply]), det_succ_row_zero,
    Finset.sum_eq_single 0 _ (by simp)]
  · rw [succAbove_zero, hW_eq, det_mul_column, ih]
    simp only [Nat.succ_eq_add_one, coe_ofNat_eq_mod, Nat.zero_mod,
      pow_zero, show W 0 0 = w 0 ^ n by simp [W, projVandermonde_apply], one_mul, hr]
    field_simp
    simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_fin, Function.comp_apply]
    field_simp
    simp only [prod_univ_succ, Ioi_zero_eq_map, Finset.prod_map, coe_succEmb, prod_Ioi_succ]
  intro j _ hj0
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero hj0
  rw [mul_eq_zero, mul_eq_zero]
  refine .inl (.inr ?_)
  simp only [of_apply, projVandermonde_apply_of_ne_zero h0, val_succ, coe_castSucc, cons_succ, W, r]
  ring

/-- The formula for the determinant of a projective Vandermonde matrix. -/
theorem det_projVandermonde (v w : Fin n → R) : (projVandermonde v w).det =
    ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j * w i - v i * w j) := by
  let u (b : Bool) (i : Fin n) := (algebraMap (MvPolynomial (Fin n × Bool) ℤ)
    (FractionRing (MvPolynomial (Fin n × Bool) ℤ))) (MvPolynomial.X ⟨i, b⟩)
  have hdet := det_projVandermonde_of_field (u true) (u false)
  simp only [u] at hdet
  norm_cast at hdet
  rw [projVandermonde_map, ← RingHom.map_det, IsFractionRing.coe_inj] at hdet
  apply_fun MvPolynomial.eval₂Hom (Int.castRingHom R) (fun x ↦ (if x.2 then v else w) x.1) at hdet
  rw [RingHom.map_det] at hdet
  convert hdet <;>
  simp [← Matrix.ext_iff, projVandermonde_apply]

/-- The formula for the determinant of a Vandermonde matrix. -/
theorem det_vandermonde (v : Fin n → R) :
    det (vandermonde v) = ∏ i : Fin n, ∏ j ∈ Ioi i, (v j - v i) := by
  simp [vandermonde_eq_projVandermonde, det_projVandermonde]

theorem det_vandermonde_eq_zero_iff [IsDomain R] {v : Fin n → R} :
    det (vandermonde v) = 0 ↔ ∃ i j : Fin n, v i = v j ∧ i ≠ j := by
  constructor
  · simp only [det_vandermonde v, Finset.prod_eq_zero_iff, sub_eq_zero, forall_exists_index]
    rintro i ⟨_, j, h₁, h₂⟩
    exact ⟨j, i, h₂, (mem_Ioi.mp h₁).ne'⟩
  · simp only [Ne, forall_exists_index, and_imp]
    refine fun i j h₁ h₂ => Matrix.det_zero_of_row_eq h₂ (funext fun k => ?_)
    rw [vandermonde_apply, vandermonde_apply, h₁]

theorem det_vandermonde_ne_zero_iff [IsDomain R] {v : Fin n → R} :
    det (vandermonde v) ≠ 0 ↔ Function.Injective v := by
  unfold Function.Injective
  simp only [det_vandermonde_eq_zero_iff, Ne, not_exists, not_and, Classical.not_not]

@[simp]
theorem det_vandermonde_add (v : Fin n → R) (a : R) :
    (Matrix.vandermonde fun i ↦ v i + a).det = (Matrix.vandermonde v).det := by
  simp [Matrix.det_vandermonde]

@[simp]
theorem det_vandermonde_sub (v : Fin n → R) (a : R) :
    (Matrix.vandermonde fun i ↦ v i - a).det = (Matrix.vandermonde v).det := by
  rw [← det_vandermonde_add v (- a)]
  simp only [← sub_eq_add_neg]

theorem eq_zero_of_forall_index_sum_pow_mul_eq_zero [IsDomain R] {f v : Fin n → R}
    (hf : Function.Injective f) (hfv : ∀ j, (∑ i : Fin n, f j ^ (i : ℕ) * v i) = 0) : v = 0 :=
  eq_zero_of_mulVec_eq_zero (det_vandermonde_ne_zero_iff.mpr hf) (funext hfv)

theorem eq_zero_of_forall_index_sum_mul_pow_eq_zero [IsDomain R] {f v : Fin n → R}
    (hf : Function.Injective f) (hfv : ∀ j, (∑ i, v i * f j ^ (i : ℕ)) = 0) : v = 0 := by
  apply eq_zero_of_forall_index_sum_pow_mul_eq_zero hf
  simp_rw [mul_comm]
  exact hfv

theorem eq_zero_of_forall_pow_sum_mul_pow_eq_zero [IsDomain R] {f v : Fin n → R}
    (hf : Function.Injective f) (hfv : ∀ i : Fin n, (∑ j : Fin n, v j * f j ^ (i : ℕ)) = 0) :
    v = 0 :=
  eq_zero_of_vecMul_eq_zero (det_vandermonde_ne_zero_iff.mpr hf) (funext hfv)

open Polynomial

theorem eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials (v : Fin n → R)
    (p : Fin n → R[X]) (h_deg : ∀ i, (p i).natDegree ≤ i) :
    Matrix.of (fun i j => ((p j).eval (v i))) =
    (Matrix.vandermonde v) * (Matrix.of (fun (i j : Fin n) => (p j).coeff i)) := by
  ext i j
  simp_rw [Matrix.mul_apply, eval, Matrix.of_apply, eval₂]
  simp only [Matrix.vandermonde]
  have : (p j).support ⊆ range n := supp_subset_range <| Nat.lt_of_le_of_lt (h_deg j) <| Fin.prop j
  rw [sum_eq_of_subset _ (fun j => zero_mul ((v i) ^ j)) this, ← Fin.sum_univ_eq_sum_range]
  congr
  ext k
  rw [mul_comm, Matrix.of_apply, RingHom.id_apply]

theorem det_eval_matrixOfPolynomials_eq_det_vandermonde (v : Fin n → R) (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree = i) (h_monic : ∀ i, Monic <| p i) :
    (Matrix.vandermonde v).det = (Matrix.of (fun i j => ((p j).eval (v i)))).det := by
  rw [Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials v p (fun i ↦
      Nat.le_of_eq (h_deg i)), Matrix.det_mul,
      Matrix.det_matrixOfPolynomials p h_deg h_monic, mul_one]

lemma det_vandermonde_id_eq_superFactorial (n : ℕ) :
    (vandermonde fun i : Fin (n + 1) ↦ (i : R)).det = n.superFactorial := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Nat.superFactorial, det_vandermonde, Fin.prod_univ_succAbove _ 0]
    push_cast
    congr
    · simp only [Fin.val_zero, Nat.cast_zero, sub_zero]
      norm_cast
      simp [Fin.prod_univ_eq_prod_range (fun i ↦ (↑i + 1)) (n + 1)]
    · rw [det_vandermonde] at hn
      simp [hn]

private lemma of_eval_descPochhammer_eq_mul_of_choose {n : ℕ} (v : Fin n → ℕ) :
    (of fun i j : Fin n => (descPochhammer ℤ j).eval (v i : ℤ)).det =
    (∏ i : Fin n, Nat.factorial i) *
      (of fun i j : Fin n => (Nat.choose (v i) j : ℤ)).det := by
  convert det_mul_row (fun (i : Fin n) => ((Nat.factorial (i : ℕ)) : ℤ)) _
  · rw [of_apply, descPochhammer_eval_eq_descFactorial ℤ _ _]
    congr
    exact Nat.descFactorial_eq_factorial_mul_choose _ _
  · rw [Nat.cast_prod]

lemma superFactorial_dvd_vandermonde_det {n : ℕ} (v : Fin (n + 1) → ℤ) :
    ↑n.superFactorial ∣ (vandermonde v).det := by
  let m := inf' univ ⟨0, mem_univ _⟩ v
  let w' := fun i ↦ (v i - m).toNat
  have hw' : ∀ i, (w' i : ℤ) = v i - m := fun i ↦ Int.toNat_sub_of_le (inf'_le _ (mem_univ _))
  have h := det_eval_matrixOfPolynomials_eq_det_vandermonde (fun i ↦ ↑(w' i))
      (fun i => descPochhammer ℤ i)
      (fun i => descPochhammer_natDegree ℤ i)
      (fun i => monic_descPochhammer ℤ i)
  conv_lhs at h => simp only [hw', det_vandermonde_sub]
  use (of (fun (i j : Fin (n + 1)) => (Nat.choose (w' i) (j : ℕ) : ℤ))).det
  simp [h, of_eval_descPochhammer_eq_mul_of_choose w', Fin.prod_univ_eq_prod_range]

end Matrix
