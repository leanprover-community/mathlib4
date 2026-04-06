/-
Copyright (c) 2026 Slava Naprienko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Slava Naprienko
-/
import Mathlib.Tactic

/-!
# The Desnanot-Jacobi identity

We prove the **Desnanot-Jacobi identity** (also known as the Lewis Carroll identity
or Dodgson condensation identity): for any matrix `M` over a commutative ring,
`det(M) * det(M₁ₖ¹ᵏ) = det(M₁¹) * det(Mₖᵏ) - det(M₁ᵏ) * det(Mₖ¹)`,
where subscripts and superscripts denote row and column deletion.

The proof proceeds by multiplying `M` by an auxiliary matrix built from the adjugate.

## Main results

- `desnanot_jacobi`: the Desnanot-Jacobi identity over any commutative ring.
-/

open Matrix Finset

variable {n : ℕ} {R : Type*} [CommRing R]

@[simp]
private lemma succ_cast_succ_ne_zero (j : Fin n) :
    (j.succ.castSucc : Fin (n + 2)) ≠ 0 := by simp

@[simp]
private lemma succ_cast_succ_ne_last (j : Fin n) :
    (j.succ.castSucc : Fin (n + 2)) ≠ Fin.last (n + 1) := by simp

@[simp]
private lemma cast_succ_succ_ne_last (j : Fin n) :
    (j.castSucc.succ : Fin (n + 2)) ≠ Fin.last (n + 1) := by simp

@[simp]
private lemma last_ne_cast_succ_succ (j : Fin n) :
    Fin.last (n + 1) ≠ (j.castSucc.succ : Fin (n + 2)) :=
  (cast_succ_succ_ne_last j).symm

def M11 (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :=
  M.submatrix (Fin.succAbove 0) (Fin.succAbove 0)

def Mkk (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :=
  M.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove

def M1k (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :=
  M.submatrix (Fin.succAbove 0) (Fin.last (n + 1)).succAbove

def Mk1 (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :=
  M.submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove 0)

def M1k_1k (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :=
  M.submatrix (Fin.succAbove 0 ∘ Fin.succAbove (Fin.last n))
              (Fin.succAbove 0 ∘ Fin.succAbove (Fin.last n))

private def auxAdjugateM (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) R := fun i j =>
  if j = 0 then adjugate M i 0
  else if j = Fin.last (n + 1) then adjugate M i (Fin.last (n + 1))
  else if i = j then 1
  else 0

private def auxP (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) R := fun i j =>
  if j = 0 then if i = 0 then M.det else 0
  else if j = Fin.last (n + 1) then if i = Fin.last (n + 1) then M.det else 0
  else M i j

private lemma aux_adjugate_m_m11_id (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    ((auxAdjugateM M).submatrix (Fin.succAbove 0) (Fin.succAbove 0)).submatrix
      (Fin.last n).succAbove (Fin.last n).succAbove = 1 := by
  ext i j
  simp [auxAdjugateM, Fin.succ_inj, Matrix.one_apply]

private lemma aux_adjugate_m_m1n_id (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    ((auxAdjugateM M).submatrix (Fin.succAbove 0) (Fin.last (n + 1)).succAbove).submatrix
      (Fin.last n).succAbove (Fin.succAbove 0) = 1 := by
  ext i j
  simp only [auxAdjugateM, submatrix_apply, Fin.succAbove_zero, Fin.succAbove_last, one_apply]
  simp only [succ_cast_succ_ne_zero, succ_cast_succ_ne_last, ite_false]
  congr 1
  exact propext ⟨fun h => by simp [Fin.ext_iff] at h ⊢; omega, fun h => by subst h; rfl⟩

private lemma mul_aux_adjugate_m_eq_aux_p (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    M * auxAdjugateM M = auxP M := by
  ext i j
  simp only [auxAdjugateM, auxP, mul_apply]
  rcases eq_or_ne j 0 with rfl | hj0
  · have h := congr_fun (congr_fun (mul_adjugate M) i) 0
    simpa only [smul_eq_mul, smul_apply, one_apply, mul_boole] using h
  · rcases eq_or_ne j (Fin.last (n + 1)) with rfl | hjk
    · have h := congr_fun (congr_fun (mul_adjugate M) i) (Fin.last (n + 1))
      simpa only [smul_eq_mul, smul_apply, one_apply, mul_boole] using h
    · simp only [hj0, hjk, mul_ite, mul_one, mul_zero]
      rw [sum_eq_single j]
      · exact if_pos rfl
      · exact fun b _ hbj => if_neg hbj
      · exact fun hj => False.elim (hj (mem_univ j))

private lemma det_aux_p_eq (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    (auxP M).det = M.det ^ 2 * (M1k_1k M).det := by
  let Q := (auxP M).submatrix Fin.succ Fin.succ
  have h_PM :
    (auxP M).submatrix (Fin.succ ∘ Fin.castSucc) (Fin.succ ∘ Fin.castSucc) = M1k_1k M := by
    ext i j; simp [auxP, M1k_1k, submatrix_apply, Function.comp, Fin.succ_ne_zero]
  have h1 : (auxP M).det = M.det * Q.det := by
    rw [det_succ_column (auxP M) 0, sum_eq_single 0]
    · simp [auxP, Q]
    · intro i _ hi; simp [auxP, hi]
    · simp
  have h2 : Q.det = M.det * (M1k_1k M).det := by
    rw [det_succ_column Q (Fin.last n), sum_eq_single (Fin.last n)]
    · simp [Q, h_PM, auxP]
    · intro b _ hb; simp [Q, auxP, hb]
    · simp
  rw [h1, h2, pow_two, mul_assoc]

private lemma det_aux_adjugate_m_eq (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    (auxAdjugateM M).det = (M11 M).det * (Mkk M).det - (M1k M).det * (Mk1 M).det := by
  let f0 := (0 : Fin (n + 2)).succAbove
  let fn := (Fin.last (n + 1)).succAbove
  let M'11 := (auxAdjugateM M).submatrix f0 f0
  let M'1n := (auxAdjugateM M).submatrix f0 fn
  have h_M'_expand : (auxAdjugateM M).det =
      auxAdjugateM M 0 0 * M'11.det + (-1 : R) ^ (n + 1) *
      auxAdjugateM M 0 (Fin.last (n + 1)) * M'1n.det := by
    rw [Matrix.det_succ_row (auxAdjugateM M) 0, Fin.sum_univ_succ]
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp [M'11, M'1n, f0, fn]
    · intro b _ hb
      have h1 : (b.succ : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero b
      have h2 : (b.succ : Fin (n + 2)) ≠ Fin.last (n + 1) := by
        intro h; apply hb; exact Fin.succ_inj.mp (by rw [h, ← Fin.succ_last])
      simp [auxAdjugateM, h1, h1.symm, h2]
    · simp
  rw [h_M'_expand]
  have h_M'00 : auxAdjugateM M 0 0 = (M11 M).det := by
    change adjugate M 0 0 = (M11 M).det; rw [adjugate_fin_succ_eq_det_submatrix]; simp [M11]
  have h_M'0n : auxAdjugateM M 0 (Fin.last (n + 1)) = (-1) ^ (n + 1) * (Mk1 M).det := by
    simp [auxAdjugateM, adjugate_fin_succ_eq_det_submatrix, Mk1]
  have h_M'11_det : M'11.det = (Mkk M).det := by
    rw [det_succ_column M'11 (Fin.last n), sum_eq_single (Fin.last n)]
    · have h_entry : M'11 (Fin.last n) (Fin.last n) = (Mkk M).det := by
        simp [M'11, auxAdjugateM, f0, submatrix_apply,
            Fin.succAbove_zero, Fin.succ_last, adjugate_fin_succ_eq_det_submatrix, Mkk]
      rw [h_entry, aux_adjugate_m_m11_id, det_one, mul_one]
      simp only [Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    · intro b _ hb
      obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (Ne.symm hb)
      suffices hdet : (M'11.submatrix b.succAbove (Fin.last n).succAbove).det = 0 by rw [hdet]; ring
      exact det_eq_zero_of_row_eq_zero r fun j => by
        simp [submatrix_apply, M'11, auxAdjugateM, f0, Fin.succAbove_zero, hr]
    · simp
  have h_M'1n : M'1n.det = -(M1k M).det := by
    rw [det_succ_column M'1n 0, sum_eq_single (Fin.last n)]
    · have h_entry : M'1n (Fin.last n) 0 = adjugate M (Fin.last (n + 1)) 0 := by
        simp [M'1n, auxAdjugateM, f0, fn, submatrix_apply,
            Fin.succAbove_zero, Fin.succAbove_last, Fin.succ_last]
      rw [h_entry, adjugate_fin_succ_eq_det_submatrix]
      simp only [Fin.val_zero, zero_add, Fin.val_last, M1k]
      have hp : n + 0 + (n + 1) = 2 * n + 1 := by omega
      rw [aux_adjugate_m_m1n_id, det_one, mul_one, ← mul_assoc,
      ← pow_add, hp, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul]
    · intro b _ hb
      obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (Ne.symm hb)
      suffices hdet : (M'1n.submatrix b.succAbove (Fin.succAbove 0)).det = 0 by rw [hdet]; ring
      exact det_eq_zero_of_row_eq_zero r fun j => by
        simp [submatrix_apply, M'1n, auxAdjugateM,
            f0, fn, Fin.succAbove_zero, Fin.succAbove_last, Fin.succ_last, hr]
    · simp
  rw [h_M'00, h_M'11_det, h_M'0n, h_M'1n]
  rw [mul_neg, ← mul_assoc, ← mul_pow, neg_mul_neg, one_mul, one_pow]
  ring

private theorem det_desnanot_jacobi_mul
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    M.det * (M.det * (M1k_1k M).det) =
    M.det * ((M11 M).det * (Mkk M).det - (M1k M).det * (Mk1 M).det) := by
  have h_det_prod : M.det * (auxAdjugateM M).det = (auxP M).det := by
    rw [← det_mul, mul_aux_adjugate_m_eq_aux_p M]
  rw [det_aux_p_eq M, det_aux_adjugate_m_eq M] at h_det_prod
  rw [pow_two, mul_assoc] at h_det_prod
  exact h_det_prod.symm

abbrev UnivRing (n : ℕ) := MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℤ

noncomputable def univMatrix (n : ℕ) : Matrix (Fin (n + 2)) (Fin (n + 2)) (UnivRing n) :=
  fun i j => MvPolynomial.X (i, j)

lemma univMatrix_det_ne_zero {n : ℕ} : (univMatrix n).det ≠ 0 := by
  intro h
  let f_eval : Fin (n + 2) × Fin (n + 2) → ℤ := fun p => if p.1 = p.2 then 1 else 0
  let eval_hom : UnivRing n →+* ℤ := MvPolynomial.eval f_eval
  have h1 : eval_hom (univMatrix n).det = eval_hom 0 := congrArg eval_hom h
  rw [map_zero] at h1
  have h2 : eval_hom (univMatrix n).det = (eval_hom.mapMatrix (univMatrix n)).det :=
    RingHom.map_det eval_hom (univMatrix n)
  rw [h2] at h1
  have h3 : eval_hom.mapMatrix (univMatrix n) = 1 := by
    ext i j
    change eval_hom (MvPolynomial.X (i, j)) = if i = j then 1 else 0
    simp [eval_hom, f_eval]
  rw [h3, Matrix.det_one] at h1
  exact zero_ne_one h1.symm

private theorem desnanot_jacobi_domain {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) (hM : M.det ≠ 0) :
    M.det * (M1k_1k M).det = (M11 M).det * (Mkk M).det - (M1k M).det * (Mk1 M).det := by
  exact mul_left_cancel₀ hM (det_desnanot_jacobi_mul M)

private theorem desnanot_jacobi_univ (n : ℕ) :
    (univMatrix n).det * (M1k_1k (univMatrix n)).det =
    (M11 (univMatrix n)).det * (Mkk (univMatrix n)).det -
    (M1k (univMatrix n)).det * (Mk1 (univMatrix n)).det :=
  desnanot_jacobi_domain (univMatrix n) univMatrix_det_ne_zero

noncomputable def evalMap {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) : UnivRing n →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) (fun p => M p.1 p.2)

/-- The **Desnanot-Jacobi identity** (Lewis Carroll identity, Dodgson condensation):
for any `(n+2) × (n+2)` matrix `M` over a commutative ring,
`det(M) · det(M_interior) = det(M₁₁) · det(Mₙₙ) - det(M₁ₙ) · det(Mₙ₁)`. -/
theorem desnanot_jacobi {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    M.det * (M1k_1k M).det =
    (M11 M).det * (Mkk M).det - (M1k M).det * (Mk1 M).det := by
  have hu := desnanot_jacobi_univ n
  have h_eval := congrArg (evalMap M) hu
  simp only [map_sub, map_mul] at h_eval
  have h_map {p : ℕ} (f g : Fin p → Fin (n + 2)) :
      evalMap M ((univMatrix n).submatrix f g).det = (M.submatrix f g).det := by
    rw [RingHom.map_det]
    congr 1; ext i j; simp [evalMap, univMatrix]
  have h_map_M : evalMap M (univMatrix n).det = M.det := by
    rw [RingHom.map_det]
    congr 1; ext i j; simp [evalMap, univMatrix]
  simp only [M11, Mkk, M1k, Mk1, M1k_1k] at h_eval ⊢
  simp only [h_map_M, h_map] at h_eval
  exact h_eval
