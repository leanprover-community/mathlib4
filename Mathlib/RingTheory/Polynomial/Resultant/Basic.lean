/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen, Andrew Yang
-/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# Resultant of two polynomials

This file contains basic facts about resultant of two polynomials over commutative rings.

## Main definitions

* `Polynomial.resultant`: The resultant of two polynomials `p` and `q` is defined as the determinant
  of the Sylvester matrix of `p` and `q`.
* `Polynomial.discr`: The discriminant of a polynomial `f` is defined as the resultant of `f` and
  `f.derivative`, modified by factoring out a sign and a power of the leading term.

## TODO

* The eventual goal is to prove the following property:
  `resultant (∏ a ∈ s, (X - C a)) f = ∏ a ∈ s, f.eval a`.
  This allows us to write the `resultant f g` as the product of terms of the form `a - b` where `a`
  is a root of `f` and `b` is a root of `g`.
* A smaller intermediate goal is to show that the Sylvester matrix corresponds to the linear map
  that we will call the Sylvester map, which is `R[X]_n × R[X]_m →ₗ[R] R[X]_(n + m)` given by
  `(p, q) ↦ f * p + g * q`, where `R[X]_n` is
  `Polynomial.degreeLT` in `Mathlib.RingTheory.Polynomial.Basic`.
* Resultant of two binary forms (i.e. homogeneous polynomials in two variables), after binary forms
  are implemented.

-/

open Set

namespace Polynomial

section sylvester

variable {R S : Type*} [Semiring R] [Semiring S]

/-- The Sylvester matrix of two polynomials `f` and `g` of degrees `m` and `n` respectively is a
`(m+n) × (m+n)` matrix with the coefficients of `f` and `g` arranged in a specific way. Here, `m`
and `n` are free variables, not necessarily equal to the actual degrees of the polynomials `f` and
`g`. -/
def sylvester (f g : R[X]) (m n : ℕ) : Matrix (Fin (m + n)) (Fin (m + n)) R :=
  .of fun i j ↦ j.addCases
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + n) then g.coeff (i - j₁) else 0)
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + m) then f.coeff (i - j₁) else 0)

variable (f g : R[X]) (m n : ℕ)

@[simp] theorem sylvester_zero_left_deg :
    sylvester f g 0 m = Matrix.diagonal (fun _ ↦ f.coeff 0) :=
  Matrix.ext fun i j ↦ j.addCases nofun fun j ↦ by
    rw [sylvester, Matrix.of_apply, Fin.addCases_right, Matrix.diagonal_apply]
    split_ifs <;> simp_all [Fin.ext_iff]

lemma sylvester_comm :
    sylvester f g m n = (sylvester g f n m).reindex (finCongr (add_comm n m))
      (finSumFinEquiv.symm.trans <|
        (Equiv.sumComm _ _).trans finSumFinEquiv) := by
  ext i j
  induction j using Fin.addCases <;> simp [sylvester]

lemma sylvester_map_map (φ : R →+* S) :
    sylvester (f.map φ) (g.map φ) m n = φ.mapMatrix (sylvester f g m n) := by
  ext i j; induction j using Fin.addCases <;> simp [sylvester, apply_ite φ]

/--
The Sylvester matrix for `f` and `f.derivative`, modified by dividing the bottom row by
the leading coefficient of `f`. Important because its determinant is (up to a sign) the
discriminant of `f`.
-/
noncomputable def sylvesterDeriv (f : R[X]) :
    Matrix (Fin (f.natDegree - 1 + f.natDegree)) (Fin (f.natDegree - 1 + f.natDegree)) R :=
  letI n := f.natDegree
  if hn : n = 0 then 0
  else (f.derivative.sylvester f (n - 1) n).updateRow ⟨2 * n - 2, by cutsat⟩
    (fun j ↦ if ↑j = n - 2 then 1 else (if ↑j = 2 * n - 2 then n else 0))

/-- We can get the usual Sylvester matrix of `f` and `f.derivative` back from the modified one
by multiplying the last row by the leading coefficient of `f`. -/
lemma sylvesterDeriv_updateRow (f : R[X]) (hf : 0 < f.natDegree) :
    (sylvesterDeriv f).updateRow ⟨2 * f.natDegree - 2, by cutsat⟩
      (f.leadingCoeff • (sylvesterDeriv f ⟨2 * f.natDegree - 2, by cutsat⟩)) =
    (f.derivative.sylvester f (f.natDegree - 1) f.natDegree) := by
  by_cases hn : f.natDegree = 0
  · ext ⟨i, hi⟩; cutsat
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [sylvesterDeriv, dif_neg hn]
  rcases ne_or_eq i (2 * f.natDegree - 2) with hi' | rfl
  · -- Top part of matrix
    rw [Matrix.updateRow_ne (Fin.ne_of_val_ne hi'),
      Matrix.updateRow_ne (Fin.ne_of_val_ne hi')]
  · -- Bottom row
    simp only [sylvester, Fin.addCases, mem_Icc, coeff_derivative, eq_rec_constant, leadingCoeff,
      Matrix.updateRow_self, Matrix.updateRow_apply, ↓reduceIte, Pi.smul_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Matrix.of_apply, Fin.castLT_mk, tsub_le_iff_right, Fin.cast_mk,
      Fin.subNat_mk, dite_eq_ite]
    split_ifs
    on_goal 2 => rw [show f.natDegree = 1 by cutsat]
    on_goal 3 =>
      rw [← Nat.cast_one (R := R), ← Nat.cast_add, show f.natDegree = 1 by cutsat]
      norm_num
    on_goal 6 =>
      rw [← Nat.cast_one (R := R), ← Nat.cast_add]
      #adaptation_note
      /--
      Prior to nightly-2025-09-09,
      these two steps were not needed (i.e. `grind` just finished from here)
      -/
      have : 2 * f.natDegree - 2 - (j - (f.natDegree - 1)) + 1 = f.natDegree := by grind
      simp [this]
    all_goals grind

end sylvester

section resultant

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The resultant of two polynomials `f` and `g` is the determinant of the Sylvester matrix of `f`
and `g`. The size arguments `m` and `n` are implemented as `optParam`, meaning that the default
values are `f.natDegree` and `g.natDegree` respectively, but they can also be specified to be
other values. -/
def resultant (f g : R[X]) (m : ℕ := f.natDegree) (n : ℕ := g.natDegree) : R :=
  (sylvester f g m n).det

variable (f g p : R[X]) (r : R) (m n k : ℕ)

lemma resultant_map_map (φ : R →+* S) :
    resultant (f.map φ) (g.map φ) m n = φ (resultant f g m n) := by
  simp [resultant, Polynomial.sylvester_map_map, RingHom.map_det]

@[simp] theorem resultant_zero_left_deg : resultant f g 0 m = f.coeff 0 ^ m := by
  simp [resultant]

/-- For polynomial `f` and constant `a`, `Res(f, a) = a ^ m`. -/
theorem resultant_C_zero_left : resultant (C r) g 0 m = r ^ m := by simp

/-- `Res(f, g) = (-1)ᵐⁿ Res(g, f)` -/
lemma resultant_comm : resultant f g m n = (-1) ^ (m * n) * resultant g f n m := by
  classical
  rw [resultant, resultant, sylvester_comm, Matrix.det_reindex, Equiv.Perm.sign_eq_prod_prod_Ioi]
  congr 1
  dsimp
  simp only [Fin.cast_lt_cast, Units.coe_prod, apply_ite, Units.val_one, Units.val_neg,
    Int.reduceNeg, Int.cast_prod, Int.cast_one, Int.cast_neg]
  simp_rw [← finSumFinEquiv.prod_comp, ← Finset.prod_map_equiv finSumFinEquiv.symm]
  simp only [Equiv.symm_apply_apply, ← Fin.val_fin_lt, Equiv.symm_symm, Function.comp_apply,
    Finset.prod_eq_prod_ite_mem (Finset.map _ _), Finset.mem_map_equiv, Finset.mem_Ioi,
    Fintype.prod_sum_type, finSumFinEquiv_apply_left, Fin.coe_castAdd, Sum.swap_inl,
    finSumFinEquiv_apply_right, Fin.coe_natAdd, Sum.swap_inr, add_lt_add_iff_left,
    ← ite_not (α := R) (p := _ < _) (y := 1), ← ite_and, and_not_self]
  simp [(Fin.isLt _).trans_le, (Fin.isLt _).le.trans, pow_mul]

@[simp] theorem resultant_zero_right_deg : resultant f g m 0 = g.coeff 0 ^ m := by
  rw [resultant_comm]; simp

/-- `Res(a, g) = a ^ deg g` -/
theorem resultant_C_zero_right (r : R) : resultant f (C r) m 0 = r ^ m := by simp

@[simp]
theorem resultant_zero_right : resultant f 0 m n = 0 ^ m * f.coeff 0 ^ n := by
  obtain _ | m := m; · simp
  have (i : Fin (m + 1 + n)) : sylvester f 0 (m + 1) n i ⟨0, by omega⟩ = 0 := by
    simp [sylvester, show (0 : Fin (m + 1 + n)) = Fin.castAdd _ 0 from rfl, Fin.addCases_left]
  simpa [resultant] using Matrix.det_eq_zero_of_column_eq_zero ⟨0, by simp⟩ this

@[simp]
theorem resultant_zero_left : resultant 0 g m n = 0 ^ n * g.coeff 0 ^ m := by
  rw [resultant_comm, resultant_zero_right]
  cases n <;> simp

theorem resultant_zero_zero : resultant (0 : R[X]) 0 m n = 0 ^ (m + n) := by simp [pow_add]

/-- See `resultant_add_mul_right`. -/
private lemma resultant_add_mul_monomial_right (hk : k + m ≤ n) (hf : f.natDegree ≤ m) :
    resultant f (g + f * monomial k r) m n = resultant f g m n := by
  obtain rfl | hm := eq_or_ne m 0
  · obtain ⟨q, rfl⟩ := natDegree_eq_zero.mp (le_zero_iff.mp hf); simp
  let M₁ := f.sylvester (g + f * monomial k r) m n
  let M₂ := f.sylvester g m n
  let M (i : ℕ) : Matrix (Fin (m + n)) (Fin (m + n)) R :=
    .of fun j₁ j₂ ↦ if j₂.1 < i then M₁ j₁ j₂ else M₂ j₁ j₂
  have (i : ℕ) (hi : i ≤ m) : (M i).det = M₂.det := by
    induction i with
    | zero => simp [M]; rfl
    | succ i IH =>
      rw [← IH (by omega), ← Matrix.det_updateCol_add_smul_self (i := ⟨i, by omega⟩)
        (j := ⟨i + k + m, by omega⟩) (c := -r) (M (i + 1)) (by simp; omega)]
      congr 1
      ext j₁ j₂
      simp only [Matrix.of_apply, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, add_assoc,
        add_lt_add_iff_left, Nat.lt_one_iff, Nat.add_eq_zero, hm, and_false, smul_eq_mul,
        Matrix.updateCol_apply, Fin.ext_iff, M, M₂, neg_mul, ← sub_eq_add_neg]
      obtain rfl | h := eq_or_ne ↑j₂ i
      · simp only [↓reduceIte, sylvester, Set.mem_Icc, coeff_add, Fin.eta, Matrix.of_apply,
          lt_self_iff_false, M₁]
        induction j₂ using Fin.addCases with
        | left j₂ =>
          dsimp at hi
          have : Fin.mk (n := m + n) (↑j₂ + (k + m)) (by omega) = Fin.natAdd m ⟨j₂ + k, by omega⟩ :=
            Fin.ext (by simp; omega)
          simp only [Fin.addCases_left, Fin.coe_castAdd, this, Fin.addCases_right, mul_ite,
            mul_zero, ← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', ite_add_zero,
            coeff_mul_C, add_assoc, add_eq_left, ← ite_and, ← mul_comm r, tsub_add_eq_tsub_tsub,
            add_sub_assoc, sub_eq_zero]
          split_ifs with h₁ h₂ h₂ <;> try rfl
          · rw [coeff_eq_zero_of_natDegree_lt, mul_zero]
            exact hf.trans_lt (by omega)
          · omega
        | right i =>
          simp only [Fin.coe_natAdd] at hi
          have : Fin.mk (n := m + n) (m + ↑i + (k + m)) (by omega) =
              Fin.natAdd m ⟨↑i + (k + m), by omega⟩ := Fin.ext (by simp; omega)
          simp only [Fin.addCases_right, Fin.coe_natAdd, sub_eq_self, this]
          rw [if_neg, mul_zero]
          omega
      split_ifs with h₁ h₂ h₃ h₄ h₅ <;> try first | omega | rfl
  rw [resultant, resultant, ← this m le_rfl]
  congr 1
  ext i j
  induction j using Fin.addCases <;> simp [M, sylvester, M₁, M₂]

/-- `Res(f, g + fp) = Res(f, g)` if `deg f + deg p ≤ deg g`. -/
lemma resultant_add_mul_right (hp : p.natDegree + m ≤ n) (hf : f.natDegree ≤ m) :
    resultant f (g + f * p) m n = resultant f g m n := by
  have H : p.support ⊆ Finset.range (n - m + 1) := by
    simp only [Finset.subset_iff, Finset.mem_range]
    exact fun x hx ↦ (le_natDegree_of_mem_supp _ hx).trans_lt (by omega)
  rw [← p.sum_monomial_eq, Polynomial.sum_eq_of_subset _ (by simp) H]
  set k := n - m + 1
  replace H := show k ≤ n - m + 1 from le_rfl
  clear_value k
  induction k generalizing g with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    rw [mul_zero, add_zero]
  | succ k IH =>
    rw [Finset.sum_range_succ, mul_add, ← add_assoc, resultant_add_mul_monomial_right, IH] <;> omega

/-- `Res(f + gp, g) = Res(f, g)` if `deg g + deg p ≤ deg f`. -/
lemma resultant_add_mul_left (hk : p.natDegree + n ≤ m) (hg : g.natDegree ≤ n) :
    resultant (f + g * p) g m n = resultant f g m n := by
  rw [resultant_comm, resultant_add_mul_right _ _ _ _ _ hk hg, resultant_comm,
    ← mul_assoc, ← pow_add, mul_comm m n, ← two_mul, pow_mul]
  ring

/-- `Res(f, a • g) = a ^ {deg f} * Res(f, g)`. -/
lemma resultant_C_mul_right (r : R) :
    resultant f (C r * g) m n = r ^ m * resultant f g m n := by
  let M₁ := f.sylvester (C r * g) m n
  let M₂ := f.sylvester g m n
  let M (i : ℕ) : Matrix (Fin (m + n)) (Fin (m + n)) R :=
    .of fun j₁ j₂ ↦ if j₂.1 < i then M₁ j₁ j₂ else M₂ j₁ j₂
  have (i : ℕ) (hi : i ≤ m) : (M i).det = r ^ i * M₂.det := by
    induction i with
    | zero => simp [M]; rfl
    | succ i IH =>
      suffices (M i).updateCol ⟨i, by omega⟩ (r • fun j ↦ M i j ⟨i, by omega⟩) = (M (i + 1)) by
        rw [pow_succ', mul_assoc, ← IH (by omega), ← this, Matrix.det_updateCol_smul,
          Matrix.updateCol_eq_self]
      ext j₁ j₂
      simp only [Matrix.of_apply, lt_self_iff_false, ↓reduceIte, Matrix.updateCol_apply,
        Fin.ext_iff, Pi.smul_apply, smul_eq_mul, M, M₂]
      obtain rfl | h := eq_or_ne ↑j₂ i
      · simp only [↓reduceIte, sylvester, Set.mem_Icc, Fin.eta, Matrix.of_apply,
          lt_add_iff_pos_right, zero_lt_one, coeff_C_mul, M₁]
        induction j₂ using Fin.addCases with
        | left j₂ => simp
        | right i => simp at hi; omega
      split_ifs with h₁ h₂ h₃ h₄ h₅ <;> try first | omega | rfl
  rw [resultant, resultant, ← this m le_rfl]
  congr 1
  ext i j
  induction j using Fin.addCases <;> simp [M, sylvester, M₁, M₂]

/-- `Res(a • f, g) = a ^ {deg g} * Res(f, g)`. -/
lemma resultant_C_mul_left (r : R) :
    resultant (C r * f) g m n = r ^ n * resultant f g m n := by
  rw [resultant_comm, resultant_C_mul_right, resultant_comm, mul_left_comm, ← mul_assoc ((-1) ^ _),
    mul_comm n m, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

lemma resultant_succ_left_deg (hf : f.natDegree ≤ m) :
    resultant f g (m + 1) n = (-1) ^ n * g.coeff n * resultant f g m n := by
  obtain _ | n := n
  · simp [pow_succ']
  rw [resultant, Matrix.det_succ_row (i := .last _),
      Finset.sum_eq_single (by exact ((Fin.last m).castAdd (n + 1))) _ (by simp)]
  · rw [resultant, ← Matrix.det_reindex_self (finCongr (show (m + 1).add n = m + (n + 1) by grind))]
    simp only [Nat.add_eq, Nat.succ_eq_add_one, Fin.val_last, Fin.coe_castAdd, Fin.succAbove_last,
      Matrix.reindex_apply, finCongr_symm, Matrix.submatrix_submatrix]
    congr 2
    · trans (-1) ^ (2 * m + (n + 1))
      · congr 1; omega
      · simp [pow_add]
    · simp only [sylvester, Set.mem_Icc, Matrix.of_apply, Fin.val_last, Fin.addCases_left]
      rw [if_pos (by omega)]
      simp [add_assoc, add_comm 1]
    · ext i j
      simp only [sylvester, Set.mem_Icc, Matrix.submatrix_apply, Function.comp_apply,
        finCongr_apply, Matrix.of_apply, Fin.coe_castSucc, Fin.coe_cast]
      induction j using Fin.addCases with
      | left j =>
        have : ((Fin.last m).castAdd (n + 1)).succAbove ((j.castAdd (n + 1)).cast (by grind)) =
          j.castSucc.castAdd (n + 1) := by ext; simp [Fin.succAbove, Fin.lt_iff_val_lt_val]
        simp [this]
      | right j =>
        have : ((Fin.last m).castAdd (n + 1)).succAbove ((j.natAdd m).cast (by grind)) =
          j.natAdd _ := by ext; simp [Fin.succAbove, Fin.lt_iff_val_lt_val, add_right_comm]
        simp only [ite_and, this, Fin.addCases_right]
        split_ifs with h₁ h₂ h₃ h₃ <;> try first | omega | rfl
        exact coeff_eq_zero_of_natDegree_lt (by omega)
  · rintro (b : Fin ((m + 1) + (n + 1))) - hb
    suffices f.sylvester g (m + 1) (n + 1) (.last (m + 1 + n)) b = 0 by simp [this]
    induction b using Fin.addCases with
    | left b =>
      simp only [Nat.add_eq, Nat.succ_eq_add_one, ne_eq, Fin.ext_iff, Fin.coe_castAdd,
        Fin.val_last] at hb
      simp only [sylvester, Set.mem_Icc, Matrix.of_apply, Fin.val_last, Fin.addCases_left,
        ite_eq_right_iff, and_imp]
      intros
      omega
    | right i => simpa [sylvester] using fun _ _ ↦ coeff_eq_zero_of_natDegree_lt (by omega)

lemma resultant_add_left_deg (hf : f.natDegree ≤ m) :
    resultant f g (m + k) n = (-1) ^ (n * k) * g.coeff n ^ k * resultant f g m n := by
  induction k with
  | zero => simp
  | succ k IH => simp [← add_assoc, resultant_succ_left_deg, hf.trans, IH]; ring

lemma resultant_add_right_deg (k : ℕ) (hg : g.natDegree ≤ n) :
    resultant f g m (n + k) = f.coeff m ^ k * resultant f g m n := by
  rw [resultant_comm, resultant_add_left_deg _ _ _ _ _ hg, resultant_comm,
    mul_assoc, mul_left_comm (f.coeff m ^ k)]
  simp only [← mul_assoc, ← pow_add, ← mul_add, mul_comm _ m]
  ring_nf
  simp [mul_comm]

lemma resultant_eq_zero_of_lt_lt (hf : f.natDegree < m) (hg : g.natDegree < n) :
    resultant f g m n = 0 := by
  obtain _ | m := m; · omega
  obtain _ | n := n; · omega
  rw [resultant_add_left_deg _ _ _ _ _ (by omega), resultant_add_right_deg _ _ _ _ _ (by omega)]
  simp [coeff_eq_zero_of_natDegree_lt hg]

@[simp]
theorem resultant_C_left (r : R) :
    resultant (C r) g m n = (-1) ^ (m * n) * g.coeff n ^ m * r ^ n := by
  rw [← zero_add m, resultant_add_left_deg _ _ _ _ _ (by simp), mul_comm n m]
  simp

@[simp] theorem resultant_C_right (r : R) : resultant f (C r) m n = f.coeff m ^ n * r ^ m := by
  rw [← zero_add n, resultant_add_right_deg _ _ _ _ _ (by simp)]
  simp

@[simp] theorem resultant_one_left : resultant 1 g m n = (-1) ^ (m * n) * g.coeff n ^ m := by
  simpa [-resultant_C_left] using resultant_C_left g m n 1

@[simp] theorem resultant_one_right : resultant f 1 m n = f.coeff m ^ n := by
  simpa [-resultant_C_right] using resultant_C_right f m n 1

/-- `Res(X - r, g) = g(r)` -/
lemma resultant_X_sub_C_left (r : R) (hg : g.natDegree ≤ n) :
    (X - C r).resultant g 1 n = eval r g := by
  nontriviality R
  obtain hg | hg := g.natDegree.eq_zero_or_pos
  · obtain ⟨s, rfl⟩ := natDegree_eq_zero.mp hg
    simp
  conv_lhs => rw [← g.modByMonic_add_div (monic_X_sub_C r)]
  rw [resultant_add_mul_right _ _ _ _ _ _ (natDegree_X_sub_C_le _), modByMonic_X_sub_C_eq_C_eval]
  · simp
  · rw [natDegree_divByMonic g (monic_X_sub_C r), natDegree_sub_C, natDegree_X]
    omega

/-- `Res(f, X - r) = (-1)^{deg f} * f(r)` -/
lemma resultant_X_sub_C_right (r : R) (hf : f.natDegree ≤ m) :
    f.resultant (X - C r) m 1 = (-1) ^ m * eval r f := by
  rw [resultant_comm, resultant_X_sub_C_left _ _ _ hf]
  simp

end resultant

section disc

variable {R : Type*} [CommRing R]

/-- The discriminant of a polynomial, defined as the determinant of `f.sylvesterDeriv` modified
by a sign. The sign is chosen so polynomials over `ℝ` with all roots real have non-negative
discriminant. -/
noncomputable def discr (f : R[X]) : R :=
  f.sylvesterDeriv.det * (-1) ^ (f.natDegree * (f.natDegree - 1) / 2)

@[deprecated (since := "2025-10-20")] alias disc := discr

/-- The discriminant of a constant polynomial is `1`. -/
@[simp] lemma discr_C (r : R) : discr (C r) = 1 := by
  let e : Fin ((C r).natDegree - 1 + (C r).natDegree) ≃ Fin 0 := finCongr (by simp)
  simp [discr, ← Matrix.det_reindex_self e]

/-- The discriminant of a linear polynomial is `1`. -/
lemma discr_of_degree_eq_one {f : R[X]} (hf : f.degree = 1) : discr f = 1 := by
  rw [← Nat.cast_one, degree_eq_iff_natDegree_eq_of_pos one_pos] at hf
  let e : Fin (f.natDegree - 1 + f.natDegree) ≃ Fin 1 := finCongr (by cutsat)
  have : f.sylvesterDeriv.reindex e e = !![1] := by
    have : NeZero (f.natDegree - 1 + f.natDegree) := ⟨by cutsat⟩
    ext ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨rfl⟩ : i = 0 := by cutsat
    obtain ⟨rfl⟩ : j = 0 := by cutsat
    simp [e, sylvesterDeriv, mul_comm, hf]
  simp [discr, ← Matrix.det_reindex_self e, this, hf]

/-- Standard formula for the discriminant of a quadratic polynomial. -/
lemma discr_of_degree_eq_two {f : R[X]} (hf : f.degree = 2) :
    discr f = f.coeff 1 ^ 2 - 4 * f.coeff 0 * f.coeff 2 := by
  rw [← Nat.cast_two, degree_eq_iff_natDegree_eq_of_pos two_pos] at hf
  let e : Fin (f.natDegree - 1 + f.natDegree) ≃ Fin 3 := finCongr (by cutsat)
  rw [discr, ← Matrix.det_reindex_self e]
  have : f.sylvesterDeriv.reindex e e =
    !![f.coeff 0,     f.coeff 1,         0;
        f.coeff 1, 2 * f.coeff 2, f.coeff 1;
        1,                     0,         2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e, sylvesterDeriv, sylvester, coeff_derivative, mul_comm, Fin.addCases,
        one_add_one_eq_two, hf, Fin.cast]
  simp only [this, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val, hf]
  ring_nf

@[deprecated (since := "2025-10-20")] alias disc_C := discr_C
@[deprecated (since := "2025-10-20")] alias disc_of_degree_eq_one := discr_of_degree_eq_one
@[deprecated (since := "2025-10-20")] alias disc_of_degree_eq_two := discr_of_degree_eq_two

/-- Relation between the resultant and the discriminant.

(Note this is actually false when `f` is a constant polynomial not equal to 1, so the assumption on
the degree is genuinely needed.) -/
lemma resultant_deriv {f : R[X]} (hf : 0 < f.degree) :
    resultant f f.derivative f.natDegree (f.natDegree - 1) =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff * f.discr := by
  rw [← natDegree_pos_iff_degree_pos] at hf
  rw [resultant_comm, resultant, ← sylvesterDeriv_updateRow f hf, Matrix.det_updateRow_smul,
    Matrix.updateRow_eq_self, discr, mul_comm f.natDegree]
  ring_nf
  rw [Nat.div_mul_cancel (by convert Nat.two_dvd_mul_add_one (f.natDegree - 1) using 2; omega)]

private lemma sylvesterDeriv_of_natDegree_eq_three {f : R[X]} (hf : f.natDegree = 3) :
    f.sylvesterDeriv.reindex (finCongr <| by rw [hf]) (finCongr <| by rw [hf]) =
    !![ f.coeff 0,         0, 1 * f.coeff 1,             0,             0;
        f.coeff 1, f.coeff 0, 2 * f.coeff 2, 1 * f.coeff 1,             0;
        f.coeff 2, f.coeff 1, 3 * f.coeff 3, 2 * f.coeff 2, 1 * f.coeff 1;
        f.coeff 3, f.coeff 2,             0, 3 * f.coeff 3, 2 * f.coeff 2;
                0,         1,             0,             0,             3] := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  -- In this proof we do as much as possible of the `simp` work before drilling down into the
  -- `fin_cases` constructs. This means the simps are not terminal, so they are not squeezed;
  -- but the proof runs much faster this way.
  simp only [sylvesterDeriv, hf, OfNat.ofNat_ne_zero, ↓reduceDIte, sylvester, Fin.addCases,
    Nat.add_one_sub_one, Fin.coe_castLT, mem_Icc, Fin.val_fin_le, Fin.coe_subNat, Fin.coe_cast,
    tsub_le_iff_right, coeff_derivative, eq_rec_constant, dite_eq_ite, Nat.reduceMul, Nat.reduceSub,
    Nat.cast_ofNat, Matrix.reindex_apply, finCongr_symm, Matrix.submatrix_apply, finCongr_apply,
    Fin.cast_mk, Matrix.updateRow_apply, Fin.mk.injEq, Matrix.of_apply, Fin.mk_le_mk, one_mul,
    Matrix.cons_val', Matrix.cons_val_fin_one]
  have hi' : i ∈ Finset.range 5 := Finset.mem_range.mpr hi
  have hj' : j ∈ Finset.range 5 := Finset.mem_range.mpr hj
  fin_cases hi' <;>
  · simp only [and_true, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta,
      le_add_iff_nonneg_left, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val,
      mul_one, Nat.cast_zero, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLeDiff, nonpos_iff_eq_zero,
      OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat, ↓reduceIte, zero_add, zero_le, zero_tsub]
    fin_cases hj' <;> simp [mul_comm, one_add_one_eq_two, (by norm_num : (2 : R) + 1 = 3)]

/-- Standard formula for the discriminant of a cubic polynomial. -/
lemma discr_of_degree_eq_three {f : R[X]} (hf : f.degree = 3) :
    discr f = f.coeff 2 ^ 2 * f.coeff 1 ^ 2
              - 4 * f.coeff 3 * f.coeff 1 ^ 3
              - 4 * f.coeff 2 ^ 3 * f.coeff 0
              - 27 * f.coeff 3 ^ 2 * f.coeff 0 ^ 2
              + 18 * f.coeff 3 * f.coeff 2 * f.coeff 1 * f.coeff 0 := by
  apply natDegree_eq_of_degree_eq_some at hf
  let e : Fin ((f.natDegree - 1) + f.natDegree) ≃ Fin 5 := finCongr (by rw [hf])
  rw [discr, ← Matrix.det_reindex_self e, sylvesterDeriv_of_natDegree_eq_three hf]
  simp [Matrix.det_succ_row_zero (n := 4), Matrix.det_succ_row_zero (n := 3), Fin.succAbove,
    Matrix.det_fin_three, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, hf]
  ring_nf

@[deprecated (since := "2025-10-20")] alias disc_of_degree_eq_three := discr_of_degree_eq_three

end disc

end Polynomial
