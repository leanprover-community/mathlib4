/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen, Andrew Yang
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.FieldTheory.Extension
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.FieldTheory.Extension
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.Polynomial.DegreeLT

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

@[expose] public section

open Set

namespace Polynomial

section sylvester

variable {R S : Type*} [Semiring R] [Semiring S]

/-- The Sylvester matrix of two polynomials `f` and `g` of degrees `m` and `n` respectively is a
`(m+n) × (m+n)` matrix with the coefficients of `f` and `g` arranged in a specific way. Here, `m`
and `n` are free variables, not necessarily equal to the actual degrees of the polynomials `f` and
`g`.

Note that the natural definition would be a `Matrix (Fin (m + n)) (Fin m ⊕ Fin n) R` but we prefer
having this as a square matrix to take determinants later on.
-/
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
      (finSumFinEquiv.symm.trans <| (Equiv.sumComm _ _).trans finSumFinEquiv) := by
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

@[simp]
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
    ← Finset.prod_ite_mem_eq (Finset.map _ _), Finset.mem_map_equiv, Finset.mem_Ioi,
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
  have (i : Fin (m + 1 + n)) : sylvester f 0 (m + 1) n i ⟨0, by cutsat⟩ = 0 := by
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
      rw [← IH (by cutsat), ← Matrix.det_updateCol_add_smul_self (i := ⟨i, by cutsat⟩)
        (j := ⟨i + k + m, by cutsat⟩) (c := -r) (M (i + 1)) (by simp; omega)]
      congr 1
      ext j₁ j₂
      simp only [Matrix.of_apply, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, add_assoc,
        add_lt_add_iff_left, Nat.lt_one_iff, Nat.add_eq_zero_iff, hm, and_false, smul_eq_mul,
        Matrix.updateCol_apply, Fin.ext_iff, M, M₂, neg_mul, ← sub_eq_add_neg]
      obtain rfl | h := eq_or_ne ↑j₂ i
      · simp only [↓reduceIte, sylvester, Set.mem_Icc, coeff_add, Fin.eta, Matrix.of_apply,
          lt_self_iff_false, M₁]
        induction j₂ using Fin.addCases with
        | left j₂ =>
          dsimp at hi
          have : Fin.mk (n := m + n) (↑j₂ + (k + m)) (by cutsat) = .natAdd m ⟨j₂ + k, by cutsat⟩ :=
            Fin.ext (by simp; omega)
          simp only [Fin.addCases_left, Fin.coe_castAdd, this, Fin.addCases_right, mul_ite,
            mul_zero, ← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', ite_add_zero,
            coeff_mul_C, add_assoc, add_eq_left, ← ite_and, ← mul_comm r, tsub_add_eq_tsub_tsub,
            add_sub_assoc, sub_eq_zero]
          split_ifs with h₁ h₂ h₂ <;> try rfl
          · rw [coeff_eq_zero_of_natDegree_lt, mul_zero]
            exact hf.trans_lt (by cutsat)
          · omega
        | right i =>
          simp only [Fin.coe_natAdd] at hi
          have : Fin.mk (n := m + n) (m + ↑i + (k + m)) (by cutsat) =
              Fin.natAdd m ⟨↑i + (k + m), by cutsat⟩ := Fin.ext (by simp; omega)
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
    exact fun x hx ↦ (le_natDegree_of_mem_supp _ hx).trans_lt (by cutsat)
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
      suffices (M i).updateCol ⟨i, by cutsat⟩ (r • fun j ↦ M i j ⟨i, by cutsat⟩) = (M (i + 1)) by
        rw [pow_succ', mul_assoc, ← IH (by cutsat), ← this, Matrix.det_updateCol_smul,
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
      rw [if_pos (by cutsat)]
      simp [add_assoc, add_comm 1]
    · ext i j
      simp only [sylvester, Set.mem_Icc, Matrix.submatrix_apply, Function.comp_apply,
        finCongr_apply, Matrix.of_apply, Fin.coe_castSucc, Fin.coe_cast]
      induction j using Fin.addCases with
      | left j =>
        have : ((Fin.last m).castAdd (n + 1)).succAbove ((j.castAdd (n + 1)).cast (by grind)) =
          j.castSucc.castAdd (n + 1) := by ext; simp [Fin.succAbove, Fin.lt_def]
        simp [this]
      | right j =>
        have : ((Fin.last m).castAdd (n + 1)).succAbove ((j.natAdd m).cast (by grind)) =
          j.natAdd _ := by ext; simp [Fin.succAbove, Fin.lt_def, add_right_comm]
        simp only [ite_and, this, Fin.addCases_right]
        split_ifs with h₁ h₂ h₃ h₃ <;> try first | omega | rfl
        exact coeff_eq_zero_of_natDegree_lt (by cutsat)
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
    | right i => simpa [sylvester] using fun _ _ ↦ coeff_eq_zero_of_natDegree_lt (by cutsat)

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
  rw [resultant_add_left_deg _ _ _ _ _ (by cutsat), resultant_add_right_deg _ _ _ _ _ (by cutsat)]
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
@[simp] lemma resultant_X_sub_C_left (r : R) (hg : g.natDegree ≤ n) :
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

/-- `Res(X + r, g) = g(-r)` -/
@[simp] lemma resultant_X_add_C_left (r : R) (hg : g.natDegree ≤ n) :
    (X + C r).resultant g 1 n = eval (-r) g := by
  rw [← resultant_X_sub_C_left g n (-r) hg, map_neg, sub_neg_eq_add]

/-- `Res(f, X - r) = (-1)^{deg f} * f(r)` -/
@[simp] lemma resultant_X_sub_C_right (r : R) (hf : f.natDegree ≤ m) :
    f.resultant (X - C r) m 1 = (-1) ^ m * eval r f := by
  rw [resultant_comm, resultant_X_sub_C_left _ _ _ hf]
  simp

/-- `Res(f, X + r) = (-1)^{deg f} * f(-r)` -/
@[simp] lemma resultant_X_add_C_right (r : R) (hf : f.natDegree ≤ m) :
    f.resultant (X + C r) m 1 = (-1) ^ m * eval (-r) f := by
  rw [← resultant_X_sub_C_right f m (-r) hf, map_neg, sub_neg_eq_add]

/-- If `f` and `g` are monic and splits, then `Res(f, g) = ∏ (α - β)`,
where `α` and `β` runs through the roots of `f` and `g` respectively. -/
lemma resultant_eq_prod_roots_sub
    {K : Type*} [Field K] (f g : K[X]) (hf : f.Monic) (hg : g.Monic)
    (hf' : f.Splits) (hg' : g.Splits) :
    resultant f g = ((f.roots ×ˢ g.roots).map fun ij ↦ ij.1 - ij.2).prod := by
  wlog hfg : g.natDegree ≤ f.natDegree
  · trans ((f.roots ×ˢ g.roots).map fun ij ↦ (-1) * (ij.2 - ij.1)).prod
    · rw [resultant_comm, this g f hg hf hg' hf' (le_of_not_ge hfg), ← Multiset.map_swap_product,
        Multiset.map_map, Multiset.prod_map_mul]
      simp [hf'.natDegree_eq_card_roots, hg'.natDegree_eq_card_roots]
    · simp
  generalize hN : f.natDegree + g.natDegree = N
  induction N using Nat.strong_induction_on generalizing K with | h n IH =>
  by_cases hr : g ∣ f
  · obtain ⟨r, rfl⟩ := hr
    have hr' : r ≠ 0 := by simpa [hg.ne_zero] using hf.ne_zero
    rw [← resultant_add_mul_left _ _ (-r) _ _ _ le_rfl]
    · rw [mul_neg, add_neg_cancel, resultant_zero_left]
      by_cases H : g.natDegree = 0
      · obtain rfl := hg.natDegree_eq_zero.mp H
        simp
      · simp only [zero_pow H]
        rw [hg'.natDegree_eq_card_roots, Multiset.card_eq_zero,
          Multiset.eq_zero_iff_forall_notMem, not_forall_not] at H
        obtain ⟨x, hx⟩ := H
        rw [Multiset.prod_eq_zero, zero_mul]
        simp only [Multiset.mem_map, Prod.exists]
        exact ⟨x, x, Multiset.mem_product.mpr (by simp_all [hg.ne_zero]), by simp⟩
    · rw [natDegree_mul hg.ne_zero (by simpa [hg.ne_zero] using hf.ne_zero),
        natDegree_neg, add_comm]
  let r := C (f %ₘ g).leadingCoeff⁻¹ * (f %ₘ g)
  have hr₀ : f %ₘ g ≠ 0 := by simpa [modByMonic_eq_zero_iff_dvd, hg]
  have hrd : r.natDegree < g.natDegree := by
    simp [r, natDegree_C_mul, hr₀, natDegree_modByMonic_lt _ hg (show g ≠ 1 by aesop)]
  have hr : r.Monic := by
    dsimp only [r]
    rw [Monic, leadingCoeff, natDegree_C_mul (by simpa), coeff_C_mul, leadingCoeff,
      inv_mul_cancel₀ (by simpa)]
  let L := r.SplittingField
  have := IH _ (by simp; cutsat)
    (g.map (algebraMap K L)) (r.map (algebraMap K L)) (hg.map _) (hr.map _)
    (hg'.map _) (SplittingField.splits _) (by simpa [r, natDegree_C_mul, hr₀] using hrd.le) rfl
  rw [resultant_map_map, natDegree_map, natDegree_map, resultant_C_mul_right,
    map_mul, inv_pow, map_inv₀, inv_mul_eq_iff_eq_mul₀ (by simp [hr₀])] at this
  rw [← f.modByMonic_add_div hg, resultant_add_mul_left, f.modByMonic_add_div hg,
    ← Nat.sub_add_cancel (hrd.le.trans hfg), add_comm, resultant_add_left_deg, resultant_comm]
  · apply (algebraMap K L).injective
    rw [map_mul, map_mul, map_mul, this, map_sub_roots_sprod_eq_prod_map_eval _ _ hf hf',
      map_sub_sprod_roots_eq_prod_map_eval _ _ (hr.map _) (SplittingField.splits _), map_mul,
        roots_map _ (by simpa only [Splits, map_id])]
    have : (g.roots.map (eval · f)).prod =
        (f %ₘ g).leadingCoeff ^ g.natDegree * (g.roots.map (eval · r)).prod := by
      trans (g.roots.map ((f %ₘ g).leadingCoeff * eval · r)).prod
      · congr 1
        refine Multiset.map_congr rfl ?_
        simp only [mem_roots', ne_eq, IsRoot.def, eval_mul, eval_C, leadingCoeff_eq_zero, hr₀,
          not_false_eq_true, mul_inv_cancel_left₀, and_imp, r]
        intro x hx hxg
        conv_lhs => rw [← f.modByMonic_add_div hg, eval_add, eval_mul, hxg, zero_mul, add_zero]
      · simp [hg'.natDegree_eq_card_roots]
    simp only [coeff_natDegree, hg.leadingCoeff, one_pow, map_one, map_multiset_prod,
      ← hf'.natDegree_eq_card_roots, ← hg'.natDegree_eq_card_roots, this, map_mul, Multiset.map_map,
      map_pow, map_neg, mul_one, eval_map_algebraMap, Function.comp_apply]
    simp only [← mul_assoc, ← pow_add, ← add_mul, Nat.sub_add_cancel (hrd.le.trans hfg),
      mul_comm g.natDegree]
    congr 3 with x
    exact aeval_algebraMap_apply _ _ _
  · simp [r, hr₀, natDegree_C_mul]
  · rw [f.modByMonic_add_div hg, natDegree_divByMonic _ hg, Nat.sub_add_cancel hfg]
  · simp

/-- If `f` splits with leading coeff `a` and degree `n`,
then `Res(f, g) = aⁿ * ∏ g(α)` where `α` runs through the roots of `f`. -/
nonrec lemma resultant_eq_prod_eval [IsDomain R]
    (f g : R[X]) (n : ℕ) (hg : g.natDegree ≤ n) (hf : f.Splits) :
    resultant f g f.natDegree n = f.leadingCoeff ^ n * (f.roots.map g.eval).prod := by
  wlog hR : IsField R
  · let K := FractionRing R
    apply FaithfulSMul.algebraMap_injective R K
    have := this (f.map (algebraMap R K)) (g.map (algebraMap R K)) n (natDegree_map_le.trans hg)
      (hf.map _) (Field.toIsField _)
    simp only [resultant_map_map, natDegree_map_eq_of_injective, leadingCoeff_map_of_injective,
      FaithfulSMul.algebraMap_injective R K, ← hf.natDegree_eq_card_roots,
      ← roots_map_of_injective_of_card_eq_natDegree] at this
    simpa [map_multiset_prod, aeval_algebraMap_apply, Multiset.map_map] using this
  by_cases hf0 : f = 0
  · simp [hf0]
  wlog hfm : f.Monic
  · letI inst := hR.toField
    have H : (C f.leadingCoeff⁻¹ * f).Monic := by
      rw [Monic, ← coeff_natDegree, natDegree_C_mul (by simp [hf0]), coeff_C_mul]; simp [hf0]
    have := this (C f.leadingCoeff⁻¹ * f) g n hg (.mul (.C _) hf) hR (by simpa) H
    simpa [hf0, natDegree_C_mul, resultant_C_mul_left, inv_mul_eq_iff_eq_mul₀, roots_C_mul,
      H.leadingCoeff] using this
  simp only [hfm.leadingCoeff, one_pow, one_mul]
  clear hf0
  by_cases hg0 : g = 0
  · subst hg0
    by_cases hf' : f.natDegree = 0
    · obtain ⟨r, rfl⟩ := hfm.natDegree_eq_zero.mp hf'; simp
    simp [← hf.natDegree_eq_card_roots, hf']
  wlog hgm : g.Monic
  · letI inst := hR.toField
    have := this f (C g.leadingCoeff⁻¹ * g) n (by simpa [hg0, natDegree_C_mul]) hf hR hfm (by simpa)
      (by rw [Monic, ← coeff_natDegree, natDegree_C_mul (by simp [hg0]), coeff_C_mul]; simp [hg0])
    rw [resultant_C_mul_right, inv_pow, inv_mul_eq_iff_eq_mul₀ (by simp [hg0])] at this
    simpa [← hf.natDegree_eq_card_roots, inv_pow, mul_left_comm (_ ^ g.natDegree), hg0] using this
  letI inst := hR.toField
  let L := g.SplittingField
  apply (algebraMap R L).injective
  have := resultant_eq_prod_roots_sub (f.map (algebraMap R L))
    (g.map (algebraMap R L)) (hfm.map _) (hgm.map _) (hf.map _) (SplittingField.splits _)
  simp_rw [natDegree_map] at this
  rw [← resultant_map_map, ← Nat.add_sub_cancel' hg, resultant_add_right_deg _ _ _ _ _ (by simp),
    this, coeff_map, coeff_natDegree, hfm.leadingCoeff, map_one, one_pow, one_mul,
    map_sub_sprod_roots_eq_prod_map_eval _ _ (hgm.map _) (SplittingField.splits _),
    roots_map _ (by simp [hf]), map_multiset_prod, Multiset.map_map]
  simp only [eval_map_algebraMap, Function.comp_apply, Multiset.map_map, L]
  congr; ext; simp [aeval_algebraMap_apply]

set_option linter.unusedVariables false in
-- the variable names are used in the code action of `induction`.
/-- An induction principle useful to prove statements about resultants.
Let `P` be a predicate on a polynomial.
If `R → S` injective implies `(∀ p : S[X], P p) → (∀ p : R[X], P p)`,
and if `R → S` surjective implies `(∀ p : R[X], P p) → (∀ p : S[X], P p)`,
then we may reduce to the case where `R` is a field and `p` splits. -/
nonrec lemma induction_of_Splits_of_injective_of_surjective.{u}
    {R : Type u} [CommRing R] (p : R[X])
    (P : ∀ {R : Type u} [CommRing R], R[X] → Prop)
    (Splits : ∀ (R : Type u) [Field R] (p : R[X]) (hp : p.Splits), P p)
    (injective : ∀ (R S : Type u) [CommRing R] [CommRing S]
      (φ : R →+* S) (hφ : Function.Injective φ) (p : R[X]) (IH : P (p.map φ)), P p)
    (surjective : ∀ (R S : Type u) [CommRing R] [CommRing S]
      (φ : R →+* S) (hφ : Function.Surjective φ) (p : S[X]) (IH : ∀ q : R[X], P q), P p) : P p := by
  wlog hR : IsDomain R generalizing R
  · exact surjective _ _ (MvPolynomial.eval₂Hom (algebraMap ℤ R) id)
      (fun x ↦ ⟨.X x, by simp [MvPolynomial.eval₂Hom]⟩) p
      (fun _ ↦ this _ inferInstance)
  wlog hR : IsField R generalizing R
  · exact injective _ _ _ (FaithfulSMul.algebraMap_injective R (FractionRing R)) _
      (this _ inferInstance (Field.toIsField _))
  wlog hp : p.Splits generalizing R
  · letI inst := hR.toField
    exact injective _ _ _ (algebraMap R p.SplittingField).injective _
      (this _ inferInstance (Field.toIsField _) (SplittingField.splits _))
  letI inst := hR.toField
  exact Splits _ _ hp

/-- `Res(f, g₁ * g₂) = Res(f, g₁) * Res(f, g₂)`. -/
nonrec lemma resultant_mul_right (f g₁ g₂ : R[X]) (m : ℕ) (hm : f.natDegree ≤ m) :
    resultant f (g₁ * g₂) m (g₁.natDegree + g₂.natDegree) =
      resultant f g₁ m * resultant f g₂ m := by
  wlog hgn : m = f.natDegree
  · obtain ⟨c, rfl⟩ := le_iff_exists_add.mp hm
    simp [resultant_add_left_deg, this f g₁ g₂, coeff_mul_degree_add_degree]
    ring_nf
  subst hgn; clear hm
  induction f using induction_of_Splits_of_injective_of_surjective with
  | Splits R f hff =>
    simp [resultant_eq_prod_eval, natDegree_mul_le, hff]
    ring_nf
  | injective R SatisfiesM φ hφ f IH =>
    apply hφ
    have := IH (g₁.map φ) (g₂.map φ)
    rw [← Polynomial.map_mul] at this
    simpa only [resultant_map_map, ← map_mul, natDegree_map_eq_of_injective hφ] using this
  | surjective R S φ hφ f IH =>
    obtain ⟨f', hf', e⟩ := Polynomial.mem_lifts_and_degree_eq (Polynomial.map_surjective φ hφ f)
    obtain ⟨g₁', hg₁, e₁⟩ := Polynomial.mem_lifts_and_degree_eq (Polynomial.map_surjective φ hφ g₁)
    obtain ⟨g₂', hg₂, e₂⟩ := Polynomial.mem_lifts_and_degree_eq (Polynomial.map_surjective φ hφ g₂)
    rw [← hg₁, ← hg₂, ← hf', ← Polynomial.map_mul]
    simp_rw [resultant_map_map, hg₁, hg₂, hf', ← natDegree_eq_natDegree e₁,
      ← natDegree_eq_natDegree e₂, ← natDegree_eq_natDegree e, IH, map_mul]

/-- `Res(f₁ * f₂, g) = Res(f₁, g) * Res(f₂, g)`. -/
lemma resultant_mul_left (f₁ f₂ g : R[X]) (n : ℕ) (hn : g.natDegree ≤ n) :
    resultant (f₁ * f₂) g (f₁.natDegree + f₂.natDegree) n =
      resultant f₁ g f₁.natDegree n * resultant f₂ g f₂.natDegree n := by
  rw [resultant_comm, resultant_mul_right _ _ _ n hn, resultant_comm, resultant_comm f₂]
  ring_nf
  simp

/-- `Res(f, f) = 0` unless `deg f = 0`. Also see `resultant_self_eq_zero`. -/
@[simp] nonrec lemma resultant_self (f : R[X]) : resultant f f = 0 ^ f.natDegree := by
  induction f using induction_of_Splits_of_injective_of_surjective with
  | Splits R f hf =>
    by_cases h : f.natDegree = 0
    · obtain ⟨r, rfl⟩ := natDegree_eq_zero.mp h; simp
    rw [resultant_eq_prod_eval _ _ _ le_rfl hf]
    simp [zero_pow h, h, hf.exists_eval_eq_zero (degree_ne_of_natDegree_ne h), eq_or_ne f]
  | injective R S φ hφ f IH =>
    apply hφ
    simpa only [resultant_map_map, natDegree_map_eq_of_injective hφ, map_zero, map_pow] using IH
  | surjective R S φ hφ f IH =>
    obtain ⟨f', hf', e⟩ := Polynomial.mem_lifts_and_degree_eq (Polynomial.map_surjective φ hφ f)
    rw [← hf', resultant_map_map, hf', ← natDegree_eq_natDegree e, IH f', map_pow, map_zero]

lemma resultant_self_eq_zero (f : R[X]) (h : f.natDegree ≠ 0) :
    resultant f f = 0 := by
  simp [resultant_self, h]

lemma resultant_dvd_leadingCoeff_pow [IsDomain R] (f g : R[X]) (H : IsCoprime f g) :
    ∃ n, resultant f g ∣ f.leadingCoeff ^ n := by
  obtain rfl | hf := eq_or_ne f 0
  · simp only [isCoprime_zero_left, isUnit_iff] at H
    aesop
  obtain rfl | hg := eq_or_ne g 0
  · simp only [isCoprime_zero_right, isUnit_iff] at H
    aesop
  have ⟨a, b, e⟩ := H
  obtain rfl | ha := eq_or_ne a 0
  · obtain ⟨r, hr, rfl⟩ := isUnit_iff.mp (.of_mul_eq_one_right b (by simpa using e))
    simp [hr.pow]
  obtain rfl | hb := eq_or_ne b 0
  · obtain ⟨r, hr, rfl⟩ := isUnit_iff.mp (.of_mul_eq_one_right a (by simpa using e))
    simp [hr.pow]
  have := resultant_mul_right f b g _ le_rfl
  rw [← resultant_add_mul_right _ _ a _ _ _ le_rfl, add_comm, mul_comm f, e,
    resultant_one_right] at this
  · exact ⟨_, _, this.trans (mul_comm _ _)⟩
  · by_contra! H
    rw [← natDegree_mul ha hf, ← natDegree_mul hb hg] at H
    have := natDegree_add_eq_left_of_natDegree_lt H
    simp only [e, natDegree_one] at this
    cutsat

lemma resultant_ne_zero [IsDomain R] (f g : R[X]) (H : IsCoprime f g) :
    resultant f g ≠ 0 := by
  obtain rfl | hf := eq_or_ne f 0
  · simp only [isCoprime_zero_left, isUnit_iff] at H
    aesop
  intro e
  simpa [e, hf] using resultant_dvd_leadingCoeff_pow f g H

@[simp]
lemma resultant_prod_left {ι : Type*} (s : Finset ι) (f : ι → R[X]) (g : R[X])
    (n : ℕ) (hf : ∏ i ∈ s, (f i).leadingCoeff ≠ 0) (hn : g.natDegree ≤ n) :
    (∏ i ∈ s, f i).resultant g (∏ i ∈ s, f i).natDegree n =
      ∏ i ∈ s, (f i).resultant g (f i).natDegree n := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has IH =>
    have hf' : ∏ i ∈ s, (f i).leadingCoeff ≠ 0 := by aesop
    rw [Finset.prod_insert has, natDegree_mul' (by simpa [*, leadingCoeff_prod'] using hf),
      resultant_mul_left _ _ _ _ hn, IH hf', Finset.prod_insert has]

@[simp]
lemma resultant_prod_right {ι : Type*} (s : Finset ι) (f : R[X]) (g : ι → R[X])
    (m : ℕ) (hm : f.natDegree ≤ m) (hg : ∏ i ∈ s, (g i).leadingCoeff ≠ 0) :
    f.resultant (∏ i ∈ s, g i) m = ∏ i ∈ s, f.resultant (g i) m := by
  simp_rw [resultant_comm f]
  rw [resultant_prod_left _ _ _ _ hg hm, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← Finset.mul_sum, natDegree_prod' _ _ hg]

@[simp]
lemma resultant_pow_left (hf : f.leadingCoeff ^ m ≠ 0) (hn : g.natDegree ≤ n) :
    (f ^ m).resultant g (f ^ m).natDegree n = (f.resultant g f.natDegree n) ^ m := by
  convert resultant_prod_left (Finset.range m) (fun _ ↦ f) g n (by simpa) hn <;> simp

@[simp]
lemma resultant_pow_right (hm : f.natDegree ≤ m) (hg : g.leadingCoeff ^ n ≠ 0) :
    f.resultant (g ^ n) m (g ^ n).natDegree = (f.resultant g m g.natDegree) ^ n := by
  convert resultant_prod_right (Finset.range n) f (fun _ ↦ g) m hm (by simpa) <;> simp

lemma resultant_X_sub_C_pow_left (r : R) (g : R[X]) (m n : ℕ) (hn : g.natDegree ≤ n) :
    ((X - C r) ^ m).resultant g m n = eval r g ^ m := by
  nontriviality R
  convert resultant_pow_left _ _ _ _ _ _ <;> simp [natDegree_pow', hn]

lemma resultant_X_sub_C_pow_right (f : R[X]) (r : R) (m n : ℕ) (hm : f.natDegree ≤ m) :
    f.resultant ((X - C r) ^ n) m n = (-1) ^ (m * n) * eval r f ^ n := by
  rw [resultant_comm, resultant_X_sub_C_pow_left _ _ _ _ hm]

lemma resultant_X_pow_left (g : R[X]) (m n : ℕ) (hn : g.natDegree ≤ n) :
    (X ^ m).resultant g m n = g.coeff 0 ^ m := by
  convert resultant_X_sub_C_pow_left 0 g m n hn <;> simp [coeff_zero_eq_eval_zero]

lemma resultant_X_pow_right (f : R[X]) (m n : ℕ) (hm : f.natDegree ≤ m) :
    f.resultant (X ^ n) m n = (-1) ^ (m * n) * f.coeff 0 ^ n := by
  convert resultant_X_sub_C_pow_right f 0 m n hm <;> simp [coeff_zero_eq_eval_zero]

nonrec lemma resultant_scaleRoots (f g : R[X]) (r : R) :
    resultant (f.scaleRoots r) (g.scaleRoots r) =
      r ^ (f.natDegree * g.natDegree) * resultant f g := by
  rw [natDegree_scaleRoots, natDegree_scaleRoots]
  obtain rfl | hf := eq_or_ne f 0; · simp
  obtain rfl | hg := eq_or_ne g 0; · simp
  induction f using induction_of_Splits_of_injective_of_surjective with
  | Splits R f hf' =>
    by_cases hf0 : f.natDegree = 0
    · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hf0; simp
    by_cases hg0 : g.natDegree = 0
    · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hg0; simp
    obtain rfl | hr := eq_or_ne r 0
    · rw [scaleRoots_zero, scaleRoots_zero, Algebra.smul_def, Algebra.smul_def]
      simp [resultant_C_mul_right, resultant_X_pow_right, *, (Ne.symm hf0)]
    conv_lhs => rw [← natDegree_scaleRoots f r, ← natDegree_scaleRoots g r]
    rw [resultant_eq_prod_eval _ _ _ le_rfl hf',
      resultant_eq_prod_eval _ _ _ le_rfl (hf'.scaleRoots _),
      roots_scaleRoots _ (isUnit_iff_ne_zero.mpr hr)]
    simp only [Multiset.map_map, Function.comp_def, scaleRoots_eval_mul]
    simp only [leadingCoeff_scaleRoots, natDegree_scaleRoots, Multiset.prod_map_mul,
      Multiset.map_const', Multiset.prod_replicate, ← hf'.natDegree_eq_card_roots]
    ring
  | injective R S φ hφ f IH =>
    have := IH (g.map φ) (φ r) (by simpa using (map_injective _ hφ).ne hf)
      (by simpa using (map_injective _ hφ).ne hg)
    apply hφ
    rw [← map_scaleRoots, ← map_scaleRoots] at this
    · simpa [natDegree_map_eq_of_injective hφ] using this
    all_goals simpa [map_eq_zero_iff _ hφ]
  | surjective R S φ hφ f IH =>
    obtain ⟨f', hf', ef⟩ := Polynomial.mem_lifts_and_degree_eq (Polynomial.map_surjective φ hφ f)
    obtain ⟨g', hg', eg⟩ := Polynomial.mem_lifts_and_degree_eq (Polynomial.map_surjective φ hφ g)
    obtain ⟨r, rfl⟩ := hφ r
    have hfl : f.leadingCoeff = φ f'.leadingCoeff := by
      simp_rw [← coeff_natDegree, ← natDegree_eq_natDegree ef, ← hf', coeff_map]
    have hgl : g.leadingCoeff = φ g'.leadingCoeff := by
      simp_rw [← coeff_natDegree, ← natDegree_eq_natDegree eg, ← hg', coeff_map]
    rw [← hf', ← map_scaleRoots _ _ _ (by simpa [← hfl]), ← hg',
      ← map_scaleRoots _ _ _ (by simpa [← hgl]), hf', hg',
      ← natDegree_eq_natDegree ef, ← natDegree_eq_natDegree eg,
      resultant_map_map, IH f' g' r (by aesop) (by aesop)]
    rw [← hf', ← hg', resultant_map_map]
    simp

lemma resultant_integralNormalization (f g : R[X]) (hg : g.natDegree ≠ 0) :
    resultant (f.scaleRoots g.leadingCoeff) g.integralNormalization =
      g.leadingCoeff ^ (f.natDegree * (g.natDegree - 1)) * resultant f g := by
  rw [natDegree_scaleRoots, natDegree_integralNormalization]
  wlog hR : IsDomain R
  · by_cases hf0 : f = 0; · simp [hf0]
    by_cases hg0 : g = 0; · simp [hg0]
    let S := MvPolynomial R ℤ
    let φ : S →+* R := MvPolynomial.eval₂Hom (algebraMap _ _) id
    have hφ : Function.Surjective φ := fun x ↦ ⟨.X x, by simp [φ, MvPolynomial.eval₂Hom]⟩
    obtain ⟨f', hf', ef⟩ := Polynomial.mem_lifts_and_degree_eq (Polynomial.map_surjective φ hφ f)
    obtain ⟨g', hg', eg⟩ := Polynomial.mem_lifts_and_degree_eq (Polynomial.map_surjective φ hφ g)
    have hfl : f.leadingCoeff = φ f'.leadingCoeff := by
      simp_rw [← coeff_natDegree, ← natDegree_eq_natDegree ef, ← hf', coeff_map]
    have hgl : g.leadingCoeff = φ g'.leadingCoeff := by
      simp_rw [← coeff_natDegree, ← natDegree_eq_natDegree eg, ← hg', coeff_map]
    rw [← natDegree_eq_natDegree ef, ← natDegree_eq_natDegree eg,
      ← hf', hgl, ← map_scaleRoots _ _ _ (by simpa [← hfl]), ← hg', integralNormalization_map _ _
      (by simpa [← hgl]), resultant_map_map,
      this f' g' (by simpa [natDegree_eq_natDegree eg]) inferInstance]
    simp [resultant_map_map]
  by_cases hg0 : g = 0; · simp [hg0]
  apply mul_right_injective₀ (a := g.leadingCoeff ^ f.natDegree) (by simp [hg0])
  dsimp
  have := resultant_scaleRoots f g g.leadingCoeff
  rw [natDegree_scaleRoots, natDegree_scaleRoots,
    ← integralNormalization_mul_C_leadingCoeff, mul_comm, resultant_C_mul_right] at this
  rw [this, ← mul_assoc, ← pow_add, add_comm, ← Nat.mul_add_one, Nat.sub_add_cancel (by cutsat)]

/-- `Res(f(x + r), g(x + r)) = Res(f, g)`. -/
nonrec lemma resultant_taylor (f g : R[X]) (r : R) :
    resultant (f.taylor r) (g.taylor r) = resultant f g := by
  induction f using induction_of_Splits_of_injective_of_surjective with
  | Splits R f hf' =>
    induction hf' using Submonoid.closure_induction with
    | mem x h =>
      obtain (⟨s, rfl⟩ | ⟨s, rfl⟩) := h
      · rw [taylor_C]; simp
      · nontriviality R
        rw [map_add, taylor_X, taylor_C, add_assoc, ← map_add]
        simp [-map_add, taylor_eval]
    | one => simp
    | mul x y hx hy hx' hy' =>
      by_cases hx0 : x = 0; · simp [hx0]
      by_cases hy0 : y = 0; · simp [hy0]
      rw [taylor_mul, natDegree_mul' (by simp [*]), resultant_mul_left _ _ _ _ le_rfl]
      simp [natDegree_mul', hx0, hy0, resultant_mul_left, ← hx', ← hy']
  | injective R S φ hφ f IH =>
    apply hφ
    have := IH (g.map φ) (φ r)
    rw [← map_taylor, ← map_taylor] at this
    simpa [natDegree_map_eq_of_injective hφ] using this
  | surjective R S φ hφ f IH =>
    obtain ⟨f', hf', ef⟩ := Polynomial.mem_lifts_and_degree_eq (Polynomial.map_surjective φ hφ f)
    obtain ⟨g', hg', eg⟩ := Polynomial.mem_lifts_and_degree_eq (Polynomial.map_surjective φ hφ g)
    obtain ⟨r, rfl⟩ := hφ r
    have hfl : f.leadingCoeff = φ f'.leadingCoeff := by
      simp_rw [← coeff_natDegree, ← natDegree_eq_natDegree ef, ← hf', coeff_map]
    have hgl : g.leadingCoeff = φ g'.leadingCoeff := by
      simp_rw [← coeff_natDegree, ← natDegree_eq_natDegree eg, ← hg', coeff_map]
    rw [natDegree_taylor, natDegree_taylor, ← hf', ← map_taylor, ← hg', ← map_taylor,
      resultant_map_map, resultant_map_map, hf', hg', ← natDegree_eq_natDegree ef,
      ← natDegree_eq_natDegree eg, ← IH f' g' r, natDegree_taylor, natDegree_taylor]

end resultant

section sylvesterMap

variable {m n} {R : Type*} [CommRing R]

attribute [local simp] Polynomial.mem_degreeLT

/-- The map `(p, q) ↦ f * q + g * p` whose associated matrix is `Syl(f, g)`. -/
@[simps]
noncomputable
def sylvesterMap (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    R[X]_m × R[X]_n →ₗ[R] R[X]_(m + n) where
  toFun pq := ⟨f * pq.2 + g * pq.1, by
    obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := pq
    rw [Polynomial.mem_degreeLT]
    refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · by_cases hf' : f = 0; · simp_all
      exact (degree_mul_le _ _).trans_lt (WithBot.add_lt_add_of_le_of_lt (by simpa)
        (degree_le_of_natDegree_le hf) (by simpa using hq))
    · by_cases hg' : g = 0; · simp_all
      exact (degree_mul_le _ _).trans_lt ((WithBot.add_lt_add_of_le_of_lt (by simpa)
        (degree_le_of_natDegree_le hg) (by simpa using hp)).trans_eq (add_comm _ _))⟩
  map_add' _ _ := by ext1; dsimp; ring
  map_smul' _ _ := by ext1; simp

lemma toMatrix_sylvesterMap (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    (sylvesterMap f g hf hg).toMatrix
      ((degreeLT.basis _ _).prod (degreeLT.basis _ _)) (degreeLT.basis _ _) =
    (sylvester f g m n).reindex (.refl _) finSumFinEquiv.symm := by
  ext i (j | j)
  · suffices (if j.1 ≤ i then g.coeff (i - j) else 0) =
      if j ≤ i.1 ∧ ↑i ≤ j + n then g.coeff (i - j) else 0 by
        simpa [LinearMap.toMatrix_apply, sylvester, coeff_mul_X_pow']
    rw [ite_and]
    split_ifs with h₁ h₂ <;> try rfl
    exact coeff_eq_zero_of_natDegree_lt (by cutsat)
  · suffices (if j.1 ≤ i then f.coeff (i - j) else 0) =
      if j ≤ i.1 ∧ ↑i ≤ j + m then f.coeff (i - j) else 0 by
        simpa [LinearMap.toMatrix_apply, sylvester, coeff_mul_X_pow']
    rw [ite_and]
    split_ifs with h₁ h₂ <;> try rfl
    exact coeff_eq_zero_of_natDegree_lt (by cutsat)

lemma toMatrix_sylvesterMap' (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    (sylvesterMap f g hf hg).toMatrix
      (((degreeLT.basis _ _).prod (degreeLT.basis _ _)).reindex finSumFinEquiv)
      (degreeLT.basis _ _) = sylvester f g m n := by
  ext i j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simpa [LinearMap.toMatrix_apply] using congr($(toMatrix_sylvesterMap f g hf hg) i j)

/-- The adjugate map of the sylvester map. It takes `P` to `(p, q)` such that
`f * q + g * p = Res(f, g) * P`. -/
noncomputable
def adjSylvester (f g : R[X]) :
    R[X]_(m + n) →ₗ[R] R[X]_m × R[X]_n :=
  (f.sylvester g m n).adjugate.toLin (degreeLT.basis R (m + n))
    (((degreeLT.basis R m).prod (degreeLT.basis R n)).reindex finSumFinEquiv)

lemma sylveserMap_comp_adjSylvester (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    sylvesterMap f g hf hg ∘ₗ adjSylvester f g = f.resultant g m n • LinearMap.id := by
  let b₁ := ((degreeLT.basis R m).prod (degreeLT.basis R n)).reindex finSumFinEquiv
  let b₂ := degreeLT.basis R (m + n)
  have := congr(Matrix.toLin b₂ b₂ $(((sylvesterMap f g hf hg).toMatrix b₁ b₂).mul_adjugate))
  rwa [Matrix.toLin_mul b₂ b₁ b₂, Matrix.toLin_toMatrix, map_smul,
    toMatrix_sylvesterMap', Matrix.toLin_one, ← resultant] at this

lemma adjSylvester_comp_sylveserMap (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    adjSylvester f g ∘ₗ sylvesterMap f g hf hg = f.resultant g m n • LinearMap.id := by
  let b₁ := ((degreeLT.basis R m).prod (degreeLT.basis R n)).reindex finSumFinEquiv
  let b₂ := degreeLT.basis R (m + n)
  have := congr(Matrix.toLin b₁ b₁ $(((sylvesterMap f g hf hg).toMatrix b₁ b₂).adjugate_mul))
  rwa [Matrix.toLin_mul b₁ b₂ b₁, Matrix.toLin_toMatrix, map_smul,
    toMatrix_sylvesterMap', Matrix.toLin_one, ← resultant] at this

/-- Note that if `n = m = 0` then `resultant = 1` but `f` and `g` aren't necessarily coprime. -/
lemma exists_mul_add_mul_eq_C_resultant
    (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (H : m ≠ 0 ∨ n ≠ 0) :
    ∃ p q, p.degree < ↑n ∧ q.degree < ↑m ∧ f * p + g * q = C (f.resultant g m n) := by
  nontriviality R
  let X := adjSylvester f g ⟨1, by simpa [Polynomial.mem_degreeLT,
    ← Nat.cast_add, Nat.pos_iff_ne_zero, not_and_or, -not_and] using H⟩
  have : ((sylvesterMap f g hf hg X)).1 = _ :=
    congr(($(sylveserMap_comp_adjSylvester f g hf hg) _).1)
  refine ⟨X.2, X.1, by simpa [-SetLike.coe_mem] using X.2.2,
    by simpa [-SetLike.coe_mem] using X.1.2, by simpa [Algebra.smul_def] using this⟩

lemma isUnit_resultant_iff_isCoprime {f g : R[X]} (hf : f.Monic) :
    IsUnit (resultant f g) ↔ IsCoprime f g := by
  by_cases hf0 : f.natDegree = 0
  · obtain rfl := eq_one_of_monic_natDegree_zero hf hf0; simp [isCoprime_one_left]
  refine ⟨fun H ↦ ?_, ?_⟩
  · obtain ⟨p, q, hp, hq, e⟩ := exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl (by simp [hf0])
    exact ⟨C (H.unit⁻¹).1 * p, C (H.unit⁻¹).1 * q, by simp only [mul_assoc, ← mul_add, mul_comm p,
      mul_comm q, e, ← map_mul, IsUnit.val_inv_mul, map_one]⟩
  · intro ⟨a, b, e⟩
    suffices 1 = f.resultant b * f.resultant g from isUnit_iff_exists_inv'.mpr ⟨_, this.symm⟩
    have := resultant_mul_right f b g _ le_rfl
    obtain rfl | hb0 := eq_or_ne a 0
    · rw [show b * g = 1 by simpa using e, resultant_one_right] at this
      simpa [hf.leadingCoeff] using this
    · rw [← resultant_add_mul_right _ _ a _ _ _ le_rfl, add_comm, mul_comm, e, ← C.map_one] at this
      · simpa [hf.leadingCoeff] using this
      · by_contra! H
        replace H := natDegree_mul_le.trans_lt H
        rw [add_comm, ← hf.natDegree_mul' hb0, mul_comm f] at H
        have := natDegree_add_eq_left_of_natDegree_lt H
        simp only [e, natDegree_one] at this
        cutsat

lemma resultant_eq_zero_iff {K : Type*} [Field K] {f g : K[X]} :
    resultant f g = 0 ↔ (f ≠ 0 ∨ g ≠ 0) ∧ ¬ IsCoprime f g := by
  obtain rfl | hf := eq_or_ne f 0
  · obtain rfl | hg := eq_or_ne g 0; · simp
    simpa [isCoprime_zero_left, isUnit_iff, hg, natDegree_eq_zero] using
      show (∀ x, C x ≠ g) ↔ ∀ x ≠ 0, C x ≠ g by aesop
  have H : (C f.leadingCoeff⁻¹ * f).Monic := by
    rw [Monic, ← coeff_natDegree, natDegree_C_mul (by simpa), coeff_C_mul]; simp [hf]
  have := isUnit_resultant_iff_isCoprime (f := C f.leadingCoeff⁻¹ * f) (g := g) H
  rw [resultant_C_mul_left, IsUnit.mul_iff, natDegree_C_mul (by simp [hf]),
    isCoprime_mul_unit_left_left (isUnit_C.mpr (by simp [hf]))] at this
  simp [← this, hf]

end sylvesterMap

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
