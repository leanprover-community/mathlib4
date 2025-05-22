/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kenny Lau
-/

import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomials with degree less than `n`

This file contains the properties of the submodule of polynomials of degree less than `n` in a
commutative ring `R`, denoted `R[X]_n`.

The main result is a basis for this submodule, given by the monomials `X^i` for `i < n`.

-/


namespace Polynomial

/-- R[X]_n is notation for the submodule of polynomials of degree strictly less than n. -/
scoped notation:9000 R "[x]_" n => Polynomial.degreeLT R n

section degreeLT

variable {R : Type*} [Semiring R] {m n : ℕ} (i : Fin n) (P : R[x]_n)

variable (R) in
/-- Basis for R[X]_n given by the `X^i` with `i < n`. -/
noncomputable def degreeLT.basis (n : ℕ) : Basis (Fin n) R R[x]_n :=
  Basis.ofEquivFun (Polynomial.degreeLTEquiv R n)

instance : Module.Free R R[x]_n :=
  Module.Free.of_basis <| degreeLT.basis R n

lemma degreeLT_X_pow_mem (i : Fin n) : X ^ i.val ∈ R[x]_n := by
  nontriviality R using mem_degreeLT, WithBot.bot_lt_iff_ne_bot
  simp only [Polynomial.mem_degreeLT, Polynomial.degree_X_pow, Nat.cast_lt, Fin.is_lt]

@[simp] lemma degreeLT.basis_val (i : Fin n) :
    (degreeLT.basis R n i : R[X]) = X ^ i.val := by
  simp only [degreeLT.basis, degreeLTEquiv, Basis.coe_ofEquivFun,
    LinearEquiv.coe_symm_mk]
  rw [Finset.sum_eq_single i (by aesop) (by aesop),
      Pi.single_eq_same, monomial_one_right_eq_X_pow]

lemma degreeLT.basis_apply (i : Fin n) :
    degreeLT.basis R n i = ⟨X ^ i.val, degreeLT_X_pow_mem i⟩ :=
  Subtype.ext <| degreeLT.basis_val i

@[simp] lemma degreeLT.basis_repr : (degreeLT.basis R n).repr P i = (P : R[X]).coeff i :=
  Basis.ofEquivFun_repr_apply _ _ _

instance : Module.Finite R R[x]_n :=
  Module.Finite.of_basis (degreeLT.basis _ _)

variable (R) in
/-- Basis for R[X]_m × R[X]_n. -/
noncomputable def degreeLT.basis_prod (m n : ℕ) : Basis (Fin (m + n)) R ((R[x]_m) × (R[x]_n)) :=
  ((degreeLT.basis R m).prod (degreeLT.basis R n)).reindex finSumFinEquiv

@[simp] lemma degreeLT.basis_prod_castAdd (m n : ℕ) (i : Fin m) :
    basis_prod R m n (i.castAdd n) = (⟨X ^ i.val, degreeLT_X_pow_mem i⟩, 0) := by
  rw [basis_prod, Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd]
  ext
  · rw [Basis.prod_apply_inl_fst, basis_apply]
  · rw [Basis.prod_apply_inl_snd]

@[simp] lemma degreeLT.basis_prod_natAdd (m n : ℕ) (i : Fin n) :
    basis_prod R m n (i.natAdd m) = (0, ⟨X ^ i.val, degreeLT_X_pow_mem i⟩) := by
  rw [basis_prod, Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd]
  ext
  · rw [Basis.prod_apply_inr_fst]
  · rw [Basis.prod_apply_inr_snd, basis_apply]

noncomputable def degreeLT.addLinearEquiv {n m : ℕ} :
    (R[x]_(n + m)) ≃ₗ[R] (R[x]_n) × (R[x]_m) :=
  Basis.equiv (degreeLT.basis _ _) (degreeLT.basis_prod _ _ _) (Equiv.refl _)

@[aesop unsafe 50%]
theorem degree_add_lt_of_degree_lt {p q : R[X]} {n : ℕ}
    (hp : degree p < n) (hq : degree q < n) :
    degree (p + q) < n :=
  (degree_add_le p q).trans_lt <| max_lt hp hq

@[aesop unsafe 50%]
theorem degree_mul_lt_of_lt_left {p q : R[X]} {a : WithBot ℕ} {b : ℕ}
    (hp : degree p < a) (hq : degree q ≤ b) :
    degree (p * q) < a + b := by
  by_cases hq0 : q.degree = ⊥
  · rw [degree_eq_bot] at hq0
    rw [hq0, mul_zero, degree_zero, WithBot.bot_lt_add]
    simp [WithBot.bot_lt_iff_ne_bot, ne_bot_of_gt hp]
  · exact (degree_mul_le _ _).trans_lt (WithBot.add_lt_add_of_lt_of_le hq0 hp hq)

@[aesop unsafe 50%]
theorem degree_mul_lt_of_lt_right {p q : R[X]} {a : ℕ} {b : WithBot ℕ}
    (hp : degree p ≤ a) (hq : degree q < b) :
    degree (p * q) < a + b := by
  by_cases hp0 : p.degree = ⊥
  · rw [degree_eq_bot] at hp0
    rw [hp0, zero_mul, degree_zero, WithBot.bot_lt_add]
    simp [WithBot.bot_lt_iff_ne_bot, ne_bot_of_gt hq]
  · exact (degree_mul_le _ _).trans_lt (WithBot.add_lt_add_of_le_of_lt hp0 hp hq)

lemma mul_left_mem_degreeLT {n} (p q : R[X]) (hp : degree p ≤ m) (hq : q ∈ R[x]_n) :
    p * q ∈ R[x]_(m + n) := by
  rw [mem_degreeLT] at *
  exact degree_mul_lt_of_lt_right hp hq

lemma mul_left_mem_degreeLT' {n} (p q : R[X]) (hp : degree p ≤ m) (hq : q ∈ R[x]_n) :
    p * q ∈ R[x]_(n + m) := by
  rw [add_comm]
  exact mul_left_mem_degreeLT _ _ ‹_› ‹_›

lemma mul_right_mem_degreeLT {m} (p q : R[X]) (hp : p ∈ R[x]_m) (hq : degree q ≤ n) :
    p * q ∈ R[x]_(m + n) := by
  rw [mem_degreeLT] at *
  exact degree_mul_lt_of_lt_left hp hq

lemma mul_right_mem_degreeLT' {m} (p q : R[X]) (hp : p ∈ R[x]_m) (hq : degree q ≤ n) :
    p * q ∈ R[x]_(n + m) := by
  rw [add_comm]
  exact mul_right_mem_degreeLT _ _ ‹_› ‹_›

end degreeLT

section translate

variable {R : Type*} [CommRing R] {x : R} {m n : ℕ} {a : R} {f g : R[X]}

variable (x) in
/-- TO MOVE? -/
noncomputable def translate : R[X] ≃+* R[X] where
  invFun    := (.X - .C (-x) : R[X]).compRingHom
  left_inv  := fun P ↦ by simp [comp_assoc]
  right_inv := fun P ↦ by simp [comp_assoc]
  __ := (.X - .C x : R[X]).compRingHom

lemma translate_apply : f.translate x = f.comp (.X - .C x) :=
  rfl

@[simp] lemma translate_symm_apply : (translate x).symm f = f.translate (-x) :=
  rfl

@[simp] lemma translate_C : (C a).translate x = C a :=
  C_comp

@[simp] lemma translate_smul : (a • f).translate x = a • f.translate x := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, translate_C]

lemma natDegree_translate_le : (f.translate x).natDegree ≤ f.natDegree :=
  natDegree_comp_le.trans <| by nontriviality R; rw [natDegree_X_sub_C, mul_one]

lemma natDegree_translate : (f.translate x).natDegree = f.natDegree := by
  refine eq_of_le_of_le natDegree_translate_le ?_
  conv_lhs => rw [← (translate x).symm_apply_apply f, translate_symm_apply]
  exact natDegree_translate_le

lemma degree_translate : (f.translate x).degree = f.degree := by
  by_cases h : f = 0
  · rw [h, map_zero]
  · rw [degree_eq_natDegree h, degree_eq_natDegree ((translate x).map_ne_zero_iff.2 h),
      natDegree_translate]

variable (x n) in
noncomputable def translateLinear : (R[x]_n) ≃ₗ[R] (R[x]_n) where
  toFun := fun P ↦ ⟨P.1.translate x, mem_degreeLT.2 <| degree_translate.trans_lt <|
    mem_degreeLT.1 P.2⟩
  invFun := fun P ↦ ⟨P.1.translate (-x), mem_degreeLT.2 <| degree_translate.trans_lt <|
    mem_degreeLT.1 P.2⟩
  map_add' := fun _ _↦ Subtype.ext <| map_add _ _ _
  map_smul' := fun _ _ ↦ Subtype.ext translate_smul
  left_inv := fun _ ↦ Subtype.ext <| (Polynomial.translate x).symm_apply_apply _
  right_inv := fun _ ↦ Subtype.ext <| (Polynomial.translate x).apply_symm_apply _

@[simp] lemma translateLinear_apply (P : R[x]_n) :
    (translateLinear x n P : R[X]) = (P : R[X]).translate x :=
  rfl

@[simp] theorem translate_det' :
    LinearMap.det (translateLinear x n : (R[x]_n) →ₗ[R] _) = 1 := by
  nontriviality R
  rw [← LinearMap.det_toMatrix (degreeLT.basis R n),
    Matrix.det_of_upperTriangular, Fintype.prod_eq_one]
  · intro i
    rw [LinearMap.toMatrix_apply, degreeLT.basis_apply, LinearEquiv.coe_coe, degreeLT.basis_repr,
      translateLinear_apply, translate_apply, pow_comp, X_comp, sub_eq_add_neg, ← C_neg,
      coeff_X_add_C_pow, Nat.sub_self, pow_zero, one_mul, Nat.choose_self, Nat.cast_one]
  · intro i j hji
    rw [LinearMap.toMatrix_apply, degreeLT.basis_apply, LinearEquiv.coe_coe, degreeLT.basis_repr]
    refine coeff_eq_zero_of_degree_lt ?_
    rwa [translateLinear_apply, degree_translate, degree_X_pow, Nat.cast_lt, Fin.val_fin_lt]

@[simp] theorem translate_det :
    (translateLinear x n).det = 1 :=
  Units.ext <| by rw [LinearEquiv.coe_det, translate_det', Units.val_one]

variable (x m n) in
noncomputable def translateProd : ((R[x]_m) × (R[x]_n)) ≃ₗ[R] ((R[x]_m) × (R[x]_n)) :=
  (translateLinear x m).prodCongr (translateLinear x n)

@[simp] lemma translateProd_apply (P : (R[x]_m) × (R[x]_n)) :
    translateProd x m n P = (translateLinear x m P.1, translateLinear x n P.2) := rfl

theorem translateProd_det' :
    (translateProd x m n : ((R[x]_m) × (R[x]_n)) →ₗ[R] _).det = 1 := by
  rw [translateProd, LinearEquiv.coe_prodCongr, LinearMap.det_prodMap,
    translate_det', translate_det', one_mul]

theorem translateProd_det :
    (translateProd x m n).det = 1 :=
  Units.ext <| by rw [LinearEquiv.coe_det, translateProd_det', Units.val_one]

end translate

end Polynomial
