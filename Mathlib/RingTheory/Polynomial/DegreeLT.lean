/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kenny Lau
-/

import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomials with degree less than `n`

This file contains the properties of the submodule of polynomials of degree less than `n` in a
commutative ring `R`, denoted `R[X]_n`.

The main result is a basis for this submodule, given by the monomials `X^i` for `i < n`.

-/


variable {R : Type*} [Semiring R] {m n : ℕ}

namespace Polynomial

/-- R[X]_n is notation for the submodule of polynomials of degree strictly less than n. -/
scoped notation:9000 R "[x]_" n => Polynomial.degreeLT R n

section degreeLT

variable (R)

/-- Basis for R[X]_n given by the `X^i` with `i < n`. -/
noncomputable def degreeLT.basis (n : ℕ) : Basis (Fin n) R R[x]_n :=
  Basis.ofEquivFun (Polynomial.degreeLTEquiv R n)

lemma degreeLT_X_pow_mem {n : ℕ} (i : Fin n) : X ^ i.val ∈ R[x]_n := by
  nontriviality R using mem_degreeLT, WithBot.bot_lt_iff_ne_bot
  simp only [Polynomial.mem_degreeLT, Polynomial.degree_X_pow, Nat.cast_lt, Fin.is_lt]

@[simp] lemma degreeLT.basis_val (n : ℕ) (i : Fin n) :
    (degreeLT.basis R n i : R[X]) = X ^ i.val := by
  simp only [degreeLT.basis, degreeLTEquiv, Basis.coe_ofEquivFun,
    LinearEquiv.coe_symm_mk]
  rw [Finset.sum_eq_single i (by aesop) (by aesop),
      Pi.single_eq_same, monomial_one_right_eq_X_pow]

lemma degreeLT.basis_apply (n : ℕ) (i : Fin n) :
    degreeLT.basis R n i = ⟨X ^ i.val, degreeLT_X_pow_mem R i⟩ :=
  Subtype.ext <| degreeLT.basis_val R n i

@[simp] lemma degreeLT.basis_repr {n} (P : R[x]_n) (i : Fin n) :
    (degreeLT.basis R n).repr P i = (P : R[X]).coeff i :=
  Basis.ofEquivFun_repr_apply _ _ _

instance : Module.Finite R R[x]_n :=
  Module.Finite.of_basis (degreeLT.basis _ _)

/-- Basis for R[X]_m × R[X]_n. -/
noncomputable def degreeLT.basis_prod (m n : ℕ) : Basis (Fin (m + n)) R ((R[x]_m) × (R[x]_n)) :=
  ((degreeLT.basis R m).prod (degreeLT.basis R n)).reindex finSumFinEquiv

@[simp] lemma degreeLT.basis_prod_castAdd (m n : ℕ) (i : Fin m) :
    basis_prod R m n (i.castAdd n) = (⟨X ^ i.val, degreeLT_X_pow_mem R i⟩, 0) := by
  rw [basis_prod, Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd]
  ext
  · rw [Basis.prod_apply_inl_fst, basis_apply]
  · rw [Basis.prod_apply_inl_snd]

@[simp] lemma degreeLT.basis_prod_natAdd (m n : ℕ) (i : Fin n) :
    basis_prod R m n (i.natAdd m) = (0, ⟨X ^ i.val, degreeLT_X_pow_mem R i⟩) := by
  rw [basis_prod, Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd]
  ext
  · rw [Basis.prod_apply_inr_fst]
  · rw [Basis.prod_apply_inr_snd, basis_apply]

noncomputable def degreeLT.addLinearEquiv {n m : ℕ} :
    (R[x]_(n + m)) ≃ₗ[R] (R[x]_n) × (R[x]_m) :=
  Basis.equiv (degreeLT.basis _ _) (degreeLT.basis_prod _ _ _) (Equiv.refl _)

end degreeLT

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

end Polynomial
