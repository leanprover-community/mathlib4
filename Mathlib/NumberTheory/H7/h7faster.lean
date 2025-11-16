/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.H7.h7aux
import Mathlib.NumberTheory.H7.h7order
import Mathlib.NumberTheory.H7.House

set_option autoImplicit true
set_option linter.style.longFile 0
set_option linter.unusedTactic false
set_option linter.style.multiGoal false
set_option linter.style.longLine true
set_option linter.style.commandStart false
set_option linter.unusedSectionVars false
set_option linter.style.cdot false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.cases false

/-!
# Hilbert's Seventh Problem (Gelfond–Schneider Theorem)
The goal of this file is to formalize a proof of the **Gelfond–Schneider Theorem**, which solves
Hilbert’s Seventh Problem: namely, that for algebraic numbers `α ≠ 0, 1` and irrational algebraic
`β`, the number `α ^ β` is transcendental.

## Main results
* `gelfondSchneider`: If `α` and `β` are algebraic, `α ≠ 0`, `α ≠ 1`, and `β` is irrational, then
  `α ^ β` is transcendental.

## Implementation details
We follow the proof in Keng’s *Introduction to Number Theory*, Chapter 9, Section 5.

The structure of the proof is as follows:

* The argument proceeds by **contradiction**, assuming `a ^ b` is algebraic, and constructing a
  sequence of algebraic numbers that violate Liouville’s inequality for algebraic numbers.
* The core of the proof is an **auxiliary function lemma**, where we construct a nonzero integer
  linear combination of exponential functions that vanishes to high order at several algebraic
  points.

This is a version of **Siegel’s lemma** applied to the exponential case.
* Using estimates on the size of the coefficients and derivatives of `f`, one shows that both
`f(0)` and `f(b log a)` must be small, yet not zero, contradicting the transcendence bounds
for algebraic numbers.
* The analytic bounds on the derivatives of `f` rely on standard estimates for the exponential
function, while the algebraic part depends on **Liouville-type inequalities** and the
algebraic independence of exponential values.

Conceptually, the theorem connects transcendence theory, Diophantine approximation, and the
arithmetic of exponential functions, forming one of the cornerstones of modern transcendental
number theory.

## References
Loo-Keng Hua, Introduction to Number Theory, Springer, 1982. Chapter XII (§13).
A. O. Gelfond (1934), *Sur le septième Problème de Hilbert
T. Schneider (1934), *Transzendenzuntersuchungen periodischer Funktionen*
Lang, S. Introduction to Transcendental Numbers, Springer (1966)
-/

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
  Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section
/--
This structure encapsulates all the foundational data and hypotheses for the proof.
-/
structure GelfondSchneiderSetup where
  (α β : ℂ)
  (K : Type)
  [isField : Field K]
  [isNumberField : NumberField K]
  (σ : K →+* ℂ)
  (α' β' γ' : K)
  hirr : ∀ i j : ℤ, β ≠ i / j
  htriv : α ≠ 0 ∧ α ≠ 1
  hα : IsAlgebraic ℚ α
  hβ : IsAlgebraic ℚ β
  habc : α = σ α' ∧ β = σ β' ∧ α ^ β = σ γ'
  hd : DecidableEq (K →+* ℂ)

namespace GelfondSchneiderSetup

-- This tells Lean to automatically use the Field and NumberField instances
-- whenever it sees a variable of type `GelfondSchneiderSetup`.
attribute [instance] isField isNumberField

variable (h7 : GelfondSchneiderSetup)

open GelfondSchneiderSetup

lemma γneq0 : h7.α ^ h7.β ≠ 0 :=
  fun H => h7.htriv.1 ((cpow_eq_zero_iff h7.α h7.β).mp H).1

lemma βneq0 : h7.β ≠ 0 :=
  fun H => h7.hirr 0 1 (by simpa [div_one] using H)

lemma hneq0 : h7.α' ≠ 0 ∧ h7.β' ≠ 0 ∧ h7.γ' ≠ 0 := by
  constructor
  · intro H
    exact h7.htriv.1 (h7.habc.1 ▸ H ▸ RingHom.map_zero h7.σ)
  · constructor
    · intro H
      exact h7.βneq0 (h7.habc.2.1 ▸ H ▸ RingHom.map_zero h7.σ)
    · intro H
      exact h7.γneq0 (h7.habc.2.2 ▸ H ▸ RingHom.map_zero h7.σ)

lemma hneq1 : h7.α' ≠ 1 := by
  intro H
  apply_fun h7.σ at H
  rw [← h7.habc.1, map_one] at H
  exact h7.htriv.2 H

lemma β'ne_zero : h7.β' ≠ 0 := h7.hneq0.2.1

open Complex

lemma log_zero_zero : log h7.α ≠ 0 := by
  intro H
  have := congr_arg exp H
  rw [exp_log, exp_zero] at this
  · apply h7.htriv.2 this
  · exact h7.htriv.1

def c₁ : ℤ := abs (c' h7.α' * c' h7.β' * c' h7.γ')

lemma one_leq_c₁ : 1 ≤ h7.c₁ := by
  have h := (mul_ne_zero (mul_ne_zero (c'_neq0 h7.α')
    (c'_neq0 h7.β')) (c'_neq0 h7.γ'))
  exact Int.one_le_abs h

lemma zero_leq_c₁ : 0 ≤ h7.c₁ :=
  le_trans Int.one_nonneg h7.one_leq_c₁

lemma c₁_neq_zero : h7.c₁ ≠ 0 :=
  Ne.symm (Int.ne_of_lt h7.one_leq_c₁)

lemma one_leq_abs_c₁ : 1 ≤ |↑h7.c₁| := by
  refine Int.one_le_abs (c₁_neq_zero h7)

lemma isIntegral_c₁α : IsIntegral ℤ (h7.c₁ • h7.α') := by
  have h := IsIntegral_assoc (x := c' h7.γ') (y := c' h7.β') h7.K (c' h7.α') h7.α'
    (c'_IsIntegral h7.α')
  conv => enter [2]; rw [c₁, mul_comm, mul_comm (c' h7.α') (c' h7.β'), ← mul_assoc]
  rcases abs_choice (c' h7.γ' * c' h7.β' * c' h7.α')
  · rename_i H1; rw [H1]; exact h
  · rename_i H2; rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁β : IsIntegral ℤ (h7.c₁ • h7.β') := by
  have h := IsIntegral_assoc (x := c' h7.γ') (y := c' h7.α') h7.K (c' h7.β') h7.β'
    (c'_IsIntegral h7.β')
  rw [c₁, mul_comm, ← mul_assoc]
  rcases abs_choice (c' h7.γ' * c' h7.α' * c' h7.β')
  · rename_i H1; rw [H1]; exact h
  · rename_i H2; rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁γ : IsIntegral ℤ (h7.c₁ • h7.γ') := by
  have h := IsIntegral_assoc (x := c' h7.α') (y := c' h7.β') h7.K (c' h7.γ') h7.γ'
    (c'_IsIntegral h7.γ')
  rw [c₁]
  rcases abs_choice (c' h7.α' * c' h7.β' * c' h7.γ')
  · rename_i H1; rw [H1]; exact h
  · rename_i H2; rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

def h : ℕ := Module.finrank ℚ h7.K

def m : ℕ := 2 * h7.h + 2

lemma one_le_m : 1 ≤ h7.m := by
  unfold m;
  rw [le_iff_lt_or_eq]
  left
  trans
  apply one_lt_two
  simp only [lt_add_iff_pos_left, Nat.ofNat_pos,
  mul_pos_iff_of_pos_left]
  unfold h; exact Module.finrank_pos

-- `q` is a parameter, so it remains an argument.
def n (q : ℕ) : ℕ := q ^ 2 / (2 * h7.m)

-- These are parameters for the auxiliary function construction.
variable (q : ℕ) (hq0 : 0 < q)
variable (u : Fin (h7.m * h7.n q))
variable (t : Fin (q * q))

-- `a, b, k, l` are values that depend on the context variables `t` and `u`.
def a : ℕ := (finProdFinEquiv.symm.toFun t).1 + 1
def b : ℕ := (finProdFinEquiv.symm.toFun t).2 + 1
def k : ℕ := (finProdFinEquiv.symm.toFun u).2
def l : ℕ := (finProdFinEquiv.symm.toFun u).1 + 1

lemma b_le_q : b q t ≤ q :=
  bar' (finProdFinEquiv.symm.toFun t).2

lemma l_le_m : h7.l q u ≤ h7.m :=
  bar' (finProdFinEquiv.symm.toFun u).1

lemma a_le_q : a q t ≤ q :=
  bar' (finProdFinEquiv.symm.toFun t).1

lemma k_le_n_sub1 : (h7.k q u : ℤ) ≤ (h7.n q - 1 : ℤ) := by
  rw [sub_eq_add_neg]
  have : (k h7 q u : ℤ) + 1 ≤ ↑(h7.n q) → (h7.k q u : ℤ) ≤ ↑(h7.n q) + -1 := by
    simp only [Int.reduceNeg, le_add_neg_iff_add_le, imp_self]
  apply this
  norm_cast
  exact bar' (finProdFinEquiv.symm.toFun u).2

lemma al_leq_mq : a q t * h7.l q u ≤ q * h7.m := by
  apply mul_le_mul (a_le_q q t) (h7.l_le_m q u) (zero_le _) (zero_le _)

lemma bl_leq_mq : b q t * h7.l q u ≤ q * h7.m := by
  apply mul_le_mul (b_le_q q t) (h7.l_le_m q u) (zero_le _) (zero_le _)

lemma k_le_n : k h7 q u  ≤ h7.n q := Fin.is_le'

abbrev c_coeffs0 (q : ℕ)
(u : Fin (h7.m * h7.n q)) (t : Fin (q * q)) :=
  h7.c₁^(h7.k q u : ℕ) * h7.c₁^ (a q t * h7.l q u) * h7.c₁^(b q t * h7.l q u)

lemma c₁ac (u : h7.K) (n k a l : ℕ) (hnk : a * l ≤ n * k)
    (H : IsIntegral ℤ (↑h7.c₁ * u)) :
    IsIntegral ℤ (h7.c₁ ^ (n * k) • u ^ (a *l)) := by
  have : h7.c₁ ^ (n * k) = h7.c₁ ^ (n * k - a * l) * h7.c₁ ^ (a *l) := by
    rw [← pow_add]; rwa [Nat.sub_add_cancel]
  rw [this, zsmul_eq_mul]
  simp only [Int.cast_mul, Int.cast_pow]; rw [mul_assoc]
  apply IsIntegral.mul
  · apply IsIntegral.pow _ _
    exact IsIntegral.Cast h7.K h7.c₁
  rw [← mul_pow]; exact IsIntegral.pow H _

lemma c₁b (n : ℕ) :
    1 ≤ n → (k : ℕ) → k ≤ n - 1 → (a : ℕ) → 1 ≤ a → (b : ℕ) → 1 ≤ b →
    IsIntegral ℤ (h7.c₁ ^ (n - 1) • (↑a + ↑b • h7.β') ^ k) := by
  intros hn k hkn a ha b hb
  have : h7.c₁^(n - 1) = h7.c₁^(n - 1 - k) * h7.c₁^k := by
    rwa [← pow_add, Nat.sub_add_cancel]
  rw [this]
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, nsmul_eq_mul, mul_assoc]
  apply IsIntegral.mul
  · apply IsIntegral.pow
    · apply IsIntegral.Cast
  rw [← mul_pow]
  apply IsIntegral.pow
  rw [mul_add]
  apply IsIntegral.add
  · apply IsIntegral.mul <| IsIntegral.Cast _ _
    · apply IsIntegral.Nat
  rw [mul_comm, mul_assoc]
  apply IsIntegral.mul <| IsIntegral.Nat _ _
  rw [mul_comm, ← zsmul_eq_mul]
  exact isIntegral_c₁β h7

open Nat in include hq0 in omit hq0 in
lemma c1a0 :
 IsIntegral ℤ (h7.c₁ ^ (a q t * h7.l q u) • (h7.α' ^ (a q t * h7.l q u : ℕ))) := by
  apply h7.c₁ac h7.α' (a q t) (h7.l q u) (a q t) (h7.l q u) ?_ ?_
  · rw [mul_comm]
  · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁α

open Nat in include hq0 in omit hq0 in
lemma c1c0 :
    IsIntegral ℤ (h7.c₁ ^ (b q t * h7.l q u) • (h7.γ'^ (b q t * (h7.l q u) : ℕ))) := by
  apply h7.c₁ac h7.γ' (b q t) (h7.l q u) (b q t) (h7.l q u) ?_ ?_
  · rw [mul_comm]
  · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁γ

open Nat in include hq0 in
lemma c1a :
 IsIntegral ℤ (h7.c₁^(h7.m * q) • (h7.α' ^ (a q t * h7.l q u : ℕ))) := by
  apply h7.c₁ac h7.α' (h7.m) q (a q t) (h7.l q u) ?_ ?_
  · rw [mul_comm]
    exact Nat.mul_le_mul
      (add_le_of_le_sub (le_of_ble_eq_true rfl)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).1.isLt))
      (add_le_of_le_sub hq0 (le_sub_one_of_lt ((finProdFinEquiv.symm.1 t).1).isLt))
  · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁α

open Nat in include hq0 in
lemma c1c : IsIntegral ℤ (h7.c₁ ^ (h7.m * q) • (h7.γ'^ (b q t * h7.l q u : ℕ))) := by
  apply h7.c₁ac h7.γ' (h7.m) q (b q t) (h7.l q u) ?_ ?_
  · rw [mul_comm]
    exact Nat.mul_le_mul
      (add_le_of_le_sub (le_of_ble_eq_true rfl)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).1.isLt))
        (add_le_of_le_sub hq0 (le_sub_one_of_lt
        (finProdFinEquiv.symm.1 t).2.isLt))
  · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁γ

abbrev sys_coe : h7.K := (a q t + b q t • h7.β')^(h7.k q u) *
h7.α' ^(a q t * h7.l q u) * h7.γ' ^((b q t) * h7.l q u)

variable (h2mq : 2 * h7.m ∣ q ^ 2)

include h2mq in
lemma q_eq_2sqrtmn : q^2 = 2*h7.m*h7.n q := by
  refine Eq.symm (Nat.mul_div_cancel' h2mq)

include h2mq in
lemma q_eq_sqrtmn : q = Real.sqrt (2*h7.m*h7.n q) := by
  norm_cast
  rw [← q_eq_2sqrtmn h7 q h2mq]
  simp only [Nat.cast_pow, Nat.cast_nonneg, Real.sqrt_sq]

include hq0 h2mq in
lemma card_mn_pos : 0 < h7.m * h7.n q := by
  simp only [CanonicallyOrderedAdd.mul_pos]
  constructor
  · exact Nat.zero_lt_succ (2 * h7.h + 1)
  · dsimp [n]
    simp only [Nat.div_pos_iff, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    constructor
    · exact Nat.zero_lt_succ (2 * h7.h + 1)
    apply Nat.le_of_dvd
    · positivity
    exact h2mq

include hq0 h2mq in
lemma one_le_n : 1 ≤ h7.n q := by {
  dsimp only [n]
  rw [Nat.one_le_div_iff]
  · apply Nat.le_of_dvd (Nat.pow_pos hq0) h2mq
  · exact Nat.zero_lt_succ (Nat.mul 2 (2 * h7.h + 1) + 1)}

include hq0 h2mq in
lemma n_neq_0 : h7.n q ≠ 0 := Nat.ne_zero_of_lt (one_le_n h7 q hq0 h2mq)

include hq0 h2mq in
lemma qsqrt_leq_2m : 2 * h7.m ≤ q^2 := by {
  apply Nat.le_of_dvd (Nat.pow_pos hq0) h2mq}

-- include hq0 h2mq in
-- lemma one_lt_n : 1 < h7.n q := by
--   dsimp only [n]
--   refine (Nat.lt_div_iff_mul_lt_of_dvd ?_ h2mq).mpr ?_
--   simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
--   unfold m
--   exact Nat.add_one_ne_zero (2 * h7.h + 1)
--   simp only [one_mul]
--   rw [h7.q_eq_2sqrtmn q h2mq]


lemma hm : 0 < h7.m := Nat.zero_lt_succ (2 * h7.h + 1)

include hq0 h2mq in
lemma h0m : 0 < h7.m * h7.n q :=
  mul_pos (h7.hm) (one_le_n h7 q hq0 h2mq)

include hq0 h2mq in
lemma hmn : h7.m * h7.n q < q*q := by
  rw [← Nat.mul_div_eq_iff_dvd] at h2mq
  rw [← pow_two q, ← mul_lt_mul_left (Nat.zero_lt_two)]
  rw [← mul_assoc, n, h2mq, lt_mul_iff_one_lt_left]
  · exact one_lt_two
  · exact Nat.pow_pos hq0

include h2mq in
lemma sq_le_two_mn : q^2 ≤ 2 * h7.m * h7.n q := by
  dsimp only [n]
  refine Nat.le_sqrt'.mp ?_
  rw [← Nat.mul_div_eq_iff_dvd] at h2mq
  refine Nat.le_sqrt'.mpr ?_
  nth_rw 1 [← h2mq]

include h2mq in
lemma q_le_two_mn : q ≤ 2 * h7.m * h7.n q := by
  calc q ≤ q^2 := Nat.le_pow (Nat.zero_lt_two)
       _ ≤ _ := (sq_le_two_mn h7 q h2mq)

lemma n_sub_1_le_n :
  h7.n q - 1 ≤ h7.n q := Nat.sub_le (h7.n q) 1

abbrev c_coeffs (q : ℕ) := h7.c₁^(h7.n q - 1) * h7.c₁^(h7.m * q) * h7.c₁^(h7.m * q)

open Nat in include hq0 h2mq in
lemma c₁IsInt (u : Fin (h7.m * h7.n q)) (t : Fin (q * q)) :
  IsIntegral ℤ (h7.c_coeffs q • h7.sys_coe q u t) := by
  unfold c_coeffs
  unfold sys_coe
  rw [triple_comm h7.K
    (h7.c₁^(h7.n q - 1) : ℤ)
    (h7.c₁^(h7.m * q) : ℤ)
    (h7.c₁^(h7.m * q) : ℤ)
    (((a q t : ℕ) + b q t • h7.β')^(h7.k q u : ℕ))
    (h7.α' ^ (a q t * h7.l q u))
    (h7.γ' ^ (b q t * h7.l q u))]
  rw [mul_assoc]
  apply IsIntegral.mul
  · exact h7.c₁b (h7.n q) (one_le_n h7 q hq0 h2mq)
      (h7.k q u) (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).2.isLt)
      (a q t) (le_add_left 1 (finProdFinEquiv.symm.1 t).1)
      (b q t) (le_add_left 1 (finProdFinEquiv.symm.1 t).2)
  · exact IsIntegral.mul (c1a h7 q hq0 u t) (c1c h7 q hq0 u t)

lemma c₁neq0 : h7.c₁ ≠ 0 := by
  unfold c₁
  have hcα := (c'_both h7.α').2.1
  have hcβ := (c'_both h7.β').2.1
  have hcγ := (c'_both h7.γ').2.1
  unfold c'
  intros H
  simp_all only [ne_eq, mem_setOf_eq, abs_eq_zero, mul_eq_zero, or_self]

lemma c₁αneq0 : h7.c₁ • h7.α' ≠ 0 := by {
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  constructor
  · rw [← ne_eq]
    exact h7.c₁neq0
  · rw [← ne_eq]
    exact (h7.hneq0).1}

lemma c₁cneq0 : h7.c₁ • h7.γ' ≠ 0 := by {
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  constructor
  · rw [← ne_eq]
    exact h7.c₁neq0
  · rw [← ne_eq]
    exact (h7.hneq0).2.2}

lemma c_coeffs_neq_zero : h7.c_coeffs q ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (h7.c₁neq0))
  (pow_ne_zero _ (h7.c₁neq0))) (pow_ne_zero _ (h7.c₁neq0))

def A : Matrix (Fin (h7.m * h7.n q)) (Fin (q * q)) (𝓞 h7.K) :=
  fun i j => RingOfIntegers.restrict _ (fun _ => (c₁IsInt h7 q hq0 h2mq i j)) ℤ

lemma α'_neq_zero : h7.α' ^ (a q t * h7.l q u) ≠ 0 :=
  pow_ne_zero _ (h7.hneq0).1

lemma γ'_neq_zero : h7.γ' ^ (b q t * h7.l q u) ≠ 0 :=
  pow_ne_zero _ (h7.hneq0).2.2

lemma β'_neq_zero (y : ℕ) : (↑↑(a q t) + (↑(b q t)) • h7.β') ^ y ≠ 0 := by
  apply pow_ne_zero
  intro H
  have H1 : h7.β' = (↑↑(a q t))/(-(↑(b q t))) := by
    rw [eq_div_iff_mul_eq]
    rw [← eq_neg_iff_add_eq_zero] at H
    rw [mul_neg, mul_comm, H]
    have : (↑↑(b q t)) ≠ 0 := by
      simp only [ne_eq]
      unfold b
      simp only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply, Fin.coe_modNat,
        AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
    unfold b
    simp only [Equiv.toFun_as_coe, nsmul_eq_mul]
    intros H
    norm_cast at H
    have : b q t ≠ 0 := by {unfold b; aesop}
    apply this
    exact H.1
  apply h7.hirr (↑(a q t)) (-(↑(b q t)))
  rw [h7.habc.2.1, H1]
  simp only [map_div₀, map_natCast, map_neg, Int.cast_natCast, Int.cast_neg]

lemma sum_b
   (i1 i2 j1 j2 : ℕ) (Heq : ¬i2 = j2) : i1 + i2 • h7.β ≠ j1 + j2 • h7.β := by {
      intros H
      have hb := h7.hirr (i1 - j1) (j2 - i2)
      apply hb
      have h1 : i1 + i2 • h7.β = j1 + j2 • h7.β  ↔
        (i1 + i2 • h7.β) - (j1 + j2 • h7.β) = 0 := Iff.symm sub_eq_zero
      rw [h1] at H
      have h2 : ↑i1 + ↑i2 • h7.β - (↑j1 + ↑j2 • h7.β) = 0 ↔
         ↑i1 + i2 • h7.β - ↑j1 - ↑j2 • h7.β = 0 := by
          simp_all only [ne_eq, Int.cast_sub, nsmul_eq_mul,
            iff_true, sub_self, add_sub_cancel_left]
      rw [h2] at H
      have h3 : ↑i1 + i2 • h7.β - ↑j1 - j2 • h7.β = 0 ↔
          ↑i1 - ↑j1 + ↑i2 • h7.β - ↑j2 • h7.β = 0 := by
        ring_nf
      rw [h3] at H
      have hij2 : i2 ≠ j2 := by
        by_contra HC
        apply Heq
        exact HC
      have h4 : ↑i1 - ↑j1 + ↑i2 • h7.β - ↑j2 • h7.β = 0 ↔
        ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • h7.β = 0 := by {
        rw [sub_eq_add_neg]
        simp only [nsmul_eq_mul]
        rw [← neg_mul, add_assoc, ← add_mul]
        simp only [smul_eq_mul]
        rw [← sub_eq_add_neg]}
      rw [h4] at H
      have h5 : ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • h7.β =0 ↔
       ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • h7.β) := by
        rw [add_eq_zero_iff_eq_neg]
      rw [h5] at H
      have h6 : ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • h7.β) ↔
          ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • h7.β := by
        refine Eq.congr_right ?_
        simp only [smul_eq_mul]
        rw [← neg_mul]
        simp only [neg_sub]
      rw [h6] at H
      have h7 : ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • h7.β ↔
         (↑i1 - ↑j1) /(↑j2 - ↑i2 : ℂ) = h7.β := by
        simp only [smul_eq_mul]
        rw [div_eq_iff, mul_comm]
        intros HC
        apply hij2
        rw [sub_eq_zero] at HC
        simp only [Nat.cast_inj] at HC
        exact HC.symm
      rw [h7] at H
      rw [H.symm]
      simp only [Int.cast_sub, Int.cast_natCast]}

include hq0 in
lemma b_sum_neq_0 : ↑q + q • h7.β' ≠ 0 := by
  have qneq0 : q ≠ 0 := Nat.ne_zero_of_lt hq0
  have hirr' : ∀ (i j : ℤ), h7.σ h7.β' ≠ h7.σ (↑i / ↑j) := by {
    intros i j
    simp only [map_div₀, map_intCast, ne_eq]
    intros H
    rw [← h7.habc.2.1] at H
    apply h7.hirr i j
    exact H}
  simp only [map_div₀, map_intCast, ne_eq] at hirr'
  have := h7.sum_b q q 0 0 qneq0
  simp only [nsmul_eq_mul] at this
  simp only [CharP.cast_eq_zero, zero_mul, add_zero] at this
  intros H
  apply this
  apply_fun h7.σ at H
  simp only [nsmul_eq_mul, map_add, map_natCast, map_mul, map_zero] at H
  rw [← H]
  congr
  exact h7.habc.2.1

lemma one_leq_house_c₁β : 1 ≤ house (h7.c₁ • h7.β') := by
  apply house_gt_one_of_isIntegral
  · exact h7.isIntegral_c₁β
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  rw [← ne_eq, ne_eq]
  exact ⟨h7.c₁neq0, h7.hneq0.2.1⟩

lemma one_leq_house_c₁α : 1 ≤ house (h7.c₁ • h7.α') := by
  apply house_gt_one_of_isIntegral
  · exact h7.isIntegral_c₁α
  exact h7.c₁αneq0

lemma house_bound_c₁α : house (h7.c₁ • h7.α') ^ (a q t * h7.l q u)
  ≤ house (h7.c₁ • h7.α')^(h7.m * q) := by
    apply house_alg_int_leq_pow
    · rw [mul_comm h7.m q]; exact h7.al_leq_mq q u t
    · exact h7.c₁αneq0
    · exact h7.isIntegral_c₁α

lemma isInt_β_bound : IsIntegral ℤ (h7.c₁ • (↑q + q • h7.β')) := by {
  simp only [nsmul_eq_mul, smul_add]
  apply IsIntegral.add
  · rw [zsmul_eq_mul]
    apply IsIntegral.mul (IsIntegral.Cast h7.K h7.c₁) (IsIntegral.Nat h7.K q)
  · rw [zsmul_eq_mul, ← mul_assoc]; nth_rw 2 [mul_comm]; rw [mul_assoc]
    apply IsIntegral.mul (IsIntegral.Nat h7.K q)
    rw [← zsmul_eq_mul]
    exact h7.isIntegral_c₁β}

lemma isInt_β_bound_low (q : ℕ) (t : Fin (q * q)) :
    IsIntegral ℤ (h7.c₁ • (↑(a q t) + b q t • h7.β')) := by {
  simp only [nsmul_eq_mul, smul_add, zsmul_eq_mul]
  apply IsIntegral.add
  · apply IsIntegral.mul (IsIntegral.Cast h7.K h7.c₁) (IsIntegral.Nat h7.K (a q t))
  · rw [← mul_assoc]; nth_rw 2 [mul_comm]; rw [mul_assoc]
    apply IsIntegral.mul (IsIntegral.Nat h7.K (b q t)) ?_
    · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁β}

lemma bound_c₁β (q : ℕ) (hq0 : 0 < q) :
  1 ≤ house ((h7.c₁ • (q + q • h7.β'))) := by
  apply house_gt_one_of_isIntegral
  · exact h7.isInt_β_bound q
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  constructor
  · rw [← ne_eq]; exact h7.c₁neq0
  · rw [← ne_eq]; apply h7.b_sum_neq_0 q hq0

lemma one_leq_house_c₁γ : 1 ≤ house (h7.c₁ • h7.γ') := by
  apply house_gt_one_of_isIntegral
  · exact h7.isIntegral_c₁γ
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  constructor
  · rw [← ne_eq]; exact h7.c₁neq0
  · rw [← ne_eq]; exact h7.hneq0.2.2

include u t in
lemma sys_coe_ne_zero : h7.sys_coe q u t ≠ 0 := by
  unfold sys_coe
  rw [mul_assoc]
  apply mul_ne_zero
    (mod_cast β'_neq_zero h7 q t (h7.k q u))
  · exact mul_ne_zero (mod_cast α'_neq_zero h7 q u t)
      (mod_cast γ'_neq_zero h7 q u t)

lemma hM_neq0 : h7.A q hq0 h2mq ≠ 0 := by
  simp (config := { unfoldPartialApp := true }) only [A]
  rw [Ne, funext_iff]
  simp only [zsmul_eq_mul, RingOfIntegers.restrict]
  intros H
  let u : Fin (h7.m * h7.n q) := ⟨0, h7.card_mn_pos q hq0 h2mq⟩
  specialize H u
  rw [funext_iff] at H
  let t : Fin (q * q) := ⟨0, (mul_pos hq0 hq0)⟩
  specialize H t
  simp only [Int.cast_mul, Int.cast_pow, zero_apply] at H
  injection H with H
  simp only [mul_eq_zero, pow_eq_zero_iff', Int.cast_eq_zero, ne_eq, not_or] at H
  rcases H
  · rename_i H1; rcases H1;
    · rename_i H1 ; rcases H1 with ⟨H1, H11⟩
      · apply h7.c₁neq0; assumption
      · rename_i H11; apply h7.c₁neq0; exact H11.1
    rename_i H1; apply h7.c₁neq0; exact H1.1
  · rename_i H2;
    rcases H2 with ⟨H2, H22⟩
    · apply h7.β'_neq_zero q t (h7.k q u)
      simp_all only [nsmul_eq_mul, ne_eq, not_false_eq_true,
      zero_pow, t, u]
    · rename_i H1; apply (h7.hneq0).1; exact H1.1
    rename_i H2;
    apply (h7.hneq0).2.2
    exact H2.1

lemma cardmn :
    Fintype.card (Fin (h7.m * h7.n q)) = h7.m * h7.n q := by
  simp only [Fintype.card_fin]

omit hq0 h2mq in
lemma cardqq : card (Fin (q*q)) = q * q := by
  simp only [Fintype.card_fin]

lemma housec1_gt_zero : 0 ≤ @house.c₁ h7.K _ _ h7.hd := by
  apply mul_nonneg
  · rw [le_iff_eq_or_lt]
    · right
      simp only [Nat.cast_pos]
      exact Module.finrank_pos
  · apply mul_nonneg
    · simp only [le_sup_iff, zero_le_one, true_or]
    · apply (le_trans zero_le_one (le_max_left ..))

def c₂ : ℤ := (|h7.c₁| ^ (((1 + 2*h7.m * (↑2*h7.m))) + (1 + 2*h7.m * (↑2*h7.m))))

omit h2mq in
lemma one_leq_c₂ : 1 ≤ h7.c₂ := by
  apply le_trans (Int.cast_one_le_of_pos (h7.one_leq_abs_c₁))
  · nth_rw 1 [← pow_one (a:= |h7.c₁|)]
    unfold c₂
    simp only [Int.cast_eq]
    apply pow_le_pow_right₀ (h7.one_leq_abs_c₁)
    exact
      Nat.le_add_left 1
        ((1 + 2 * h7.m * (2 * h7.m)).add
          (Nat.add 1
            (((2 * h7.m).mul (Nat.mul 2 (2 * h7.h + 1) + 1)).add (Nat.mul 2 (2 * h7.h + 1) + 1))))

lemma zero_leq_c₂ : 0 ≤ h7.c₂ :=
  le_trans Int.one_nonneg (h7.one_leq_c₂)

-- include h2mq in
-- lemma c_coeffs_le_c₂_pow_n :
--     ↑(h7.c₁^ (h7.n q - 1) * h7.c₁  ^ (h7.m * q)
--       * h7.c₁ ^ (h7.m * q)) ≤ h7.c₂ ^(h7.n q) := by
--   calc _ = ↑h7.c₁ ^ ((h7.n q - 1) + (h7.m * q) + (h7.m * q)) := ?_
--        _ ≤ h7.c₂ ^(h7.n q) := ?_
--   · rw [← pow_add, ← pow_add]
--   · dsimp [c₂]; rw [← pow_mul]
--     sorry

--     -- refine pow_le_pow_right₀ (mod_cast h7.one_leq_c₁) ?_
--     -- · rw [add_mul,one_mul]
--     --   rw [add_assoc]; rw [Eq.symm (Nat.two_mul (h7.m * q))]; rw [mul_assoc]
--     --   calc _ ≤ h7.n q - 1 + 2 * (h7.m * (2 * h7.m * h7.n q)) := ?_
--     --        _ ≤ h7.n q + 2 * h7.m * (2 * h7.m * h7.n q) := ?_
--     --   · simp only [add_le_add_iff_left, Nat.ofNat_pos, mul_le_mul_left]
--     --     apply mul_le_mul (le_refl _)
--     --       (h7.q_le_two_mn q h2mq) (Nat.zero_le q)
--     --       (Nat.zero_le (h7.m))
--     --   · have : 2 * (h7.m * (2 * h7.m * h7.n q) ) =
--     --       2 * h7.m * (2 * h7.m * h7.n q) := by simp only [mul_assoc]
--     --     rw [this]; clear this
--     --     simp only [add_le_add_iff_right, tsub_le_iff_right,
--     --       le_add_iff_nonneg_right, zero_le]

def c₃ : ℝ := h7.c₂ * (1 + house h7.β')* Real.sqrt (2*h7.m) *
  (max 1 (((house h7.α' ^ (2*h7.m^2)) * house h7.γ' ^(2*h7.m^2))))

lemma one_leq_c₃ : 1 ≤ h7.c₃ := by
  dsimp [c₃]
  trans
  · have := h7.one_leq_c₂
    norm_cast at this
  · simp only [mul_assoc]
    norm_cast
    refine one_le_mul_of_one_le_of_one_le ?_ ?_
    · norm_cast;
      exact h7.one_leq_c₂
    · have h1 : 1 ≤ (1 + house h7.β') := by
        simp only [le_add_iff_nonneg_right]; apply house_nonneg
      have h2 : 1 ≤ (max 1 ((house h7.α' ^ (2 * h7.m ^ 2) *
        house h7.γ' ^ (2 * h7.m ^ 2)) ^ 2 * ↑(h7.m))) := by
         apply le_max_left
      have h3 : 1 ≤ ((Real.sqrt ((2*h7.m)))) := by
         rw [Real.one_le_sqrt]
         have h1 := h7.hm
         calc 1 ≤ (h7.m : ℝ) := by exact mod_cast h1
              _ ≤ 2*h7.m := by {
                refine le_mul_of_one_le_left ?_ ?_
                simp only [Nat.cast_nonneg]
                exact one_le_two
                }
         --exact Nat.le_of_ble_eq_true rfl
      calc 1 ≤ (1 + house h7.β') := h1
           _ ≤ (1 + house h7.β') * (Real.sqrt ((2*h7.m))) := by
            nth_rw 1 [← mul_one (a := (1 + house h7.β'))]
            apply mul_le_mul (Preorder.le_refl (1 + house h7.β')) (h3)
              (zero_le_one' ℝ) (zero_le_one.trans h1)
      nth_rw 1 [← mul_one (a := (1 + house h7.β') * (Real.sqrt ((2*h7.m))))]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      simp only [mul_assoc]
      apply mul_le_mul
      · apply Preorder.le_refl
      · apply mul_le_mul
        · apply Preorder.le_refl
        · simp only [le_sup_left]
        · positivity
        · positivity
      · simp only [Nat.ofNat_nonneg, Real.sqrt_mul, mul_one, Real.sqrt_pos, Nat.ofNat_pos,
        mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
      · refine Left.add_nonneg ?_ ?_
        · simp only [zero_le_one]
        · exact house_nonneg h7.β'

lemma zero_leq_c₃ : 0 ≤ h7.c₃ := by
  apply le_trans zero_le_one (h7.one_leq_c₃)

-- include h2mq in
-- lemma house_leq_house : house (h7.c_coeffs q : h7.K)
--       ≤ house ((h7.c₂ ^ h7.n q :ℤ) : h7.K) := by
--     rw [house_intCast, house_intCast (x := h7.c₂ ^ (h7.n q : ℕ))]
--     simp only [Int.cast_abs, Int.cast_mul, Int.cast_pow]
--     have := c_coeffs_le_c₂_pow_n h7 q h2mq
--     apply abs_le_abs
--     · norm_cast
--     · norm_cast
--       calc _ ≤ (h7.c₁ ^ (h7.n q - 1) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) := by {
--         simp only [neg_le_self_iff]
--         apply mul_nonneg
--         · apply mul_nonneg
--           · apply pow_nonneg (IsAbsoluteValue.abv_nonneg' (c' h7.α' * c' h7.β' * c' h7.γ'))
--           · apply pow_nonneg (IsAbsoluteValue.abv_nonneg' (c' h7.α' * c' h7.β' * c' h7.γ'))
--         · apply pow_nonneg (IsAbsoluteValue.abv_nonneg' (c' h7.α' * c' h7.β' * c' h7.γ'))
--           }
--            _ ≤ h7.c₂ ^ (h7.n q : ℕ) := this

lemma c2_abs_val : ↑|h7.c₂| ≤ h7.c₂ :=
  abs_le_of_sq_le_sq (le_refl _) (h7.zero_leq_c₂)

include hq0 h2mq in
lemma c2_abs_val_pow : ↑|(h7.c₂ ^ h7.n q : ℤ)| ≤ (h7.c₂ ^ h7.n q : ℤ) := by
  simp only [abs_pow]
  refine (pow_le_pow_iff_left₀ (abs_nonneg _)
    (h7.zero_leq_c₂)
    (h7.n_neq_0 q hq0 h2mq)).mpr (h7.c2_abs_val)

lemma house_muls (s t : ℕ) (h : s ≤ t) (_ : 0 ≤ t) :
  (s • house h7.β') ≤ (t • house h7.β') := by
  simp only [nsmul_eq_mul]
  apply mul_le_mul
  · simp only [Nat.cast_le]
    apply h
  · simp only [le_refl]
  · exact house_nonneg h7.β'
  · positivity

lemma house_add_mul_leq :
    house (h7.c₁ • (↑(a q t) + b q t • h7.β')) ≤
     (|h7.c₁| * |(q : ℤ)|) * (1 + house (h7.β')) := by
  calc _ ≤ house (h7.c₁ • (a q t : ℤ) + h7.c₁ • (b q t : ℤ) • h7.β') := ?_
       _ ≤ house (h7.c₁ • ((a q t : ℤ) : h7.K)) +
        house (h7.c₁ • ((b q t : ℤ) • h7.β')) := ?_
       _ ≤ house (h7.c₁ : h7.K) * house ((a q t : ℤ) : h7.K) +
         house (h7.c₁ : h7.K) * house ((b q t : ℤ) • h7.β') := ?_
       _ ≤  house (h7.c₁ : h7.K) * house ((a q t : ℤ) : h7.K) +
         house (h7.c₁ : h7.K) * (house ((b q t : ℤ) : h7.K) * house ( h7.β')) := ?_
       _ = |h7.c₁| * |(a q t : ℤ)| + |h7.c₁| * |((b q t) : ℤ)| * house (h7.β') := ?_
       _ ≤ |h7.c₁| * |(q : ℤ)| + |h7.c₁| * |((q) : ℤ)| * house h7.β' := ?_
       _ = |h7.c₁| * |(q : ℤ)| * (1 + house h7.β') := ?_
  · norm_cast; rw [smul_add]
  · apply house_add_le
  · refine add_le_add (by rw [zsmul_eq_mul]; apply house_mul_le)
                      (by rw [zsmul_eq_mul]; apply house_mul_le)
  · refine add_le_add ?_ ?_
    · apply mul_le_mul (le_refl _) (le_refl _); all_goals apply house_nonneg
    · refine mul_le_mul (le_refl _) (by rw [zsmul_eq_mul]; apply house_mul_le)
        (house_nonneg _) (house_nonneg _)
  · rw [house_intCast]; rw [house_intCast]; rw [house_intCast]; rw [mul_assoc]
  · refine add_le_add
      (mul_le_mul (le_refl _)
        (mod_cast bar' (finProdFinEquiv.symm.toFun t).1)
        (Int.cast_nonneg.mpr (Int.zero_le_ofNat (a q t)))
        (Int.cast_nonneg.mpr (abs_nonneg (h7.c₁)))) ?_
    · rw [mul_assoc, mul_assoc]
      apply mul_le_mul (Preorder.le_refl _)
      · apply mul_le_mul (mod_cast bar' (finProdFinEquiv.symm.toFun t).2) (le_refl _)
          (house_nonneg _) ?_
        · simp only [Nat.abs_cast, Int.cast_natCast, Nat.cast_nonneg]
      · apply mul_nonneg
        · simp only [Int.cast_abs, abs_nonneg]
        · apply house_nonneg
      · simp only [Int.cast_abs, abs_nonneg]
  · rw [mul_add]
    simp only [Int.cast_abs, mul_one]

lemma c₃_pow :
  h7.c₃ ^ ↑(h7.n q : ℝ) = h7.c₂ ^ ↑(h7.n q) * ((1 + house (h7.β'))^ ↑(h7.n q)) *
   (((Real.sqrt ((2*h7.m)))) ^ ↑(h7.n q)) *
  (max 1 (((house (h7.α') ^ (2*h7.m^2)) *
    house (h7.γ') ^(2*h7.m^2))))^ ↑(h7.n q) := by
    unfold c₃
    simp only [Real.rpow_natCast]
    rw [mul_pow, mul_pow, mul_pow]

include h2mq in
lemma q_eq_n_etc : ↑q ^ ((h7.n q) - 1) ≤
  (Real.sqrt (2*h7.m)^((h7.n q)- 1))* (Real.sqrt (h7.n q))^((h7.n q)- 1) := by
  have : (Real.sqrt ((2*h7.m)*(h7.n q))) =
    Real.sqrt (2*h7.m)* Real.sqrt (h7.n q) := by {
    rw [Real.sqrt_mul]
    simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg]}
  rw [← mul_pow]
  refine pow_le_pow_left₀ ?_ ?_ ((h7.n q - 1))
  · simp only [Nat.cast_nonneg]
  · rw [← this]
    rw [Real.le_sqrt]
    · norm_cast; apply sq_le_two_mn h7 q h2mq
    · positivity
    · positivity

lemma sq_n : (Real.sqrt (h7.n q))^((h7.n q : ℝ)-1) =
   (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1)/2) := by
  nth_rw 1 [Real.sqrt_eq_rpow, ← Real.rpow_mul, mul_comm, mul_div]
  · simp only [mul_one]
  · simp only [Nat.cast_nonneg]

include h2mq in
lemma pow_c₂ : h7.m * q - a q t * h7.l q u ≤ h7.m * (2 * (h7.m * h7.n q)) := by
  simp only [tsub_le_iff_right]
  calc _ ≤  h7.m * (2 * (h7.m * h7.n q)) := ?_
       _ ≤ h7.m * (2 * (h7.m * h7.n q)) + a q t * h7.l q u := ?_
  · apply mul_le_mul
    · rfl
    · have := h7.q_le_two_mn q h2mq
      simp only [mul_assoc] at *
      exact this
    · simp only [zero_le]
    · simp only [zero_le]
  · simp only [le_add_iff_nonneg_right, zero_le]

include h2mq in
lemma pow_c₂' : h7.m * q - b q t * h7.l q u ≤ h7.m * (2 * (h7.m * h7.n q)) := by
  simp only [tsub_le_iff_right]
  calc _ ≤  h7.m * (2 * (h7.m * h7.n q)) := ?_
       _ ≤ h7.m * (2 * (h7.m * h7.n q)) + b q t * h7.l q u := ?_
  · apply mul_le_mul
    · rfl
    · have := h7.q_le_two_mn q h2mq
      simp only [mul_assoc] at *
      exact this
    · simp only [zero_le]
    · simp only [zero_le]
  · simp only [le_add_iff_nonneg_right, zero_le]

lemma c_coeffspow' :
  ((h7.c₁ : ℤ) ^ ((h7.n q)- 1) *
   (h7.c₁ : ℤ) ^ (h7.m * q) * (h7.c₁) ^ (h7.m * q)) =
    ((h7.c₁ : ℤ) ^ (((h7.n q) - 1 - h7.k q u)) *
      (h7.c₁ : ℤ) ^ (h7.m * q - (a q t * h7.l q u) ) *
      (h7.c₁ : ℤ) ^ (h7.m * q - ((b q t * h7.l q u)))) •
  ((h7.c₁) ^ (h7.k q u ) * (h7.c₁ ) ^ (a q t * h7.l q u) *
    (h7.c₁) ^ (b q t * h7.l q u )) := by
  have := triple_comm_int
  rw [this]
  congr
  · simp only [zsmul_eq_mul, Int.cast_pow]
    simp only [Int.cast_eq]
    rw [← pow_add (m := (h7.n q - 1 - h7.k q u)) (n:=h7.k q u) (a:=h7.c₁)]
    have : (h7.n q - 1 - h7.k q u + h7.k q u) = (h7.n q - 1) := by {
      rw [add_comm]
      refine add_tsub_cancel_of_le ?_
      refine Nat.le_sub_of_add_le ?_
      exact bar' (finProdFinEquiv.symm.toFun u).2
    }
    rw [this]
  · simp only [smul_eq_mul]
    rw [← pow_add]
    have : (h7.m * q - (a q t * h7.l q u) + (a q t * h7.l q u)) = (h7.m * q) := by {
      rw [add_comm]
      refine add_tsub_cancel_of_le ?_
      rw [mul_comm h7.m]
      exact al_leq_mq h7 q u t
    }
    rw [this]
  · simp only [smul_eq_mul]
    rw [← pow_add]
    have : (h7.m * q - (b q t * h7.l q u) + (b q t * h7.l q u)) = (h7.m * q) := by {
      rw [add_comm]
      refine add_tsub_cancel_of_le ?_
      rw [mul_comm h7.m]
      exact bl_leq_mq h7 q u t
    }
    rw [this]

include hq0 h2mq in
lemma hAkl : --∀ (k : Fin (h7.m * h7.n q)) (l : Fin (q * q)),
  house ((algebraMap (𝓞 h7.K) h7.K) ((A h7 q) hq0 h2mq u t)) ≤
      (h7.c₃ ^ (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2))  := by {
    unfold A sys_coe
    simp only [RingOfIntegers.restrict, RingOfIntegers.map_mk]
    --have:= Real.rpow_natCast (x:=↑(h7.n q : ℝ)) (n:= (((h7.n q) - 1) / 2))

    calc
         _ = house (((h7.c₁ : h7.K) ^ ((h7.n q - 1) - h7.k q u) *
            (h7.c₁ : h7.K) ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u : ℕ)) •
         (((h7.c₁ : h7.K) ^ h7.k q u) * ((a q t : h7.K) + (b q t) * h7.β') ^ h7.k q u *
          ((h7.c₁ : h7.K) ^ (a q t * h7.l q u)) * h7.α' ^ (a q t * h7.l q u) *
          ((h7.c₁ : h7.K) ^ (b q t * h7.l q u)) * h7.γ' ^ (b q t * h7.l q u))) := ?_

         _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u : ℕ) *
            (h7.c₁ : h7.K) ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u : ℕ))) *
             house (h7.c₁ ^ (h7.k q u) • (↑(a q t) + (b q t) • h7.β') ^ (h7.k q u)) *
             house (h7.c₁ ^ (a q t * h7.l q u) • h7.α' ^ (a q t * h7.l q u)) *
             house (h7.c₁ ^ (b q t * h7.l q u) • h7.γ' ^ (b q t * h7.l q u)) := ?_

         _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u : ℕ) *
            (h7.c₁ : h7.K) ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u : ℕ))) *
             house (h7.c₁ • (↑(a q t) + (b q t) • h7.β')) ^ (h7.k q u) *
             house (h7.c₁ • h7.α') ^ (a q t * h7.l q u) *
             house (h7.c₁ • h7.γ') ^ (b q t * h7.l q u) := ?_

         _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u : ℕ) *
            (h7.c₁ : h7.K) ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u : ℕ))) *
             house (h7.c₁ • (↑(a q t) + b q t • h7.β')) ^ (h7.n q - 1) *
             house (h7.c₁ • h7.α') ^ (h7.m * q) *
             house (h7.c₁ • h7.γ') ^ (h7.m * q) := ?_

         _ ≤  |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u : ℕ) *
            (h7.c₁) ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * (h7.c₁) ^ (h7.m * q - b q t * h7.l q u : ℕ)))| *
             (|h7.c₁| * (|(q : ℤ)| * (1 + house (h7.β')))) ^ (h7.n q - 1) *
             (|h7.c₁| * house (h7.α')) ^ (h7.m * (2 * (h7.m * h7.n q))) *
             (|h7.c₁| * house (h7.γ')) ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_

         _ = |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u : ℕ) *
            (h7.c₁) ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * (h7.c₁) ^ (h7.m * q - b q t * h7.l q u : ℕ)))| *
            |h7.c₁ ^ (h7.n q - 1)| • (↑|↑q| * (1 + house h7.β')) ^ (h7.n q - 1) *
            |h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q)))| •
              house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
            |h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q)))| •
              house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_

         _ ≤ |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u : ℕ) *
            (h7.c₁) ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * (h7.c₁) ^ (h7.m * q - b q t * h7.l q u : ℕ)))| *
             ↑|h7.c₁| ^ ((h7.n q - 1) + (2 * h7.m * (2 * (h7.m * h7.n q))))
            * (↑|↑q| ^ ((h7.n q ) - 1) * (1 + house h7.β') ^ (h7.n q - 1) *
               house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
               house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_

         _ = |(h7.c₁) ^ (h7.n q - 1 - h7.k q u : ℕ)| *
            |(h7.c₁) ^ (h7.m * q - a q t * h7.l q u : ℕ)|
             * |(h7.c₁) ^ (h7.m * q - b q t * h7.l q u : ℕ)| *
             ↑|h7.c₁| ^ ((h7.n q - 1) + (2 * h7.m * (2 * (h7.m * h7.n q))))
            * (↑|↑q| ^ ((h7.n q)- 1) * (1 + house h7.β') ^ (h7.n q - 1) *
               house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
               house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_

         _ = |(h7.c₁)| ^ (h7.n q - 1 - h7.k q u : ℕ) *
            |(h7.c₁)| ^ (h7.m * q - a q t * h7.l q u : ℕ)
             * |(h7.c₁)| ^ (h7.m * q - b q t * h7.l q u : ℕ) *
             ↑|h7.c₁| ^ ((h7.n q - 1) + (2 * h7.m * (2 * (h7.m * h7.n q))))
            * (↑|↑q| ^ ((h7.n q) - 1) * (1 + house h7.β') ^ (h7.n q - 1) *
               house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
               house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_

         _ ≤  ↑(h7.c₂)^(h7.n q)
             * (↑|↑q| ^ ((h7.n q ) - 1) *
              (1 + house h7.β') ^ (h7.n q - 1) *
               house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
                house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_

         _ ≤ (h7.c₃)^(h7.n q : ℝ) * ((Real.sqrt (h7.n q))^((h7.n q : ℝ)-1)) := ?_

         _ ≤ (h7.c₃ ^ (h7.n q: ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2)) := ?_

    ·
      unfold c_coeffs
      rw [h7.c_coeffspow' q u t, smul_assoc]
      rw [triple_comm h7.K (h7.c₁^(h7.k q u))
        (h7.c₁^(a q t * h7.l q u)) (h7.c₁^(b q t * h7.l q u))
        (((a q t) + b q t • h7.β')^(h7.k q u))
         (h7.α' ^ (a q t * h7.l q u)) (h7.γ' ^ (b q t * h7.l q u))]
      simp only [nsmul_eq_mul, zsmul_eq_mul,
        Int.cast_pow, Int.cast_mul, smul_eq_mul,mul_assoc]
    ·
      simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow,mul_assoc]
      trans
      apply house_mul_le
      apply mul_le_mul ?_ ?_ (house_nonneg _) (house_nonneg _)
      · rfl
      · rw [← mul_assoc,← mul_assoc,← mul_assoc]
        trans
        apply house_mul_le
        rw [← mul_assoc]
        apply mul_le_mul
        · rw [mul_assoc]; apply house_mul_le
        · rfl
        · apply (house_nonneg _)
        · apply mul_nonneg (house_nonneg _) (house_nonneg _)
    · simp only [mul_assoc]
      apply mul_le_mul
      · rfl
      · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow]
        rw [← mul_pow]; rw [← mul_pow]; rw [← mul_pow]
        apply mul_le_mul (house_pow_le _ _)
        · apply mul_le_mul (house_pow_le _ _) (house_pow_le _ _) (house_nonneg _)
            (by apply pow_nonneg (house_nonneg _))
        · apply mul_nonneg (house_nonneg _) (house_nonneg _)
        · apply pow_nonneg; apply house_nonneg
      · apply mul_nonneg (house_nonneg _) (by
          apply mul_nonneg (house_nonneg _) (house_nonneg _))
      · apply house_nonneg
    ·
      apply mul_le_mul
      · apply mul_le_mul
        · apply mul_le_mul
          · rfl
          · apply house_alg_int_leq_pow
            · refine (Nat.le_sub_iff_add_le' ?_).mpr ?_
              · apply one_le_n h7 q hq0 h2mq
              · rw [add_comm]; exact bar' (finProdFinEquiv.symm.toFun u).2
            · intros H
              rw [zsmul_eq_mul] at H
              simp only [mul_eq_zero, Int.cast_eq_zero] at H
              cases' H with h1 h2
              · apply h7.c₁_neq_zero; exact h1
              · apply h7.β'_neq_zero q t 1; rw [pow_one]; exact h2
            · apply isInt_β_bound_low
          · apply pow_nonneg; apply house_nonneg
          · apply house_nonneg
        · apply house_alg_int_leq_pow
          · rw [mul_comm h7.m q]; apply al_leq_mq h7 q u t
          · exact h7.c₁αneq0
          · exact h7.isIntegral_c₁α
        · apply pow_nonneg; apply house_nonneg
        · apply mul_nonneg ((house_nonneg _))
          · apply pow_nonneg; apply house_nonneg
      · apply house_alg_int_leq_pow
        · rw [mul_comm h7.m q]; apply bl_leq_mq h7 q u t
        · exact h7.c₁cneq0
        · exact h7.isIntegral_c₁γ
      · apply pow_nonneg; apply house_nonneg
      · apply mul_nonneg
        · apply mul_nonneg; apply house_nonneg; apply pow_nonneg; apply house_nonneg
        · apply pow_nonneg; apply house_nonneg
    ·
      apply mul_le_mul
      · apply mul_le_mul
        · apply mul_le_mul
          · rw [← house_intCast (K:=h7.K)]
            simp only [Int.cast_mul, Int.cast_pow, le_refl]
          · refine pow_le_pow_left₀ ?_ ?_ (h7.n q - 1)
            · apply house_nonneg
            · rw [← mul_assoc]
              apply h7.house_add_mul_leq q t
          · apply pow_nonneg; apply house_nonneg
          · simp only [Int.cast_abs, Int.cast_mul, Int.cast_pow, abs_nonneg]
        · calc _ ≤ house (h7.c₁ • h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
               _ ≤ (↑|h7.c₁| * house h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
          · refine
            house_alg_int_leq_pow (h7.c₁ • h7.α') (h7.m * q)
              (h7.m * (2 * (h7.m * h7.n q))) ?_ ?_ ?_
            · apply mul_le_mul
              · apply Preorder.le_refl
              · exact (by { have H := q_le_two_mn h7 q h2mq; rw [mul_assoc] at H; exact H })
              · simp only [zero_le]
              · simp only [zero_le]
            · exact h7.c₁αneq0
            · exact h7.isIntegral_c₁α
          · refine pow_le_pow_left₀ ?_ ?_ (h7.m * (2 * (h7.m * h7.n q)))
            · apply house_nonneg
            · calc _ ≤ house (h7.c₁ : h7.K)  * house (h7.α') := ?_
                   _ ≤ _ := ?_
              · simp only [zsmul_eq_mul]
                apply house_mul_le
              · simp only [house_intCast, Int.cast_abs, le_refl]
        · apply pow_nonneg; apply house_nonneg
        · apply mul_nonneg
          · simp only [Int.cast_abs, abs_nonneg]
          · apply pow_nonneg
            apply mul_nonneg
            · simp only [Int.cast_abs, abs_nonneg]
            · apply mul_nonneg
              · simp only [Nat.abs_cast, Int.cast_natCast, Nat.cast_nonneg]
              · refine Left.add_nonneg ?_ ?_
                · simp only [zero_le_one]
                · exact house_nonneg h7.β'
      · calc _ ≤ house (h7.c₁ • h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
             _ ≤ (↑|h7.c₁| * house h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
        · refine
            house_alg_int_leq_pow (h7.c₁ • h7.γ') (h7.m * q)
              (h7.m * (2 * (h7.m * h7.n q))) ?_ ?_ ?_
          · apply mul_le_mul
            · apply Preorder.le_refl
            · exact (by { have H := q_le_two_mn h7 q h2mq; rw [mul_assoc] at H; exact H })
            · simp only [zero_le]
            · simp only [zero_le]
          · exact h7.c₁cneq0
          · exact h7.isIntegral_c₁γ
        refine pow_le_pow_left₀ ?_ ?_ (h7.m * (2 * (h7.m * h7.n q)))
        · apply house_nonneg
        · calc _ ≤ house (h7.c₁ : h7.K)  * house (h7.γ') := ?_
               _ ≤ _ := ?_
          · simp only [zsmul_eq_mul]
            apply house_mul_le
          · simp only [house_intCast, Int.cast_abs, le_refl]
      · apply pow_nonneg; apply house_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · simp only [Int.cast_abs, abs_nonneg]
          · apply pow_nonneg
            apply mul_nonneg
            · simp only [Int.cast_abs, abs_nonneg]
            · apply mul_nonneg
              · simp only [Nat.abs_cast, Int.cast_natCast, Nat.cast_nonneg]
              · refine Left.add_nonneg ?_ ?_
                · simp only [zero_le_one]
                · exact house_nonneg h7.β'
        · apply pow_nonneg;
          · apply mul_nonneg
            · simp only [Int.cast_abs, abs_nonneg]
            · apply house_nonneg
    · rw [zsmul_eq_mul]; rw [zsmul_eq_mul]; rw [zsmul_eq_mul]
      rw [mul_pow]; rw [mul_pow]; rw [mul_pow]
      rw [mul_pow]; rw [mul_pow]; rw [abs_pow]; rw [abs_pow]
      congr
      simp only [Int.cast_abs, Int.cast_pow]
      simp only [Nat.abs_cast, Int.cast_natCast]
      simp only [Int.cast_abs, Int.cast_pow]
      simp only [Int.cast_abs, Int.cast_pow]
    ·
      have := triple_comm ℝ
       |(h7.c₁^(h7.n q - 1) : ℤ)|
       |(h7.c₁^(h7.m * (2 * (h7.m * h7.n q))) : ℤ)|
       |(h7.c₁^(h7.m * (2 * (h7.m * h7.n q))) : ℤ)|
       ((↑|↑q| * (1 + house (h7.β')))^(h7.n q - 1))
       ((house h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))))
       ((house h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))))
      simp only [mul_assoc] at *
      simp only [zsmul_eq_mul] at *
      rw [← this]; clear this
      rw [abs_pow]; rw [abs_pow]; rw [← pow_add]; rw [← pow_add]
      apply mul_le_mul
      · simp only [abs_pow, Int.cast_pow, Int.cast_abs, le_refl]
      · apply mul_le_mul
        · rw [← pow_add]; rw [← pow_add]
          rw [Eq.symm (Nat.two_mul (h7.m * (2 * (h7.m * h7.n q))))]
          simp only [Int.cast_pow, Int.cast_abs, le_refl]
        · rw [mul_pow]
          simp only [mul_assoc]; simp only [Nat.abs_cast, le_refl]
        · apply mul_nonneg
          · apply pow_nonneg
            apply mul_nonneg
            · simp only [Nat.abs_cast, Nat.cast_nonneg]
            · refine Left.add_nonneg ?_ ?_
              · simp only [zero_le_one]
              · exact house_nonneg h7.β'
          · apply mul_nonneg; apply pow_nonneg;apply house_nonneg
            apply pow_nonneg; apply house_nonneg
        · apply pow_nonneg; simp only [Int.cast_abs, abs_nonneg]
      · simp only [Int.cast_mul, Int.cast_pow, Int.cast_abs, Nat.abs_cast]
        apply mul_nonneg
        · apply mul_nonneg
          · apply pow_nonneg; simp only [abs_nonneg]
          · apply mul_nonneg;
            · apply pow_nonneg; simp only [abs_nonneg]
            · apply pow_nonneg; simp only [abs_nonneg]
        · apply mul_nonneg;
          · apply pow_nonneg;
            apply mul_nonneg;
            · simp only [Nat.cast_nonneg]
            · refine Left.add_nonneg ?_ ?_
              · simp only [zero_le_one]
              · exact house_nonneg h7.β'
          · apply mul_nonneg;
            · apply pow_nonneg; apply house_nonneg
            · apply pow_nonneg; apply house_nonneg
      · simp only [Int.cast_abs, abs_nonneg]

    · rw [← pow_add]; rw [← pow_add]
      simp only [Int.cast_abs, Int.cast_pow, Nat.abs_cast, abs_pow]
      rw [← pow_add]; rw [← pow_add]; rw [← pow_add]; rw [← pow_add]


    · rw [abs_pow]; rw [abs_pow]; rw [abs_pow]
      simp only [mul_assoc,Int.cast_pow, Int.cast_abs, Nat.abs_cast]

    ·
      apply mul_le_mul
      · rw [← pow_add]; rw [← pow_add]; rw [← pow_add]
        simp only [Int.cast_abs]
        unfold c₂
        simp only [Int.cast_pow, Int.cast_abs]
        rw [← pow_mul]
        refine pow_le_pow_right₀ ?_ ?_
        · exact mod_cast h7.one_leq_abs_c₁
        · rw [add_mul]
          rw [add_mul]
          simp only [one_mul]
          simp only [mul_assoc]
          rw [(Nat.two_mul (h7.m * (2 * (h7.m * h7.n q))))]
          simp only [add_assoc]
          refine Nat.add_le_add ?_ ?_
          · simp only [tsub_le_iff_right]
            refine Nat.le_succ_of_le ?_
            exact Nat.le_add_right (h7.n q) (h7.k q u)
          · refine Nat.add_le_add ?_ ?_
            · exact pow_c₂ h7 q u t h2mq
            · refine Nat.add_le_add ?_ ?_
              ·  exact pow_c₂' h7 q u t h2mq
              · simp only [add_le_add_iff_right, tsub_le_iff_right, le_add_iff_nonneg_right,
                zero_le]
      · simp only [Nat.abs_cast, le_refl]
      · apply mul_nonneg;
        · apply mul_nonneg;
          · apply mul_nonneg;
            · apply pow_nonneg; simp only [abs_nonneg]
            · apply pow_nonneg;
              refine Left.add_nonneg ?_ ?_
              · simp only [zero_le_one]
              · exact house_nonneg h7.β'
          · apply pow_nonneg; apply house_nonneg
        · apply pow_nonneg; apply house_nonneg
      · apply pow_nonneg; simp only [Int.cast_nonneg];exact zero_leq_c₂ h7

    ·
      rw [h7.c₃_pow q]
      simp only [mul_assoc]
      apply mul_le_mul
      · rfl
      · calc _ ≤ (Real.sqrt (2*h7.m)^(h7.n q -1))* (Real.sqrt (h7.n q))^((h7.n q) -1)
                * ((1 + house h7.β') ^ (h7.n q - 1) *
                  (house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
                    house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))))) := ?_

             _ ≤ (Real.sqrt (2*h7.m)^(h7.n q -1))
                * ((1 + house h7.β') ^ (h7.n q - 1) * (house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q)))
                * house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))))) * (Real.sqrt (h7.n q))^(((h7.n q) : ℝ)-1) := ?_

             _ ≤ √(2 * ↑(h7.m)) ^ (h7.n q - 1) *
                ((1 + house h7.β') ^ (h7.n q - 1) * (house h7.α' ^ (h7.m * 2 * h7.m * h7.n q)
                * house h7.γ' ^ (h7.m * 2 * h7.m * h7.n q))) * (Real.sqrt (h7.n q))^(((h7.n q) : ℝ)-1) := ?_

             _ ≤ √(2 * ↑(h7.m)) ^ ((h7.n q)) *
               ((1 + house h7.β') ^ ((h7.n q)) * (house h7.α' ^ (h7.m * 2 * h7.m)) ^ (h7.n q)
                * (house h7.γ' ^ (h7.m * 2 * h7.m)) ^ (h7.n q)) *  (Real.sqrt (h7.n q ))
                 ^(((h7.n q) : ℝ)-1) := ?_

        · apply mul_le_mul
          · simp only [Nat.abs_cast]

            apply h7.q_eq_n_etc q h2mq
          · apply Preorder.le_refl
          · apply mul_nonneg
            · apply pow_nonneg
              · refine Left.add_nonneg ?_ ?_
                · simp only [zero_le_one]
                · exact house_nonneg h7.β'
            · apply mul_nonneg
              · apply pow_nonneg; apply house_nonneg
              · apply pow_nonneg; apply house_nonneg
          · apply mul_nonneg
            · apply pow_nonneg; simp only [Real.sqrt_nonneg]
            · apply pow_nonneg; simp only [Real.sqrt_nonneg]
        · simp only [mul_assoc]
          nth_rw 3 [mul_comm]
          simp only [mul_assoc]
          simp only [Nat.ofNat_nonneg, Real.sqrt_mul]
          apply mul_le_mul
          · apply Preorder.le_refl
          · apply mul_le_mul
            · apply Preorder.le_refl
            · apply mul_le_mul
              · apply Preorder.le_refl
              · apply mul_le_mul
                · apply Preorder.le_refl
                ·
                  rw [← Real.rpow_natCast (x:=√(h7.n q : ℝ))]
                  apply Real.rpow_le_rpow_of_exponent_le
                  · refine Real.one_le_sqrt.mpr ?_
                    simp only [Nat.one_le_cast]
                    exact one_le_n h7 q hq0 h2mq
                  · rw [le_iff_lt_or_eq]
                    right
                    refine Nat.cast_pred ?_
                    refine Nat.zero_lt_of_ne_zero ?_
                    exact n_neq_0 h7 q hq0 h2mq
                · simp only [Real.sqrt_nonneg, pow_nonneg]
                · apply pow_nonneg; apply house_nonneg
              · apply mul_nonneg
                · apply pow_nonneg; apply house_nonneg
                · simp only [Real.sqrt_nonneg, pow_nonneg]
              · apply pow_nonneg; apply house_nonneg
            · apply mul_nonneg
              · apply pow_nonneg; apply house_nonneg
              · apply mul_nonneg
                · apply pow_nonneg; apply house_nonneg
                · simp only [Real.sqrt_nonneg, pow_nonneg]
            · apply pow_nonneg
              · refine Left.add_nonneg ?_ ?_
                · simp only [zero_le_one]
                · exact house_nonneg h7.β'
          · apply mul_nonneg
            · apply pow_nonneg
              · refine Left.add_nonneg ?_ ?_
                · simp only [zero_le_one]
                · exact house_nonneg h7.β'
            · apply mul_nonneg
              · apply pow_nonneg; apply house_nonneg
              · apply mul_nonneg
                · apply pow_nonneg; apply house_nonneg
                · simp only [Real.sqrt_nonneg, pow_nonneg]
          · apply pow_nonneg;
            apply mul_nonneg
            · simp only [Real.sqrt_nonneg]
            · simp only [Real.sqrt_nonneg]
        · simp only [mul_assoc]
          apply mul_le_mul
          · apply Preorder.le_refl
          · apply mul_le_mul
            · apply Preorder.le_refl
            · apply mul_le_mul
              · apply Preorder.le_refl
              · apply Preorder.le_refl
              · apply mul_nonneg
                · apply pow_nonneg; apply house_nonneg
                · apply Real.rpow_nonneg; simp only [Real.sqrt_nonneg]
              · apply pow_nonneg; apply house_nonneg
            · apply mul_nonneg;
              · apply pow_nonneg; apply house_nonneg
              · apply mul_nonneg;
                · apply pow_nonneg; apply house_nonneg
                · apply Real.rpow_nonneg
                  · simp only [Real.sqrt_nonneg]
            · apply pow_nonneg;
              · refine Left.add_nonneg ?_ ?_
                · simp only [zero_le_one]
                · exact house_nonneg h7.β'
          · apply mul_nonneg;
            · apply pow_nonneg
              · refine Left.add_nonneg ?_ ?_
                · simp only [zero_le_one]
                · exact house_nonneg h7.β'
            · apply mul_nonneg;
              · apply pow_nonneg; apply house_nonneg
              · apply mul_nonneg;
                · apply pow_nonneg; apply house_nonneg
                · apply Real.rpow_nonneg;
                  simp only [Real.sqrt_nonneg]
          · apply pow_nonneg;
            simp only [Nat.ofNat_nonneg, Real.sqrt_mul, Real.sqrt_pos, Nat.ofNat_pos,
              mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
        · simp only [mul_assoc]
          apply mul_le_mul
          · refine Bound.pow_le_pow_right_of_le_one_or_one_le ?_
            left
            constructor
            · refine Real.one_le_sqrt.mpr ?_
              nth_rw 1 [← mul_one (a:=1)]
              apply mul_le_mul
              · simp only [Nat.one_le_ofNat]
              · simp only [Nat.one_le_cast]
                unfold m
                simp only [le_add_iff_nonneg_left, zero_le]
              · simp only [zero_le_one]
              · simp only [Nat.ofNat_nonneg]
            · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
          · apply mul_le_mul
            · refine Bound.pow_le_pow_right_of_le_one_or_one_le ?_
              left
              constructor
              · simp only [le_add_iff_nonneg_right]
                apply house_nonneg
              · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
            · apply mul_le_mul
              · rw [← pow_mul]
                simp only [mul_assoc]
                apply Preorder.le_refl
              · rw [← pow_mul]
                simp only [mul_assoc]
                apply Preorder.le_refl
              · apply mul_nonneg
                · apply pow_nonneg; apply house_nonneg
                · apply Real.rpow_nonneg; simp only [Real.sqrt_nonneg]
              · apply pow_nonneg; apply pow_nonneg; apply house_nonneg
            · apply mul_nonneg;
              · apply pow_nonneg; apply house_nonneg
              · apply mul_nonneg;
                · apply pow_nonneg; apply house_nonneg
                · apply Real.rpow_nonneg; simp only [Real.sqrt_nonneg]
            · apply pow_nonneg;
              · refine Left.add_nonneg ?_ ?_
                · simp only [zero_le_one]
                · exact house_nonneg h7.β'
          · apply mul_nonneg;
            · apply pow_nonneg;
              · refine Left.add_nonneg ?_ ?_
                · simp only [zero_le_one]
                · exact house_nonneg h7.β'
            · apply mul_nonneg;
              · apply pow_nonneg; apply house_nonneg
              · apply mul_nonneg;
                · apply pow_nonneg; apply house_nonneg
                · apply Real.rpow_nonneg; simp only [Real.sqrt_nonneg]
          · apply pow_nonneg; simp only [Real.sqrt_nonneg]
        · nth_rw 2 [← mul_assoc]
          rw [mul_comm  ((1 + house h7.β') ^ (h7.n q)) (((Real.sqrt ((2*h7.m)))) ^ (h7.n q))]
          simp only [mul_assoc]
          apply mul_le_mul
          · refine pow_le_pow_left₀ ?_ ?_ (h7.n q)
            · simp only [Real.sqrt_nonneg]
            · apply Preorder.le_refl
          · apply mul_le_mul
            · apply Preorder.le_refl
            · simp only  [← mul_assoc]
              apply mul_le_mul
              · rw [← mul_pow]
                refine pow_le_pow_left₀ ?_ ?_ (h7.n q)
                · apply mul_nonneg;
                  · apply pow_nonneg; apply house_nonneg
                  · apply pow_nonneg; apply house_nonneg
                · have : ((h7.m * 2) * h7.m) = (2 * h7.m^2) := by {
                    rw [mul_comm]
                    rw [← mul_assoc]
                    rw [pow_two]
                    rw [mul_comm]
                  }
                  rw [this]; clear this
                  calc _ ≤ ((house h7.α' ^ (2 * h7.m ^ 2) *
                      house h7.γ' ^ (2 * h7.m ^ 2))) := ?_
                       _ ≤ max 1 ((house h7.α' ^ (2 * h7.m^ 2) * house h7.γ' ^ (2 * h7.m ^ 2))
                        ) := ?_
                  · apply Preorder.le_refl
                  · simp only [le_sup_right]
              · apply Preorder.le_refl
              · apply Real.rpow_nonneg; simp only [Real.sqrt_nonneg]
              · apply pow_nonneg
                simp only [le_sup_iff, zero_le_one, true_or]
            · apply mul_nonneg;
              · apply pow_nonneg;apply pow_nonneg;apply house_nonneg
              · apply mul_nonneg;
                · apply pow_nonneg; apply pow_nonneg;apply house_nonneg
                · apply Real.rpow_nonneg; simp only [Real.sqrt_nonneg]
            · apply pow_nonneg;
              · refine Left.add_nonneg ?_ ?_
                · simp only [zero_le_one]
                · exact house_nonneg h7.β'
          · apply mul_nonneg;
            · apply pow_nonneg;
              · refine Left.add_nonneg ?_ ?_
                · simp only [zero_le_one]
                · exact house_nonneg h7.β'
            · apply mul_nonneg;
              · apply pow_nonneg; apply pow_nonneg; apply house_nonneg
              · apply mul_nonneg;
                · apply pow_nonneg; apply pow_nonneg; apply house_nonneg
                · apply Real.rpow_nonneg; simp only [Real.sqrt_nonneg]
          · apply pow_nonneg; simp only [Real.sqrt_nonneg]
      · apply mul_nonneg;
        · apply pow_nonneg;simp only [Nat.abs_cast, Nat.cast_nonneg]
        · apply mul_nonneg;
          · apply pow_nonneg;
            · refine Left.add_nonneg ?_ ?_
              · simp only [zero_le_one]
              · exact house_nonneg h7.β'
          · apply mul_nonneg;
            · apply pow_nonneg; apply house_nonneg
            · apply pow_nonneg; apply house_nonneg
      · apply pow_nonneg; norm_cast; apply h7.zero_leq_c₂
    · rw [le_iff_eq_or_lt]
      left
      rw [← sq_n]
}

def applylemma82 [DecidableEq (h7.K →+* ℂ)] :=
    NumberField.house.exists_ne_zero_int_vec_house_le h7.K
  (h7.A q hq0 h2mq)
  (hM_neq0 h7 q hq0 h2mq)
  (h7.h0m q hq0 h2mq)
  (h7.hmn q hq0 h2mq)
  (cardqq q)
  (fun u t => hAkl h7 q hq0 u t h2mq)
  (h7.cardmn q)

variable [ DecidableEq (h7.K →+* ℂ)]

abbrev η : Fin (q * q) → 𝓞 h7.K :=
  (applylemma82 h7 q hq0 h2mq).choose

def c₄ : ℝ :=
  (max 1 ((house.c₁ h7.K) * house.c₁ h7.K * 2 * h7.m)) * h7.c₃

lemma one_leq_c₄ : 1 ≤ h7.c₄ := by
  dsimp [c₄]
  refine one_le_mul_of_one_le_of_one_le ?_ (h7.one_leq_c₃)
  · exact le_max_left 1 (house.c₁ h7.K * house.c₁ h7.K * 2 * ↑(h7.m))

lemma zero_leq_c₄ : 0 ≤ h7.c₄ := by
  unfold c₄
  simp only [lt_sup_iff, zero_lt_one, true_or, mul_nonneg_iff_of_pos_left]
  exact zero_leq_c₃ h7

lemma q_sq_real: (q * q : ℝ) = q^2 := by {
  norm_cast; exact Eq.symm (pow_two ↑q)}

include h2mq in
omit [DecidableEq (h7.K →+* ℂ)] in
lemma q_eq_2sqrtmn_real [DecidableEq (h7.K →+* ℂ)] : (q^2 : ℝ) = 2*h7.m*h7.n q := by
  norm_cast; refine Eq.symm (Nat.mul_div_cancel' h2mq)

include h2mq hq0 in
omit [DecidableEq (h7.K →+* ℂ)] in
lemma fracmqn : (↑(h7.m : ℝ) * ↑(h7.n q : ℝ) /
  (2 * ↑(h7.m : ℝ) * ↑(h7.n q : ℝ) - (h7.m * (h7.n q : ℝ))) : ℝ) = 1 := by
    have : 2 * ↑(h7.m : ℝ) * ↑(h7.n q : ℝ) - ↑(h7.m : ℝ) * ↑(h7.n q : ℝ)=
      ↑(h7.m : ℝ) * ↑(h7.n q : ℝ ) := by ring
    rw [this]
    norm_cast
    refine (div_eq_one_iff_eq ?_).mpr rfl
    simp only [Nat.cast_mul, ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
    constructor
    · rw [← ne_eq]; exact Ne.symm (Nat.zero_ne_add_one (2 * h7.h + 1))
    · rw [← ne_eq]; refine h7.n_neq_0 q hq0 h2mq

include hq0 h2mq in
omit [DecidableEq (h7.K →+* ℂ)] in
lemma hfrac : ↑(h7.n q : ℝ) * ↑(h7.n q : ℝ) ^ ((↑(h7.n q : ℝ) - 1) / 2) =
  ↑(h7.n q : ℝ) ^ ((↑(h7.n q : ℝ) + 1) / 2) := by {
    nth_rw 1 [← Real.rpow_one (x := ↑(h7.n q))]
    rw [← Real.rpow_add]
    · congr; ring
    · norm_cast
      have := h7.one_le_n q hq0 h2mq
      linarith}

open NumberField.house in
lemma fromlemma82_bound :
  house (algebraMap (𝓞 h7.K) h7.K (h7.η q hq0 h2mq t)) ≤
     h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) := by
  calc _ ≤  house.c₁ h7.K * (house.c₁ h7.K * ↑(q * q) *
    (h7.c₃ ^ (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2))) ^
      ((h7.m * h7.n q : ℝ) / (↑(q * q : ℝ) - ↑(h7.m * h7.n q ))) := ?_
       _ = (house.c₁ h7.K * (house.c₁ h7.K * 2 * h7.m *
    (h7.c₃ ^ (h7.n q : ℝ)) * ((h7.n q : ℝ) *
    (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2)))) := ?_
       _ ≤ h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1)/2) : ℝ) := ?_
  · exact mod_cast ((applylemma82 h7 q hq0 h2mq).choose_spec).2.2 t
  · rw [← pow_two q]
    rw [q_sq_real q]
    rw [h7.q_eq_2sqrtmn q h2mq]
    rw [h7.q_eq_2sqrtmn_real q h2mq]
    have fracmqn := h7.fracmqn q hq0 h2mq
    nth_rw 2 [← Nat.cast_mul] at fracmqn
    rw [fracmqn]; clear fracmqn
    rw [Real.rpow_one]
    rw [h7.hfrac q hq0 h2mq]
    simp only [mul_eq_mul_left_iff]
    left
    rw [mul_assoc]; rw [mul_assoc]; rw [mul_assoc]; rw [mul_assoc]; rw [mul_assoc];
    refine (mul_right_inj' ?_).mpr ?_
    · have : 1 ≤ house.c₁ h7.K := by {
      unfold house.c₁
      have : 0 < ↑(Module.finrank ℚ h7.K) := Module.finrank_pos
      refine one_le_mul_of_one_le_of_one_le ?_ ?_
      · exact Nat.one_le_cast.mpr this
      · unfold house.c₂
        refine one_le_mul_of_one_le_of_one_le ?_ ?_
        apply le_max_left
        apply le_max_left}
      refine Ne.symm (ne_of_lt ?_)
      linarith
    · have : ↑(2 * (h7.m * h7.n q)) * (h7.c₃ ^
        ↑(h7.n q : ℝ) * ↑(h7.n q) ^ ((↑(h7.n q: ℝ) - 1) / 2))=
        ↑(2 * h7.m) * (h7.c₃ ^ ↑(h7.n q : ℝ) *
        (h7.n q * ↑(h7.n q) ^ ((↑(h7.n q : ℝ) - 1) / 2))) := by {
          nth_rw 4 [← mul_assoc]
          nth_rw 8 [← mul_comm]
          simp only [Nat.cast_mul, Nat.cast_ofNat, Real.rpow_natCast]
          simp only [mul_assoc]}
      rw [this]
      rw [hfrac h7 q hq0 h2mq]
      rw [← mul_assoc]
      rw [← mul_assoc]
      rw [← mul_assoc]
      simp only [Nat.cast_mul, Nat.cast_ofNat, Real.rpow_natCast]
  · rw [hfrac h7 q hq0 h2mq]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · unfold c₄
      rw [Real.mul_rpow]
      · refine mul_le_mul_of_nonneg_right ?_ ?_
        · trans
          · apply le_max_right 1 ((house.c₁ h7.K * house.c₁ h7.K * 2 * ↑(h7.m)))
          · nth_rw 1 [← Real.rpow_one
              (x := max 1 (house.c₁ h7.K * house.c₁ h7.K * 2 * ↑(h7.m)))]
            apply Real.rpow_le_rpow_of_exponent_le
            apply le_max_left
            · simp only [Nat.one_le_cast]
              exact one_le_n h7 q hq0 h2mq
        · simp only [Real.rpow_natCast]
          apply pow_nonneg
          · apply (le_trans zero_le_one (one_leq_c₃ h7))
      · apply (le_trans zero_le_one (le_max_left ..))
      · apply (le_trans zero_le_one (one_leq_c₃ h7))
    · apply Real.rpow_nonneg
      simp only [Nat.cast_nonneg]


lemma decompose_ij (i j : Fin (q * q)) : i = j ↔
  (finProdFinEquiv.symm.1 i).1 = (finProdFinEquiv.symm.1 j).1 ∧
    ((finProdFinEquiv.symm.1 i).2 : Fin q) = (finProdFinEquiv.symm.1 j).2 := by
  apply Iff.intro
  · intro H; rw [H]; constructor <;> rfl
  · intro H
    rcases H with ⟨H1, H2⟩
    have : finProdFinEquiv.symm.1 i = finProdFinEquiv.symm.1 j := by
      rw [← Prod.eta (finProdFinEquiv.symm.toFun i), H1]
      rw [← Prod.eta (finProdFinEquiv.symm.toFun j), H2]
    clear H1 H2
    have := congr_arg finProdFinEquiv.toFun this
    simp only [Equiv.toFun_as_coe, EmbeddingLike.apply_eq_iff_eq] at this
    assumption

def ρ : ℂ := (a q t + (b q t • h7.β)) * Complex.log h7.α

lemma hdist : ∀ (i j : Fin (q * q)), i ≠ j → ρ h7 q i ≠ ρ h7 q j := by
  intros i j hij
  rw [ne_eq, decompose_ij q] at hij
  rw [not_and'] at hij
  unfold ρ
  simp only [not_or, ne_eq, mul_eq_mul_right_iff, not_or]
  constructor
  · by_cases Heq : (finProdFinEquiv.symm.1 i).2 = (finProdFinEquiv.symm.1 j).2
    · unfold a b
      rw [Heq]
      have := hij Heq
      intro H
      apply this
      simp only [Equiv.toFun_as_coe, nsmul_eq_mul, add_left_inj, Nat.cast_inj] at H
      exact Fin.eq_of_val_eq H
    · let i2 : ℕ := (finProdFinEquiv.symm.toFun i).2 + 1
      let j2 : ℕ := (finProdFinEquiv.symm.toFun j).2 + 1
      let i1 : ℕ := (finProdFinEquiv.symm.toFun i).1 + 1
      let j1 : ℕ := (finProdFinEquiv.symm.toFun j).1 + 1
      have hb := h7.hirr (i1 - j1) (j2 - i2)
      rw [← ne_eq]
      change i1 + i2 • h7.β ≠ j1 + j2 • h7.β
      intros H
      have hb := h7.hirr (i1 - j1) (j2 - i2)
      apply hb
      have h1 : i1 + i2 • h7.β = j1 + j2 • h7.β  ↔
        (i1 + i2 • h7.β) - (j1 + j2 • h7.β) = 0 := Iff.symm sub_eq_zero
      rw [h1] at H
      have h2 : ↑i1 + ↑i2 • h7.β - (↑j1 + ↑j2 • h7.β) = 0 ↔
         ↑i1 + i2 • h7.β - ↑j1 - ↑j2 • h7.β = 0 := by {
          simp_all only [ne_eq, Equiv.toFun_as_coe,
          finProdFinEquiv_symm_apply,
            nsmul_eq_mul, iff_true, sub_self,
            add_sub_cancel_left]}
      rw [h2] at H
      have h3 : ↑i1 + i2 • h7.β - ↑j1 - j2 • h7.β = 0 ↔
          ↑i1 - ↑j1 + ↑i2 • h7.β - ↑j2 • h7.β = 0 := by {
        ring_nf}
      rw [h3] at H
      have hij2 : i2 ≠ j2 := by {
        by_contra HC
        apply Heq
        refine Fin.eq_of_val_eq ?_
        exact Nat.succ_inj.mp HC
        }
      have h4 : ↑i1 - ↑j1 + ↑i2 • h7.β - ↑j2 • h7.β = 0 ↔
        ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • h7.β = 0 := by {
        rw [sub_eq_add_neg]
        simp only [nsmul_eq_mul]
        rw [← neg_mul, add_assoc, ← add_mul]
        simp only [smul_eq_mul]
        rw [← sub_eq_add_neg]}
      rw [h4] at H
      have h5 : ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • h7.β = 0 ↔
       ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • h7.β) := by {
        rw [add_eq_zero_iff_eq_neg]}
      rw [h5] at H
      have h6 : ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • h7.β) ↔
          ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • h7.β := by {
        refine Eq.congr_right ?_
        simp only [smul_eq_mul]
        rw [← neg_mul]
        simp only [neg_sub]}
      rw [h6] at H
      have h7 : ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • h7.β ↔
         (↑i1 - ↑j1) /(↑j2 - ↑i2 : ℂ) =  h7.β := by {
        simp only [smul_eq_mul]
        rw [div_eq_iff, mul_comm]
        intros HC
        apply hij2
        rw [sub_eq_zero] at HC
        simp only [Nat.cast_inj] at HC
        exact HC.symm}
      rw [h7] at H
      rw [H.symm]
      simp only [Int.cast_sub, Int.cast_natCast]
  · exact h7.log_zero_zero

abbrev V := vandermonde (fun t => h7.ρ q t)

lemma vandermonde_det_ne_zero : det (h7.V q) ≠ 0 := by
  by_contra H
  rw [V, det_vandermonde_eq_zero_iff] at H
  rcases H with ⟨i, j, ⟨hij, hij'⟩⟩
  apply h7.hdist q i j hij'
  exact hij

open Differentiable Complex

abbrev R : ℂ → ℂ := fun x => ∑ t, (canonicalEmbedding h7.K)
  ((algebraMap (𝓞 h7.K) h7.K) ((h7.η q hq0 h2mq) t)) h7.σ
  * exp (h7.ρ q t * x)

def iteratedDeriv_of_R (k' : ℕ) : deriv^[k'] (fun x => (h7.R q hq0 h2mq) x) =
    fun x => ∑ t, (h7.σ ((h7.η q hq0 h2mq) t)) * exp (h7.ρ q t * x) * (h7.ρ q t)^k' := by
  induction' k' with k' hk
  · simp only [pow_zero, mul_one]; rfl
  · rw [← iteratedDeriv_eq_iterate] at *
    simp only [iteratedDeriv_succ]
    conv => enter [1]; rw [hk]
    ext x
    rw [deriv, fderiv_fun_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, fderiv_eq_smul_deriv,
      deriv_mul_const_field', deriv_const_mul_field', smul_eq_mul, one_mul]
    rw [Finset.sum_congr rfl]
    intros t ht
    rw [mul_assoc, mul_assoc, mul_eq_mul_left_iff, map_eq_zero]; left
    rw [cexp_mul, mul_assoc, (pow_succ' (h7.ρ q t) k')]
    · rw [mul_comm, mul_assoc, mul_eq_mul_left_iff,
         Eq.symm (pow_succ' (h7.ρ q t) k')]; left; rfl
    · intros i hi
      apply mul ?_ (differentiable_const (h7.ρ q i ^ k'))
      · apply mul <| differentiable_const _
        apply Differentiable.cexp
        apply mul (differentiable_const _) (differentiable_fun_id)

lemma iteratedDeriv_of_R_is_zero (hR : h7.R q hq0 h2mq = 0) :
  ∀ z k', deriv^[k'] (fun z => h7.R q hq0 h2mq z) z = 0 := by
intros z k'
rw [hR]
simp only [Pi.zero_apply]
rw [← iteratedDeriv_eq_iterate]
rw [iteratedDeriv]
simp_all only [iteratedFDeriv_zero_fun, Pi.zero_apply,
  ContinuousMultilinearMap.zero_apply]

lemma vecMul_of_R_zero (hR : h7.R q hq0 h2mq = 0) :
  (h7.V q).vecMul (fun t => h7.σ ((h7.η q hq0 h2mq) t)) = 0 := by
  unfold V
  rw [funext_iff]
  intros k
  simp only [Pi.zero_apply]
  have deriv_eq : ∀ k', deriv^[k'] (fun x => (h7.R q hq0 h2mq) x) =
    fun x => ∑ t, (h7.σ (h7.η q hq0 h2mq t)) *
    exp (h7.ρ q t * x) * (h7.ρ q t)^k' := by {
      intros k'
      exact h7.iteratedDeriv_of_R q hq0 h2mq k'}
  have deriv_eq_0 : ∀ k', deriv^[k'] (fun x => h7.R q hq0 h2mq x) 0 = 0 := by {
    intros k'
    apply iteratedDeriv_of_R_is_zero
    exact hR}
  rw [← deriv_eq_0 k]
  rw [deriv_eq]
  simp only [mul_zero, exp_zero, mul_one]
  unfold vecMul dotProduct vandermonde
  simp only [of_apply]

lemma ηvec_eq_zero (hVecMulEq0 : (h7.V q).vecMul
  (fun t => h7.σ ((h7.η q hq0 h2mq) t)) = 0) :
    (fun t => h7.σ ((h7.η q hq0 h2mq) t )) = 0 := by {
  apply eq_zero_of_vecMul_eq_zero
    (h7.vandermonde_det_ne_zero q) hVecMulEq0}

lemma hbound_sigma : h7.η q hq0 h2mq ≠ 0 := by
  have := (applylemma82 h7 q hq0 h2mq).choose_spec.1
  apply this

lemma R_nonzero : h7.R q hq0 h2mq ≠ 0 := by
  by_contra H
  have HC := (ηvec_eq_zero h7 q hq0 h2mq)
    (vecMul_of_R_zero h7 q hq0 h2mq H)
  simp only at HC
  apply hbound_sigma h7 q hq0 h2mq
  rw [funext_iff] at HC
  simp only [Pi.zero_apply, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff] at HC
  unfold η at *
  ext t
  specialize HC t
  simp only [ne_eq, Pi.zero_apply, map_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  exact HC

variable (hγ : h7.α ^ h7.β = h7.σ h7.γ')

lemma sys_coe_bar :
  Complex.exp (h7.ρ q t * h7.l q u) * (h7.ρ q t ^ (h7.k q u : ℕ) *
  Complex.log h7.α ^ (-(h7.k q u) : ℤ)) = h7.σ (h7.sys_coe q u t) := by {
  calc
      _ = cexp (h7.ρ q t * h7.l q u) *
          (((↑(a q t) + ↑(b q t) • h7.β) *
          Complex.log h7.α) ^ (h7.k q u : ℕ)
          * Complex.log h7.α ^ (-↑(h7.k q u) : ℤ)) := ?_

      _ = cexp (h7.ρ q t * (h7.l q u)) *
        ( (↑(a q t) + ↑(b q t) • h7.β)^ (h7.k q u : ℕ) *
          (Complex.log h7.α) ^ (h7.k q u : ℕ) *
        Complex.log h7.α ^ (-(h7.k q u) : ℤ)) := ?_

      _ = cexp (h7.ρ q t * h7.l q u) *
        ( (↑(a q t) + ↑(b q t) • h7.β)^ (h7.k q u : ℕ) *
          ((Complex.log h7.α) ^ (h7.k q u : ℕ)
          * Complex.log h7.α ^ (-(h7.k q u) : ℤ))) := ?_

      _ = cexp (h7.ρ q t * h7.l q u) *
      ( (↑(a q t) + ↑(b q t) • h7.β)^ (h7.k q u : ℕ)) := ?_

      _ = h7.σ (h7.sys_coe q u t) := ?_

  · nth_rw 2 [ρ]
  · rw [mul_pow]
  · rw [mul_assoc]
  ·  have  : (Complex.log h7.α ^ (h7.k q u) *
         Complex.log h7.α ^ (-(h7.k q u) : ℤ)) = 1 := by {
       simp only [zpow_neg, zpow_natCast]
       refine Complex.mul_inv_cancel ?_
       by_contra H
       apply h7.log_zero_zero
       simp only [pow_eq_zero_iff', ne_eq] at H
       apply H.1}
     rw [this]
     rw [mul_one]
  · unfold sys_coe
    have h1 : h7.σ ((↑(a q t)+ ↑(b q t) • h7.β') ^ ((h7.k q u) : ℕ)) =
      (↑(a q t) + ↑(b q t) * h7.β) ^ ((h7.k q u) : ℕ) := by {
      simp only [nsmul_eq_mul, map_pow, map_add, map_natCast, map_mul]
      rw [h7.habc.2.1]}
    rw [map_mul]
    rw [map_mul]
    unfold a b k at *
    rw [h1]; clear h1
    rw [mul_comm]
    rw [mul_assoc]
    simp only [nsmul_eq_mul, map_pow,
      mul_eq_mul_left_iff, pow_eq_zero_iff', ne_eq]
    left
    have : h7.σ h7.α' ^ (a q t * h7.l q u) * h7.σ h7.γ' ^ (b q t * h7.l q u) =
    h7.α ^ (a q t * h7.l q u) * (h7.σ h7.γ')^ (b q t * h7.l q u) := by {rw [h7.habc.1]}
    unfold a b l at *
    rw [this]
    have : h7.σ h7.γ' = h7.α^h7.β := by {rw [h7.habc.2.2]}
    rw [this]
    rw [ρ]
    have : h7.α ^ ((a q t * h7.l q u)) * h7.α ^ (↑(b q t * h7.l q u) * h7.β) =
      h7.α ^ ((a q t * h7.l q u) + (↑(b q t * h7.l q u) * h7.β)) := by {
        rw [cpow_add]
        · rw [cpow_nat_mul]
          simp only [mul_eq_mul_right_iff, pow_eq_zero_iff',
            cpow_eq_zero_iff, ne_eq, mul_eq_zero,
            not_or]
          left
          rw [cpow_nat_mul]
          simp only [cpow_natCast]
          exact pow_mul' h7.α (a q t) (h7.l q u)
        · exact h7.htriv.1}
    rw [cpow_nat_mul] at this
    unfold a b l at *
    rw [this]; clear this
    rw [cpow_def_of_ne_zero]
    have : Complex.log h7.α * (↑(a q t) * ↑(h7.l q u) + ↑(b q t * (h7.l q u)) * h7.β) =
       (↑(a q t) + b q t • h7.β) *
        Complex.log h7.α * ↑(h7.l q u) := by {
      nth_rw 4 [mul_comm]
      have : ( ↑((h7.l q u) * (b q t)) * h7.β) =
        ( ↑(((b q t) * h7.β) * (h7.l q u))) := by {
        simp only [Nat.cast_mul, mul_rotate (↑(h7.l q u)) (↑(b q t)) h7.β]}
      rw [this]
      have : (↑(a q t) * ↑(h7.l q u) + ((b q t * h7.β) * (h7.l q u))) =
        ((↑(a q t)  + (b q t * h7.β)) * (h7.l q u)) :=
        Eq.symm (RightDistribClass.right_distrib
          (↑(a q t)) (↑(b q t) * h7.β) ↑(h7.l q u))
      rw [this]
      simp only [nsmul_eq_mul]
      nth_rw 1 [← mul_assoc]
      nth_rw 1 [mul_comm]
      nth_rw 1 [mul_comm]
      nth_rw 5 [mul_comm]}
    unfold a b l at *
    rw [this]
    · exact h7.htriv.1}

include hq0 h2mq in
lemma sys_coe_foo :(Complex.log h7.α)^(-(h7.k q u) : ℤ) *
 deriv^[h7.k q u] (h7.R q hq0 h2mq) (h7.l q u) =
     ∑ t, h7.σ ↑((h7.η q hq0 h2mq) t) * h7.σ (h7.sys_coe q u t) := by
  rw [iteratedDeriv_of_R, mul_sum, Finset.sum_congr rfl]
  intros t ht
  rw [mul_assoc, mul_comm, mul_assoc]
  simp only [mul_eq_mul_left_iff, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  left
  have := sys_coe_bar h7 q u t
  unfold l at this
  rw [mul_assoc]
  unfold l
  exact this

lemma deriv_sum_blah :
  h7.σ (h7.c_coeffs q) * ((Complex.log h7.α)^ (-(h7.k q u) : ℤ) *
  deriv^[h7.k q u] (h7.R q hq0 h2mq) (h7.l q u)) =
    h7.σ ((h7.A q hq0 h2mq *ᵥ (h7.η q hq0 h2mq)) u) := by {
    have := sys_coe_foo h7 q hq0 u h2mq
    rw [this]
    unfold Matrix.mulVec
    unfold dotProduct
    simp only [← map_mul, ← map_sum]
    congr
    simp only [map_sum, map_mul]
    rw [mul_sum]
    rw [Finset.sum_congr rfl]
    intros x hx
    simp (config := { unfoldPartialApp := true }) only [A]
    simp only [RingOfIntegers.restrict, zsmul_eq_mul, RingOfIntegers.map_mk]
    simp only [Int.cast_mul, Int.cast_pow]
    simp only [mul_assoc]
    rw [mul_comm  (a:= (↑(h7.η q hq0 h2mq x)))
    (b:=
          ((↑(a q x) + b q x • h7.β') ^ h7.k q u *
           (h7.α' ^ (a q x * h7.l q u) * h7.γ' ^ (b q x * h7.l q u))))]
    simp only [mul_assoc]
    }

lemma deriv_sum_blah_zero :
  h7.σ (h7.c_coeffs q) * ((Complex.log h7.α)^ (-(h7.k q u) : ℤ) *
  deriv^[h7.k q u] (h7.R q hq0 h2mq) (h7.l q u)) =
    0 := by {
      rw [deriv_sum_blah]
      have hMt0 := (applylemma82 h7 q hq0 h2mq).choose_spec.2.1
      simp only [ne_eq, Nat.cast_mul, Real.rpow_natCast, map_eq_zero,
        FaithfulSMul.algebraMap_eq_zero_iff] at *
      unfold η
      simp_all only [ne_eq, Nat.cast_mul, Real.rpow_natCast, Pi.zero_apply]
    }

lemma iteratedDeriv_vanishes (k : Fin (h7.n q)) (l' : Fin (h7.m)) :
  deriv^[k] (h7.R q hq0 h2mq) (l' + 1) = 0 := by
  let u : Fin (h7.m * h7.n q) := (finProdFinEquiv.toFun ⟨l',k⟩)
  have h1 := deriv_sum_blah_zero h7 q hq0 u h2mq
  unfold GelfondSchneiderSetup.k at *
  unfold GelfondSchneiderSetup.l at *
  unfold u at *
  simp only [Equiv.toFun_as_coe,
    Equiv.symm_apply_apply] at *
  have : (h7.σ (h7.c_coeffs q) *
   (Complex.log h7.α)^(-k : ℤ)) * deriv^[k] (h7.R q hq0 h2mq) (l'+1) =
    (h7.σ (h7.c_coeffs q) *
    (Complex.log h7.α)^(-k : ℤ)) * 0 → deriv^[k] (h7.R q hq0 h2mq) (l' + 1) = 0 := by {
      apply mul_left_cancel₀
      by_contra H
      simp only [Int.cast_mul, Int.cast_pow, map_mul, map_pow,
        map_intCast, zpow_neg, zpow_natCast,
        mul_eq_zero, pow_eq_zero_iff', Int.cast_eq_zero, ne_eq, not_or, inv_eq_zero] at H
      rcases H with ⟨h1, h2⟩
      · apply h7.c₁neq0; assumption
      ·  apply h7.c₁neq0; rename_i h2; exact h2.1
      · apply h7.c₁neq0; rename_i h2; exact h2.1
      ·  apply h7.log_zero_zero; rename_i h2; exact h2.1
        }
  rw [this]
  rw [mul_zero]
  rw [mul_assoc]
  simp only [mul_assoc] at *
  rw [← h1]
  simp only [Int.cast_mul, Int.cast_pow, map_mul, map_pow, map_intCast, zpow_neg, zpow_natCast,
    Nat.cast_add, Nat.cast_one]


lemma R_analyt_at_point (point : ℂ) : AnalyticAt ℂ (h7.R q hq0 h2mq) point := by
  apply Differentiable.analyticAt
  unfold R
  apply Differentiable.fun_sum
  intros i hk
  apply Differentiable.fun_mul
  · apply differentiable_const
  · apply (differentiable_exp.comp ((differentiable_const _).mul differentiable_fun_id))

lemma anever : ∀ (z : ℂ), AnalyticAt ℂ (h7.R q hq0 h2mq) z := by
  intros z
  unfold R
  apply Differentiable.analyticAt
  apply Differentiable.fun_sum
  intros i hk
  exact
  (differentiable_const _).mul
    (differentiable_exp.comp ((differentiable_const _).mul differentiable_fun_id))

lemma order_neq_top : ∀ (l' : Fin (h7.m)),
    analyticOrderAt (h7.R q hq0 h2mq) (l' + 1) ≠ ⊤ := by {
  intros l' H
  rw [← zero_iff_order_inf] at H
  apply h7.R_nonzero q hq0 h2mq
  rw [funext_iff]
  intros z
  exact H z
  intros z
  exact h7.anever q hq0 h2mq z}

lemma order_neq_top_min_one : ∀ z : ℂ,
  analyticOrderAt (h7.R q hq0 h2mq) z ≠ ⊤ := by {
  intros l' H
  rw [← zero_iff_order_inf] at H
  apply h7.R_nonzero
  rw [funext_iff]
  intros z
  exact H z
  intros z
  exact h7.anever q hq0 h2mq z}

lemma Rorder_exists (z : ℂ) :
  ∃ r, (analyticOrderAt (h7.R q hq0 h2mq) z) = some r := by
  have : (analyticOrderAt (h7.R q hq0 h2mq) z) ≠ ⊤ := by
   exact h7.order_neq_top_min_one q hq0 h2mq z
  revert this
  cases'(analyticOrderAt (h7.R q hq0 h2mq) z) with r
  · intro this_1; simp_all only [ne_eq, not_true_eq_false]
  · intros hr; use r; rfl

def R_order (z : ℂ) : ℕ :=
  (Rorder_exists h7 q hq0 h2mq z).choose

def R_order_prop {z : ℂ} :=
  (Rorder_exists h7 q hq0 h2mq z).choose_spec

lemma R_order_eq (z) :
  (analyticOrderAt (h7.R q hq0 h2mq) z)
    = h7.R_order q hq0 h2mq z :=
    (Rorder_exists h7 q hq0 h2mq z).choose_spec

lemma exists_min_order_at :
  let s : Finset (Fin (h7.m)) := Finset.univ
  ∃ l₀' ∈ s, (∃ y, (analyticOrderAt (h7.R q hq0 h2mq) (l₀' + 1)) = y ∧
   (∀ (l' : Fin (h7.m)), l' ∈ s → y ≤ (analyticOrderAt (h7.R q hq0 h2mq) (l' + 1)))) := by
  intros s
  have Hs : s.Nonempty := by {
     refine univ_nonempty_iff.mpr ?_
     refine Fin.pos_iff_nonempty.mp ?_
     exact h7.hm}
  let f : (Fin (h7.m)) → ℕ∞ := fun x => (analyticOrderAt (h7.R q hq0 h2mq) (x + 1))
  have := exists_mem_finset_min' s f Hs
  obtain ⟨x, hx, ⟨r, h1, h2⟩⟩ := this
  use x
  constructor
  · exact hx
  · constructor
    · constructor
      · exact id (Eq.symm h1)
      · intros x hx
        exact h2 x hx

abbrev l₀' : Fin (h7.m) := (exists_min_order_at h7 q hq0 h2mq).choose

--def l₀ : ℂ := (h7.l₀' q hq0 h2mq) + 1

abbrev l₀_prop :=
  (exists_min_order_at h7 q hq0 h2mq).choose_spec.2

abbrev r' := (l₀_prop h7 q hq0 h2mq).choose

abbrev r'_prop :
  let s : Finset (Fin (h7.m)) := Finset.univ
  analyticOrderAt (h7.R q hq0 h2mq) ↑↑(h7.l₀' q hq0 h2mq + 1 : ℂ) =
    h7.r' q hq0 h2mq ∧
    ∀ l' ∈ s, h7.r' q hq0 h2mq ≤ analyticOrderAt (h7.R q hq0 h2mq) (↑↑l' +1) := by
  let l₀_prop := h7.l₀_prop q hq0 h2mq
  have := (h7.l₀_prop q hq0 h2mq).choose_spec
  exact this

lemma r_exists :
  ∃ r, r' h7 q hq0 h2mq = some r := by
  have := (r'_prop h7 q hq0 h2mq).1
  have H := order_neq_top_min_one h7 q hq0 h2mq (l₀' h7 q hq0 h2mq + 1)
  have : r' h7 q hq0 h2mq ≠ ⊤ := by rw [this] at H; exact H
  revert this
  cases' r' h7 q hq0 h2mq with r
  · intro this_1; simp_all only [ne_eq, not_true_eq_false]
  · intros hr; use r; rfl

def r := (r_exists h7 q hq0 h2mq).choose

abbrev r_spec : h7.r' q hq0 h2mq = ↑(h7.r q hq0 h2mq) :=
  (r_exists h7 q hq0 h2mq).choose_spec

abbrev r_prop :
  let s : Finset (Fin (h7.m)) := Finset.univ
  analyticOrderAt (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) =
   h7.r q hq0 h2mq ∧
  ∀ l' ∈ s, h7.r q hq0 h2mq ≤ analyticOrderAt (h7.R q hq0 h2mq) (↑↑l' + 1) := by
  intros s
  rw [← (h7.r_spec q hq0 h2mq)]
  apply h7.r'_prop q hq0 h2mq

lemma r_div_q_geq_0 : 0 ≤ (h7.r q hq0 h2mq) / q := by {simp_all only [zero_le]}

lemma exists_nonzero_iteratedFDeriv : deriv^[h7.r q hq0 h2mq]
 (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) ≠ 0 := by {
  have Hrprop := (h7.r_prop q hq0 h2mq).1
  obtain ⟨l₀, y, r, h1, h2⟩ :=
    (h7.exists_min_order_at q hq0 h2mq)
  have hA1 := h7.R_analyt_at_point q hq0 h2mq (h7.l₀' q hq0 h2mq + 1)
  exact ((iterated_deriv_eq_zero_if_order_eq_n (h7.l₀' q hq0 h2mq + 1) (h7.r q hq0 h2mq)
   (h7.R q hq0 h2mq) hA1) Hrprop).2}

lemma order_geq_n_foo (l' : Fin (h7.m)) :
  (∀ k', k' < h7.n q → deriv^[k'] (h7.R q hq0 h2mq) (l' + 1) = 0)
   → h7.n q ≤ analyticOrderAt (h7.R q hq0 h2mq) (l' + 1) := by
  intros H
  apply iterated_deriv_eq_zero_imp_n_leq_order
  · exact h7.anever q hq0 h2mq (l' + 1)
  · apply order_neq_top h7 q hq0 h2mq l'
  exact H

lemma order_geq_n : ∀ l' : Fin (h7.m),
    h7.n q ≤ analyticOrderAt (h7.R q hq0 h2mq) (l' + 1) := by
  intros l'
  apply order_geq_n_foo
  intros k hk
  have H := h7.iteratedDeriv_vanishes q hq0 h2mq ⟨k,hk⟩ l'
  rw [H]

lemma n_leq_r : h7.n q ≤ h7.r q hq0 h2mq := by
    have := h7.r_prop q hq0 h2mq
    obtain ⟨hr,hprop⟩ := this
    have := h7.order_geq_n q hq0 h2mq (h7.l₀' q hq0 h2mq)
    have H : h7.n q ≤ (h7.r q hq0 h2mq : ℕ∞) → h7.n q ≤ h7.r q hq0 h2mq := by {
      simp only [Nat.cast_le, imp_self]}
    apply H
    rw [← hr]
    apply this

lemma rneq0 : h7.r q hq0 h2mq ≠ 0 := by
  have H := n_leq_r h7 q hq0 h2mq
  have : 0 < h7.n q := by
    unfold n; simp only [Nat.div_pos_iff, Nat.ofNat_pos,
    mul_pos_iff_of_pos_left]
    constructor
    · unfold m; exact Nat.zero_lt_succ (2 * h7.h + 1)
    · exact qsqrt_leq_2m h7 q hq0 h2mq
  simp_all only [ne_eq]
  apply Aesop.BuiltinRules.not_intro
  intro a
  simp_all only [nonpos_iff_eq_zero, lt_self_iff_false]

lemma r_qt_0 : 0 < h7.r q hq0 h2mq := by
  refine Nat.zero_lt_of_ne_zero ?_
  exact h7.rneq0 q hq0 h2mq

lemma one_le_r : 1 ≤  h7.r q hq0 h2mq := by
  refine Nat.zero_lt_of_ne_zero ?_
  exact h7.rneq0 q hq0 h2mq

lemma l0_neq0 :  0 ≠ (h7.l₀' q hq0 h2mq : ℕ) := by {
  have := h7.l₀_prop q hq0 h2mq
  obtain ⟨r, hprop, H2⟩ := this
  by_contra H
  unfold l₀' at *
  rw [← H] at hprop
  simp only [CharP.cast_eq_zero, zero_add] at hprop
  let one : Fin (h7.m) := ⟨0, by {
    have : 1 < h7.m := by {sorry}
    sorry}⟩
  sorry



}


def cρ : ℤ := abs (h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁^(2*h7.m * q))

abbrev sys_coe_r : h7.K := (a q t + b q t • h7.β')^(h7.r q hq0 h2mq) *
 h7.α' ^(a q t * (h7.l₀' q hq0 h2mq + 1)) * h7.γ' ^(b q t * (h7.l₀' q hq0 h2mq + 1))

include u t in
lemma sys_coe_ne_zero_r : h7.sys_coe_r q hq0 t h2mq ≠ 0 := by
  unfold sys_coe_r
  intros H
  simp only [mul_eq_zero, pow_eq_zero_iff'] at H
  cases' H with H1 H2
  · cases' H1 with H1 H2
    · rcases H1 with ⟨h1, h2⟩
      have := h7.β'_neq_zero q t (h7.r q hq0 h2mq)
      apply this
      rw [h1]
      simp only [pow_eq_zero_iff', ne_eq, true_and]
      exact h2
    · exfalso
      exact h7.hneq0.1 H2.1
  · exfalso
    exact h7.hneq0.2.2 H2.1

def ρᵣ : ℂ := (Complex.log h7.α)^(-(h7.r q hq0 h2mq) : ℤ) *
 deriv^[h7.r q hq0 h2mq] (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1)

lemma sys_coe_bar_r :
  exp (h7.ρ q t * (h7.l₀' q hq0 h2mq + 1)) *
  h7.ρ q t ^ (h7.r q hq0 h2mq : ℕ) *
  Complex.log h7.α ^ (-(h7.r q hq0 h2mq) : ℤ) = h7.σ (h7.sys_coe_r q hq0 t h2mq) := by {
    nth_rw 2 [ρ]
    rw [mul_pow, mul_assoc, mul_assoc]
    have : (Complex.log h7.α ^ (h7.r q hq0 h2mq : ℕ) *
      Complex.log h7.α ^ (-h7.r q hq0 h2mq : ℤ)) = 1 := by {
      simp only [zpow_neg, zpow_natCast]
      refine Complex.mul_inv_cancel ?_
      by_contra H
      apply h7.log_zero_zero
      simp only [pow_eq_zero_iff', ne_eq] at H
      apply H.1}
    rw [this];clear this
    rw [mul_one]
    unfold sys_coe_r
    rw [mul_comm]
    change _ = h7.σ ((↑(a q t) + b q t • h7.β') ^ (h7.r q hq0 h2mq : ℕ)
      * (h7.α' ^ (a q t * (h7.l₀' q hq0 h2mq + 1))) * (h7.γ' ^ (b q t * (h7.l₀' q hq0 h2mq + 1))))
    rw [map_mul]
    rw [map_mul]
    nth_rw 1 [mul_assoc]
    have : h7.σ ((↑(a q t) + (b q t) • h7.β') ^ (h7.r q hq0 h2mq)) =
        (↑(a q t) + ↑(b q t) * h7.β) ^ ((h7.r q hq0 h2mq)) := by {
      simp only [nsmul_eq_mul, map_pow, map_add, map_natCast, map_mul]
      simp_all only [a, b]
      congr
      rw [h7.habc.2.1]
      }
    rw [this];clear this
    rw [map_pow]
    rw [map_pow]
    have : (↑(a q t) + (b q t) • h7.β) ^
      (h7.r q hq0 h2mq) * cexp (h7.ρ q t * (h7.l₀' q hq0 h2mq + 1)) =
        (↑(a q t) + ↑(b q t) * h7.β)^(h7.r q hq0 h2mq) *
          cexp (h7.ρ q t * (h7.l₀' q hq0 h2mq + 1)) := by {
      simp_all only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply,
        Fin.coe_modNat,
        Fin.coe_divNat, Nat.cast_add, Nat.cast_one, nsmul_eq_mul,b, a]}
    rw [this];clear this
    simp only [mul_eq_mul_left_iff, pow_eq_zero_iff']
    left
    rw [ρ]
    have : cexp (( ↑(a q t) + (b q t) • h7.β) * Complex.log h7.α * (h7.l₀' q hq0 h2mq + 1)
        ) =
        cexp ((↑(a q t) + ↑(b q t) • h7.β) * Complex.log h7.α * (h7.l₀' q hq0 h2mq +1)) := by {
          simp_all only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply,
          Fin.coe_modNat,
            Fin.coe_divNat, Nat.cast_add, Nat.cast_one,
            nsmul_eq_mul, b, a]}
    rw [this];clear this
    have : h7.σ h7.α' ^ ((a q t) * (h7.l₀' q hq0 h2mq + 1)) *
       h7.σ h7.γ' ^ ((b q t) * (h7.l₀' q hq0 h2mq + 1)) =
       h7.α ^ ((a q t) * (h7.l₀' q hq0 h2mq + 1)) *
       (h7.σ h7.γ')^ ((b q t) * (h7.l₀' q hq0 h2mq + 1)) := by {
      simp only [mul_eq_mul_right_iff, pow_eq_zero_iff',
        map_eq_zero, ne_eq, mul_eq_zero, not_or]
      left
      congr
      rw [← h7.habc.1]}
    rw [← h7.habc.1]
    --rw [← h7.habc.2.2]
    --rw [this]
    have : h7.σ h7.γ' = h7.α^h7.β := by {rw [h7.habc.2.2]}
    rw [this]; clear this
    have : Complex.exp (Complex.log h7.α) = h7.α := by {
      apply Complex.exp_log
      exact h7.htriv.1}
    clear this
    rw [← cpow_nat_mul]
    have : cexp ((↑(a q t) + (b q t) • h7.β) *
      Complex.log h7.α * (h7.l₀' q hq0 h2mq +1)) =
        h7.α ^ ((a q t) * (h7.l₀' q hq0 h2mq + 1)) *
        h7.α ^ (↑((b q t) * (h7.l₀' q hq0 h2mq +1 )) * h7.β) ↔
      cexp ((↑(a q t) + (b q t) • h7.β) *
      Complex.log h7.α * (h7.l₀' q hq0 h2mq + 1)) =
        h7.α ^ (((a q t) * (h7.l₀' q hq0 h2mq +1)) +
         ((↑(b q t) * (h7.l₀' q hq0 h2mq + 1)) * h7.β)) := by {
        rw [cpow_add]
        simp only [nsmul_eq_mul, Nat.cast_mul]
        norm_cast
        exact h7.htriv.1}
    rw [this]; clear this
    rw [cpow_def_of_ne_zero]
    have : Complex.log h7.α * (↑(a q t) * (h7.l₀' q hq0 h2mq +1) +
       ((b q t) * (h7.l₀' q hq0 h2mq + 1)) * h7.β) =
        (↑(a q t) + (b q t) • h7.β) * Complex.log h7.α * (h7.l₀' q hq0 h2mq + 1) := by {
      nth_rw 4 [mul_comm]
      have : ( ((h7.l₀' q hq0 h2mq + 1) * (b q t)) * h7.β) =
        ( (((b q t) * h7.β) * (h7.l₀' q hq0 h2mq + 1))) := by {
          exact mul_rotate (↑↑(h7.l₀' q hq0 h2mq) + 1) (↑(b q t)) h7.β
          }
      rw [this];clear this
      have H : (↑(a q t) * (h7.l₀' q hq0 h2mq + 1) +
        (((b q t) * h7.β) * (h7.l₀' q hq0 h2mq +1))) =
        (((a q t)  + ((b q t) * h7.β)) *  ↑((↑(h7.l₀' q hq0 h2mq : ℕ) + 1  :ℂ))) :=
        Eq.symm (RightDistribClass.right_distrib
          (↑(a q t)) (↑(b q t) * h7.β) (h7.l₀' q hq0 h2mq + 1))
      --norm_cast at this
      rw [H]



      rw [mul_comm, mul_assoc]
      nth_rw 3 [mul_comm]
      rw [← mul_assoc, nsmul_eq_mul]
      }
    rw [this]
    exact h7.htriv.1
    }


def deriv_R_k_eval_at_l0' :
  deriv^[h7.r q hq0 h2mq] (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) =
  ∑ t, h7.σ ((h7.η q hq0 h2mq) t) *
  cexp (h7.ρ q t * (h7.l₀' q hq0 h2mq + 1)) * (h7.ρ q t) ^ (h7.r q hq0 h2mq) := by
  rw [iteratedDeriv_of_R]

lemma sys_coe_foo_r :
 (Complex.log h7.α)^(-h7.r q hq0 h2mq : ℤ) * deriv^[h7.r q hq0 h2mq]
 (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) =
 ∑ t, h7.σ ↑((h7.η q hq0 h2mq) t) * h7.σ (h7.sys_coe_r q hq0 t h2mq) := by {
  rw [h7.deriv_R_k_eval_at_l0' q hq0 h2mq, mul_sum, Finset.sum_congr rfl]
  intros t ht
  rw [mul_assoc, mul_comm, mul_assoc]
  unfold η
  simp only [mul_eq_mul_left_iff, map_eq_zero,
    FaithfulSMul.algebraMap_eq_zero_iff]
  left
  have := sys_coe_bar_r h7 q hq0 t h2mq
  rw [← this]
  }

















































































def rho := ∑ t : Fin (q * q), (h7.η q hq0 h2mq t) * (h7.sys_coe_r q hq0 t h2mq)

def rho_eq_ρᵣ : h7.σ (rho h7 q hq0 h2mq) = ρᵣ h7 q hq0 h2mq := by
  unfold rho ρᵣ
  rw [sys_coe_foo_r]
  simp only [map_sum, map_mul, nsmul_eq_mul, map_pow, map_add, map_natCast]

lemma ρᵣ_nonzero : ρᵣ h7 q hq0 h2mq ≠ 0 := by
  unfold ρᵣ
  simp only [zpow_neg, zpow_natCast, mul_eq_zero, inv_eq_zero,
    pow_eq_zero_iff', ne_eq, not_or, not_and, Decidable.not_not]
  constructor
  · intros hlog
    by_contra H
    apply h7.log_zero_zero
    exact hlog
  · have := h7.exists_nonzero_iteratedFDeriv q hq0 h2mq
    simp_all only [ne_eq, not_false_eq_true]

lemma cρ_ne_zero : h7.cρ q hq0 h2mq ≠ 0 := by
  unfold cρ
  apply abs_ne_zero.mpr <| mul_ne_zero _ _
  all_goals { apply pow_ne_zero _ (h7.c₁neq0) }

lemma c₁bρ (a b n : ℕ) : 1 ≤ n → h7.k q u ≤ n - 1 → 1 ≤ (a : ℕ) → 1 ≤ (b : ℕ) →
  IsIntegral ℤ (h7.c₁^(n - 1) • (a + b • h7.β') ^ (h7.k q u)) := by  {
  intros hn hkn ha hb
  have : h7.c₁^(n - 1) = h7.c₁ ^ (n - 1 - (h7.k q u))
    * h7.c₁^(h7.k q u) := by {
    simp_all only [← pow_add, Nat.sub_add_cancel]}
  rw [this]
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, nsmul_eq_mul, mul_assoc]
  apply IsIntegral.mul
  · apply IsIntegral.pow
    · apply IsIntegral.Cast
  rw [← mul_pow]
  apply IsIntegral.pow
  rw [mul_add]
  apply IsIntegral.add
  · apply IsIntegral.mul <| IsIntegral.Cast _ _
    · apply IsIntegral.Nat
  rw [mul_comm, mul_assoc]
  apply IsIntegral.mul <| IsIntegral.Nat _ _
  rw [mul_comm, ← zsmul_eq_mul]
  exact h7.isIntegral_c₁β}

lemma ρ_is_int :
  IsIntegral ℤ (h7.cρ q hq0 h2mq • rho h7 q hq0 h2mq) := by
  unfold rho
  unfold cρ
  unfold sys_coe_r
  have : h7.c₁ ^ (2 * h7.m * q) = h7.c₁ ^ (h7.m * q)
  * h7.c₁ ^ (h7.m * q) := by {
      rw [← pow_add]; ring}
  rw [this]
  cases' abs_choice (h7.c₁ ^ h7.r q hq0 h2mq
  * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) with H1 H2
  · rw [← mul_assoc, H1]
    rw [Finset.smul_sum]
    apply IsIntegral.sum
    intros x hx
    rw [zsmul_eq_mul]
    nth_rw 1 [mul_comm]
    rw [mul_assoc]
    apply IsIntegral.mul
    · exact RingOfIntegers.isIntegral_coe ((h7.η q hq0 h2mq) x)
    · rw [mul_comm]
      rw [← zsmul_eq_mul]
      have := triple_comm h7.K
        (h7.c₁^(h7.r q hq0 h2mq) : ℤ)
        (h7.c₁^(h7.m * q) : ℤ)
        (h7.c₁^(h7.m * q) : ℤ)
        (((a q x : ℕ) + b q x • h7.β')^(h7.r q hq0 h2mq))
        (h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)))
        (h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1)))
      have : IsIntegral ℤ
         ((h7.c₁ ^ (h7.r q hq0 h2mq) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) •
        ((↑(a q x) + b q x • h7.β') ^ (h7.r q hq0 h2mq) *
          h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
          h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1)))) =
       IsIntegral ℤ
         (h7.c₁ ^ (h7.r q hq0 h2mq) • (↑(a q x) + b q x • h7.β') ^ (h7.r q hq0 h2mq) *
          h7.c₁ ^ (h7.m * q) • h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
          h7.c₁ ^ (h7.m * q) • h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1))) := by {
        rw [← this]
          }
      simp_rw [this]
      apply IsIntegral.mul
      · apply IsIntegral.mul
        · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow]
          rw [← mul_pow]
          apply IsIntegral.pow
          rw [mul_add]
          apply IsIntegral.add
          · apply IsIntegral.mul <| IsIntegral.Cast _ _
            · apply IsIntegral.Nat
          · rw [mul_comm]
            rw [mul_assoc]
            apply IsIntegral.mul
            · apply IsIntegral.Nat
            · rw [mul_comm];
              have := h7.isIntegral_c₁β
              simp only [zsmul_eq_mul] at this
              exact this
        · apply h7.c₁ac
          · rw [mul_comm]
            apply Nat.mul_le_mul
            · exact bar' (h7.l₀' q hq0 h2mq)
            · exact bar' (finProdFinEquiv.symm.toFun x).1
          · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁α
      · have : h7.c₁ ^ (h7.m * q - ((b q x) * (h7.l₀' q hq0 h2mq + 1))) *
           (h7.c₁ ^ ((b q x) * (h7.l₀' q hq0 h2mq + 1))) =
              (h7.c₁ ^ ((h7.m * q))) := by
          rw [← pow_add,Nat.sub_add_cancel]
          nth_rw 1 [mul_comm]
          apply mul_le_mul
          · exact bar' (h7.l₀' q hq0 h2mq)
          · change (b q x) ≤ q
            have : ↑(finProdFinEquiv.symm.toFun x).2 ≤ q := Fin.is_le'
            exact bar' (finProdFinEquiv.symm.toFun x).2
          · simp only [zero_le]
          · simp only [zero_le]
        rw [← this]
        simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow]
        rw [mul_assoc]
        apply IsIntegral.mul
        · apply IsIntegral.pow
          · apply IsIntegral.Cast
        · rw [← mul_pow]
          apply IsIntegral.pow
          · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁γ
  · rw [Finset.smul_sum]
    apply IsIntegral.sum
    intros x hx
    rw [← mul_assoc, H2]
    rw [zsmul_eq_mul]
    nth_rw 1 [mul_comm]
    rw [mul_assoc]
    apply IsIntegral.mul
    · exact RingOfIntegers.isIntegral_coe ((h7.η q hq0 h2mq) x)
    · rw [mul_comm]
      rw [← zsmul_eq_mul]
      have H := triple_comm h7.K
        (h7.c₁^(h7.r q hq0 h2mq))
        (h7.c₁^(h7.m * q) : ℤ)
        (h7.c₁^(h7.m * q) : ℤ)
        (((a q x : ℕ) + (b q x) • h7.β')^(h7.r q hq0 h2mq))
        (h7.α' ^ ((a q x) * ((h7.l₀' q hq0 h2mq + 1))))
        (h7.γ' ^ ((b q x) * ((h7.l₀' q hq0 h2mq + 1))))
      have : IsIntegral ℤ (-(h7.c₁ ^ h7.r q hq0 h2mq * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)) •
    ((↑(a q x) + b q x • h7.β') ^ h7.r q hq0 h2mq * h7.α' ^ (a q x * (h7.l₀' q hq0 h2mq + 1)) *
      h7.γ' ^ (b q x * (h7.l₀' q hq0 h2mq + 1)))) =
         IsIntegral ℤ ((h7.c₁ ^ (h7.r q hq0 h2mq) •
          (↑(a q x) + (b q x) • h7.β') ^ (h7.r q hq0 h2mq)
           * h7.c₁ ^ (h7.m * q) • h7.α' ^ ((a q x) *
           (h7.l₀' q hq0 h2mq + 1)) * h7.c₁ ^ (h7.m * q) •
             h7.γ' ^ ((b q x) * (h7.l₀' q hq0 h2mq + 1)))) := by
          rw [← H]
          rw [neg_smul]
          simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_mul, Int.cast_pow,
            IsIntegral.neg_iff]
      clear H
      rw [this]
      apply IsIntegral.mul
      · apply IsIntegral.mul
        · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow]
          rw [← mul_pow]
          apply IsIntegral.pow
          rw [mul_add]
          · apply IsIntegral.add
            · apply IsIntegral.mul <| IsIntegral.Cast _ _
              · apply IsIntegral.Nat
            ·rw [mul_comm, mul_assoc]
             apply IsIntegral.mul <| IsIntegral.Nat _ _
             rw [mul_comm, ← zsmul_eq_mul]
             exact h7.isIntegral_c₁β
        · apply h7.c₁ac
          · rw [mul_comm]
            apply Nat.mul_le_mul
            exact bar' (h7.l₀' q hq0 h2mq)
            exact bar' (finProdFinEquiv.symm.toFun x).1
          · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁α
      · have : h7.c₁ ^ (h7.m * q - (b q x * (h7.l₀' q hq0 h2mq + 1))) *
           (h7.c₁ ^ ((b q x) * (h7.l₀' q hq0 h2mq + 1))) = (h7.c₁ ^ ((h7.m * q))) := by
          rw [← pow_add, Nat.sub_add_cancel]
          nth_rw 1 [mul_comm]
          apply mul_le_mul
          · exact bar' (h7.l₀' q hq0 h2mq)
          · exact bar' (finProdFinEquiv.symm.toFun x).2
          · simp only [zero_le]
          · simp only [zero_le]
        rw [← this]
        simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow]
        rw [mul_assoc]
        apply IsIntegral.mul
        · apply IsIntegral.pow
          · apply IsIntegral.Cast
        · rw [← mul_pow]
          apply IsIntegral.pow
          · rw [← zsmul_eq_mul]; exact h7.isIntegral_c₁γ

def c1ρ : 𝓞 h7.K := RingOfIntegers.restrict _
  (fun _ => (ρ_is_int h7 q hq0 h2mq)) ℤ

lemma one_leq_c1rho : 1 ≤ ↑(h7.cρ q hq0 h2mq) := by
  apply Int.one_le_abs
  by_contra H
  simp only [mul_eq_zero, pow_eq_zero_iff', ne_eq,
    OfNat.ofNat_ne_zero, false_or, not_or] at H
  cases' H with h1 h2
  · apply (h7.c₁neq0)
    exact h1.1
  · apply (h7.c₁neq0)
    exact h2.1

lemma one_leq_norm_c1rho : 1 ≤ norm (h7.cρ q hq0 h2mq) := by
  have := one_leq_c1rho h7 q hq0 h2mq
  have : |(h7.cρ q hq0 h2mq)| = ‖(h7.cρ q hq0 h2mq : ℤ)‖ := by
    simp only [Int.cast_abs]
    exact rfl
  rw [← this]
  simp only [Int.cast_abs, ge_iff_le]
  have:= Int.one_le_abs (z:= (h7.cρ q hq0 h2mq))
  norm_cast
  apply this
  exact cρ_ne_zero h7 q hq0 h2mq

lemma zero_leq_c1rho : 0 ≤ ↑(h7.cρ q hq0 h2mq) := by
    have := one_leq_c1rho h7 q hq0 h2mq
    exact Int.le_of_lt this

lemma crho_leq_abs_crho :
    (h7.cρ q hq0 h2mq) ≤ abs (h7.cρ q hq0 h2mq):= by
  apply le_abs_self

lemma abs_crho_leq_norm_crho :
    abs (h7.cρ q hq0 h2mq) ≤ norm (h7.cρ q hq0 h2mq) := by
  simp only [Int.cast_abs]
  rfl

lemma norm_crho_leq_house_crho : norm (h7.cρ q hq0 h2mq) ≤
  house (h7.cρ q hq0 h2mq : h7.K) := by
  rw [house_intCast]
  simp only [Int.cast_abs]
  exact Preorder.le_refl ‖h7.cρ q hq0 h2mq‖

lemma norm_cρ_pos : 0 < ‖h7.cρ q hq0 h2mq‖ := by
  rw [norm_pos_iff]
  have := h7.cρ_ne_zero q hq0 h2mq
  unfold cρ at this
  exact this

lemma h1 : 1 ≤ ‖h7.cρ q hq0 h2mq‖ ^ Module.finrank ℚ h7.K := by {
      rw [one_le_pow_iff_of_nonneg]
      · rw [Int.norm_eq_abs]
        have := (h7.norm_cρ_pos q hq0 h2mq)
        rw [Int.norm_eq_abs] at this
        unfold cρ
        simp only [Int.cast_abs, Int.cast_mul, Int.cast_pow, abs_abs]
        rw [← pow_add]
        simp only [abs_pow]
        have : 1 ≤ |↑(h7.c₁)| := by {
          rw [le_abs']
          right
          exact h7.one_leq_c₁}
        refine one_le_pow₀ ?_
        exact mod_cast this
      · apply norm_nonneg
      · have : 0 < Module.finrank ℚ h7.K  := Module.finrank_pos
        simp_all only [ne_eq]
        intro a
        simp_all only [lt_self_iff_false]}

  lemma norm_Algebra_norm_rho_nonzero :
    ‖(Algebra.norm ℚ) (rho h7 q hq0 h2mq)‖ ≠ 0 := by
    rw [norm_ne_zero_iff, Algebra.norm_ne_zero_iff]
    intros H
    apply_fun h7.σ at H
    rw [rho_eq_ρᵣ] at H
    simp only [map_zero] at H
    apply ρᵣ_nonzero h7 q hq0 h2mq
    exact H

lemma c1rho_neq_0 : h7.c1ρ q hq0 h2mq ≠ 0 := by
  intros H
  injection H with H1
  simp only [zsmul_eq_mul, mul_eq_zero, Int.cast_eq_zero] at H1
  cases' H1 with h1 h2
  · apply cρ_ne_zero h7 q hq0 h2mq
    exact h1
  · apply_fun h7.σ at h2
    rw [rho_eq_ρᵣ] at h2
    simp only [map_zero] at h2
    apply ρᵣ_nonzero h7 q hq0 h2mq
    exact h2

lemma house_geq_1 : 1 ≤ house (h7.c1ρ q hq0 h2mq : h7.K) := by
  apply house_gt_one_of_isIntegral
  exact RingOfIntegers.isIntegral_coe (h7.c1ρ q hq0 h2mq)
  have := one_leq_c1rho h7 q hq0 h2mq
  simp only [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  rw [← ne_eq]
  exact c1rho_neq_0 h7 q hq0 h2mq

--#check norm_le_house_norm

lemma eq5zero : 1 ≤ norm
    (Algebra.norm ℚ ((algebraMap (𝓞 h7.K) h7.K) (h7.c1ρ q hq0 h2mq))) := by
  --rw [this]
  have := norm_le_house_norm ((algebraMap (𝓞 h7.K) h7.K) (h7.c1ρ q hq0 h2mq))

  -- have := abs_norm_eq_prod_embeddings_norm
  --   ((algebraMap (𝓞 h7.K) h7.K) (h7.c1ρ q hq0 h2mq))
  -- rw [etc (σ0 := ((h7.σ)).toRatAlgHom)] at this
  -- rw [this]
  -- simp only [RingHom.toRatAlgHom_apply, Complex.norm_mul, norm_prod] at this


  --have := exists_conjugate_abs_gt_one (h7.c1rho_neq_0 q hq0 h2mq)

  -- have := @Algebra.norm_algebraMap ℚ _ h7.K _ _ (h7.cρ q hq0 h2mq)
  -- simp only [map_intCast] at this
  -- rw [this]
  -- simp only [norm_pow, Int.norm_cast_rat, ge_iff_le]

  have h2 : 0 < ‖(Algebra.norm ℚ) (ρᵣ h7 q hq0 h2mq)‖ := by {
    --rw [← rho_eq_ρᵣ]
    --unfold rho
    rw [norm_pos_iff]
    intros H
    --have := h7.norm_Algebra_norm_rho_nonzero q hq0 h2mq
    --rw [Algebra.norm_eq_zero_iff] at H
    --simp only [map_sum, map_mul, nsmul_eq_mul, map_pow, map_add, map_natCast] at H
    sorry
    -- --rw [norm_pos_iff]
    }
  sorry

  --   -- have := abs_norm_eq_prod_embeddings_norm ( α := rho h7 q hq0 h2mq)
  --   -- --have Hnorm_neq_0 := norm_ne_zero_iff
  --   -- have := ρᵣ_nonzero h7 q hq0 h2mq
  --   -- rw [← rho_eq_ρᵣ] at this
  --   -- --simp only [ne_eq, norm_eq_zero,
  --   -- -- Algebra.norm_eq_zero_iff] at Hnorm_neq_0
  --   -- intros H
  --   -- apply this
  --   -- simp only [map_eq_zero]
  --   -- apply_fun h7.σ
  --   -- · apply_fun (Algebra.norm ℚ)
  --   --   · simp only [map_zero]
  --   --     rw [H]
  --   --     sorry
  --   --   · sorry
  --   -- · exact RingHom.injective h7.σ
  --   }

  -- calc 1 ≤ ‖h7.cρ q hq0 h2mq‖ ^ Module.finrank ℚ h7.K := h7.h1 q hq0 h2mq
  --      _ ≤ ‖h7.cρ q hq0 h2mq‖ ^ Module.finrank ℚ h7.K *
  --        ‖(Algebra.norm ℚ) (rho h7 q hq0 h2mq)‖ := ?_
  -- · nth_rw 1 [← mul_one (‖h7.cρ q hq0 h2mq‖ ^ Module.finrank ℚ h7.K)]
  --   rw [mul_le_mul_left]
  --   · sorry
  --   · have := h7.h1 q hq0 h2mq
  --     rw [le_iff_eq_or_lt] at this
  --     cases' this with h1 h2
  --     · rw [← h1]
  --       simp only [zero_lt_one]
  --     · sorry


def c₅ : ℝ := ((abs (h7.c₁) + 1) ^ (((↑(h7.h) * (1+4 * h7.m^2)))))

lemma c5nonneg : 0 < h7.c₅ := by {
    unfold c₅
    apply pow_pos
    simp only [Int.cast_abs]
    refine add_pos_of_nonneg_of_pos ?_ ?_
    · simp only [abs_nonneg]
    · simp only [zero_lt_one]
}

lemma eq5 : h7.c₅ ^ (-(h7.r q hq0 h2mq) : ℝ)
  < norm (Algebra.norm ℚ (rho h7 q hq0 h2mq)) := by

  simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]

  have h1 : 1 ≤ ‖(h7.cρ q hq0 h2mq) ^ Module.finrank ℚ h7.K‖ *
     ‖(Algebra.norm ℚ) (rho h7 q hq0 h2mq)‖ := by {

  have := eq5zero h7 q hq0 h2mq
  unfold c1ρ at this
  unfold RingOfIntegers.restrict at this
  simp only [zsmul_eq_mul] at this
  simp only [RingOfIntegers.map_mk, map_mul, norm_mul] at this

  have H := @Algebra.norm_algebraMap ℚ _ h7.K _ _ (h7.cρ q hq0 h2mq)
  simp only [map_intCast] at H
  simp only [norm_pow, ge_iff_le]
  rw [H] at this
  simp only [norm_pow, Int.norm_cast_rat] at this
  exact this}

  have h2 : ‖(h7.cρ q hq0 h2mq) ^ Module.finrank ℚ h7.K‖⁻¹
    ≤ norm (Algebra.norm ℚ (rho h7 q hq0 h2mq)) := by {
    have : 0 < ‖ (h7.cρ q hq0 h2mq)^ Module.finrank ℚ h7.K‖ := by {
      rw [norm_pos_iff]
      simp only [ne_eq, pow_eq_zero_iff', not_and, Decidable.not_not]
      intros H
      by_contra H1
      apply h7.cρ_ne_zero q hq0 h2mq
      exact H }
    rw [← mul_le_mul_left this]
    · rw [mul_inv_cancel₀]
      · simp_all only [norm_pow]
      · simp only [norm_pow, ne_eq, pow_eq_zero_iff', norm_eq_zero,
          not_and, Decidable.not_not]
        intros H
        rw [H] at this
        simp only [norm_pow, norm_zero] at this
        rw [zero_pow] at this
        by_contra H1
        simp_all only [norm_pow, lt_self_iff_false]
        · simp_all only [norm_pow]
          have : 0 < Module.finrank ℚ h7.K := by {
            exact Module.finrank_pos}
          simp_all only [norm_zero, ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [pow_zero, one_mul, zero_lt_one, lt_self_iff_false]
          }

  calc _ = _ := ?_
       h7.c₅ ^ ((-h7.r q hq0 h2mq : ℤ)) <
        abs (h7.c₁)^ ((- h7.h : ℤ) * (h7.r q hq0 h2mq + 2 * h7.m * q) ) := ?_
       _ ≤ ‖(h7.cρ q hq0 h2mq) ^ Module.finrank ℚ h7.K‖⁻¹ := ?_
       _ ≤ norm (Algebra.norm ℚ (rho h7 q hq0 h2mq)) := ?_

  · simp only [zpow_neg, zpow_natCast]
  · simp only [zpow_neg, zpow_natCast, neg_mul]
    rw [inv_lt_inv₀]
    · rw [mul_add]
      have : (h7.h : ℤ) * h7.r q hq0 h2mq + h7.h
      * (2 * h7.m * ↑q) = h7.h * h7.r q hq0 h2mq + h7.h * 2 * h7.m * ↑q := by
        rw [mul_assoc, mul_assoc, mul_assoc]
      rw [this]
      have : ((h7.h : ℤ) * h7.r q hq0 h2mq + ↑(h7.h) * 2 * ↑(h7.m) * ↑q)  =
         ((h7.h : ℤ) * (↑(h7.r q hq0 h2mq) + 2 * ↑(h7.m) * ↑q)) :=
         Eq.symm (Mathlib.Tactic.Ring.mul_add rfl rfl this)
      rw [this]
      dsimp [c₅]
      norm_cast
      nth_rw 2 [pow_mul]
      have :  (((abs (h7.c₁) + 1) ^ h7.h) ^ (1 + 4 * h7.m ^ 2)) ^ h7.r q hq0 h2mq=
        ((abs (h7.c₁) + 1) ^ (h7.h * (1 + 4 * h7.m ^ 2) * h7.r q hq0 h2mq)) := by {
          rw [pow_mul]
          rw [pow_mul]
        }
      rw [this]; clear this
      calc _ ≤ abs (h7.c₁) ^ (h7.h * (h7.r q hq0 h2mq + 2 * h7.m * q^2)):= ?_
           _ ≤ abs (h7.c₁) ^ (h7.h * (h7.r q hq0 h2mq + 4 * h7.m ^ 2 * h7.n q)) := ?_
           _ ≤ abs (h7.c₁) ^( h7.h * (1 + 4 * h7.m ^ 2) * h7.r q hq0 h2mq) := ?_

           _ < (abs (h7.c₁) + 1) ^ (h7.h * (1 + 4 * h7.m ^ 2) * h7.r q hq0 h2mq) := ?_
      · refine pow_le_pow_right₀ ?_ ?_
        · exact one_leq_abs_c₁ h7
        · simp only [mul_assoc]
          refine Nat.mul_le_mul ?_ ?_
          · simp only [le_refl]
          · rw [q_eq_2sqrtmn h7 q h2mq]
            simp only [add_le_add_iff_left, Nat.ofNat_pos, mul_le_mul_left]
            refine Nat.mul_le_mul ?_ ?_
            · simp only [le_refl]
            · trans
              · have : q ≤ q^2 := by {
                 refine Nat.le_pow ?_
                 simp only [Nat.ofNat_pos]}
                apply this
              · rw [q_eq_2sqrtmn h7 q h2mq]
      · simp only [mul_assoc]
        refine pow_le_pow_right₀ ?_ ?_
        · exact one_leq_abs_c₁ h7
        · refine Nat.mul_le_mul ?_ ?_
          · simp only [le_refl]
          · rw [q_eq_2sqrtmn h7 q h2mq]
            simp only [add_le_add_iff_left]
            have : 2 * (h7.m * (2 * h7.m * h7.n q))=
              4 * h7.m ^ 2 * h7.n q := by {
              rw [mul_assoc, mul_assoc]
              ring}
            rw [this]
            simp only [mul_assoc,le_refl]
      · rw [mul_add]
        rw [mul_add]
        rw [add_mul]
        simp only [mul_one]
        refine pow_le_pow_right₀ ?_ ?_
        · exact one_leq_abs_c₁ h7
        · simp only [add_le_add_iff_left]
          simp only [mul_assoc]
          refine Nat.mul_le_mul ?_ ?_
          · simp only [le_refl]
          · simp only [Nat.ofNat_pos, mul_le_mul_left]
            refine Nat.mul_le_mul ?_ ?_
            · simp only [le_refl]
            · exact n_leq_r h7 q hq0 h2mq
      · refine pow_lt_pow_left₀ ?_ ?_ ?_
        · simp only [lt_add_iff_pos_right, zero_lt_one]
        · simp only [abs_nonneg]
        · intros H
          simp only [mul_eq_zero, Nat.add_eq_zero,
            one_ne_zero, OfNat.ofNat_ne_zero,
            Nat.pow_eq_zero, ne_eq, not_false_eq_true, and_true,
             false_or, false_and, or_false] at H
          cases' H with h1 h2
          · have : 0 ≠ h7.h := by {
            refine Ne.symm ((fun {n} ↦ Nat.pos_iff_ne_zero.mp) ?_)
            dsimp [h]
            exact Module.finrank_pos
            }
            apply this
            exact h1.symm
          · apply rneq0 h7 q hq0 h2mq
            exact h2
    ·
      unfold c₅
      trans
      · have : (0 : ℝ) < 1 := by {simp only [zero_lt_one]}
        apply this
      · apply one_lt_pow₀
        stop
        simp only [lt_sup_iff, Nat.one_lt_ofNat, true_or]
        exact rneq0 α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
    · have : 1 ≤ abs (h7.c₁) ^ (↑(h7.h) *
       ((↑(h7.r q hq0 h2mq)) + 2 * ↑(h7.m) * (↑q))) := by {
        refine one_le_pow₀ ?_
        have : 1 ≤ h7.c₁ := h7.one_leq_c₁
        exact one_leq_abs_c₁ h7
        }
      calc (0 : ℝ) < 1 := by {simp only [zero_lt_one]}
           (1 : ℝ) ≤ abs (h7.c₁) ^ (↑(h7.h) *
           ((↑(h7.r q hq0 h2mq)) + 2 * ↑(h7.m) * (↑q))) := mod_cast this
  · unfold cρ
    simp only [neg_mul, zpow_neg]
    simp only [Int.cast_abs, norm_pow]
    rw [Int.norm_eq_abs]
    simp only [Int.cast_abs, Int.cast_mul, Int.cast_pow, abs_abs]
    rw [← abs_pow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add]
    rw [← Real.rpow_mul]
    rw [mul_comm]
    norm_cast
    simp only [Int.cast_pow, Int.cast_abs, abs_pow]
    unfold h
    simp only [le_refl]
    · simp only [Int.cast_nonneg]; exact zero_leq_c₁ h7
    · rw [lt_iff_le_and_ne]
      constructor
      · simp only [Int.cast_nonneg]
        exact zero_leq_c₁ h7
      · simp only [ne_eq]
        intros H
        apply c₁_neq_zero h7
        symm
        exact mod_cast H
  · exact h2

lemma crho_abs_eq : |h7.c₁ ^ h7.r q hq0 h2mq * h7.c₁ ^ (2 * h7.m * q)| =
  h7.c₁ ^ h7.r q hq0 h2mq * h7.c₁ ^ (2 * h7.m * q) := by
    rw [abs_eq_self]
    apply mul_nonneg
    · apply pow_nonneg
      exact zero_leq_c₁ h7
    · apply pow_nonneg
      exact zero_leq_c₁ h7

def c₆ : ℝ := (|↑h7.c₁| * (1 + house h7.β'))

lemma c₆_nonneg : 0 ≤ h7.c₆  := by {
  unfold c₆ house
  positivity
}

lemma one_leq_c₆ : 1 ≤ h7.c₆ := by {
  unfold c₆
  refine one_le_mul_of_one_le_of_one_le ?_ ?_
  · norm_cast; exact one_leq_abs_c₁ h7
  · simp only [le_add_iff_nonneg_right]
    exact house_nonneg h7.β'
}

def c₇ : ℝ := ((((|↑h7.c₁| * |↑h7.c₁| *
  (|↑h7.c₁| * (house h7.α' * (|↑h7.c₁| * house h7.γ'))))) ^ h7.m))

lemma one_leq_c₇ : 1 ≤ h7.c₇ := by
  unfold c₇
  simp only [abs_mul_abs_self]
  have hc: 0 ≤ h7.c₁ := by {exact zero_leq_c₁ h7}
  have :=house_num_mul_int (c':=h7.c₁) (α := h7.γ') hc
  rw [Real.norm_eq_abs] at this
  rw [← this]
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [mul_assoc (↑h7.c₁ * (h7.c₁:ℝ)) |↑h7.c₁| (house h7.α')]
  have :=house_num_mul_int (c':=h7.c₁) (α := h7.α') hc
  rw [Real.norm_eq_abs] at this
  rw [← this]
  calc _ ≤ (↑h7.c₁ * ↑h7.c₁ * house (↑h7.c₁ * h7.α') * house (↑h7.c₁ * h7.γ')) := ?_
       _ ≤ (↑h7.c₁ * ↑h7.c₁ * house (↑h7.c₁ * h7.α') * house (↑h7.c₁ * h7.γ')) ^ h7.m := ?_
  · refine one_le_mul_of_one_le_of_one_le ?_ ?_
    · refine one_le_mul_of_one_le_of_one_le ?_ ?_
      · refine one_le_mul_of_one_le_of_one_le ?_ ?_
        · norm_cast; exact one_leq_c₁ h7
        · norm_cast; exact one_leq_c₁ h7
      · rw [← smul_eq_mul]
        refine house_gt_one_of_isIntegral ?_ ?_
        · exact mod_cast h7.isIntegral_c₁α
        · exact mod_cast h7.c₁αneq0
    · rw [← smul_eq_mul]
      refine house_gt_one_of_isIntegral ?_ ?_
      · exact mod_cast h7.isIntegral_c₁γ
      · exact mod_cast h7.c₁cneq0
  · nth_rw 1 [← pow_one (a :=↑h7.c₁ * ↑h7.c₁ *
      house (↑h7.c₁ * h7.α') * house (↑h7.c₁ * h7.γ'))]
    refine pow_le_pow_right₀ ?_ ?_
    · refine one_le_mul_of_one_le_of_one_le ?_ ?_
      · refine one_le_mul_of_one_le_of_one_le ?_ ?_
        · refine one_le_mul_of_one_le_of_one_le ?_ ?_
          · norm_cast; exact one_leq_c₁ h7
          · norm_cast; exact one_leq_c₁ h7
        · rw [← smul_eq_mul]
          refine house_gt_one_of_isIntegral ?_ ?_
          · exact mod_cast h7.isIntegral_c₁α
          · exact mod_cast h7.c₁αneq0
      · rw [← smul_eq_mul]
        refine house_gt_one_of_isIntegral ?_ ?_
        · exact mod_cast h7.isIntegral_c₁γ
        · exact mod_cast h7.c₁cneq0
    · unfold m
      exact Nat.le_add_left 1 (2 * h7.h + 1)

lemma c_coeffspow_r :
  ((h7.c₁) ^ (h7.r q hq0 h2mq) * (h7.c₁) ^ (h7.m * q) * (h7.c₁) ^ (h7.m * q)) =
  ((h7.c₁) ^ ((h7.r q hq0 h2mq)) *
  (h7.c₁) ^ (h7.m * q - (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))) *
  (h7.c₁) ^ (h7.m * q - ((b q t * (↑(h7.l₀' q hq0 h2mq) + 1))))) •
  (h7.c₁) ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
  (h7.c₁) ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)) := by {
    rw [← one_mul (h7.c₁ ^ (a q t * (↑(h7.l₀' q hq0 h2mq : ℕ) + 1)))]
    have :=  triple_comm_int
    simp only [mul_assoc]
    rw [ smul_mul_assoc
          (h7.c₁ ^ h7.r q hq0 h2mq *
            (h7.c₁ ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
              h7.c₁ ^ (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1))))
          (1 * h7.c₁ ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)))
          (h7.c₁ ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))]
    rw [Int.mul_assoc 1 (h7.c₁ ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)))
          (h7.c₁ ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))]
    simp only [← mul_assoc]
    rw [this]
    congr
    · simp only [Int.zsmul_eq_mul, mul_one]
    · simp only [smul_eq_mul]
      rw [← pow_add]
      have : (h7.m * q - (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))
      + (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))) = (h7.m * q) := by
        rw [add_comm]
        refine add_tsub_cancel_of_le ?_
        rw [mul_comm h7.m]
        apply mul_le_mul (a_le_q q t) ?_ (zero_le _) (zero_le _)
        · exact bar' (h7.l₀' q hq0 h2mq)
      rw [this]
    · simp only [smul_eq_mul]
      rw [← pow_add]
      have : (h7.m * q - (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))
        + (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))) = (h7.m * q) := by
        rw [add_comm]
        refine add_tsub_cancel_of_le ?_
        rw [mul_comm h7.m]
        apply mul_le_mul (b_le_q q t) ?_ (zero_le _) (zero_le _)
        · exact bar' (h7.l₀' q hq0 h2mq)
      rw [this]
  }

lemma eq6a : house (rho h7 q hq0 h2mq) ≤
  (q*q) *(h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) *
        (h7.c₆* q) ^(h7.r q hq0 h2mq) * (h7.c₇)^(q : ℤ)) := by
  calc
       _ ≤ norm (h7.cρ q hq0 h2mq : ℝ) * house (rho h7 q hq0 h2mq) := ?_

       _ ≤ (norm (h7.cρ q hq0 h2mq : ℝ))  *
          house (∑ t, ( ((algebraMap (𝓞 h7.K) h7.K) ((h7.η q hq0 h2mq) t)) *
        ((h7.sys_coe_r q hq0 t h2mq)))) := ?_

       _ ≤ (norm (h7.cρ q hq0 h2mq : ℝ)) *
         ∑ t, house ( ((algebraMap (𝓞 h7.K) h7.K) ((h7.η q hq0 h2mq) t)) *
       ((h7.sys_coe_r q hq0 t h2mq))) := ?_

       _ = (∑ t, house ((h7.cρ q hq0 h2mq) *
         (algebraMap (𝓞 h7.K) h7.K ((h7.η q hq0 h2mq) t) *
          h7.sys_coe_r q hq0 t h2mq))) := ?_

       _ = ∑ t, house ((algebraMap (𝓞 h7.K) h7.K) (h7.η q hq0 h2mq t) *
        (↑h7.c₁ ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
          (↑h7.c₁ ^ (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
            (h7.c₁ ^ h7.r q hq0 h2mq • (↑(a q t) + b q t • h7.β') ^ h7.r q hq0 h2mq *
              (h7.c₁ ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) •
                  h7.α' ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
                h7.c₁ ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)) •
                  h7.γ' ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))))))) := ?_

       _ ≤ ∑ t, house ((algebraMap (𝓞 h7.K) h7.K) (h7.η q hq0 h2mq t)) *
        (house (((h7.c₁ : h7.K) ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1)))) *
          (house (((h7.c₁ : h7.K) ^
              (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))) *
            (house (((h7.c₁ : h7.K) ^ h7.r q hq0 h2mq •
              (↑(a q t) + b q t • h7.β') ^ h7.r q hq0 h2mq)) *
              (house (((h7.c₁ : h7.K) ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) •
                  h7.α' ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)))) *
                (house ((h7.c₁ : h7.K) ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)) •
                  h7.γ' ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))
                  ))))) := ?_

       _ ≤ (∑ t, h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) *
        (↑|h7.c₁ ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1))| *
        (↑|h7.c₁ ^ (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1))| *
          (((|h7.c₁| * (|(q : ℤ)| * (1 + house (h7.β')))) ^ (h7.r q hq0 h2mq)) *
             house ((h7.c₁ • h7.α')) ^ (h7.m * q) *
             house ((h7.c₁ • h7.γ')) ^ (h7.m * q))))) := ?_

       _ ≤ ∑ (t : Fin (q * q)), h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) *
          (↑|h7.c₁| ^ (h7.m * q) *
          (↑|h7.c₁| ^ (h7.m * q) *
          ((|h7.c₁|^ (h7.r q hq0 h2mq) *
            (|(q : ℤ)|^ (h7.r q hq0 h2mq) * (1 + house (h7.β')) ^ (h7.r q hq0 h2mq)) *
             ((|h7.c₁|^ (h7.m * q) * house (h7.α') ^ (h7.m * q)) *
             (|h7.c₁|^ (h7.m * q)  * house h7.γ' ^ (h7.m * q))))))) := ?_

       _ ≤  (q*q) *(h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) *
        (h7.c₆* q) ^(h7.r q hq0 h2mq) * (h7.c₇)^(q : ℤ)) := ?_

  · rw [← one_mul (house (h7.rho q hq0 h2mq))]
    apply mul_le_mul
    · exact h7.one_leq_norm_c1rho q hq0 h2mq
    · simp only [one_mul, le_refl]
    · exact house_nonneg (h7.rho q hq0 h2mq)
    · simp only [norm_nonneg]
  · unfold rho
    simp only [le_refl]
  · apply mul_le_mul
    · simp only [le_refl]
    · exact
      house_sum_le_sum_house Finset.univ fun i ↦
        (algebraMap (𝓞 h7.K) h7.K) (h7.η q hq0 h2mq i)
        * h7.sys_coe_r q hq0 i h2mq
    · exact
      house_nonneg (∑ t, (algebraMap (𝓞 h7.K) h7.K)
        (h7.η q hq0 h2mq t) * h7.sys_coe_r q hq0 t h2mq)
    · exact norm_nonneg (h7.cρ q hq0 h2mq)
  · rw [mul_sum]
    apply Finset.sum_congr rfl
    intros i hi
    rw [house_num_mul_int
    (α := ((algebraMap (𝓞 h7.K) h7.K)
    (h7.η q hq0 h2mq i) * h7.sys_coe_r q hq0 i h2mq))]
    · exact zero_leq_c1rho h7 q hq0 h2mq
  · apply Finset.sum_congr rfl
    intros t ht
    rw [Algebra.left_comm (↑(h7.cρ q hq0 h2mq))
      (h7.η q hq0 h2mq t) (h7.sys_coe_r q hq0 t h2mq)]
    simp only [← zsmul_eq_mul]
    unfold sys_coe_r
    unfold cρ
    rw [crho_abs_eq]
    have : h7.c₁ ^ (2 * h7.m * q) = h7.c₁ ^ (h7.m * q)
     * h7.c₁ ^ (h7.m * q) := by {
       rw [← pow_add]; ring}
    rw [this]; clear this
    have := h7.c_coeffspow_r q hq0 t h2mq
    simp only [mul_assoc] at this
    rw [this]; clear this
    rw [Int.mul_comm (h7.c₁ ^ h7.r q hq0 h2mq)
     (h7.c₁ ^ (h7.m * q - a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
    h7.c₁ ^ (h7.m * q - b q t * (↑(h7.l₀' q hq0 h2mq) + 1)))]
    simp only [mul_assoc]
    simp only [nsmul_eq_mul, zsmul_eq_mul,
     Int.cast_mul, Int.cast_pow]
    simp only [mul_assoc]
    simp only [Int.cast_eq]
    ring_nf
  · apply Finset.sum_le_sum
    intros t ht
    · trans
      · apply house_mul_le
      · refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
        · simp only [le_refl]
        · trans
          apply house_mul_le
          · refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
            · simp only [le_refl]
            · trans
              apply house_mul_le
              refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
              · simp only [le_refl]
              · trans
                apply house_mul_le
                refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
                · simp only [nsmul_eq_mul, zsmul_eq_mul,
                    Int.cast_pow, smul_eq_mul, le_refl]
                · trans
                  apply house_mul_le
                  refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
                  · simp only [zsmul_eq_mul, Int.cast_pow, smul_eq_mul, le_refl]
                  · simp only [zsmul_eq_mul, Int.cast_pow, smul_eq_mul, le_refl]
                  · simp only [zsmul_eq_mul, Int.cast_pow]
                    apply house_nonneg
                  · apply house_nonneg
                · apply house_nonneg
                · dsimp [house]
                  positivity
              · apply house_nonneg
              · dsimp [house]
                positivity
            · apply house_nonneg
            · dsimp [house]
              positivity
        · apply house_nonneg
        · dsimp [house]
          positivity
  · apply Finset.sum_le_sum
    intros t ht
    apply mul_le_mul
    · apply h7.fromlemma82_bound q hq0 t h2mq
    · simp only [mul_assoc]
      apply mul_le_mul
      · norm_cast
        rw [house_intCast]
      · apply mul_le_mul
        · norm_cast
          rw [house_intCast]
        · apply mul_le_mul
          · simp only [nsmul_eq_mul, smul_eq_mul]
            rw [← mul_pow]
            rw [mul_add]
            calc _ ≤  house ((↑h7.c₁ * ↑(a q t) + ↑h7.c₁ *
                  (↑(b q t) * h7.β'))) ^ h7.r q hq0 h2mq :=?_
                 _ ≤  (↑|h7.c₁| * (↑|↑q| * (1 + house h7.β'))) ^ h7.r q hq0 h2mq := ?_
            · apply house_pow_le _ _

            · rw [← mul_add]
              rw [pow_le_pow_iff_left₀]
              · have := house_add_mul_leq h7 q t
                simp only [mul_assoc] at *
                norm_cast at *
                simp only [nsmul_eq_mul, zsmul_eq_mul] at this
                exact this
              · apply house_nonneg
              · unfold house
                positivity
              · exact rneq0 h7 q hq0 h2mq
            · simp only [Int.cast_abs, Nat.abs_cast, Int.cast_natCast, le_refl]
              --apply house_add_mul_leq h7
          · apply mul_le_mul
            · simp only [smul_eq_mul, zsmul_eq_mul]
              rw [← mul_pow]
              trans
              apply house_pow_le _ _
              apply house_alg_int_leq_pow
              · rw [mul_comm h7.m  q]
                apply mul_le_mul (a_le_q q t) ?_ (zero_le _) (zero_le _)
                · exact bar' (h7.l₀' q hq0 h2mq)
              · rw [← smul_eq_mul]
                exact mod_cast h7.c₁αneq0
              · rw [← smul_eq_mul]
                exact mod_cast h7.isIntegral_c₁α
            · simp only [smul_eq_mul, zsmul_eq_mul]
              rw [← mul_pow]
              trans
              apply house_pow_le _ _
              apply house_alg_int_leq_pow
              · rw [mul_comm h7.m  q]
                apply mul_le_mul (b_le_q q t) ?_ (zero_le _) (zero_le _)
                · exact bar' (h7.l₀' q hq0 h2mq)
              · rw [← smul_eq_mul]
                exact mod_cast h7.c₁cneq0
              · rw [← smul_eq_mul]
                exact mod_cast h7.isIntegral_c₁γ
            · unfold house
              positivity
            · unfold house
              positivity
          · unfold house
            positivity
          · unfold house
            positivity
        · unfold house
          positivity
        · positivity
      · unfold house; positivity
      · positivity
    · unfold house; positivity
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        · exact zero_leq_c₄ h7
      · positivity
  · apply Finset.sum_le_sum
    intros t ht
    apply mul_le_mul
    · simp only [Real.rpow_natCast, le_refl]
    · apply mul_le_mul
      · simp only [abs_pow, Int.cast_pow, Int.cast_abs]
        refine pow_le_pow_right₀ ?_ ?_
        · norm_cast; exact one_leq_abs_c₁ h7
        · exact Nat.sub_le (h7.m * q) (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))
      · apply mul_le_mul
        · simp only [abs_pow, Int.cast_pow, Int.cast_abs]
          refine pow_le_pow_right₀ ?_ ?_
          · norm_cast; exact one_leq_abs_c₁ h7
          · exact Nat.sub_le (h7.m * q) (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))
        · nth_rw 1 [mul_assoc]
          apply mul_le_mul
          · rw [← mul_pow]
            rw [← mul_pow]
          · apply mul_le_mul
            · simp only [zsmul_eq_mul, Int.cast_abs]
              rw [← mul_pow]
              refine pow_le_pow_left₀ ?_ ?_ (h7.m * q)
              · apply house_nonneg
              · trans
                · apply house_mul_le
                · simp only [house_intCast, Int.cast_abs, le_refl]
            · simp only [zsmul_eq_mul, Int.cast_abs]
              rw [← mul_pow]
              refine pow_le_pow_left₀ ?_ ?_ (h7.m * q)
              · apply house_nonneg
              · trans
                · apply house_mul_le
                · simp only [house_intCast, Int.cast_abs, le_refl]
            · unfold house; positivity
            · unfold house; positivity
          · unfold house; positivity
          · simp only [Int.cast_abs, Nat.abs_cast, Int.cast_natCast]
            unfold house
            positivity
        · unfold house; positivity
        · positivity
      · unfold house; positivity
      · positivity
    · unfold house; positivity
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        · exact zero_leq_c₄ h7
      · positivity
  · simp only [ sum_const, card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    apply mul_le_mul
    · simp only [Nat.cast_mul, le_refl]
    · nth_rw 4 [mul_assoc]
      apply mul_le_mul
      · simp only [Real.rpow_natCast, le_refl]
      · simp only [← mul_assoc]
        rw [← mul_pow]
        simp only [mul_assoc]
        rw [← mul_pow]
        rw [← mul_pow]
        rw [← mul_pow]
        simp only [Int.cast_abs,
        Nat.abs_cast, Int.cast_natCast, zpow_natCast]
        rw [mul_comm ((1 + house h7.β') ^ h7.r q hq0 h2mq)
          ((|↑h7.c₁| * (house h7.α' * (|↑h7.c₁| * house h7.γ'))) ^ (h7.m * q))]
        nth_rw 3 [← mul_assoc]
        rw [mul_comm ((q:ℝ) ^ h7.r q hq0 h2mq)
         ((|↑h7.c₁| * (house h7.α' * (|↑h7.c₁| * house h7.γ'))) ^ (h7.m * q))]
        nth_rw 2 [← mul_assoc]
        rw [mul_comm  (|(h7.c₁ : ℝ)| ^ h7.r q hq0 h2mq)
          ((|(h7.c₁ : ℝ)| * (house h7.α' * (|(h7.c₁ : ℝ)| *
           house h7.γ'))) ^ (h7.m * q) * (q : ℝ) ^ h7.r q hq0 h2mq)]
        nth_rw 1 [← mul_assoc]
        rw [mul_comm  ((h7.c₆ * ↑q) ^ h7.r q hq0 h2mq) (h7.c₇ ^ q)]
        simp only [mul_assoc]
        rw [← mul_pow]
        rw [← mul_pow]
        nth_rw 1 [← mul_assoc]
        rw [← mul_pow]
        rw [pow_mul]
        rw [← mul_comm  (q : ℝ)  h7.c₆]
        unfold c₇ c₆
        simp only [mul_assoc]
        rfl
      · unfold house; positivity
      · apply mul_nonneg
        · simp only [Real.rpow_natCast]
          apply pow_nonneg
          · exact zero_leq_c₄ h7
        · positivity
    · apply mul_nonneg
      · apply mul_nonneg
        · simp only [Real.rpow_natCast]
          apply pow_nonneg
          · exact zero_leq_c₄ h7
        · positivity
      · unfold house; positivity
    · positivity

theorem bound_n_leq_r.extracted_1_1 :
   ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) ≤
     ((h7.r q hq0 h2mq : ℝ)^((1/2) * ((h7.r q hq0 h2mq : ℝ) + 1))) := by {
      calc _ ≤ ((h7.r q hq0 h2mq : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) := ?_
           _ ≤ ((h7.r q hq0 h2mq : ℝ)^((1/2)* ((h7.r q hq0 h2mq : ℝ) + 1))) := ?_
      · refine Real.rpow_le_rpow ?_ ?_ ?_
        · simp only [Nat.cast_nonneg]
        · simp only [Nat.cast_le]; exact n_leq_r h7 q hq0 h2mq
        · refine div_nonneg ?_ ?_
          · norm_cast
            exact Nat.le_add_left 0 (h7.n q + 1)
          · simp only [Nat.ofNat_nonneg]
      · apply Real.rpow_le_rpow_of_exponent_le_or_ge
        left
        · simp only [Nat.one_le_cast, one_div]
          constructor
          · have : 0 < h7.r q hq0 h2mq := r_qt_0 h7 q hq0 h2mq
            exact this
          · ring_nf
            simp only [one_div, add_le_add_iff_left,
             inv_pos, Nat.ofNat_pos, mul_le_mul_right, Nat.cast_le]
            exact n_leq_r h7 q hq0 h2mq}

lemma bound_n_leq_r :
  (h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)) ≤
  ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ)) *
    ((h7.r q hq0 h2mq : ℝ)^((1/2)* ((h7.r q hq0 h2mq : ℝ) + 1))))) := by {
    apply mul_le_mul
    · simp only [Real.rpow_natCast]
      refine pow_le_pow_right₀ ?_ ?_
      · exact one_leq_c₄ h7
      · exact n_leq_r h7 q hq0 h2mq
    · exact bound_n_leq_r.extracted_1_1 h7 q hq0 h2mq
    · apply Real.rpow_nonneg
      simp only [Nat.cast_nonneg]
    · apply Real.rpow_nonneg
      exact zero_leq_c₄ h7}

lemma q_le_2sqrtmr : q^2 ≤ 2*h7.m*h7.r q hq0 h2mq := by
  trans
  apply h7.sq_le_two_mn q h2mq
  refine Nat.mul_le_mul ?_ ?_
  · simp only [le_refl]
  · exact n_leq_r h7 q hq0 h2mq

lemma sqt_etc : Real.sqrt (2*h7.m*(h7.r q hq0 h2mq)) =
  Real.sqrt (2*h7.m) * (h7.r q hq0 h2mq : ℝ)^(1/2 : ℝ) := by {
    rw [Real.sqrt_mul]
    · congr
      exact Real.sqrt_eq_rpow ↑(h7.r q hq0 h2mq)
    · positivity}

def c₈ : ℝ := (h7.c₆ * √(2 * ↑h7.m) * h7.c₇ ^ (2 * h7.m) * h7.c₄ * (2 * ↑h7.m))

lemma c7_nonneg : 0 ≤ h7.c₇ := by {
  unfold c₇ house
  positivity
}

lemma c8_nonneg : 0 ≤ h7.c₈ := by {
  unfold c₈
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · exact c₆_nonneg h7
        · simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
          Real.sqrt_pos, Nat.ofNat_pos,
          mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
      · apply pow_nonneg
        · exact c7_nonneg h7
    · exact zero_leq_c₄ h7
  · positivity
}

lemma c8_geq_one : 1 ≤ h7.c₈ := by
  unfold c₈
  have : 1 ≤ h7.c₆ := h7.one_leq_c₆
  have : 1 ≤ h7.c₇ := h7.one_leq_c₇
  have := h7.one_leq_c₄
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_mul_of_one_le_of_one_le
    · apply one_le_mul_of_one_le_of_one_le
      · apply one_le_mul_of_one_le_of_one_le
        · (expose_names; exact this_1)
        · rw [Real.one_le_sqrt]
          apply one_le_mul_of_one_le_of_one_le
          · simp only [Nat.one_le_ofNat]
          · simp only [Nat.one_le_cast]
            exact Nat.le_of_ble_eq_true rfl
      · (expose_names; exact one_le_pow₀ this_2)
    · exact this
  · apply one_le_mul_of_one_le_of_one_le
    · simp only [Nat.one_le_ofNat]
    · simp only [Nat.one_le_cast]
      exact Nat.le_of_ble_eq_true rfl

lemma zero_lt_r : 0 < h7.r q hq0 h2mq := by {
  exact r_qt_0 h7 q hq0 h2mq
}

theorem q_sq2_neq_1 (m q : ℕ) (hq0 : 0 < q)
    (h2mq : 2 * m ∣ q ^ 2) : q ^ 2 ≠ 1 := by
  intro hq2eq1
  have hdiv1 : 2 * m ∣ 1 := by
    exact (Nat.ModEq.dvd_iff
     (congrFun (congrArg HMod.hMod hq2eq1) (q ^ 2)) h2mq).mp h2mq
  cases m with
  | zero =>
    simp [*] at hdiv1
  | succ m' =>
    have h_two_eq_one : 2 * (m'.succ) = 1 := Nat.eq_one_of_dvd_one hdiv1
    have h_ge_two : 2 * (m'.succ) ≥ 2 := by
      calc
        2 * (m'.succ) = 2 + 2 * m' := by {
          simp only [Nat.succ_eq_add_one]
          ring_nf
        }
        _ ≥ 2 := Nat.le_add_right _ _
    have absurd_le : 1 ≥ 2 := by rwa [h_two_eq_one] at h_ge_two
    have gt21 : 2 > 1 := by decide
    exact (Nat.not_le_of_gt gt21) absurd_le

theorem eq6b.extracted_1_1 :
  q * q ≤ (2 * h7.m : ℝ) ^ (h7.r q hq0 h2mq: ℝ) * (h7.r q hq0 h2mq: ℝ) := by {
    calc _ = (q^2: ℝ) := ?_
         _ ≤ (2 * ↑h7.m: ℝ) * (h7.n q: ℝ) := ?_
         _ ≤ (2 * ↑h7.m: ℝ) ^ (h7.n q: ℝ) := ?_
         _ ≤ ((2*h7.m: ℝ)^(h7.r q hq0 h2mq: ℝ)) := ?_
         _ ≤ (2 * ↑h7.m : ℝ) ^ (h7.r q hq0 h2mq: ℝ) * (h7.r q hq0 h2mq: ℝ) := ?_
    · exact q_sq_real q
    · norm_cast
      have := h7.sq_le_two_mn q h2mq
      exact this
    · have : (2 * ↑h7.m) * h7.n q ≤ (2 * ↑h7.m) ^h7.n q := by {
        refine Nat.mul_le_pow ?_ (h7.n q)
        simp only [ne_eq, mul_eq_one,
          OfNat.ofNat_ne_one, false_and, not_false_eq_true]}
      simp only [Real.rpow_natCast, ge_iff_le]
      exact mod_cast this
    · apply Real.rpow_le_rpow_of_exponent_le
      · have : 1 ≤ 2 * (h7.m : ℝ) := by {
              unfold m
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
              ring_nf
              refine le_add_of_le_of_nonneg ?_ ?_
              · simp only [Nat.one_le_ofNat]
              · positivity}
        exact this
      · norm_cast
        exact n_leq_r h7 q hq0 h2mq
    · nth_rw 1 [← mul_one (a:= (2 * (h7.m : ℝ)) ^ (h7.r q hq0 h2mq : ℝ))]
      apply mul_le_mul
      · simp only [Real.rpow_natCast, le_refl]
      · exact mod_cast (h7.one_le_r q hq0 h2mq)
      · simp only [zero_le_one]
      · positivity}

theorem eq6b.extracted_1_2 :
  q * q ≤ (2 * h7.m : ℝ) ^ (h7.r q hq0 h2mq: ℝ) := by {
    calc _ = (q^2: ℝ) := ?_
         _ ≤ (2 * ↑h7.m: ℝ) * (h7.n q: ℝ) := ?_
         _ ≤ (2 * ↑h7.m: ℝ) ^ (h7.n q: ℝ) := ?_
         _ ≤ ((2*h7.m: ℝ)^(h7.r q hq0 h2mq: ℝ)) := ?_
    · exact q_sq_real q
    · norm_cast
      have := h7.sq_le_two_mn q h2mq
      exact this
    · have : (2 * ↑h7.m) * h7.n q ≤ (2 * ↑h7.m) ^h7.n q := by {
        refine Nat.mul_le_pow ?_ (h7.n q)
        simp only [ne_eq, mul_eq_one,
          OfNat.ofNat_ne_one, false_and, not_false_eq_true]}
      simp only [Real.rpow_natCast, ge_iff_le]
      exact mod_cast this
    · apply Real.rpow_le_rpow_of_exponent_le
      · have : 1 ≤ 2 * (h7.m : ℝ) := by {
              unfold m
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
              ring_nf
              refine le_add_of_le_of_nonneg ?_ ?_
              · simp only [Nat.one_le_ofNat]
              · positivity}
        exact this
      · norm_cast
        exact n_leq_r h7 q hq0 h2mq}

lemma eq6b : (q*q) * ((((h7.c₄ ^ (h7.n q : ℝ) *
  ((h7.n q : ℝ) ^ (((h7.n q : ℝ)+ 1)/2)))) *
  (h7.c₆* q) ^(h7.r q hq0 h2mq) * (h7.c₇)^q)) ≤
  h7.c₈^(h7.r q hq0 h2mq : ℝ) *
   (h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) + 3/2) := by {

    calc
         _ ≤ (((2*h7.m)^(h7.r q hq0 h2mq : ℝ))* ((h7.r q hq0 h2mq)) *
             ((((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ)) *
             ((h7.r q hq0 h2mq : ℝ)^((1/2)* ((h7.r q hq0 h2mq : ℝ) + 1))))) *
             (((h7.c₆* Real.sqrt (2*h7.m) *
             (h7.r q hq0 h2mq: ℝ)^(1/2 : ℝ)) ^(h7.r q hq0 h2mq: ℝ)) *
             ((h7.c₇)^(2*h7.m))^(h7.r q hq0 h2mq: ℝ)))) := ?_

         _ ≤ h7.c₈^(h7.r q hq0 h2mq : ℝ) *
           (h7.r q hq0 h2mq : ℝ)^((h7.r q hq0 h2mq : ℝ) + 3/2) := ?_

    · apply mul_le_mul
      · exact eq6b.extracted_1_1 h7 q hq0 h2mq
      · simp only [mul_assoc]
        apply mul_le_mul
        · simp only [Real.rpow_natCast]
          refine pow_le_pow_right₀ ?_ ?_
          · exact one_leq_c₄ h7
          · exact n_leq_r h7 q hq0 h2mq
        · apply mul_le_mul
          · exact bound_n_leq_r.extracted_1_1 h7 q hq0 h2mq
          · apply mul_le_mul
            · simp only [Real.rpow_natCast]
              refine pow_le_pow_left₀ ?_ ?_ (h7.r q hq0 h2mq)
              · unfold c₆ house
                positivity
              · refine mul_le_mul_of_nonneg_left ?_ ?_
                have := h7.q_eq_sqrtmn q h2mq
                calc _ ≤ √(2 * ↑h7.m) * ↑(h7.n q) ^ (1 / 2 : ℝ) := ?_
                     _ ≤ √(2 * ↑h7.m) * ↑(h7.r q hq0 h2mq) ^ (1 / 2 : ℝ) :=?_
                · rw [this]
                  rw [Real.sqrt_mul]
                  refine mul_le_mul_of_nonneg_left ?_ ?_
                  · rw [le_iff_lt_or_eq]
                    right
                    exact Real.sqrt_eq_rpow ↑(h7.n q)
                  · simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
                      Real.sqrt_pos, Nat.ofNat_pos,
                      mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
                  · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left,
                      Nat.cast_nonneg]
                · refine mul_le_mul_of_nonneg_left ?_ ?_
                  · apply Real.rpow_le_rpow
                    · simp only [Nat.cast_nonneg]
                    · simp only [Nat.cast_le]
                      exact n_leq_r h7 q hq0 h2mq
                    · simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
                  · simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
                    Real.sqrt_pos, Nat.ofNat_pos,
                    mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
                · unfold c₆ house
                  positivity
            · simp only [Real.rpow_natCast]
              rw [← pow_mul]
              refine pow_le_pow_right₀ ?_ ?_
              · exact one_leq_c₇ h7
              · trans
                apply h7.q_le_two_mn q h2mq
                apply mul_le_mul
                · simp only [le_refl]
                · exact n_leq_r h7 q hq0 h2mq
                · positivity
                · positivity
            · unfold c₇ house
              positivity
            · unfold c₆ house
              positivity
          · unfold c₇ c₆ house
            positivity
          · positivity
        · unfold c₆ c₇ house
          positivity
        · simp only [Real.rpow_natCast]
          unfold c₄
          apply pow_nonneg
          simp only [lt_sup_iff, zero_lt_one, true_or,
            mul_nonneg_iff_of_pos_left]
          exact zero_leq_c₃ h7
      · unfold c₆ c₇ house
        · apply mul_nonneg
          · apply mul_nonneg
            · simp only [Real.rpow_natCast]
              · apply mul_nonneg
                · apply pow_nonneg
                  exact zero_leq_c₄ h7
                · positivity
            · positivity
          · positivity
      · positivity
    · nth_rw 2 [Real.mul_rpow]
      nth_rw 4 [mul_comm]
      nth_rw 2 [mul_assoc]
      simp only [← mul_assoc]
      nth_rw 3 [mul_assoc]
      nth_rw 1 [← mul_comm]
      rw [mul_comm ((2 * (h7.m : ℝ)) ^ (h7.r q hq0 h2mq : ℝ)) (h7.r q hq0 h2mq: ℝ)]
      nth_rw 3 [← Real.rpow_one ((h7.r q hq0 h2mq))]
      simp only [← mul_assoc]
      nth_rw 1  [← Real.rpow_add]
      simp only [mul_assoc]
      rw [← Real.mul_rpow]
      rw [← mul_assoc]
      rw [← mul_assoc]
      nth_rw 8 [mul_comm]
      rw [mul_rotate]
      nth_rw 1 [← mul_assoc]
      nth_rw 1 [← mul_assoc]
      rw [← Real.mul_rpow]
      nth_rw 1 [mul_assoc]
      nth_rw 1 [mul_assoc]
      nth_rw 3 [← mul_assoc]
      nth_rw 1 [← Real.rpow_mul]
      nth_rw 1  [← Real.rpow_add]
      nth_rw 7 [mul_comm]
      simp only [← mul_assoc]
      nth_rw 1 [← Real.mul_rpow]
      apply mul_le_mul
      · unfold c₈
        simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
          Real.rpow_natCast, le_refl]
      · ring_nf
        simp only [le_refl]
      · positivity
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        · apply h7.c8_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · apply mul_nonneg
            · apply h7.c₆_nonneg
            · simp only [Nat.ofNat_nonneg,
              Real.sqrt_mul, Real.sqrt_pos, Nat.ofNat_pos,
              mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
          · apply pow_nonneg
            · apply h7.c7_nonneg
        · exact zero_leq_c₄ h7
      · positivity
      · simp only [Nat.cast_pos]
        apply h7.zero_lt_r
      · simp only [Nat.cast_nonneg]
      · apply mul_nonneg
        · exact c₆_nonneg h7
        · simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
          Real.sqrt_pos, Nat.ofNat_pos,
          mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
      · apply mul_nonneg
        · apply pow_nonneg
          · exact c7_nonneg h7
        · exact zero_leq_c₄ h7
      · apply pow_nonneg
        · exact c7_nonneg h7
      · exact zero_leq_c₄ h7
      · simp only [Nat.cast_pos]
        exact r_qt_0 h7 q hq0 h2mq
      · apply mul_nonneg
        · exact c₆_nonneg h7
        · simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
          Real.sqrt_pos, Nat.ofNat_pos,
          mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
      · positivity
  }

lemma eq6 : house (rho h7 q hq0 h2mq) ≤ h7.c₈^(h7.r q hq0 h2mq : ℝ) *
(h7.r q hq0 h2mq : ℝ)^((h7.r q hq0 h2mq : ℝ) + 3/2) := by
  trans
  apply h7.eq6a q hq0 h2mq
  exact h7.eq6b q hq0 h2mq




























































































































































































































/-
We formalize the existence of a function R' : ℂ → ℂ,
analytic in a neighborhood of l' + 1,
such that R(z) = (z - (l' + 1))^r * R'(z) in a neighborhood of l' + 1.
so this o is (I hope) R_order l' -/
lemma exists_R'_at_l'_plus_one (l' : Fin (h7.m))  :
  ∃ (R' : ℂ → ℂ) (U : Set ℂ), (U ∈ nhds (l' + 1 : ℂ)) ∧ (l' + 1 : ℂ) ∈ U ∧
    (∀ z ∈ U, (h7.R q hq0 h2mq) z = (z - (l' + 1))^(h7.r q hq0 h2mq) * R' z) ∧
    AnalyticOn ℂ R' U ∧ R' (l' + 1) ≠ 0 := by
  have hA := h7.anever q hq0 h2mq (l' + 1)
  have (z : ℂ) := h7.R_order_eq q hq0 h2mq z
  have := this (l' + 1)
  rw [AnalyticAt.analyticOrderAt_eq_natCast] at this
  obtain ⟨R'', ⟨horder, ⟨hRneq0, hfilter⟩⟩⟩ := this
  let o : ℕ := h7.R_order q hq0 h2mq (↑↑l' + 1)
  -- have h0or : 0 ≤ (o - r) := by {
  --   simp only [zero_le]
  --it's the min
  have : o ≥ h7.r q hq0 h2mq := by {
    simp only [ge_iff_le]
    unfold o
    have HR := r_prop h7 q hq0 h2mq
    simp only [Finset.mem_univ, forall_const] at HR
    have := R_order_eq h7 q hq0 h2mq (l' + 1)
    obtain ⟨hr1,hr2⟩  := HR
    have hr2 := hr2 (l')
    rw [this] at hr2
    simp only [Nat.cast_le] at hr2
    exact hr2
  }
  --have : (o - h7.r ...) + h7.r ... = o by sorry
  let R' (z : ℂ) := ((z - (l' + 1))^(o - h7.r q hq0 h2mq)) * R'' z
  use R'
  rw [unfilter] at hfilter
  obtain ⟨U, ⟨hU, hU_prop⟩⟩ := hfilter
  use U
  constructor
  · exact hU
  · constructor
    · exact mem_of_mem_nhds hU
    · constructor
      · intros z hz
        unfold R'
        have : (z - (l' + 1)) ^ (h7.r q hq0 h2mq : ℕ) *
           (z - (l' + 1)) ^ (o - h7.r q hq0 h2mq) = (z - (l' + 1)) ^ (o) := by {
            rw [← pow_add]
            rw [sub_eq_add_neg]
            congr
            simp_all only [ne_eq, ge_iff_le, smul_eq_mul, add_tsub_cancel_of_le, o]
             }
        rw [← mul_assoc]
        rw [this]
        unfold R o
        simp only [smul_eq_mul] at hU_prop z hz
        exact  hU_prop z hz
      · constructor
        ·
          -- have hlU := mem_of_mem_nhds (x := (↑↑l' + 1)) (s := U) hU
          -- have := AnalyticOnAt R'' (↑↑l' + 1) U hU
          -- intros x hx




          intros x hx
          refine analyticWithinAt ?_
          unfold R'
          refine fun_mul ?_ ?_
          · apply Differentiable.analyticAt
            · apply Differentiable.fun_pow
              · simp only [differentiable_fun_id,
                 differentiable_const, Differentiable.fun_sub]
          · sorry
            -- refine AnalyticOnAt R'' x ?_ ?_ ?_
            -- · exact U
            -- · sorry


        · unfold R'
          by_contra H
          simp only [sub_self, mul_eq_zero, pow_eq_zero_iff', ne_eq, true_and] at H
          cases' H with H1 H2
          · sorry
          · apply hRneq0
            exact H2
  · exact hA

def R'U (l' : Fin (h7.m)) : ℂ → ℂ := (exists_R'_at_l'_plus_one h7 q hq0 h2mq l').choose

def U (l' : Fin (h7.m)) : Set ℂ :=
  (exists_R'_at_l'_plus_one h7 q hq0 h2mq l').choose_spec.choose

def R'prop (l' : Fin (h7.m)) :
  let R'U := R'U h7 q hq0 h2mq l'
  let U := U h7 q hq0 h2mq l'
  (U ∈ nhds (l' + 1 : ℂ)) ∧ ↑↑l' + 1 ∈ U ∧
  (∀ z ∈ U, (h7.R q hq0 h2mq) z = (z - (↑↑l' + 1)) ^ h7.r q hq0 h2mq * R'U z)
   ∧ AnalyticOn ℂ R'U U ∧ R'U (↑↑l' + 1) ≠ 0 := by
  intros R'U U
  have := (exists_R'_at_l'_plus_one h7 q hq0 h2mq l').choose_spec.choose_spec
  exact this

def R'R (l' : Fin (h7.m)) : ℂ → ℂ := fun z =>
  (h7.R q hq0 h2mq) z * (z - (↑l' + 1))^(-(h7.r q hq0 h2mq) : ℤ)

def R' (l' : Fin (h7.m)) : ℂ → ℂ :=
  let R'U := R'U h7 q hq0 h2mq l'
  let R'R := R'R h7 q hq0 h2mq l'
  let U := U h7 q hq0 h2mq l'
  letI : ∀ z, Decidable (z ∈ U) := by {
    intros z
    exact Classical.propDecidable (z ∈ U)}
  fun z =>
    if z = l' + 1 then
      R'U z
    else
      R'R z

-- lemma: R' is equal to R'_nhd on U
lemma R'_eq_R'U (l' : Fin (h7.m)) :
  let R' := h7.R' l'
  let R'U := R'U h7 q hq0 h2mq l'
  let U := h7.U q hq0 h2mq l'
  ∀ z ∈ U, h7.R' q hq0 h2mq l' z = h7.R'U q hq0 h2mq l' z := by
    intros R' R'U U z hz
    unfold GelfondSchneiderSetup.R'
    split_ifs
    · rfl
    · unfold R'R
      have R'prop := (R'prop h7 q hq0 h2mq l').2.2.1 z hz
      rw [R'prop]
      unfold GelfondSchneiderSetup.R'U
      rw [mul_comm, ← mul_assoc]
      have : (z - (↑↑l' + 1)) ^ (-(h7.r q hq0 h2mq) : ℤ) *
          (z - (↑↑l' + 1)) ^ (h7.r q hq0 h2mq) = 1 := by
        rw [← zpow_natCast]
        simp only [zpow_neg]
        refine inv_mul_cancel₀ ?_
        intro H
        simp only [zpow_natCast, pow_eq_zero_iff', ne_eq] at H
        have : ¬z = ↑↑l' + 1 := by {simp_all only [not_false_eq_true, U]}
        apply this
        obtain ⟨H1,H2⟩ := H
        rw [sub_eq_zero] at H1
        exact H1
      rw [this]
      simp only [one_mul]

lemma R'_eq_R'R (l' : Fin (h7.m)) :
  let R' := h7.R' q hq0 h2mq l'
  let R'R := h7.R'R q hq0 h2mq l'
  ∀ z ∈ {z : ℂ | z ≠ l' + 1}, R' z = R'R z := by
    intros R' R'R z hz
    unfold R'
    unfold GelfondSchneiderSetup.R' GelfondSchneiderSetup.R'R
    simp only [mem_setOf_eq] at hz
    split
    · rename_i h
      subst h
      simp_all only [ne_eq, not_true_eq_false]
    · rfl

lemma R'R_analytic (l' : Fin (h7.m)) :
  let R'R := h7.R'R q hq0 h2mq l'
  AnalyticOn ℂ R'R {z : ℂ | z ≠ l' + 1} := by
    unfold R'R
    simp only
    refine AnalyticOn.mul ?_ ?_
    · apply AnalyticOnSubset _ _ univ
      simp only [Set.subset_univ]
      have := h7.anever q hq0 h2mq
      apply analyticOn_univ.mpr fun x a ↦ this x
    · apply AnalyticOn.fun_zpow ?_
      intros z hz
      simp only [mem_setOf_eq] at hz
      exact sub_ne_zero_of_ne hz
      apply AnalyticOn.sub analyticOn_id analyticOn_const

lemma R'analytic (l' : Fin (h7.m)) :
  let R' := R' h7 q hq0 h2mq l'
  ∀ z : ℂ, AnalyticAt ℂ R' z := by
    let U := h7.U q hq0 h2mq l'
    intros R' z
    by_cases H : z = l' + 1
    · have R'prop := (R'prop h7 q hq0 h2mq l')
      apply AnalyticOnAt _ _ U _
      have := R'_eq_R'U
        h7 q hq0 h2mq l'
      rw [AnalyticOnEquiv _ _ U this]
      exact R'prop.2.2.2.1
      rw [H]
      exact R'prop.1
    · apply AnalyticOnAt _ _ {z : ℂ | z ≠ l' + 1} _
      have := R'_eq_R'R h7 q hq0 h2mq l'
      rw [AnalyticOnEquiv _ _ {z : ℂ | z ≠ l' + 1} this]
      apply R'R_analytic
      apply IsOpen.mem_nhds isOpen_ne
      simp only [ne_eq, mem_setOf_eq, H, not_false_eq_true]

lemma R'onC (l' : Fin (h7.m)) :
  let R' := R' h7 q hq0 h2mq l'
  ∀ z : ℂ, (h7.R q hq0 h2mq) z = (z - (l' + 1))^(h7.r q hq0 h2mq) * R' z := by
  intros R' z
  let U := (exists_R'_at_l'_plus_one
    h7 q hq0 h2mq l').choose_spec.choose
  unfold R'
  unfold GelfondSchneiderSetup.R'
  split
  · have R'prop := (R'prop h7 q hq0 h2mq l')
    simp only at R'prop
    apply R'prop.2.2.1
    have : z = ↑↑l' + 1 := by
      rename_i H
      subst H
      simp_all only [ne_eq]
    rw [this]
    apply R'prop.2.1
  · unfold R'R
    rw [mul_comm, mul_assoc]
    have : (z - (↑↑l' + 1)) ^ (-(h7.r q hq0 h2mq) : ℤ) *
        (z - (↑↑l' + 1)) ^ (h7.r q hq0 h2mq) = 1 := by
      rw [← zpow_natCast]
      simp only [zpow_neg]
      refine inv_mul_cancel₀ ?_
      intros H
      simp only [zpow_natCast, pow_eq_zero_iff', ne_eq] at H
      obtain ⟨H1,H2⟩ := H
      have : ¬z = ↑↑l' + 1 := by {simp_all only [not_false_eq_true]}
      apply this
      rwa [sub_eq_zero] at H1
    rw [this]
    simp only [mul_one]

--def Sk' (hk : k K q u ≠ l₀ ) : ℂ → ℂ := ((r).factorial)

--#check EMetric.

def ks : Finset ℂ := Finset.image (fun (k': ℕ) => (k' + 1 : ℂ)) (Finset.range h7.m)

lemma z_in_ks : z ∈ (h7.ks) ↔ ∃ k': Fin (h7.m), z = k' + 1 := by
  apply Iff.intro
  · intros hz
    dsimp [ks] at hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨k',hk'⟩ := hz
    refine Fin.exists_iff.mpr ?_
    use k', hk'.1
    simp_all only
  · intros hk
    obtain ⟨k, hk⟩ := hk
    dsimp [ks]
    rw [hk]
    subst hk
    simp_all only [Finset.mem_image, Finset.mem_range,
      add_left_inj, Nat.cast_inj, exists_eq_right, Fin.is_lt]

def S.U : Set ℂ := (h7.ks)ᶜ

lemma S.U_ne_of_mem {z : ℂ} (hz : z ∈ (S.U h7)) (k' : Fin (h7.m)) : z ≠ (k' + 1 : ℂ) := by
  dsimp [S.U, ks] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists, not_and] at hz
  intro H
  apply hz k' k'.isLt
  exact H.symm

lemma S.U_is_open : IsOpen (S.U h7) := by
  unfold S.U
  rw [EMetric.isOpen_iff]
  intros z hz
  have : (Finset.image (dist z) (ks h7)).Nonempty := by
    dsimp [ks]
    simp only [Finset.image_nonempty, nonempty_range_iff, ne_eq]
    exact Nat.add_one_ne_zero (2 * h7.h + 1)
  let ε := Finset.min' (Finset.image (dist z) (ks h7)) this
  use ENNReal.ofReal ε
  constructor
  · dsimp [ε]
    simp only [ENNReal.ofReal_pos, lt_min'_iff, Finset.mem_image,
      forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, dist_pos, ne_eq, forall_mem_not_eq]
    exact hz
  · simp only [Metric.emetric_ball]
    dsimp [ε]
    rw [Set.compl_def]
    refine subset_setOf.mpr ?_
    intros x hx
    simp only [mem_coe]
    rw [Metric.mem_ball] at hx
    intros H
    rw [lt_min'_iff] at hx
    simp only [Finset.mem_image, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂] at hx
    have := hx x H
    rw [dist_comm z x] at this
    apply lt_irrefl (dist x z) this

lemma S.U_nhds :
  ∀ z, z ∈ U h7 → (S.U h7) ∈ nhds z :=
  fun z hz => IsOpen.mem_nhds (U_is_open h7) hz

lemma zneq0 : ∀ (h : z ∈ S.U h7) (k' : Fin (h7.m)), (z - (k' + 1 : ℂ)) ≠ 0 := by
  intros hz k'
  dsimp [S.U, ks] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists,
    not_and] at hz
  intros H
  apply hz k' k'.isLt
  symm
  rw [sub_eq_zero] at H
  exact H

lemma z_in_ks' (z : ℂ) : z ∈ (h7.ks) ↔ ∃ k': Fin (h7.m), z = k' + 1 := by
  apply Iff.intro
  · intros hz
    dsimp [ks] at hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨k',hk'⟩ := hz
    refine Fin.exists_iff.mpr ?_
    use k', hk'.1
    simp_all only
  · intros hk
    obtain ⟨k, hk⟩:=hk
    dsimp [ks]
    rw [hk]
    subst hk
    simp_all only [Finset.mem_image, Finset.mem_range,
      add_left_inj, Nat.cast_inj, exists_eq_right, Fin.is_lt]

lemma S.U_ne_of_mem' {z : ℂ}  (hz : z ∈ (S.U h7)) (k' : Fin (h7.m)) : z ≠ (k' + 1 : ℂ) := by
  dsimp [S.U, ks] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists, not_and] at hz
  intro H
  apply hz k' k'.isLt
  exact H.symm

def SR : ℂ → ℂ := fun z =>
  (h7.R q hq0 h2mq) z * (h7.r q hq0 h2mq).factorial *
    ((z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq) : ℤ)) *
    (∏ k' ∈ Finset.range (h7.m) \ {↑(h7.l₀' q hq0 h2mq)},
      ((h7.l₀' q hq0 h2mq - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq))

lemma SR_analytic_S.U : AnalyticOn ℂ (h7.SR q hq0 h2mq) (S.U h7) := by
  unfold GelfondSchneiderSetup.SR
  refine AnalyticOn.mul ?_ ?_
  · apply AnalyticOn.mul ?_ ?_
    · apply AnalyticOn.mul ?_ ?_
      · have := h7.anever q hq0 h2mq
        exact
          AnalyticOnSubset (h7.R q hq0 h2mq) (S.U h7)
            (fun ⦃a⦄ ↦ True) (fun ⦃a⦄ a ↦ trivial) (analyticOn_univ.mpr fun x a ↦ this x)
      · exact analyticOn_const
    · apply AnalyticOn.fun_zpow
      · apply AnalyticOnSubset
        · have : (S.U h7) ⊆ Set.univ := by {exact fun ⦃a⦄ a ↦ trivial}
          exact this
        · refine analyticOn_univ_iff_differentiable.mpr ?_
          refine (fun_sub_iff_left ?_).mpr ?_
          simp only [differentiable_const]
          simp only [differentiable_fun_id]
      · intros z hz
        dsimp [S.U, ks] at hz
        simp only [coe_image, coe_range, mem_compl_iff,
          Set.mem_image, Set.mem_Iio, not_exists, not_and] at hz
        have := hz (h7.l₀' q hq0 h2mq)
        intros HC
        apply this
        simp only [Fin.is_lt]
        rw [sub_eq_zero] at HC
        rw [HC]
  · apply Finset.analyticOn_fun_prod
    intros u hu
    simp only [mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hu
    apply AnalyticOn.fun_pow
    refine AnalyticOn.div ?_ ?_ ?_
    · exact analyticOn_const
    · refine DifferentiableOn.analyticOn ?_ ?_
      · simp only [differentiableOn_const, DifferentiableOn.fun_sub_iff_left]
        refine differentiableOn ?_
        exact differentiable_fun_id
      · exact S.U_is_open h7
    · intros x hx
      dsimp [S.U, ks] at hx
      simp only [coe_image, coe_range, mem_compl_iff,
        Set.mem_image, Set.mem_Iio, not_exists, not_and] at hx
      have := hx u hu.1
      intros H
      apply this
      rw [sub_eq_zero] at H
      exact id (Eq.symm H)

-- functions are equal and both analytic are analytic

lemma SR_Analytic : ∀ z, z ∈ S.U h7 → AnalyticAt ℂ (h7.SR q hq0 h2mq) z := by
  intros z hz
  apply AnalyticOnAt
  · apply S.U_nhds h7 z
    exact hz
  · exact SR_analytic_S.U h7 q hq0 h2mq

def SRl0 : ℂ → ℂ := fun z =>
  (h7.R' q hq0 h2mq (h7.l₀' q hq0 h2mq)) z * ((h7.r q hq0 h2mq).factorial)  *
    (∏ k' ∈ Finset.range (h7.m) \ {↑(h7.l₀' q hq0 h2mq)},
    ((h7.l₀' q hq0 h2mq - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq))

def SRl (l' : Fin (h7.m)) : ℂ → ℂ := fun z =>
  (h7.R' q hq0 h2mq l') z *
    (h7.r q hq0 h2mq).factorial *
    ((z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq) : ℤ)) *
    (∏ k' ∈ (Finset.range (h7.m) \ ({↑(h7.l₀' q hq0 h2mq : ℕ)} ∪ {↑(l' : ℕ)})),
      ((h7.l₀' q hq0 h2mq - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq)) *
    (((h7.l₀' q hq0 h2mq)- (l' + 1)) ^ (h7.r q hq0 h2mq))

def S : ℂ → ℂ :=
  fun z =>
    let R' := h7.R' q hq0 h2mq
    if H : ∃ (k' : Fin (h7.m)), z = (k' : ℂ) + 1 then
      let k' := H.choose
      if k' = h7.l₀' q hq0 h2mq then
        h7.SRl0 q hq0 h2mq z
      else
        h7.SRl q hq0 h2mq k' z
    else
      h7.SR q hq0 h2mq z

lemma SR_eq_SRl0 :
  z ∈ (S.U h7) → (h7.SRl0 q hq0 h2mq) z = (h7.SR q hq0 h2mq) z := by
  intros hz
  unfold S.U at *
  unfold SRl0
  dsimp [SR]
  nth_rw 3 [mul_assoc]
  simp only [zpow_neg, zpow_natCast]
  dsimp [ks] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists,
    not_and] at hz
  have := h7.R'onC q hq0 h2mq (h7.l₀' q hq0 h2mq) z
  simp only at this
  rw [this]; clear this
  simp only [← mul_assoc]
  nth_rw 6 [mul_comm]
  rw [mul_assoc  (h7.R' q hq0 h2mq (h7.l₀' q hq0 h2mq) z)
    ((z - (↑↑(h7.l₀' q hq0 h2mq) + 1)) ^ h7.r q hq0 h2mq)]
  rw [mul_comm ((z - (↑↑(h7.l₀' q hq0 h2mq) + 1))
     ^ h7.r q hq0 h2mq) ↑(h7.r q hq0 h2mq).factorial]
  simp only [mul_assoc]
  congr
  rw [← one_mul (a:= ∏ k' ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)},
    ((↑↑(h7.l₀' q hq0 h2mq) - (↑k' + 1)) / (z - (↑k' + 1))) ^ h7.r q hq0 h2mq)]
  simp only [← mul_assoc]
  have H : ((z - ↑↑(h7.l₀' q hq0 h2mq)) ^ (h7.r q hq0 h2mq) )⁻¹ =
      (z - ↑↑(h7.l₀' q hq0 h2mq)) ^ (- (h7.r q hq0 h2mq) : ℤ) := by {
      simp only [zpow_neg, zpow_natCast]}
  have : 1 =  (z - (↑↑(h7.l₀' q hq0 h2mq) + 1)) ^ ↑(h7.r q hq0 h2mq) *
      (z - (↑↑(h7.l₀' q hq0 h2mq) + 1)) ^ (-↑((h7.r q hq0 h2mq) : ℤ)) := by {
    simp only [zpow_neg, zpow_natCast]
    symm
    apply Complex.mul_inv_cancel
    intros Hz
    simp only [pow_eq_zero_iff', ne_eq] at Hz
    have : (h7.l₀' q hq0 h2mq) < h7.m :=  by {simp only [Fin.is_lt]}
    have H := hz  ↑((h7.l₀' q hq0 h2mq)) this
    apply H
    rw [sub_eq_add_neg] at Hz
    rw [add_eq_zero_iff_eq_neg] at Hz
    simp only [neg_neg] at Hz
    symm
    rw [Hz.1]}
  simp only [zpow_neg, zpow_natCast] at this
  nth_rw 1 [this]
  simp only [mul_one]

--fix l+1
lemma SR_eq_SRl (l' : Fin (h7.m)) (hl : l' ≠ h7.l₀' q hq0 h2mq) :
    z ∈ (S.U h7) → (h7.SRl q hq0 h2mq l') z = (h7.SR q hq0 h2mq) z := by
  intros hz
  unfold GelfondSchneiderSetup.S.U at *
  dsimp [GelfondSchneiderSetup.SR, GelfondSchneiderSetup.SRl]
  nth_rw 3 [mul_assoc]
  simp only [zpow_neg, zpow_natCast]
  dsimp [ks] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists,
    not_and] at hz
  have := R'onC h7 q hq0 h2mq l' z
  simp only at this
  rw [this]; clear this
  simp only [← mul_assoc]
  nth_rw 8 [mul_comm]
  rw [mul_assoc  (h7.R' q hq0 h2mq (l') z) ((z - (↑↑(l') + 1)) ^ h7.r q hq0 h2mq)]
  rw [mul_comm ((z - (↑↑(l') + 1)) ^ h7.r q hq0 h2mq) ↑(h7.r q hq0 h2mq).factorial]
  unfold R'
  simp only [mul_assoc]
  have : l' < h7.m := by {simp only [Fin.is_lt]}
  have H := (hz l' this)
  simp only at H

  -- simp only [mul_assoc]
  -- congr
  -- rw [← one_mul (a:= ∏ k' ∈ Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)},
  --   ((↑↑(h7.l₀' q hq0 h2mq) - (↑k' + 1)) / (z - (↑k' + 1))) ^ h7.r q hq0 h2mq)]
  -- simp only [← mul_assoc]
  -- have H : ((z - ↑↑(h7.l₀' q hq0 h2mq)) ^ (h7.r q hq0 h2mq) )⁻¹ =
  --     (z - ↑↑(h7.l₀' q hq0 h2mq)) ^ (- (h7.r q hq0 h2mq) : ℤ) := by {
  --     simp only [zpow_neg, zpow_natCast]}
  -- --rw [this]; clear this
  have : 1 =  (z - (↑↑(h7.l₀' q hq0 h2mq) + 1)) ^ ↑(h7.r q hq0 h2mq) *
      (z - (↑↑(h7.l₀' q hq0 h2mq) + 1)) ^ (-↑((h7.r q hq0 h2mq) : ℤ)) := by {
    simp only [zpow_neg, zpow_natCast]
    symm
    apply Complex.mul_inv_cancel
    intros Hz
    simp only [pow_eq_zero_iff', ne_eq] at Hz
    have : (h7.l₀' q hq0 h2mq) < h7.m :=  by {simp only [Fin.is_lt]}
    have H := hz  ↑((h7.l₀' q hq0 h2mq)) this
    apply H
    rw [sub_eq_add_neg] at Hz
    rw [add_eq_zero_iff_eq_neg] at Hz
    simp only [neg_neg] at Hz
    symm
    rw [Hz.1]}
  split
  · rename_i H
    rw [H]
    simp only [add_sub_add_right_eq_sub, sub_self,
      mul_eq_mul_left_iff, Nat.cast_eq_zero]
    left; left
    rw [zero_pow]
    simp only [zero_mul, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', ne_eq]
    right
    right
    constructor
    by_contra HR
    apply hl
    (expose_names; exact False.elim (hz (↑l') this_1 (id (Eq.symm H))))
    (expose_names; exact fun a ↦ hz (↑l') this_1 (id (Eq.symm H)))
    (expose_names; exact fun a ↦ hz (↑l') this_1 (id (Eq.symm H)))
  · nth_rw 6 [← mul_assoc]
    nth_rw 5 [← mul_assoc]
    nth_rw 8 [mul_comm]
    simp only [mul_assoc]
    simp only [mul_eq_mul_left_iff, inv_eq_zero,
      pow_eq_zero_iff', ne_eq, Nat.cast_eq_zero]
    left
    left
    left
    rw [mul_comm]
    nth_rw 2 [mul_comm]
    sorry


lemma S_eq_SR  :
  z ∈ (S.U h7) → h7.SR q hq0 h2mq z = h7.S q hq0 h2mq z := by
  intros hz
  unfold S.U at *
  unfold S
  simp only
  symm
  simp only [dite_eq_right_iff, forall_exists_index]
  intros x hx
  split
  · exact SR_eq_SRl0 h7 q hq0 h2mq hz
  · apply SR_eq_SRl
    subst hx
    simp_all only [ne_eq, mem_compl_iff, mem_coe,
      add_left_inj, Nat.cast_inj, not_false_eq_true]
    exact hz

lemma dist_le_zero (n m : ℕ) : dist (n : ℂ) (m : ℂ) < 1 → n = m := by {
  rw [Complex.dist_eq]
  by_cases H : m ≤ n
  · have : norm (((n : ℂ)) - (m : ℂ)) = (n - m : ℕ) := by {
     norm_cast
     }
    rw [this]
    simp only [Nat.cast_lt_one]
    intros H'
    omega
  · have : norm (((n : ℂ)) - (m : ℂ)) = norm ((m : ℂ) - (n : ℂ)) := by {
      calc
           _ = norm (-((m : ℂ) - (n : ℂ))) := ?_
           _ = norm (((m : ℂ)) - (n : ℂ)) := ?_
      · simp only [neg_sub]
      · symm
        rw [← norm_neg]
      }
    rw [this]
    have : norm (((m : ℂ)) - (n : ℂ)) = (m - n : ℕ) := by {
     simp only [not_le] at H
     have : n ≤ m := by omega
     norm_cast
     }
    rw [this]
    simp only [Nat.cast_lt_one]
    intros H'
    omega
}

--SR_analytic_S.U follow this for srl0 too
lemma SRl_is_analytic_at_ball_of_radius_one (l' : Fin (h7.m)) (hl : l' ≠ h7.l₀' q hq0 h2mq) :
  AnalyticOn ℂ (h7.SRl q hq0 h2mq l') (Metric.ball ((l' : ℂ) + 1) 1) := by
  unfold GelfondSchneiderSetup.SRl
  refine AnalyticOn.mul ?_ ?_
  · apply AnalyticOn.mul ?_ ?_
    · apply AnalyticOn.mul ?_ ?_
      · have := h7.R'analytic q hq0 h2mq
        simp only at this
        apply AnalyticOn.mul ?_ ?_
        · exact AnalyticOnNhd.analyticOn fun x a ↦ this l' x
        · exact analyticOn_const
      · apply AnalyticOn.fun_zpow
        · apply AnalyticOnSubset
          · have : (Metric.ball ((l' : ℂ) + 1) 1) ⊆ Set.univ := by {exact fun ⦃a⦄ a ↦ trivial}
            exact this
          · refine analyticOn_univ_iff_differentiable.mpr ?_
            refine (fun_sub_iff_left ?_).mpr ?_
            simp only [differentiable_const]
            simp only [differentiable_fun_id]
        · intros z hz
          simp only [Metric.mem_ball] at hz
          apply sub_ne_zero_of_ne
          intro H
          rw [H] at hz
          simp only [dist_add_right] at hz
          have : ((h7.l₀' q hq0 h2mq : ℕ) : ℂ)≠ ((l' : ℕ) : ℂ) := by {
            intros HC
            apply hl
            simp only [Nat.cast_inj] at HC
            symm
            aesop
          }
          rw [← dist_pos] at this
          have Hdist := dist_le_zero ((h7.l₀' q hq0 h2mq)) ↑↑l'
          have Hdist := Hdist hz
          rw [Hdist] at this
          subst H
          simp_all only [ne_eq, dist_self, zero_lt_one, lt_self_iff_false]
    ·
      apply Finset.analyticOn_fun_prod
      intros u hu
      simp only at hu
      apply AnalyticOn.fun_pow
      refine AnalyticOn.div ?_ ?_ ?_
      · exact analyticOn_const
      · refine DifferentiableOn.analyticOn ?_ ?_
        · simp only [differentiableOn_const,
            DifferentiableOn.fun_sub_iff_left]
          refine differentiableOn ?_
          exact differentiable_fun_id
        · exact Metric.isOpen_ball
      · intros x hx
        simp only [Metric.mem_ball] at hx
        simp only [Finset.mem_union, mem_sdiff,
          Finset.mem_range, Finset.mem_singleton] at hu
        cases' hu with h1 h2
        · intros HC
          simp only [not_or] at h2
          obtain ⟨hu, hul0⟩ := h2
          rw [sub_eq_zero] at HC
          rw [HC] at hx
          simp only [dist_add_right] at hx
          rw [← ne_eq] at *
          have Hdist := dist_le_zero u ↑↑l'
          have Hdist := Hdist hx
          rw [Hdist] at hx
          simp only [dist_self, zero_lt_one] at hx
          exact hul0 Hdist
  · exact analyticOn_const

lemma SRl0_is_analytic_at_ball_of_radius_one  :
  AnalyticOn ℂ (h7.SRl0 q hq0 h2mq) (Metric.ball (h7.l₀' q hq0 h2mq + 1) 1) := by
  unfold GelfondSchneiderSetup.SRl0
  refine AnalyticOn.mul ?_ ?_
  · apply AnalyticOn.mul ?_ ?_
    · have := h7.R'analytic q hq0 h2mq
      simp only at this
      exact AnalyticOnNhd.analyticOn fun x a ↦ this (h7.l₀' q hq0 h2mq) x
    · exact analyticOn_const
  · apply Finset.analyticOn_fun_prod
    intros u hu
    simp only [mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hu
    apply AnalyticOn.fun_pow
    refine AnalyticOn.div ?_ ?_ ?_
    · exact analyticOn_const
    · refine DifferentiableOn.analyticOn ?_ ?_
      · simp only [differentiableOn_const, DifferentiableOn.fun_sub_iff_left]
        refine differentiableOn ?_
        exact differentiable_fun_id
      · exact Metric.isOpen_ball
    · intros x hx
      simp only [Metric.mem_ball] at hx
      obtain ⟨hu, hul0⟩ := hu
      have : ((u : ℕ) : ℂ)≠ ((h7.l₀' q hq0 h2mq : ℕ) : ℂ) := by {
        intros HC
        apply hul0
        simp only [Nat.cast_inj] at HC
        symm
        aesop
          }
      rw [← dist_pos] at this
      intros HC
      rw [sub_eq_zero] at HC
      rw [HC] at hx
      simp only [dist_add_right] at hx
      have Hdist := dist_le_zero u  ↑↑(h7.l₀' q hq0 h2mq)
      have Hdist := Hdist hx
      rw [Hdist] at hx
      simp only [dist_self, zero_lt_one] at hx
      exact hul0 Hdist

lemma holS :
  --∀ x ∈ Metric.ball 0 (m K *(1 + (r/q))) \ {(l₀ : ℂ)},
  ∀ z, AnalyticAt ℂ (h7.S q hq0 h2mq) z := by
  intros z
  by_cases H : ∃ (k' : Fin (h7.m)), z = (k' : ℂ) + 1
  by_cases Hzl0 : z = h7.l₀' q hq0 h2mq + 1


  ·
    clear H
   -- obtain ⟨l', hl'⟩ := H
    apply AnalyticAtEq (f := h7.SRl0 q hq0 h2mq)
      (U := (Metric.ball (h7.l₀' q hq0 h2mq + 1) 1))
    · rw [Hzl0]
      refine IsOpen.mem_nhds ?_ ?_
      simp only [Metric.isOpen_ball]
      simp only [Metric.mem_ball, dist_self, zero_lt_one]
    · rw [Hzl0]
      simp only [Metric.mem_ball, dist_self, zero_lt_one]
    ·
      intros z hz
      have: z ∈ S.U h7 := by {
        unfold S.U ks
        simp only [coe_image, coe_range, mem_compl_iff, Set.mem_image, Set.mem_Iio, not_exists,
          not_and]
        simp only [Metric.mem_ball] at hz
        intros x hx
        intros HC
        rw [← HC] at hz
        simp only [dist_add_right] at hz
        sorry

      }
      have := h7.SR_eq_SRl0 q hq0 h2mq this
      rw [this]
      (expose_names; exact S_eq_SR h7 q hq0 h2mq this_1)

    · apply AnalyticOnAt (f:= h7.SRl0 q hq0 h2mq)
      · change (Metric.ball (↑↑(h7.l₀' q hq0 h2mq) + 1) 1) ∈ nhds z
        rw [Hzl0]
        apply Metric.ball_mem_nhds
        simp only [zero_lt_one]
      · exact (h7.SRl0_is_analytic_at_ball_of_radius_one q hq0 h2mq)

  ·
    obtain ⟨l', hl'⟩ := H
    by_cases H' : z = l' + 1
    apply AnalyticAtEq  (f := h7.SRl q hq0 h2mq l') (U:= (Metric.ball ((l' : ℂ) + 1) 1))
    · rw [hl']
      refine IsOpen.mem_nhds ?_ ?_
      simp only [Metric.isOpen_ball]
      simp only [Metric.mem_ball, dist_self, zero_lt_one]
    · rw [hl']
      simp only [Metric.mem_ball, dist_self, zero_lt_one]
    · intros z hzz
      have Hzu : z ∈ S.U h7 := by {
        unfold S.U ks
        simp only [coe_image, coe_range, mem_compl_iff, Set.mem_image, Set.mem_Iio, not_exists,
          not_and]
        simp only [Metric.mem_ball] at hzz
        -- simp only [not_forall, Classical.not_imp, Decidable.not_not] at HC
        -- simp only [exists_prop] at HC
        -- obtain ⟨x, hx⟩ := HC
        intros x hx
        have Hdist := dist_le_zero x (l' + 1)
        intros HX
        rw [← HX] at hzz
        simp only [dist_add_right] at hzz
        sorry
        -- rw [← hx.2] at hzz
        -- simp only [dist_add_right] at hzz


      }
      have := h7.S_eq_SR q hq0 h2mq Hzu
      rw [← this]
      have :  l' ≠ h7.l₀' q hq0 h2mq := by {
        intro Hcontra
        apply Hzl0
        rw [hl', Hcontra]
      }
      have := h7.SR_eq_SRl q hq0 h2mq l' this Hzu
      exact this
    · apply AnalyticOnAt (f:= h7.SRl q hq0 h2mq l')
      · change (Metric.ball (↑↑(l') + 1) 1) ∈ nhds z
        rw [hl']
        apply Metric.ball_mem_nhds
        simp only [zero_lt_one]
      · have :  l' ≠ h7.l₀' q hq0 h2mq := by {
        intro Hcontra
        apply Hzl0
        rw [hl', Hcontra]
      }
        exact (h7.SRl_is_analytic_at_ball_of_radius_one q hq0 h2mq l' this)
    apply AnalyticAtEq (U := S.U h7) (f := h7.SR q hq0 h2mq)
    · have : S.U h7 ∈ nhds z := by {
        unfold S.U ks
        simp only [coe_image, coe_range]
        by_contra HC
        apply H'
        exact hl'
      }
      exact this
    · unfold S.U ks
      simp only [coe_image, coe_range, mem_compl_iff, Set.mem_image, Set.mem_Iio, not_exists,
        not_and]
      by_contra HC
      simp only [not_forall, Decidable.not_not] at HC
      simp only [exists_prop] at HC
      apply H'
      apply hl'
    · intros z hz
      exact S_eq_SR h7 q hq0 h2mq hz
    · exact False.elim (H' hl')


  ·
    apply AnalyticAtEq (U := S.U h7) (f := h7.SR q hq0 h2mq)
    · have : z ∈ S.U h7 := by {
      unfold S.U ks
      simp only [coe_image, coe_range, mem_compl_iff,
        Set.mem_image, Set.mem_Iio, not_exists, not_and]
      simp only [not_exists] at H
      intros x hx
      have := H ⟨x,hx⟩
      simp only at this
      intros HC
      apply this
      rw [HC]
    }
      have := S.U_nhds h7 z this
      exact this
    · have : z ∈ S.U h7 := by {
      unfold S.U ks
      simp only [coe_image, coe_range, mem_compl_iff,
        Set.mem_image, Set.mem_Iio, not_exists, not_and]
      simp only [not_exists] at H
      intros x hx
      have := H ⟨x,hx⟩
      simp only at this
      intros HC
      apply this
      rw [HC]
    }
      exact this
    · intros z hz
      apply h7.S_eq_SR q hq0 h2mq
      simp only [not_exists] at H
      · exact hz
    · apply h7.SR_Analytic q hq0 h2mq z ?_
      have : z ∈ S.U h7 := by {
      unfold S.U ks
      simp only [coe_image, coe_range, mem_compl_iff, Set.mem_image,
        Set.mem_Iio, not_exists,
        not_and]
      simp only [not_exists] at H
      intros x hx
      have := H ⟨x,hx⟩
      simp only at this
      intros HC
      apply this
      rw [HC]}
      exact this




lemma hcauchy :
  (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(0, h7.m *(1 + (h7.r q hq0 h2mq / q))),
  (z - (h7.l₀' q hq0 h2mq + 1 : ℂ))⁻¹ * (h7.S q hq0 h2mq) z) =
    (h7.S q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) := by
  apply two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
  · exact countable_singleton (h7.l₀' q hq0 h2mq + 1 : ℂ)
  · have : (h7.l₀' q hq0 h2mq : ℂ) ∈
       Metric.ball 0 (h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q)) := by {
    simp only [Metric.mem_ball, dist_zero_right, norm_natCast]
    trans
    · have : (h7.l₀' q hq0 h2mq : ℝ) < h7.m := by {simp only [Nat.cast_lt, Fin.is_lt]}
      exact this
    · apply lt_mul_right (mod_cast h7.hm)
      · simp only [lt_add_iff_pos_right]
        apply div_pos (mod_cast h7.r_qt_0 q hq0 h2mq)
        · simp only [Nat.cast_pos]
          exact hq0}
    simp only [Metric.mem_ball, dist_zero_right, gt_iff_lt]
    simp only [Metric.mem_ball, dist_zero_right] at this
    sorry
    --exact this
  · intros x hx
    apply @DifferentiableWithinAt.continuousWithinAt ℂ _ _ _ _ _ _ _ _ _
    refine DifferentiableAt.differentiableWithinAt ?_
    exact AnalyticAt.differentiableAt (holS h7 q hq0 h2mq x)
  · intros x hx
    apply AnalyticAt.differentiableAt (holS h7 q hq0 h2mq x)

-- use k=r
-- use z0= l0'+1
-- R is R
-- for the application
-- one of R1 is R'

-- (hz : z ∈ Metric.sphere 0 (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ))))
--#check sys_coe_bar
def sys_coeff_foo_S : ρᵣ h7 q hq0 h2mq =
  Complex.log (h7.α) ^ (-(h7.r q hq0 h2mq : ℤ)) *
   (h7.S q hq0 h2mq) (↑↑(h7.l₀' q hq0 h2mq) + 1) := by {
  dsimp [ρᵣ]
  congr
  have HAE : ∀ (z : ℂ), AnalyticAt ℂ (h7.R q hq0 h2mq) z := by
    intros z
    exact anever h7 q hq0 h2mq z

  let R₁ : ℂ → ℂ := R' h7 q hq0 h2mq ((h7.l₀' q hq0 h2mq))

  have HR1 : ∀ (z : ℂ), AnalyticAt ℂ R₁ z := by {
    unfold R₁
    intros z
    apply R'analytic h7 q hq0 h2mq (h7.l₀' q hq0 h2mq) z
  }
  have hR₁ : ∀ (z : ℂ), (h7.R q hq0 h2mq) z =
    ((z - (h7.l₀' q hq0 h2mq + 1)) ^ (h7.r q hq0 h2mq)) * (R₁ z) := by {
    intros z
    unfold R₁
    unfold R'
    split
    · rename_i H
      rw [H]
      simp only [sub_self]
      rw [zero_pow]
      simp only [zero_mul]
      · sorry
      · exact rneq0 h7 q hq0 h2mq
    · rename_i H
      unfold R'R
      rw [mul_comm]
      simp only [mul_assoc]
      simp only [zpow_neg, zpow_natCast]
      nth_rw 2 [mul_comm]
      rw [mul_inv_cancel₀]
      simp only [mul_one]
      intros H1
      simp only [pow_eq_zero_iff'] at H1
      apply H
      rw [← sub_eq_zero]
      exact H1.1
    }

  have hr : h7.r q hq0 h2mq ≤ h7.r q hq0 h2mq := by rfl
  --r2 analytic
-- use k=r
-- use z0= l0'+1
-- R is R
-- for the application
-- one of R1 is R'
--R2 is junk
  -- have := existrprime  (z₀ := l₀' h7 q hq0 h2mq + 1)
  --      (R h7 q hq0 h2mq) R₁ HAE HR1 hR₁ (r := r h7 q hq0 h2mq) (k := r h7 q hq0 h2mq) hr
  have : ∀ z,
   ∃ R₂ : ℂ → ℂ, (∀ z : ℂ, AnalyticAt ℂ R₂ z) ∧  deriv^[(h7.r q hq0 h2mq)] (R h7 q hq0 h2mq) z =
   (z - ( l₀' h7 q hq0 h2mq + 1))^((h7.r q hq0 h2mq)-(h7.r q hq0 h2mq)) *
    ((h7.r q hq0 h2mq).factorial/((h7.r q hq0 h2mq)-(h7.r q hq0 h2mq)).factorial * R₁ z +
       (z-( l₀' h7 q hq0 h2mq + 1))* R₂ z) := by {
      intros z
      apply existrprime  (z₀ := l₀' h7 q hq0 h2mq + 1)
       (R h7 q hq0 h2mq) R₁ HAE HR1 hR₁ (r := r h7 q hq0 h2mq) (k := r h7 q hq0 h2mq) hr}


    -- existrprime (z₀ := l₀' h7 q hq0 h2mq + 1)
    -- (k := r h7 q hq0 h2mq) (r := r h7 q hq0 h2mq)
    -- (R h7 q hq0 h2mq) R₁ HAE HR1 hR₁ hr
  simp only [tsub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul] at this
  -- obtain ⟨R2,hR⟩ := this
  -- obtain ⟨R2,hR2⟩ := R2
  -- rw [hR]
  -- unfold R₁
  -- symm
  -- dsimp [S]
  -- simp only [add_left_inj, Nat.cast_inj, exists_apply_eq_apply', ↓reduceDIte]
  -- split
  -- · rename_i H
  --   unfold SRl0
  --   simp only [add_sub_add_right_eq_sub]
  --   rw [mul_comm   ↑(h7.r q hq0 h2mq).factorial
  --     (h7.R' q hq0 h2mq (h7.l₀' q hq0 h2mq) (↑↑(h7.l₀' q hq0 h2mq) + 1))]
  --   nth_rw 2 [← mul_one
  --     (a := (h7.R' q hq0 h2mq (h7.l₀' q hq0 h2mq) (↑↑(h7.l₀' q hq0 h2mq) + 1)) *
  --     ↑(h7.r q hq0 h2mq).factorial) ]
  --   congr
  --   sorry
  -- · rename_i H
  --   unfold SRl
  --   sorry
  sorry
}


lemma S_eq_SR_on_circle :
  ∀ (z : ℂ) (hz : z ∈ Metric.sphere 0
    (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)))),
  h7.S q hq0 h2mq z = h7.SR q hq0 h2mq z := by {
  intros z hz
  unfold S SR
  split
  · rename_i H1
    simp only [zpow_neg, zpow_natCast]
    --simp only [mem_sphere_iff_norm, sub_zero] at hz
    rw [← Real.norm_of_nonneg
      (r := ↑h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q))] at hz
    rw [Real.norm_eq_abs] at hz
    · split
      · rename_i H2
        unfold SRl0
        have := R'prop h7 q hq0 h2mq ( h7.l₀' q hq0 h2mq)
        simp only at this
        unfold R'
        obtain ⟨h1,h2,h3,h5⟩ := this
        split
        · have := h3
          rw [this]
          simp only [mul_assoc]
          nth_rw 3 [mul_comm]
          simp only [mul_assoc]
          congr
          · sorry--doable
          · sorry
        · unfold R'R
          nth_rw 2 [mul_assoc]
          nth_rw 3 [mul_comm]
          simp only [mul_assoc]
          congr
          simp only [zpow_neg, zpow_natCast]
      · rename_i H2
        have := R'prop h7 q hq0 h2mq (h7.l₀' q hq0 h2mq)
        simp only at this
        unfold SRl
        unfold R'
        obtain ⟨h1,h2,h3,h5⟩ := this
        split
        · rename_i H6
          rw [h3]
          nth_rw 8 [mul_comm]
          simp only [zpow_neg, zpow_natCast]
          sorry
          sorry
        · unfold R'R
          simp only [mul_assoc]
          nth_rw 2 [← mul_assoc]
          nth_rw 3 [mul_comm]
          nth_rw 5 [mul_comm]
          simp only [← mul_assoc]
          nth_rw 1 [mul_assoc]
          nth_rw 2 [mul_assoc]
          nth_rw 4 [mul_comm]
          simp only [zpow_neg, zpow_natCast]
          simp only [mul_assoc]
          congr
          sorry


          -- nth_rw 4 [mul_comm]

          -- have := R'prop h7 q hq0 h2mq (h7.l₀' q hq0 h2mq)
          -- obtain ⟨h1,h2,h3,h5⟩ := this
    · positivity
  · simp only [zpow_neg, zpow_natCast]
  }
























































































































def c₉ : ℝ := Real.exp (|1 + ‖h7.β‖| * |Real.log ‖h7.α‖| * (↑h7.m : ℝ))

lemma c9_pos : 0 < h7.c₉ := by {
  unfold c₉
  apply Real.exp_pos}

lemma c9_nonneg : 0 ≤ h7.c₉ := by {
  rw [le_iff_lt_or_eq]
  left
  exact c9_pos h7}

lemma c9_gt_1 : 1 ≤ h7.c₉ := by {
  have := h7.c9_pos
  unfold c₉
  apply Real.one_le_exp
  positivity}

variable {z:ℂ} (hz : (z : ℂ) ∈ Metric.sphere 0 (h7.m * (1 + (h7.r q hq0 h2mq / q))))
  (hl0 : (l₀ : ℝ) < (h7.m : ℝ) * (1 + h7.r q hq0 h2mq / q))

include hz in
lemma norm_hz : ‖z‖ ≤ ‖(h7.m : ℝ)‖ * ‖1 + (h7.r q hq0 h2mq : ℝ) / (q: ℝ)‖ := by
  simp only [mem_sphere_iff_norm, sub_zero] at hz
  rw [hz]
  simp only [Real.norm_eq_abs]
  apply mul_le_mul
  · simp only [Nat.abs_cast, le_refl]
  ·
    exact le_abs_self (1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))
  · refine Left.add_nonneg ?_ ?_
    · simp only [zero_le_one]
    · refine div_nonneg ?_ ?_
      · simp only [Nat.cast_nonneg]
      · simp only [Nat.cast_nonneg]
  · simp only [Nat.abs_cast, Nat.cast_nonneg]

lemma q_frac : ((↑q + ↑(h7.r q hq0 h2mq)) / ↑q : ℝ ) =
    (1 + ↑(h7.r q hq0 h2mq) / (q : ℝ)) := by
  rw [add_div]
  simp only [add_left_inj]
  refine (div_eq_one_iff_eq ?_).mpr rfl
  simp_all only [ne_eq, Nat.cast_eq_zero]
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  simp_all only [lt_self_iff_false]

include hz in
lemma abs_Rb : norm ((h7.R q hq0 h2mq) z) ≤
   (q * q) * ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ) *
    (h7.r q hq0 h2mq) ^ (((h7.r q hq0 h2mq : ℝ ) + 1) / 2))
      * (h7.c₉) ^ (h7.r q hq0 h2mq + q : ℝ)) := by

  calc _ ≤ ∑ t, (‖(canonicalEmbedding h7.K) ((algebraMap (𝓞 h7.K) h7.K)
             ((h7.η q hq0 h2mq) t)) h7.σ‖ * ‖cexp (h7.ρ q t * z)‖) := ?_

       _ ≤ ∑ t : Fin (q*q), (h7.c₄ ^ (h7.n q : ℝ))
         * (h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1) / 2)
        * Real.exp ‖(h7.ρ q t * z)‖ := ?_

       _ ≤ ∑ t : Fin (q*q), (h7.c₄ ^ (h7.n q : ℝ)) *
       (h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1) / 2) *
         Real.exp (norm ((q : ℝ) * (1 + norm h7.β) *
         Real.log (norm h7.α) * (h7.m : ℝ) *
         ((1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ))))) := ?_

       _ ≤ (q * q) * ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ) *
       (h7.r q hq0 h2mq) ^ (((h7.r q hq0 h2mq : ℝ ) + 1) / 2))
         * (h7.c₉) ^ (h7.r q hq0 h2mq + q : ℝ)) := ?_

  · unfold R
    apply norm_sum_le_of_le
    intros b hb
    simp only [Complex.norm_mul, le_refl]
  · apply sum_le_sum
    intros i hi
    apply mul_le_mul -- problem with embedding
    · have lemma82 := fromlemma82_bound h7 q hq0 i h2mq
      unfold house at lemma82
      have :  ‖(canonicalEmbedding h7.K)
         ((algebraMap (𝓞 h7.K) h7.K) (h7.η q hq0 h2mq i))‖ =
        ‖(canonicalEmbedding h7.K)
         ((algebraMap (𝓞 h7.K) h7.K) (h7.η q hq0 h2mq i)) h7.σ‖ := by
          simp only [canonicalEmbedding.apply_at]
          sorry
      rw [← this]
      exact lemma82
    · apply Complex.norm_exp_le_exp_norm
    · simp only [norm_nonneg]
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]; apply pow_nonneg; apply h7.zero_leq_c₄
      · positivity
  · apply sum_le_sum
    intros i hi
    apply mul_le_mul
    · have lemma82 := fromlemma82_bound h7 q hq0 i h2mq
      unfold house at lemma82
      apply Preorder.le_refl _
    ·
      unfold ρ
      --rw [← q_frac]
      simp only [nsmul_eq_mul, norm_mul, Real.exp_le_exp]
      calc
           _ ≤  (‖↑(a q i : ℂ)‖ + ‖↑(b q i) * h7.β‖) * ‖Complex.log h7.α‖ * ‖z‖ := ?_

           _ ≤  (‖(q : ℤ)‖ + ‖q * h7.β‖) * ‖Complex.log h7.α‖ * ‖z‖ := ?_

           _ ≤ (‖(q : ℤ)‖ + ((‖↑(q : ℤ)‖ * ‖h7.β‖))) * ‖Complex.log h7.α‖ * ‖z‖ := ?_

           _ = (‖(q : ℤ)‖ * ((1 + ‖h7.β‖))) * ‖Complex.log h7.α‖ * ‖z‖ := ?_

           _ ≤ ‖(q : ℤ)‖ * ‖1 + ‖h7.β‖‖ * ‖Real.log ‖h7.α‖‖ * ‖(↑h7.m : ℝ)‖ *
               ‖(1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))‖ := ?_

           _ ≤ ‖(q : ℝ)‖ * ‖1 + ‖h7.β‖‖ * ‖Real.log ‖h7.α‖‖ * ‖(↑h7.m : ℝ)‖ *
               ‖(1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))‖ := by {
                simp only [mul_assoc]
                simp_all
              }
      · apply mul_le_mul
        · apply mul_le_mul
          · apply norm_add_le
          · apply le_refl
          · simp only [norm_nonneg]
          · refine Left.add_nonneg ?_ ?_
            · simp only [norm_nonneg]
            · simp only [norm_nonneg]
        · simp only [le_refl]
        · simp only [norm_nonneg]
        · apply mul_nonneg
          · refine Left.add_nonneg ?_ ?_
            · simp only [norm_natCast, Nat.cast_nonneg]
            · simp only [norm_nonneg]
          · simp only [norm_nonneg]
      · apply mul_le_mul
        · apply mul_le_mul
          · refine add_le_add ?_ ?_
            · simp only [norm_natCast]
              simp only [Int.norm_natCast, Nat.cast_le]
              exact a_le_q q i
            · simp only [Complex.norm_mul, norm_natCast]
              apply mul_le_mul
              · simp only [Nat.cast_le]
                exact b_le_q q i
              · simp only [le_refl]
              · simp only [norm_nonneg]
              · simp only [Nat.cast_nonneg]
          · simp only [le_refl]
          · simp only [norm_nonneg]
          · refine Left.add_nonneg ?_ ?_
            · simp only [Int.norm_natCast, Nat.cast_nonneg]
            · simp only [norm_nonneg]
        · simp only [le_refl]
        · simp only [norm_nonneg]
        · apply mul_nonneg
          · refine Left.add_nonneg ?_ ?_
            · simp only [Int.norm_natCast, Nat.cast_nonneg]
            · simp only [norm_nonneg]
          · simp only [norm_nonneg]
      · apply mul_le_mul
        · apply mul_le_mul
          · refine add_le_add ?_ ?_
            · simp only [le_refl]
            · simp only [Complex.norm_mul, norm_natCast, Int.norm_natCast, le_refl]
          · simp only [le_refl]
          · simp only [norm_nonneg]
          · refine Left.add_nonneg ?_ ?_
            · simp only [Int.norm_natCast, Nat.cast_nonneg]
            · apply mul_nonneg
              · simp only [norm_nonneg]
              · simp only [norm_nonneg]
        · simp only [le_refl]
        · simp only [norm_nonneg]
        · positivity
      · congr
        nth_rw 1 [← mul_one (a:=(‖(q : ℤ)‖))]
        rw [mul_add]
      · simp only [mul_assoc]
        apply mul_le_mul
        · simp only [le_refl]
        · apply mul_le_mul
          · exact le_abs_self (1 + ‖h7.β‖)
          · apply mul_le_mul
            ·
              -- rw [le_iff_lt_or_eq]
              -- right
              --rw [← Complex.log_re]
              have h1 := Complex.log_ofReal_re (‖h7.α‖)
              have h2 := Complex.log_re (h7.α)
              --rw [← h2] at h1
              have h3:= Complex.ofReal_log (x:= ‖h7.α‖) (by positivity)
              --rw [← h2] at h3
              --rw [← h2]
              sorry
            · have := h7.norm_hz q hq0 h2mq hz
              trans
              apply this
              · apply mul_le_mul
                · simp only [Real.norm_natCast, le_refl]
                · simp only [Real.norm_eq_abs]
                  nth_rw 1 [← one_mul (a := |1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)|)]
                  simp only [one_mul, le_refl]
                · positivity
                · positivity
            · simp only [norm_nonneg]
            · simp only [Real.norm_eq_abs, abs_nonneg]
          · positivity
          · simp only [Real.norm_eq_abs, abs_nonneg]
        · positivity
        · simp only [Int.norm_natCast, Nat.cast_nonneg]
    · exact Real.exp_nonneg ‖h7.ρ q i * z‖
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        exact h7.zero_leq_c₄
      · apply Real.rpow_nonneg
        simp only [Nat.cast_nonneg]
  · simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
    apply mul_le_mul
    · apply Preorder.le_refl
    · apply mul_le_mul
      · apply mul_le_mul
        · simp only [Real.rpow_natCast]
          refine Bound.pow_le_pow_right_of_le_one_or_one_le ?_
          left
          exact ⟨one_leq_c₄ h7, n_leq_r h7 q hq0 h2mq⟩
        · calc _ ≤ (h7.r q hq0 h2mq : ℝ) ^ (((h7.n q : ℝ) + 1) / 2) := ?_
               _ ≤ (h7.r q hq0 h2mq : ℝ) ^ (((h7.r q hq0 h2mq :ℝ) + 1) / 2) := ?_
          · apply Real.rpow_le_rpow
            · simp only [Nat.cast_nonneg]
            · simp only [Nat.cast_le]; exact n_leq_r h7 q hq0 h2mq
            · refine div_nonneg ?_ ?_
              · norm_cast
                simp only [le_add_iff_nonneg_left, zero_le]
              · simp only [Nat.ofNat_nonneg]
          · apply Real.rpow_le_rpow_of_exponent_le
            · simp only [Nat.one_le_cast]
              trans
              apply h7.one_le_n q hq0 h2mq
              exact n_leq_r h7 q hq0 h2mq
            · refine (div_le_div_iff_of_pos_right ?_).mpr ?_
              · simp only [Nat.ofNat_pos]
              · simp only [add_le_add_iff_right, Nat.cast_le]
                exact n_leq_r h7 q hq0 h2mq
        · apply Real.rpow_nonneg; simp only [Nat.cast_nonneg]
        · apply Real.rpow_nonneg; exact zero_leq_c₄ h7
      ·
        rw [Real.rpow_def_of_pos (x:= h7.c₉)]
        · calc _ ≤ Real.exp (
                   |1 + ‖h7.β‖| * |Real.log ‖h7.α‖| * (↑h7.m) *
                       |(q : ℝ) * (1 + ↑(h7.r q hq0 h2mq) / ↑q)|) := ?_
               _ ≤ Real.exp (Real.log h7.c₉ * (↑(h7.r q hq0 h2mq) + ↑q)) := ?_

          · simp only [Real.exp_le_exp]
            rw [norm_mul];rw [norm_mul];rw [norm_mul];rw [norm_mul]
            have : ‖(q : ℝ)‖ * ‖1 + ‖h7.β‖‖ * ‖Real.log ‖h7.α‖‖ * ‖(h7.m : ℝ)‖ *
               ‖(1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))‖=
                ‖1 + ‖h7.β‖‖ * ‖Real.log ‖h7.α‖‖ * ‖(h7.m : ℝ)‖ *
              ‖(q : ℝ)‖ * ‖(1 + ↑(h7.r q hq0 h2mq : ℝ) / (q : ℝ))‖ := by {
                simp only [Real.norm_eq_abs, mul_eq_mul_right_iff, abs_eq_zero]
                left
                rw [mul_assoc]
                rw [mul_assoc]
                rw [mul_comm]
                simp only [mul_assoc]
              }
            simp only [mul_assoc] at this
            simp only [mul_assoc]
            rw [this]
            simp only [Real.norm_eq_abs]
            rw [← abs_mul]
            have : (q : ℝ) * (1 + (h7.r q hq0 h2mq : ℝ) / q) =
                       (((q : ℝ) + (h7.r q hq0 h2mq : ℝ))) := by {
                        ring_nf
                        simp only [mul_assoc]
                        nth_rw 2 [mul_comm]
                        simp only [← mul_assoc]
                        simp only [add_right_inj]
                        rw [mul_inv_cancel₀]
                        simp only [one_mul]
                        simp only [ne_eq, Nat.cast_eq_zero]
                        rw [← ne_eq]
                        exact Nat.ne_zero_of_lt hq0
                       }
            rw [this]
            simp only [Nat.abs_cast, le_refl]

          · simp only [mul_assoc]
            simp only [Real.exp_le_exp]
            unfold c₉
            simp only [Real.log_exp]
            have : |((h7.r q hq0 h2mq) + q : ℝ)| =
             (↑(h7.r q hq0 h2mq) + ↑q) := by {
              simp only [abs_eq_self]
              positivity}
            rw [← this]
            simp only [mul_assoc]
            apply mul_le_mul
            · simp only [le_refl]
            · apply mul_le_mul
              · simp only [le_refl]
              · apply mul_le_mul
                · simp only [le_refl]
                · have : (q : ℝ) * (1 + (h7.r q hq0 h2mq : ℝ) / q) =
                       (((q : ℝ) + (h7.r q hq0 h2mq : ℝ))) := by {
                        ring_nf
                        simp only [mul_assoc]
                        nth_rw 2 [mul_comm]
                        simp only [← mul_assoc]
                        simp only [add_right_inj]
                        rw [mul_inv_cancel₀]
                        simp only [one_mul]
                        simp only [ne_eq, Nat.cast_eq_zero]
                        rw [← ne_eq]
                        exact Nat.ne_zero_of_lt hq0}
                  rw [this]
                  rw [add_comm]
                · positivity
                · positivity
              · positivity
              · positivity
            · positivity
            · positivity
        · unfold c₉; apply Real.exp_pos
      · positivity
      · apply mul_nonneg
        apply Real.rpow_nonneg
        exact zero_leq_c₄ h7
        apply Real.rpow_nonneg
        · positivity
    · simp only [Real.rpow_natCast, norm_mul, Real.norm_eq_abs]
      apply mul_nonneg
      · apply mul_nonneg
        · apply pow_nonneg
          exact zero_leq_c₄ h7
        · positivity
      · apply Real.exp_nonneg
    · positivity

def c₁₀ : ℝ := (2*h7.m* h7.c₄* h7.c₉* h7.c₉^(2*h7.m : ℝ))

lemma c10_nonneg : 0 ≤ h7.c₁₀ := by
  unfold c₁₀
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · exact zero_leq_c₄ h7
    · exact c9_nonneg h7
  · apply Real.rpow_nonneg; exact c9_nonneg h7

lemma one_le_c10 : 1 ≤ h7.c₁₀ := by
  unfold c₁₀
  simp only [mul_assoc]
  nth_rw 1 [← Real.rpow_one (x := h7.c₉)]
  rw [← Real.rpow_add]
  · apply one_le_mul_of_one_le_of_one_le ?_
    · apply one_le_mul_of_one_le_of_one_le ?_
      · apply one_le_mul_of_one_le_of_one_le ?_
        · refine Real.one_le_rpow ?_ ?_
          · exact c9_gt_1 h7
          · refine Left.add_nonneg ?_ ?_
            · simp only [zero_le_one]
            · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg]
        · exact one_leq_c₄ h7
      · simp only [Nat.one_le_cast]
        apply h7.one_le_m
    · simp only [Nat.one_le_ofNat]
  · exact c9_pos h7

include hz in
lemma abs_R :(q * q) * ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ) *
    (h7.r q hq0 h2mq) ^ (((h7.r q hq0 h2mq : ℝ ) + 1) / 2))
     * (h7.c₉) ^ (h7.r q hq0 h2mq + q : ℝ))
         ≤ (h7.c₁₀)^ (h7.r q hq0 h2mq : ℝ) *
       (h7.r q hq0 h2mq : ℝ)^(1/2*((h7.r q hq0 h2mq)+3 : ℝ)) := by
    calc _ ≤ (2*h7.m : ℝ )^(h7.r q hq0 h2mq : ℝ) *(h7.r q hq0 h2mq : ℝ)*
       ((h7.c₄ ^ (h7.r q hq0 h2mq : ℝ) *
       (h7.r q hq0 h2mq : ℝ) ^ (((h7.r q hq0 h2mq : ℝ) + 1) / 2))
         * (h7.c₉) ^ (h7.r q hq0 h2mq + q : ℝ)) := ?_
       _ ≤ (h7.c₁₀ ^ (h7.r q hq0 h2mq : ℝ)) *
       (h7.r q hq0 h2mq : ℝ) ^ (1/2 * (h7.r q hq0 h2mq + 3) : ℝ) := ?_
    · apply mul_le_mul
      · apply eq6b.extracted_1_1 h7 q hq0 h2mq
      · simp only [Real.rpow_natCast, le_refl]
      · apply mul_nonneg
        · apply mul_nonneg
          · apply Real.rpow_nonneg
            · exact zero_leq_c₄ h7
          · positivity
        · apply Real.rpow_nonneg
          · exact c9_nonneg h7
      · positivity
    · unfold c₁₀
      nth_rw 2 [Real.mul_rpow]
      nth_rw 2 [Real.mul_rpow]
      nth_rw 2 [Real.mul_rpow]
      simp only [← mul_assoc]
      rw [mul_assoc
       ((2*h7.m : ℝ)^(h7.r q hq0 h2mq : ℝ)) (h7.r q hq0 h2mq : ℝ)
       (h7.c₄ ^ (h7.r q hq0 h2mq : ℝ))]
      rw [mul_comm (h7.r q hq0 h2mq : ℝ) (h7.c₄ ^ (h7.r q hq0 h2mq : ℝ))]
      simp only [mul_assoc]
      have hmul :
          (h7.r q hq0 h2mq : ℝ) *
          ((h7.r q hq0 h2mq : ℝ) ^ (((h7.r q hq0 h2mq : ℝ) + 1) / 2)
            * h7.c₉ ^ (h7.r q hq0 h2mq + q : ℝ))
          =
          ((h7.r q hq0 h2mq : ℝ) *
            ((h7.r q hq0 h2mq : ℝ) ^ (((h7.r q hq0 h2mq : ℝ) + 1) / 2)))
            * h7.c₉ ^ (h7.r q hq0 h2mq + q : ℝ) := by {
              rw [mul_assoc]
            }
      rw [hmul]; clear hmul
      apply mul_le_mul
      · simp only [Real.rpow_natCast, le_refl]
      · apply mul_le_mul
        · simp only [Real.rpow_natCast, le_refl]
        · rw [Real.rpow_add]
          rw [mul_comm]
          simp only [mul_assoc]
          apply mul_le_mul
          · simp only [Real.rpow_natCast, le_refl]
          · apply mul_le_mul
            · rw [← Real.rpow_mul]
              apply Real.rpow_le_rpow_of_exponent_le
              · exact c9_gt_1 h7
              · norm_cast
                trans
                apply h7.q_le_two_mn q h2mq
                apply mul_le_mul
                · simp only [le_refl]
                · exact n_leq_r h7 q hq0 h2mq
                · positivity
                · positivity
              · exact c9_nonneg h7
            · nth_rw 1 [← Real.rpow_one ((h7.r q hq0 h2mq))]
              rw [← Real.rpow_add]
              apply Real.rpow_le_rpow_of_exponent_le
              · simp only [Nat.one_le_cast]
                exact r_qt_0 h7 q hq0 h2mq
              · ring_nf
                simp only [one_div, le_refl]
              · simp only [Nat.cast_pos]
                exact r_qt_0 h7 q hq0 h2mq
            · positivity
            · apply Real.rpow_nonneg
              apply Real.rpow_nonneg
              · exact c9_nonneg h7
          · apply mul_nonneg
            · apply Real.rpow_nonneg
              · exact c9_nonneg h7
            · apply mul_nonneg
              · simp only [Nat.cast_nonneg]
              · apply Real.rpow_nonneg
                · simp only [Nat.cast_nonneg]
          · apply Real.rpow_nonneg
            · exact c9_nonneg h7
          · exact c9_pos h7
        · apply mul_nonneg
          · positivity
          · apply Real.rpow_nonneg
            · exact c9_nonneg h7
        · apply Real.rpow_nonneg
          · exact zero_leq_c₄ h7
      · apply mul_nonneg
        · apply Real.rpow_nonneg
          · exact zero_leq_c₄ h7
        · apply mul_nonneg
          · apply mul_nonneg
            · simp only [Nat.cast_nonneg]
            · apply Real.rpow_nonneg
              · simp only [Nat.cast_nonneg]
          · apply Real.rpow_nonneg
            · exact c9_nonneg h7
      · positivity
      · positivity
      · exact zero_leq_c₄ h7
      · apply mul_nonneg
        · positivity
        · exact zero_leq_c₄ h7
      · exact c9_nonneg h7
      · apply mul_nonneg
        · apply mul_nonneg
          ·  positivity
          · exact zero_leq_c₄ h7
        · exact c9_nonneg h7
      · apply Real.rpow_nonneg
        exact c9_nonneg h7

include hz in
lemma abs_Ra : norm ((h7.R q hq0 h2mq) z) ≤ (h7.c₁₀)^ (h7.r q hq0 h2mq : ℝ) *
       (h7.r q hq0 h2mq : ℝ)^(1/2*((h7.r q hq0 h2mq)+3 : ℝ)) := by {
  trans
  apply abs_Rb
  exact hz
  apply abs_R
  exact hz}


include hz in
lemma norm_sub_l0_lower_bound_on_sphere :
    (h7.m * (h7.r q hq0 h2mq : ℝ)) / (q : ℝ) ≤‖z - (h7.l₀' q hq0 h2mq : ℂ)‖ := by

  calc _ = (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) - h7.m : ℝ) := by ring

       _ ≤ ‖z‖ - ‖(h7.l₀' q hq0 h2mq : ℂ)‖ := by
         simp only [norm_natCast]
         have hlm : (h7.l₀' q hq0 h2mq : ℝ) < h7.m := by
           simp only [Nat.cast_lt, Fin.is_lt]
         simp only [mem_sphere_iff_norm, sub_zero] at hz
         rw [hz]
         simp only [tsub_le_iff_right, ge_iff_le]
         have : h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ))
            - (h7.l₀' q hq0 h2mq : ℝ) =
           h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ))
            + (- (h7.l₀' q hq0 h2mq : ℝ)) := rfl
         rw [this]
         rw [add_assoc]
         simp only [le_add_iff_nonneg_right, le_neg_add_iff_add_le,
           add_zero, Nat.cast_le, ge_iff_le]
         rw [le_iff_lt_or_eq]
         left
         simp only [Nat.cast_lt] at hlm
         exact hlm

       _ ≤ ‖z - (h7.l₀' q hq0 h2mq : ℂ)‖ :=
         norm_sub_norm_le z (h7.l₀' q hq0 h2mq)

include hz in
lemma norm_z_minus_km_lower_bound_on_sphere (km : Fin (h7.m)) :
  h7.m * h7.r q hq0 h2mq / q ≤ ‖z - (km : ℂ)‖ := by
  have hz' :
    ‖z‖ = h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) := by
    simpa [mem_sphere_iff_norm, sub_zero] using hz
  have hkm' : (km : ℝ) ≤ h7.m := le_of_lt (by simp [Nat.cast_lt])
  have hkm : ‖(km : ℂ)‖ ≤ (h7.m : ℝ) := by simp
  calc
  h7.m * h7.r q hq0 h2mq / q
    = (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) - h7.m : ℝ) := by ring
  _ = ‖z‖ - h7.m := by simp [hz', sub_eq_add_neg]
  _ ≤ ‖z‖ - ‖(km : ℂ)‖ := by
    simpa [sub_eq_add_neg] using add_le_add_left (neg_le_neg (hkm)) ‖z‖
  _ ≤ ‖z - (km : ℂ)‖ := norm_sub_norm_le z (km : ℂ)

-- #check Finset.univ.erase
-- #check Finset.prod_range_add_one_eq_factorial

lemma prod_dist_le'' (m l₀ : ℕ) (hl : l₀ < m) :
    ∏ k ∈ (Finset.range m \ { l₀ }), k = ∏ k ∈ ((Finset.range m).erase l₀), k  := by
  congr
  exact sdiff_singleton_eq_erase l₀ (Finset.range m)

-- #check Finset.prod_sdiff

lemma prod_sdiff_example  :
  (∏ km ∈ (Finset.range (h7.m) \ { (h7.l₀' q hq0 h2mq : ℕ) }), ‖(h7.l₀' q hq0 h2mq : ℂ) - (km : ℂ)‖)
   *(∏ km ∈ {(h7.l₀' q hq0 h2mq : ℕ)},
   ‖(h7.l₀' q hq0 h2mq : ℂ) - (km : ℂ)‖) =
   (∏ km ∈ Finset.range (h7.m), ‖(h7.l₀' q hq0 h2mq : ℂ) - (km : ℂ)‖) := by
  have hsubset : {(h7.l₀' q hq0 h2mq : ℕ)} ⊆ Finset.range h7.m := by {
    simp only [Finset.singleton_subset_iff, Finset.mem_range]
    exact (h7.l₀' q hq0 h2mq).isLt}
  exact prod_sdiff hsubset


-- lemma div_prod :
--   (∏ km ∈ (Finset.range (h7.m) \
--     {(h7.l₀' q hq0 h2mq : ℕ) }), ‖(h7.l₀' q hq0 h2mq : ℂ) - (km : ℂ)‖)  =
--   (∏ km ∈ Finset.range (h7.m),
--   ‖(h7.l₀' q hq0 h2mq : ℂ) - (km : ℂ)‖) * (1/
--   (∏ km ∈ {(h7.l₀' q hq0 h2mq : ℕ)}, ‖(h7.l₀' q hq0 h2mq : ℂ) - (km : ℂ)‖)) := by  {
--   have s₂ : Finset (ℕ) := Finset.range ((h7.m))
--   have s₁ : Finset (ℕ) := {(h7.l₀' q hq0 h2mq : ℕ)}
--   rw [← prod_sdiff_example]
--   simp only [Finset.prod_singleton]
--   rw [one_div]
--   simp only [mul_assoc]
--   rw [mul_inv_cancel₀]
--   sorry

--   -- rw [← mul_assoc]
--   -- refine Nat.eq_div_of_mul_eq_right ?_ ?_
--   -- ·
--   --   have : (h7.l₀' q hq0 h2mq : ℕ) ∈ Finset.range (h7.m) := by {
--   --     simp only [Finset.mem_range, Fin.is_lt]}
--   --   simp only [Finset.mem_range] at this
--   --   have hm : 1 ≤ h7.m := sorry
--   --   have : h7.l₀' q hq0 h2mq < h7.m := by {
--   --     simp only [Fin.is_lt]
--   --   }
--   --   exact Ne.symm (l0_neq0 h7 q hq0 h2mq)
--   -- · rw [mul_comm]
--   -- · simp only [Fin.is_lt]
--     }

-- lemma prod_norm_bound : ∏ km ∈ ( {(h7.l₀' q hq0 h2mq : ℕ)}),
--         ‖(h7.l₀' q hq0 h2mq : ℂ) - (km : ℂ)‖ ≤ (h7.m : ℝ) := by {
--     simp only [Finset.prod_singleton, sub_self, norm_zero, Nat.cast_nonneg]
--   }

-- lemma full_prod_norm_bound : ∏ km ∈ Finset.range (h7.m),
--         ‖(h7.l₀' q hq0 h2mq : ℂ) - (km : ℂ)‖ ≤ (h7.m : ℝ) := by {
--     sorry
--   }

-- lemma prod_norm_bound': ∏ km ∈ (range h7.m \ {(h7.l₀' q hq0 h2mq : ℕ)}),
--     ‖(h7.l₀' q hq0 h2mq : ℂ) - (km : ℂ)‖ ≤ (h7.m : ℝ) ^ (h7.m - 1) := by {
--     calc _ ≤ ∏ km ∈ (range h7.m \ {(h7.l₀' q hq0 h2mq : ℕ)}),
--          ‖(h7.l₀' q hq0 h2mq : ℂ) - (km : ℂ)‖ * ∏ km ∈ ( {(h7.l₀' q hq0 h2mq : ℕ)}),
--              ‖(h7.l₀' q hq0 h2mq : ℂ) - (km : ℂ)‖ := ?_
--          _ ≤ (h7.m : ℝ) := ?_
--     · sorry
--     · sorry


--   }

def c₁₁ : ℝ := sorry

lemma one_le_c11 : 1 ≤ c₁₁ := sorry

lemma c11_nonneg : 0 ≤ c₁₁ := by
  trans
  apply zero_le_one
  apply one_le_c11

include hz h2mq in
lemma abs_denom : norm (((z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq : ℤ))) *
      ∏ km ∈ (Finset.range (h7.m) \ { (h7.l₀' q hq0 h2mq : ℕ) }),
        (((((h7.l₀' q hq0 h2mq : ℂ) -
        ((km  + 1 : ℂ))) / ((z - ((km + 1 : ℂ))))) ^ (h7.r q hq0 h2mq))))

    ≤ (c₁₁) ^ (h7.r q hq0 h2mq : ℝ) *
        (q / (h7.r q hq0 h2mq)) ^ (h7.m * h7.r q hq0 h2mq : ℝ) := by
  calc
    _ ≤ norm (z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq : ℤ)) *
        norm (∏ km ∈ Finset.range (h7.m) \ { (h7.l₀' q hq0 h2mq : ℕ) },
          (((h7.l₀' q hq0 h2mq : ℂ) -
          (km : ℂ)) / (z - (km : ℂ))) ^ (h7.r q hq0 h2mq)) := ?_

    _ ≤ (h7.m * (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) ^ (-(h7.r q hq0 h2mq : ℤ)) *
        (∏ km ∈ Finset.range (h7.m) \ { (h7.l₀' q hq0 h2mq : ℕ) },
          norm ((((h7.l₀' q hq0 h2mq : ℂ) -
          (km : ℂ)) / (z - (km  : ℂ))) ^ (h7.r q hq0 h2mq))) := ?_

    _ ≤ ((h7.m * (h7.r q hq0 h2mq : ℝ) / (q : ℝ))⁻¹) ^ ((h7.r q hq0 h2mq : ℤ)) *
        (∏ km ∈ Finset.range (h7.m) \ { (h7.l₀' q hq0 h2mq : ℕ) },
          norm (( ((h7.l₀' q hq0 h2mq : ℂ) -
          (km : ℂ)) * ((h7.m * h7.r q hq0 h2mq)/ q : ℝ)⁻¹) ^ (h7.r q hq0 h2mq))) := ?_

    _ ≤ ((h7.m * (h7.r q hq0 h2mq : ℝ) / (q : ℝ))⁻¹) ^ ((h7.r q hq0 h2mq : ℝ)) *
        (∏ km ∈ Finset.range (h7.m) \ { (h7.l₀' q hq0 h2mq : ℕ) },
          norm (( ((h7.l₀' q hq0 h2mq : ℂ) -
          (km : ℂ)) * ((h7.m * h7.r q hq0 h2mq)/ q : ℝ)⁻¹) ^ (h7.r q hq0 h2mq))) := ?_

    _ ≤ (c₁₁) ^ (h7.r q hq0 h2mq : ℝ) *
        (q / (h7.r q hq0 h2mq)) ^ (h7.m * h7.r q hq0 h2mq : ℝ) := ?_


  · simp only [zpow_neg, zpow_natCast, Complex.norm_mul, norm_inv, norm_pow, norm_prod,
    Complex.norm_div]
    sorry

  · apply mul_le_mul
    · simp only [zpow_neg, zpow_natCast]
      refine inv_anti₀ ?_ ?_
      · refine pow_pos ?_ (h7.r q hq0 h2mq)
        refine Real.sqrt_ne_zero'.mp ?_
        · refine (Real.sqrt_ne_zero ?_).mpr ?_
          positivity
          refine div_ne_zero ?_ ?_
          · simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
            constructor
            · aesop
            · simp_rw [h7.rneq0]; simp only [not_false_eq_true]
          · have : 0 < (q : ℝ) := by exact mod_cast hq0
            exact Ne.symm (ne_of_lt this)
      · refine (pow_le_pow_iff_left₀ ?_ ?_ ?_).mpr ?_
        · apply mul_nonneg
          · apply mul_nonneg
            · simp only [Nat.cast_nonneg]
            · simp only [Nat.cast_nonneg]
          · simp only [inv_nonneg, Nat.cast_nonneg]
        · simp only [norm_nonneg]
        · exact rneq0 h7 q hq0 h2mq
        · sorry--apply h7.norm_sub_l0_lower_bound_on_sphere q hq0 h2mq hz
    · rw [norm_prod]
    · simp only [norm_nonneg]
    · simp only [zpow_neg, zpow_natCast, inv_nonneg]
      apply pow_nonneg
      · refine div_nonneg ?_ ?_
        · positivity
        · simp only [Nat.cast_nonneg]
  · apply mul_le_mul
    · simp only [zpow_neg, zpow_natCast]
      rw [le_iff_eq_or_lt]
      left
      ring
    · apply Finset.prod_le_prod
      intros x hx
      · apply norm_nonneg
      · intros x hx
        simp only [norm_pow]
        rw [div_eq_mul_inv]
        refine (pow_le_pow_iff_left₀ ?_ ?_ ?_).mpr ?_
        · apply norm_nonneg
        · apply norm_nonneg
        · exact rneq0 h7 q hq0 h2mq
        · simp only [Complex.norm_mul]
          apply mul_le_mul
          · simp only [le_refl]
          · simp only [norm_inv]
            simp only [mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hx
            let x' : Fin (h7.m) := ⟨x, hx.1⟩
            have := norm_z_minus_km_lower_bound_on_sphere h7 q hq0 h2mq hz x'
            unfold x' at this
            simp only at this
            simp only [inv_div, ofReal_div, ofReal_natCast, ofReal_mul, Complex.norm_div,
              norm_natCast, Complex.norm_mul, ge_iff_le]
            rw [← one_div_le_one_div]
            simp only [one_div, inv_div, div_inv_eq_mul, one_mul]
            exact this
            · refine div_pos ?_ ?_
              · norm_cast
              · apply mul_pos
                · unfold m; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
                  apply add_pos
                  · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos]
                    unfold h
                    exact Module.finrank_pos
                  · simp only [Nat.ofNat_pos]
                · simp only [Nat.cast_pos]
                  exact r_qt_0 h7 q hq0 h2mq
            · simp only [mem_sphere_iff_norm, sub_zero] at hz
              simp only [inv_pos]
              calc _ < ↑h7.m * ↑(h7.r q hq0 h2mq) / ↑q := ?_
                   _ ≤ ‖z - ↑x‖ := ?_
              · apply mul_pos
                · apply mul_pos
                  · unfold m; simp only [Nat.cast_add,
                      Nat.cast_mul, Nat.cast_ofNat]
                    apply add_pos
                    · simp only [Nat.ofNat_pos,
                        mul_pos_iff_of_pos_left, Nat.cast_pos]
                      unfold h
                      exact Module.finrank_pos
                    · simp only [Nat.ofNat_pos]
                  · simp only [Nat.cast_pos]
                    exact r_qt_0 h7 q hq0 h2mq
                · simp only [inv_pos, Nat.cast_pos]
                  exact hq0
              · exact this
          · positivity
          · positivity
    · rw [← norm_prod]; apply norm_nonneg
    · simp only [zpow_natCast]
      apply pow_nonneg
      simp only [inv_div]
      apply mul_nonneg
      · simp only [Nat.cast_nonneg]
      · simp only [_root_.mul_inv_rev]
        apply mul_nonneg
        · simp only [inv_nonneg, Nat.cast_nonneg]
        · simp only [inv_nonneg, Nat.cast_nonneg]
  · simp only [zpow_natCast, norm_pow]
    simp only [inv_div]
    simp only [ofReal_div, ofReal_natCast, ofReal_mul,
      Complex.norm_mul, Complex.norm_div, norm_natCast]

    -- have : ∀ (km : ℂ), norm (( ((h7.l₀' q hq0 h2mq : ℂ) - (km : ℂ)))) ≤
    --  ‖(h7.l₀' q hq0 h2mq : ℂ) - 1‖ + ‖1 - km‖ := by {
    --         intros km
    --         have: ‖(1 : ℂ)‖ ≤ 1 := by {
    --           simp only [norm_one, le_refl]
    --         }
    --         have h3:=norm_sub_mul_le (a := (1:ℂ)) (c := (h7.l₀' q hq0 h2mq)) (b:= km) this
    --         simp only [one_mul] at h3
    --         exact h3
    --       }
    -- have: ‖(1 : ℂ)‖ ≤ 1 := by {
    --           simp only [norm_one, le_refl]
    --         }
    -- have (km : ℂ) := norm_sub_mul_le' (a := km) (c := (h7.l₀' q hq0 h2mq)) (b := (1:ℂ)) this
    -- have : ‖((h7.l₀' q hq0 h2mq : ℕ): ℂ) - 1‖ ≤ ‖((h7.l₀' q hq0 h2mq : ℕ): ℂ)‖ := by {
    --   simp only [norm_natCast]
    --   sorry
    -- }
    apply mul_le_mul-- need to change- it's a dummy
    · sorry
    · sorry
    · sorry
    · sorry
  · conv => enter [1,2,2]; ext x; rw [mul_pow]; rw [mul_comm, Complex.norm_mul];
    rw [← Finset.pow_card_mul_prod]
    have : #(Finset.range h7.m \ {↑(h7.l₀' q hq0 h2mq)}) = h7.m -1 := by {
      rw [Finset.card_sdiff]
      simp only [Finset.card_singleton]
      rw [Finset.card_range]
      simp only [Finset.singleton_subset_iff, Finset.mem_range, Fin.is_lt]
    }
    rw [this]
    simp only [inv_div, norm_pow]
    simp only [← Real.rpow_natCast]
    simp only [ofReal_div, ofReal_natCast, ofReal_mul, Complex.norm_div, norm_natCast,
      Complex.norm_mul]
    rw [← mul_assoc]
    rw [← Real.rpow_mul]
    rw [← Real.rpow_add]
    · sorry
    · sorry
    · positivity


    --rw [Finset.prod_mul_distrib, prod_const]

def c₁₂ : ℝ := (2*h7.m : ℝ)^(h7.m/2 : ℝ) * h7.c₁₀ * c₁₁

lemma one_le_c12 : 1 ≤ h7.c₁₂ := by
  unfold c₁₂
  have := one_le_c11
  refine one_le_mul_of_one_le_of_one_le ?_ (this)
  apply one_le_mul_of_one_le_of_one_le
  · refine Real.one_le_rpow ?_ ?_
    · apply one_le_mul_of_one_le_of_one_le
      · simp only [Nat.one_le_ofNat]
      · simp only [Nat.one_le_cast]
        exact h7.one_le_m
    · positivity
  · apply one_le_c10


lemma c12_nonneg : 0 ≤ h7.c₁₂ := by
  simpa [c₁₂] using
    mul_nonneg (mul_nonneg (by positivity) (c10_nonneg h7)) c11_nonneg

lemma S_norm_bound : ∀ (hz : z ∈ Metric.sphere 0 (h7.m * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)))),
  norm (h7.S q hq0 h2mq z) ≤ (h7.c₁₂)^(h7.r q hq0 h2mq : ℝ)*
    (h7.r q hq0 h2mq : ℝ) ^
              ((((h7.r q hq0 h2mq : ℝ)* ( ( (3 : ℝ) - (h7.m: ℝ))/2 : ℝ)) + (3 / 2 : ℝ))) := by
  intros hz
  calc
    _ = norm ((h7.R q hq0 h2mq z) * ((h7.r q hq0 h2mq).factorial) *
        (((z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (-(h7.r q hq0 h2mq) : ℤ)) *
        ∏ k' ∈ Finset.range (h7.m) \ {↑(h7.l₀' q hq0 h2mq)},
         ((h7.l₀' q hq0 h2mq - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq)) : ℂ) := ?_

    _ = (h7.r q hq0 h2mq).factorial *
        (norm ((h7.R q hq0 h2mq) z) *
        norm ( (1/(z - (h7.l₀' q hq0 h2mq + 1 : ℂ)) ^ (h7.r q hq0 h2mq))) *
        norm ( (∏ k' ∈ Finset.range (h7.m) \ {↑(h7.l₀' q hq0 h2mq)},
         ((h7.l₀' q hq0 h2mq - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ (h7.r q hq0 h2mq)) : ℂ)) := ?_

    _ ≤ (h7.r q hq0 h2mq).factorial *
        ((h7.c₁₀)^(h7.r q hq0 h2mq : ℝ) *
        (h7.r q hq0 h2mq : ℝ)^(1/2*(h7.r q hq0 h2mq + 3 : ℝ)) *
        (c₁₁)^(h7.r q hq0 h2mq : ℝ) *
        (q / h7.r q hq0 h2mq : ℝ)^(h7.m * h7.r q hq0 h2mq : ℝ)) := ?_

    _ ≤ (h7.c₁₂)^(h7.r q hq0 h2mq : ℝ)*(h7.r q hq0 h2mq : ℝ) ^
        ((((h7.r q hq0 h2mq : ℝ)* ( ( (3 : ℝ) - (h7.m: ℝ))/2 : ℝ)) + (3 / 2 : ℝ))) := ?_

  · rw [h7.S_eq_SR_on_circle q hq0 h2mq z hz]
    unfold SR
    simp only [mul_assoc]
  · nth_rewrite 2 [mul_assoc]
    nth_rewrite 2 [← mul_assoc]
    rw [mul_comm  ↑(h7.r q hq0 h2mq).factorial  ‖h7.R q hq0 h2mq z‖]
    simp only [mul_assoc]
    simp only [zpow_neg, zpow_natCast, Complex.norm_mul, norm_natCast, norm_inv, norm_pow,
      norm_prod, Complex.norm_div, one_div]
  · apply mul_le_mul
    · simp only [le_refl]
    · rw [mul_assoc]
      rw [mul_assoc]
      · apply mul_le_mul
        · have := h7.abs_Ra q hq0 h2mq hz
          exact this
        · simp only [one_div, norm_inv, norm_pow, norm_prod, Complex.norm_div]
          have := abs_denom h7 q hq0 h2mq hz
          simp only [zpow_neg, zpow_natCast, Complex.norm_mul, norm_inv, norm_pow, norm_prod,
            Complex.norm_div, Real.rpow_natCast] at this
          simp only [Real.rpow_natCast, ge_iff_le]
          exact this
        · apply mul_nonneg
          · apply norm_nonneg
          · apply norm_nonneg
        · apply mul_nonneg
          · apply Real.rpow_nonneg
            exact c10_nonneg h7
          · positivity
    · apply mul_nonneg
      · apply mul_nonneg
        · simp only [norm_nonneg]
        · simp only [norm_nonneg]
      · simp only [norm_nonneg]
    · simp only [Nat.cast_nonneg]
  · simp only [← mul_assoc]
    rw [mul_comm]
    unfold c₁₂
    rw [Real.mul_rpow]
    rw [Real.mul_rpow]
    nth_rw 7 [mul_comm]
    simp only [← mul_assoc]
    rw [mul_comm]
    nth_rw 3 [mul_comm]
    ring_nf
    simp only [mul_assoc]
    apply mul_le_mul
    · simp only [Real.rpow_natCast, le_refl]
    · apply mul_le_mul
      · simp only [Real.rpow_natCast, le_refl]
      · calc _ ≤ (Real.sqrt (2*h7.m * h7.r q hq0 h2mq : ℝ))^(h7.r q hq0 h2mq * h7.m : ℝ) *
                 ((↑(h7.r q hq0 h2mq : ℝ))⁻¹ ^ (h7.m * h7.r q hq0 h2mq : ℝ) *
                (h7.r q hq0 h2mq).factorial *
                (h7.r q hq0 h2mq : ℝ)^((1/2 : ℝ)*(h7.r q hq0 h2mq + 3 : ℝ))) := ?_

             _≤ (Real.sqrt (2*h7.m : ℝ)^((h7.m * h7.r q hq0 h2mq : ℝ)) *
                ((h7.r q hq0 h2mq : ℝ)^(1/2 : ℝ))^((h7.m * h7.r q hq0 h2mq : ℝ)))*
                ((h7.r q hq0 h2mq : ℝ)^(h7.r q hq0 h2mq : ℝ) *
                (↑(h7.r q hq0 h2mq : ℝ))⁻¹ ^ (h7.m * h7.r q hq0 h2mq : ℝ) *
                (h7.r q hq0 h2mq : ℝ)^((1/2 : ℝ)*(h7.r q hq0 h2mq + 3 : ℝ))) :=?_

             _= ((↑h7.m * 2 : ℝ) ^ ((h7.m : ℝ) * (1 / 2: ℝ))) ^ (h7.r q hq0 h2mq : ℝ)*

              (h7.r q hq0 h2mq : ℝ) ^
              ((((h7.r q hq0 h2mq : ℝ)* ( ( (3 : ℝ) - (h7.m: ℝ))/2 : ℝ)) + (3 / 2 : ℝ))) := ?_

        · rw [Real.mul_rpow]
          simp only [mul_assoc]
          apply mul_le_mul
          have := h7.sqt_etc q hq0 h2mq
          have :=h7.q_le_2sqrtmr q hq0 h2mq
          apply Real.rpow_le_rpow
          · simp only [Nat.cast_nonneg]
          · rw [h7.q_eq_sqrtmn q h2mq]
            simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg,
              Real.sqrt_mul, Nat.ofNat_nonneg]
            simp only [mul_assoc]
            apply mul_le_mul
            · simp only [le_refl]
            · apply mul_le_mul
              · simp only [le_refl]
              · simp only [Nat.cast_nonneg, Real.sqrt_le_sqrt_iff, Nat.cast_le]
                exact n_leq_r h7 q hq0 h2mq
              · positivity
              · positivity
            · positivity
            · positivity
          · positivity
          · ring_nf
            simp only [one_div, le_refl]
          · positivity
          · positivity
          · positivity
          · positivity
        · rw [h7.sqt_etc q hq0 h2mq]
          rw [Real.mul_rpow]
          apply mul_le_mul
          · rw [mul_comm (h7.m : ℝ) (h7.r q hq0 h2mq : ℝ)]
          · rw [mul_comm]
            nth_rw 5 [mul_comm]
            apply mul_le_mul
            · simp only [le_refl]
            · rw [mul_comm]
              apply mul_le_mul
              · norm_cast
                exact Nat.factorial_le_pow (h7.r q hq0 h2mq)
              · simp only [le_refl]
              · positivity
              · positivity
            · positivity
            · positivity
          · positivity
          · positivity
          · positivity
          · positivity
        · rw [← Real.rpow_mul]
          rw [← Real.rpow_mul]
          rw [Real.sqrt_eq_rpow]
          rw [← Real.rpow_mul]
          rw [mul_comm (h7.m : ℝ) (1/2)]
          rw [mul_comm (h7.m : ℝ) 2]
          simp only [mul_assoc]
          congr
          rw [Real.inv_rpow]
          rw [← mul_assoc]
          rw [← Real.rpow_add]
          rw [← Real.rpow_neg]
          rw [← Real.rpow_add]
          rw [← Real.rpow_add]
          · ring_nf
          · simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq
          · simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq
          · simp only [Nat.cast_nonneg]
          · simp only [Nat.cast_pos]; exact r_qt_0 h7 q hq0 h2mq
          · simp only [Nat.cast_nonneg]
          · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg]
          · positivity
          · simp only [Nat.cast_nonneg]
        · ring_nf
          simp only [one_div, Real.rpow_natCast, le_refl]
      · positivity
      · apply Real.rpow_nonneg
        apply h7.c10_nonneg
    · apply mul_nonneg
      · apply Real.rpow_nonneg
        exact c10_nonneg h7
      · positivity
    · apply Real.rpow_nonneg
      exact c11_nonneg
    · positivity
    · exact c10_nonneg h7
    · apply mul_nonneg
      · positivity
      · exact c10_nonneg h7
    · apply c11_nonneg

lemma eq7 (l' : Fin (h7.m)) :
  ρᵣ h7 q hq0 h2mq = Complex.log (h7.α) ^ (-(h7.r q hq0 h2mq) : ℤ) *
    ((2 * ↑Real.pi * I)⁻¹ *
      (∮ z in C(0, h7.m * (1 + (h7.r q hq0 h2mq / q))),
        (z - (h7.l₀' q hq0 h2mq + 1))⁻¹ * (h7.S q hq0 h2mq) z)) := by
  calc _ = (Complex.log (h7.α)) ^ (-(h7.r q hq0 h2mq) : ℤ)
       * (h7.S q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) := ?_
       _ = (Complex.log (h7.α)) ^ (-(h7.r q hq0 h2mq) : ℤ) * ((2 * ↑Real.pi * I)⁻¹ *
    (∮ z in C(0, h7.m * (1 + (h7.r q hq0 h2mq) / q)),
     (z - (h7.l₀' q hq0 h2mq + 1))⁻¹ * (h7.S q hq0 h2mq) z)) := ?_
  · have := h7.sys_coeff_foo_S q hq0 h2mq
    exact this
  · have := h7.hcauchy q hq0 h2mq
    rw [this]

    --rw [hcauchy]
    --exact (h7.l₀' q hq0 h2mq + 1)

def c₁₃ : ℝ :=((‖Complex.log h7.α‖⁻¹ + 1)*h7.m*(2 + 1/h7.m)*h7.c₁₂)

lemma c13_nonneg : 0 ≤ h7.c₁₃ := by {
  unfold c₁₃
  apply mul_nonneg
  · positivity
  · exact h7.c12_nonneg
}
-- have : 1 ≤ h7.c₆ := h7.one_leq_c₆
--   have : 1 ≤ h7.c₇ := h7.one_leq_c₇
--   have := h7.one_leq_c₄
--   have h1 := h7.c8_geq_one
--   have := h7.one_le_c13
--   refine one_le_mul_of_one_le_of_one_le ?_ (this)
--   (expose_names; exact one_le_pow₀ h1)

lemma one_le_c13 : 1 ≤ h7.c₁₃ := by {
  unfold c₁₃
  have : 1 ≤ h7.c₁₂ := h7.one_le_c12
  refine one_le_mul_of_one_le_of_one_le ?_ (this)
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_mul_of_one_le_of_one_le
    · rw [add_comm]
      refine le_add_of_le_of_nonneg ?_ ?_
      · simp only [le_refl]
      · simp only [inv_nonneg, norm_nonneg]
    · simp only [Nat.one_le_cast]
      exact Nat.le_of_ble_eq_true rfl
  · simp only [one_div]
    refine le_add_of_le_of_nonneg ?_ ?_
    · simp only [Nat.one_le_ofNat]
    · simp only [inv_nonneg, Nat.cast_nonneg]
}

def Cnum : ℝ := ((h7.m * (h7.r q hq0 h2mq : ℝ)) / (q : ℝ))⁻¹ *
  ((h7.c₁₂)^(h7.r q hq0 h2mq : ℝ)*(h7.r q hq0 h2mq : ℝ) ^
              ((((h7.r q hq0 h2mq : ℝ)* ( ( (3 : ℝ) - (h7.m: ℝ))/2 : ℝ)) + (3 / 2 : ℝ))))

lemma hf : ∀ z ∈ Metric.sphere 0 (h7.m * (1 + ↑(h7.r q hq0 h2mq : ℝ) / ↑q)),
    ‖(z - ((↑(h7.l₀' q hq0 h2mq) : ℂ)))⁻¹ *
    (h7.SR q hq0 h2mq z)‖ ≤ h7.Cnum q hq0 h2mq := by {
      intros z hz
      have hS := S_norm_bound h7 q hq0 h2mq hz
      simp only [Complex.norm_mul, norm_inv, ge_iff_le]
      have := h7.S_eq_SR_on_circle q hq0 h2mq z hz
      rw [← this]
      unfold Cnum
      apply mul_le_mul
      · apply inv_anti₀
        · refine Real.sqrt_ne_zero'.mp ?_
          · refine (Real.sqrt_ne_zero ?_).mpr ?_
            positivity
            refine div_ne_zero ?_ ?_
            · simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
              constructor
              · rw [← ne_eq]; unfold m
                simp only [ne_eq, Nat.add_eq_zero, mul_eq_zero,
                 OfNat.ofNat_ne_zero, false_or,
                  and_false, not_false_eq_true]
              · simp_rw [h7.rneq0]; simp only [not_false_eq_true]
            · have : 0 < (q : ℝ) := by exact mod_cast hq0
              exact Ne.symm (ne_of_lt this)
        apply h7.norm_sub_l0_lower_bound_on_sphere q hq0 h2mq hz
      · exact hS
      · positivity
      · positivity
    }

-- #moogle "@zero_le_real_div?."
-- #check circleIntegral.norm_integral_le_of_norm_le_const'
--#check circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
--include hz in
lemma eq8 : norm (ρᵣ h7 q hq0 h2mq) ≤ (h7.c₁₃) ^ (h7.r q hq0 h2mq : ℝ) *
           ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) *
           ((3 - (h7.m : ℝ))) / 2 + 3 / 2)) := by

  have hR : 0 ≤ (h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q) : ℝ) := by
    apply mul_nonneg
    · simp only [Nat.cast_nonneg]
    · trans
      · exact zero_le_one
      · simp only [le_add_iff_nonneg_right]
        have := h7.r_div_q_geq_0 q hq0 h2mq
        have : 0 ≤ (h7.r q hq0 h2mq : ℝ) := by {simp only [Nat.cast_nonneg]}
        apply div_nonneg
        · simp only [Nat.cast_nonneg]
        · simp only [Nat.cast_nonneg]

  have H := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR
    (h7.hf q hq0 h2mq)

  calc _ = norm (Complex.log h7.α ^ (-(h7.r q hq0 h2mq : ℤ))
  * ((2 * Real.pi) * I)⁻¹ * ∮ (z : ℂ) in
           C(0, h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q)),
           (z - ↑((h7.l₀' q hq0 h2mq : ℂ) + 1))⁻¹ * (h7.S q hq0 h2mq z)) := ?_

       _ = norm (Complex.log (h7.α) ^ (-(h7.r q hq0 h2mq : ℤ))) *
          norm ((2 * Real.pi * I)⁻¹) * norm (∮ (z : ℂ) in
          C(0, h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q)),
          (z - ↑((h7.l₀' q hq0 h2mq : ℂ) + 1))⁻¹ * (h7.S q hq0 h2mq z)) := ?_

       _ = norm ((Complex.log (h7.α) ^ (-(h7.r q hq0 h2mq : ℤ)))) *
          norm ((2 * Real.pi * I)⁻¹) * norm (∮ (z : ℂ) in
          C(0, h7.m * (1 + ↑(h7.r q hq0 h2mq) / ↑q)),
          (z - ↑((h7.l₀' q hq0 h2mq : ℂ) + 1))⁻¹ * (h7.SR q hq0 h2mq z)) := ?_

       _ ≤ ((norm ((Complex.log h7.α))^ (-(h7.r q hq0 h2mq : ℤ)))) *
         (h7.m : ℝ) * (1 + (h7.r q hq0 h2mq : ℝ) / (q : ℝ)) *
          (h7.c₁₂) ^ (h7.r q hq0 h2mq : ℝ) *
          ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) *
           (3 - h7.m : ℝ) / 2 + 3 / 2) * ((q : ℝ) / (((h7.m : ℝ) *
            (h7.r q hq0 h2mq : ℝ))))) := ?_

       _ ≤ (h7.c₁₃) ^ (h7.r q hq0 h2mq : ℝ) *
           ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) *
           ((3 - (h7.m : ℝ))) / 2 + 3 / 2)) := ?_

  · rw [h7.eq7 q hq0 h2mq]
    simp only [mul_assoc]
    exact (h7.l₀' q hq0 h2mq)
  · simp only [zpow_neg, zpow_natCast, _root_.mul_inv_rev,
    norm_inv, norm_pow, norm_real, Real.norm_eq_abs, norm_ofNat, norm_mul]
  · simp only [mul_assoc]
    congr
    ext z
    congr
    have := h7.S_eq_SR_on_circle q hq0 h2mq z
    apply this
    sorry
  · simp only [mul_assoc]
    simp only [zpow_neg, zpow_natCast, norm_inv, norm_pow, _root_.mul_inv_rev, inv_I, neg_mul,
      norm_neg, Complex.norm_mul, norm_I, norm_real, Real.norm_eq_abs, one_mul, norm_ofNat]
    · apply mul_le_mul
      · simp only [le_refl]
      · simp only [_root_.mul_inv_rev, inv_I, neg_mul, smul_eq_mul, norm_neg, Complex.norm_mul,
          norm_I, norm_inv, norm_real, Real.norm_eq_abs, norm_ofNat, one_mul] at H
        simp only [mul_assoc] at *
        sorry
      --   trans
      --   --apply H
      --   simp only [Real.rpow_natCast]
      --   apply mul_le_mul
      --   · simp only [le_refl]
      --   · sorry
      --   · sorry
      --   · simp only [Nat.cast_nonneg]
      · positivity
      · simp only [inv_nonneg, norm_nonneg, pow_nonneg]
  · simp only [zpow_neg, zpow_natCast]
    simp only [mul_assoc]
    nth_rw 5 [← mul_comm]
    unfold c₁₃
    rw [Real.mul_rpow]
    rw [Real.mul_rpow]
    rw [Real.mul_rpow]
    simp only [mul_assoc]
    apply mul_le_mul
    · rw [← norm_inv]
      rw [← inv_pow]
      rw [← norm_inv]
      simp only [Real.rpow_natCast]
      apply pow_le_pow_left₀
      simp only [norm_inv, inv_nonneg, norm_nonneg]
      simp only [norm_inv, le_add_iff_nonneg_right, zero_le_one]
    · apply mul_le_mul
      · nth_rw 1 [← Real.rpow_one (x:= h7.m)]
        apply Real.rpow_le_rpow_of_exponent_le
        · unfold m; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          rw [le_iff_lt_or_eq]
          left
          trans
          apply one_lt_two
          simp only [lt_add_iff_pos_left, Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos]
          unfold h; exact Module.finrank_pos
        · simp only [Nat.one_le_cast]
          exact one_le_r h7 q hq0 h2mq
      · simp only [← mul_assoc]
        nth_rw 1 [mul_comm]
        nth_rw 6 [mul_comm]
        apply mul_le_mul
        · simp only [le_refl]
        · simp only [mul_assoc]
          rw [mul_comm]
          nth_rw 4 [mul_comm]
          simp only [mul_assoc]
          apply mul_le_mul
          · simp only [Real.rpow_natCast, le_refl]
          · ring_nf
            rw [mul_rotate]
            simp only [mul_assoc]
            nth_rw 2 [← mul_assoc]
            rw [inv_mul_cancel₀]
            simp only [one_mul]
            nth_rw 1 [← mul_assoc]
            rw [inv_mul_cancel₀]
            simp only [one_mul]
            calc _ ≤ (h7.m : ℝ)⁻¹ + (2*(h7.m : ℝ)*(h7.r q hq0 h2mq : ℝ))
                      * ((h7.m : ℝ)⁻¹ * (h7.r q hq0 h2mq : ℝ)⁻¹) :=?_
                 _ ≤ (2 + (h7.m : ℝ)⁻¹) ^ (h7.r q hq0 h2mq : ℝ) := ?_
            · simp only [add_le_add_iff_left]
              apply mul_le_mul
              · norm_cast
                trans
                apply h7.q_le_two_mn q h2mq
                apply mul_le_mul
                · simp only [le_refl]
                · exact n_leq_r h7 q hq0 h2mq
                · positivity
                · positivity
              · simp only [le_refl]
              · positivity
              · positivity
            · ring_nf
              rw [mul_inv_cancel₀]
              simp only [one_mul]
              rw [mul_inv_cancel₀]
              simp only [one_mul]
              nth_rw 1 [← Real.rpow_one (x:=(2 + (h7.m : ℝ)⁻¹))]
              apply Real.rpow_le_rpow_of_exponent_le
              · refine le_add_of_le_of_nonneg ?_ ?_
                · simp only [Nat.one_le_ofNat]
                · simp only [inv_nonneg, Nat.cast_nonneg]
              · simp only [Nat.one_le_cast]
                exact one_le_r h7 q hq0 h2mq
              · simp only [ne_eq, Nat.cast_eq_zero]; exact rneq0 h7 q hq0 h2mq
              · simp only [ne_eq, Nat.cast_eq_zero]
                exact Nat.ne_zero_of_lt (h7.one_le_m)
            · simp only [ne_eq, Nat.cast_eq_zero];exact rneq0 h7 q hq0 h2mq
            · simp only [ne_eq, Nat.cast_eq_zero]
              exact Nat.ne_zero_of_lt hq0
          · positivity
          · apply Real.rpow_nonneg
            exact c12_nonneg h7
        · apply mul_nonneg
          · apply mul_nonneg
            · refine Left.add_nonneg ?_ ?_
              · simp only [zero_le_one]
              · positivity
            · apply Real.rpow_nonneg
              · exact c12_nonneg h7
          · positivity
        · positivity
      · apply mul_nonneg
        · refine Left.add_nonneg ?_ ?_
          · simp only [zero_le_one]
          · positivity
        · apply mul_nonneg
          · apply Real.rpow_nonneg
            · exact c12_nonneg h7
          · positivity
      · positivity
    · apply mul_nonneg
      · simp only [Nat.cast_nonneg]
      · apply mul_nonneg
        · positivity
        · apply mul_nonneg
          · apply Real.rpow_nonneg
            exact c12_nonneg h7
          · apply mul_nonneg
            · positivity
            · positivity
    · apply Real.rpow_nonneg
      rw [add_comm]
      trans
      apply zero_le_one
      refine le_add_of_le_of_nonneg ?_ ?_
      · simp only [le_refl]
      · simp only [inv_nonneg, norm_nonneg]
    · rw [add_comm]
      trans
      apply zero_le_one
      refine le_add_of_le_of_nonneg ?_ ?_
      · simp only [le_refl]
      · simp only [inv_nonneg, norm_nonneg]
    · simp only [Nat.cast_nonneg]
    · positivity
    · positivity
    · positivity
    · exact c12_nonneg h7


def c₁₄ : ℝ := h7.c₈^((h7.h-1)) * h7.c₁₃

lemma c14_nonneg : 1 ≤ h7.c₁₄ := by
  unfold c₁₄
  have : 1 ≤ h7.c₆ := h7.one_leq_c₆
  have : 1 ≤ h7.c₇ := h7.one_leq_c₇
  have := h7.one_leq_c₄
  have h1 := h7.c8_geq_one
  have := h7.one_le_c13
  refine one_le_mul_of_one_le_of_one_le ?_ (this)
  (expose_names; exact one_le_pow₀ h1)

lemma use6and8 :
  norm ((Algebra.norm ℚ (rho h7 q hq0 h2mq))) ≤ (h7.c₁₄)^(h7.r q hq0 h2mq : ℝ) *
  (h7.r q hq0 h2mq : ℝ)^((-(h7.r q hq0 h2mq : ℝ))/2 + 3 * (h7.h)/2) := by

  calc _ ≤  ‖ρᵣ h7 q hq0 h2mq‖ * (house (rho h7 q hq0 h2mq)) ^ (((h7.h) - 1 )) := ?_

       _ ≤ (h7.c₈ ^ h7.r q hq0 h2mq * ↑(h7.r q hq0 h2mq :ℝ) ^
          ((h7.r q hq0 h2mq : ℝ) + 3 / 2))^((h7.h) -1) *
          ((h7.c₁₃) ^ (h7.r q hq0 h2mq : ℝ) *
           ((h7.r q hq0 h2mq : ℝ) ^ ((h7.r q hq0 h2mq : ℝ) *
           ((3 - (h7.m : ℝ))) / 2 + 3 / 2))) := ?_

       _ ≤ ((h7.c₁₄)^(h7.r q hq0 h2mq : ℝ)) * (↑(h7.r q hq0 h2mq: ℝ))^(
         (((h7.h: ℝ) - 1)) * ((h7.r q hq0 h2mq : ℝ) + 3/2) +
         ((((h7.r q hq0 h2mq : ℝ) * (3 - (h7.m : ℝ))) / 2) + 3 / 2)) := ?_

       _ = ((h7.c₁₄)^(h7.r q hq0 h2mq: ℝ)) * (↑(h7.r q hq0 h2mq: ℝ))^(
         ((-(h7.r q hq0 h2mq : ℝ))/2) + 3 * (h7.h)/ 2) := ?_

  · have := norm_le_house_norm (K:=h7.K) ( α := (h7.rho q hq0 h2mq)) h7.σ
    rw [← rho_eq_ρᵣ]
    unfold h
    simp only [← Real.rpow_natCast] at *
    exact this
  · nth_rw 2 [mul_comm]
    apply mul_le_mul
    · apply eq8 h7 q hq0 h2mq
    · have := h7.eq6 q hq0 h2mq
      simp only [← Real.rpow_natCast] at *
      apply Real.rpow_le_rpow
      · exact house_nonneg (h7.rho q hq0 h2mq)
      · exact this
      · simp only [Nat.cast_nonneg]
    · apply pow_nonneg
      exact house_nonneg (h7.rho q hq0 h2mq)
    · apply mul_nonneg
      · apply Real.rpow_nonneg
        exact h7.c13_nonneg
      · positivity
  · unfold c₁₄
    simp only [← Real.rpow_natCast] at *
    rw [Real.mul_rpow]
    rw [← Real.rpow_mul]
    nth_rw 3 [mul_comm]
    nth_rw 1 [← Real.rpow_mul]
    nth_rw 5 [mul_comm]
    simp only [← mul_assoc]
    nth_rw  2 [mul_assoc]
    rw [← Real.rpow_add]
    rw [mul_comm]
    simp only [← mul_assoc]
    rw [Real.rpow_mul]
    rw [← Real.mul_rpow]
    nth_rw 7 [mul_comm]
    nth_rw 2 [mul_comm]
    apply mul_le_mul
    · simp only [Real.rpow_natCast]
      simp only [le_refl]
    · rw [le_iff_lt_or_eq]
      right
      congr
      refine Nat.cast_pred ?_
      unfold h; exact Module.finrank_pos
    · positivity
    · simp only [Real.rpow_natCast]
      apply pow_nonneg
      apply mul_nonneg
      · apply pow_nonneg
        exact c8_nonneg h7
      · exact h7.c13_nonneg
    · exact h7.c13_nonneg
    · simp only [Real.rpow_natCast]
      apply pow_nonneg
      exact c8_nonneg h7
    · exact c8_nonneg h7
    · simp only [Nat.cast_pos]
      exact r_qt_0 h7 q hq0 h2mq
    · simp only [Nat.cast_nonneg]
    · exact c8_nonneg h7
    · simp only [Real.rpow_natCast]
      apply pow_nonneg
      exact c8_nonneg h7
    · apply Real.rpow_nonneg
      simp only [Nat.cast_nonneg]
  · unfold m
    simp only [mul_eq_mul_left_iff]
    left
    have :((h7.h: ℝ) - 1) * ((h7.r q hq0 h2mq : ℝ) + 3/2) +
      ((h7.r q hq0 h2mq : ℝ) * (3 - (h7.m : ℝ)) / 2 + 3 / 2)=
    (-(h7.r q hq0 h2mq : ℝ))/2 + 3 * (h7.h)/ 2 := by {
      unfold m
      rw [mul_add]
      rw [← add_div]
      rw [← add_div]
      rw [mul_div]
      rw [add_assoc]
      rw [← add_div]
      rw [add_div']
      apply Mathlib.Tactic.LinearCombination.div_eq_const
      · rw [mul_sub]
        rw [sub_mul]
        rw [sub_mul]
        rw [sub_mul]
        simp only [one_mul]
        simp only [sub_add_add_cancel]
        ring_nf
        simp only [add_assoc]
        nth_rw 2 [sub_eq_add_neg]
        simp only [add_right_inj]
        rw [sub_eq_add_neg]
        simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul]
        rw [mul_add]
        ring
      · simp only [ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true]
    }
    rw [← this]
    unfold m
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

def c₁₅ : ℝ := h7.c₁₄ * h7.c₅

theorem norm_pos_rho  :
    0 < ‖(Algebra.norm ℚ) (h7.rho q hq0 h2mq)‖ := by
  simp only [norm_pos_iff, ne_eq, Algebra.norm_eq_zero_iff]
  intros H
  apply_fun h7.σ at H
  apply ρᵣ_nonzero h7 q hq0 h2mq
  rw [rho_eq_ρᵣ] at H
  simp only [H, map_zero]

lemma eq5inv:
  norm ((Algebra.norm ℚ) (h7.rho q hq0 h2mq)) ⁻¹ <
    h7.c₅ ^ ((h7.r q hq0 h2mq : ℝ)) := by
  have eq5 := eq5 h7 q hq0 h2mq
  simp only at eq5
  rw [← inv_lt_inv₀] at eq5
  · simp only [norm_inv]
    simp only at eq5
    rw [← Real.rpow_neg] at eq5
    simp only [neg_neg] at eq5
    exact eq5
    rw [le_iff_lt_or_eq]
    left
    exact c5nonneg h7
  · exact norm_pos_rho h7 q hq0 h2mq
  · simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, inv_pos]
    apply pow_pos
    apply c5nonneg h7

lemma use5 : (h7.r q hq0 h2mq : ℝ) ^
  (((h7.r q hq0 h2mq : ℝ) - 3 * (h7.h)) / 2) <
    (h7.c₁₅) ^ (h7.r q hq0 h2mq : ℝ) := by

  have eq5 := eq5 h7 q hq0 h2mq

  have Hpow : ↑(h7.r q hq0 h2mq : ℝ) ^
    (((h7.r q hq0 h2mq : ℝ ) - 3 * h7.h) / 2) =
    (↑(h7.r q hq0 h2mq : ℝ) ^
    (-(h7.r q hq0 h2mq : ℝ ) / 2 + 3 * ↑h7.h / 2))⁻¹ := by
    rw [← one_div]
    ring_nf
    rw [← Real.rpow_neg]
    congr
    ring_nf
    simp only [Nat.cast_nonneg]

  have :  ↑(h7.r q hq0 h2mq : ℝ) ^
    (((h7.r q hq0 h2mq : ℝ) - 3 * h7.h) / 2) ≤
    (norm (↑((Algebra.norm ℚ) (h7.rho q hq0 h2mq))) ⁻¹)
      * h7.c₁₄ ^ (h7.r q hq0 h2mq : ℝ):= by
    simp only [norm_inv]
    refine (le_inv_mul_iff₀' (norm_pos_rho h7 q hq0 h2mq)).mpr ?_
    · rw [Hpow]
      refine mul_inv_le_of_le_mul₀ ?_ ?_ (use6and8 h7 q hq0 h2mq)
      · positivity
      · apply Real.rpow_nonneg (le_trans zero_le_one h7.c14_nonneg)

  calc _ = (↑(h7.r q hq0 h2mq : ℝ) ^
     (-(h7.r q hq0 h2mq : ℝ ) / 2 + 3 * ↑h7.h / 2))⁻¹ := ?_
       _ ≤ (norm (↑((Algebra.norm ℚ) (h7.rho q hq0 h2mq))))⁻¹
           * h7.c₁₄ ^ (h7.r q hq0 h2mq : ℝ) := ?_
       _ < h7.c₁₄^(h7.r q hq0 h2mq : ℝ) * h7.c₅ ^(h7.r q hq0 h2mq : ℝ) := ?_
       _ = (h7.c₁₅) ^(h7.r q hq0 h2mq : ℝ) := ?_
  · rw [← Hpow]
  · simp only at this
    rw [← Hpow]
    simp only [norm_inv] at this
    apply this
  · rw [mul_comm]
    have := eq5inv h7 q hq0 h2mq
    simp only [norm_inv, Real.rpow_natCast] at this
    refine (mul_lt_mul_left ?_).mpr ?_
    · simp only [Real.rpow_natCast]
      apply pow_pos
      have := h7.c14_nonneg
      linarith
    · simp only [Real.rpow_natCast]
      exact this
  · unfold c₁₅
    rw [← Real.mul_rpow]
    · exact le_trans zero_le_one h7.c14_nonneg
    · exact (c5nonneg h7).le

theorem gelfondSchneider (α β : ℂ) (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
  (htriv : α ≠ 0 ∧ α ≠ 1) (hirr : ∀ i j : ℤ, β ≠ i / j) :
    Transcendental ℚ (α ^ β) := fun hγ => by

  obtain ⟨K, hK, hNK, σ, hd, α', β', γ', habc⟩ :=
    getElemsInNF α β (α^β) hα hβ hγ

  let q : ℕ := sorry

  have hq0 : 0 < q := sorry
  have h7 : GelfondSchneiderSetup  := by {
    exact GelfondSchneiderSetup.mk α β K σ α' β' γ' hirr htriv hα hβ habc hd
  }
  haveI : DecidableEq (h7.K →+* ℂ) := by {
    exact h7.hd
  }
  have h2mq : 2 * h7.m ∣ q ^ 2 := sorry

  have use5 := use5 h7 q hq0 h2mq
  have hnr : h7.n q ≤ h7.r q hq0 h2mq := by {exact n_leq_r h7 q hq0 h2mq}

  --simp only at use5

  -- apply absurd main
  -- simp only [ge_iff_le, not_le]
  --exact use5
  sorry

end GelfondSchneiderSetup





































































































--   -- let ρ : (Fin q × Fin q) → (Fin m × Fin r) → K := fun (a,b) (l₀,k) =>
--   --   algebraMap (𝓞 K) K (η (a, b))

--   let ρ : (Fin q × Fin q)  → K := fun (a,b) =>
--      algebraMap (𝓞 K) K (η (a, b))

--     -- ((a+1) + (b+1) * β')^(r : ℤ)
--     -- * α'^((a+1) * (l₀+1 : ℤ))
--     -- * γ' ^((b+1) * (l₀+1 : ℤ))

--   let c₅ : ℝ := c₁^(h*r + h*2*m K*q : ℤ)

  --The norm of an algebraic integer is again an integer,
  --because it is equal (up to sign)
   --  to the constant term of the characteristic polynomial.
  --fix this (N (c₁^(r+2mq) ρ)) = c₁^r+2mq*N(ρ)
  -- have eq5 (t : Fin q × Fin q) (u : Fin m × Fin r) : c₅^((-r : ℤ)) <
  --   norm (Algebra.norm ℚ (ρ t)) := by
  --     calc c₅^((-r : ℤ)) < c₁^((- h : ℤ)*(r + 2*m K*q)) := by {
  --       simp only [zpow_neg, zpow_natCast, neg_mul]
  --       rw [inv_lt_inv]
  --       · rw [mul_add]
  --         have : (h:ℤ) * r + ↑h * (2 * m* ↑q) = (h :ℤ)* ↑r + ↑h * 2 * m* ↑q := by
  --           rw [mul_assoc, mul_assoc, mul_assoc]
  --         rw [this]
  --         refine lt_self_pow ?h ?hm
  --         · rw [← one_zpow ((h : ℤ)* ↑r + ↑h * 2 * m* ↑q )]
  --           simp only [one_zpow]
  --           simp only [c₁]
  --           simp only [Int.cast_mul, Int.cast_max, Int.cast_one]
  --           apply one_lt_pow
  --           · sorry
  --           · sorry
  --         · sorry
  --       · sorry
  --       · sorry
  --     }
  --       _ < norm (Algebra.norm ℚ (ρ t)):= sorry

--   let c₄' : ℝ  := c₄ ^ n * (↑n ^ (1 / 2) * (↑n + 1))

--   let c₆ : ℝ := sorry

--   let c₇ : ℝ := sorry

--   let c₈ : ℝ := max (c₄^n * (n^(1/2)*(n+1))*q^2*(c₆*q)^n*(c₇)^(q : ℤ)) 1

--   let c₈' : ℝ := max (c₈^r) ((c₈)^r * r ^ (r+3/2))

--   have eq6 (t : Fin q × Fin q) (u : Fin m × Fin r) :
--     house (ρ t) ≤ c₈' := by
--     calc _ ≤ c₄' := by {
--         simp only [c₄']
--         exact fromlemma82_bound t
--         }
--          _ ≤c₄'*(q^2*(c₆*q)^n*(c₇)^(q : ℤ)) := by {
--           apply  le_mul_of_one_le_right
--           · calc 0 ≤ 1 := sorry
--                  _ ≤ c₄' := sorry
--           · sorry
--          }
--          _ ≤ (c₈^r) := by { sorry
--           --apply le_max_left
--           }
--          _ ≤ c₈' := by {
--           simp only [c₈']
--           apply le_max_left
--           }

--   let S : (Fin m × Fin n) → ℂ → ℂ := fun (l₀, k) z =>
--     (r.factorial) * (R (l₀, k) z) / ((z - l₀) ^ r) *
--       ∏ k in Finset.range ((r - 1)) \ {(l₀ : ℕ)}, ((l₀ - k) / (z - k)) ^ r

--   -- --have hR : 0 < (m*(1+ (r/q)) : ℝ) := sorry
--   have alt_cauchy (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--       (∮ z in C(0, m*(1+ (r/q))), (z - l₀)⁻¹ * (S (l₀,k) z)) =
--         (2 * ↑Real.pi * I) •  S (l₀,k) l₀ := by
--     apply _root_.DifferentiableOn.circleIntegral_sub_inv_smul
--     · sorry
--     · simp only [Metric.mem_ball, dist_zero_right, norm_nat]
--       have : (l₀ : ℝ) < m := by simp only [Nat.cast_lt, Fin.is_lt]
--       trans
--       · exact this
--       · apply lt_mul_right
--         · exact mod_cast hm
--         · sorry

--   have hcauchy : ∀ (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q), (2 * ↑Real.pi * I)⁻¹ *
--     (∮ z in C(0, m*(1+ (r/q))), (z - l₀)⁻¹ * (S (l₀,k) z)) = S (l₀,k) l₀ := fun k l₀ t => by
--    apply two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
--     · have : Set.Countable {(l₀ : ℂ)} := countable_singleton (l₀ : ℂ)
--       exact this
--     · have : (l₀ : ℂ) ∈ Metric.ball 0 (m K* (1 + ↑r / ↑q)) := by {
--       simp only [Metric.mem_ball, dist_zero_right, norm_nat]
--       have : (l₀ : ℝ) < m := by simp only [Nat.cast_lt, Fin.is_lt]
--       trans
--       · exact this
--       · apply lt_mul_right
--         · exact mod_cast hm
--         · sorry}
--       exact this
--     · intros x hx
--       simp only [Metric.mem_closedBall, dist_zero_right, norm_eq_abs] at hx
--       simp only [Prod.mk.eta, div_pow, prod_div_distrib, S]
--       simp only [Prod.mk.eta, sum_prod_type, R]
--       sorry

--     · have : ∀ z ∈ Metric.ball 0 (m K *(1+ (r/q))) \ {(l₀ : ℂ)},
--          DifferentiableAt ℂ (S (l₀, k)) z := by {
--       intros z hz
--       simp only [mem_diff, Metric.mem_ball, dist_zero_right, norm_eq_abs,
--         mem_singleton_iff] at hz
--       rcases hz with ⟨hzabs, hzneq⟩
--       --simp only [S,R]
--       -- have : DifferentiableAt ℂ (R (l₀, k)) z := by {
--       --   simp only [DifferentiableAt]
--       --   use fderiv ℂ (R (l₀, k)) z
--       --   --use ∑ t, σ (η t) *σ (ρ t) * exp (σ (ρ t) * l₀)
--       -- }
--       simp only [DifferentiableAt]
--       use fderiv ℂ (S (l₀, k)) z
--       sorry
--       }
--       exact this

-- lemma alt_cauchy :
--   let r := r K α β hirr htriv σ hd α' β' γ' habc q u t hq0 h2mq
--   let S := S K α β hirr htriv σ hd α' β' γ' habc q u t hq0 h2mq
--   let l₀ := l₀ K α β hirr htriv σ hd α' β' γ' habc q u t hq0 h2mq

--   (∮ z in C(0, m * (1+ (r/q))), (z - l₀)⁻¹ * (S z)) = (2 * ↑Real.pi * I) • S l₀ := by

--   let l₀ := l₀ K α β hirr htriv σ hd α' β' γ' habc q u t hq0 h2mq

--   apply _root_.DifferentiableOn.circleIntegral_sub_inv_smul
--   · refine differentiableOn ?_
--     sorry
--   · simp only [Metric.mem_ball, dist_zero_right]
--     have : (l₀ : ℝ) < (m K) := by
--       simp only [Nat.cast_lt, Fin.is_lt]
--       unfold l₀
--       unfold _root_.l₀
--       simp only [ne_eq, Fin.is_lt]
--     trans
--     · simp only [norm_natCast]
--       exact this
--     · apply lt_mul_right
--       · simp only [Nat.cast_pos]
--         exact hm K
--       · simp_all only [Nat.cast_lt, lt_add_iff_pos_right,
--           Nat.cast_pos, div_pos_iff_of_pos_right, l₀]
--         sorry

--   have newρ (z : ℂ) (hz : z ∈ Metric.ball 0 (m K *(1+ (r/q))))
--           (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--       σ (ρ t) = log (α) ^ (-r : ℤ) * ((2 * ↑Real.pi * I)⁻¹ *
--         (∮ z in C(0, m*(1+ (r/q))), (z - l₀)⁻¹ * (S (l₀,k) z))) := by
--         calc
--       _ = (log (α))^(- r : ℤ) * (S  (l₀,k) l₀) := sorry
--       _ = log (α) ^ (-r : ℤ) * ((2 * ↑Real.pi * I)⁻¹ *
--       (∮ z in C(0, m*(1+ (r/q))), (z - l₀)⁻¹ * (S (l₀,k) z))) := by
--     {rw [← hcauchy]
--      exact t}

--   let c₉ : ℝ := sorry

--   let c₁₀ : ℝ := sorry

--   have abs_R (z : ℂ) (hz : z ∈ Metric.ball 0 (m K *(1+ (r/q)))) (k : Fin n)
--         (l₀ : Fin m) (t : Fin q × Fin q) :
--     norm (R (l₀, k) z) ≤ (c₁₀)^r * r^(1/2*(r+3)):= calc
--        _ ≤ q^2 * ‖σ (η t)‖*
--           Real.exp ((q+q*(norm (β)))*(Real.log (norm (α)))*m K*(1+r/q)) := by {
--             simp only [Prod.mk.eta, sum_prod_type, norm_eq_abs, R]
--             sorry

--           }
--        _ ≤ q^2 * (c₄)^n *n ^((1/2)*(n+1))*(c₉)^(r+q) := sorry
--        _ ≤ (c₁₀)^r * r^(1/2*(r+3)) := sorry

--   have abs_hmrqzl₀ (z : ℂ) (hz : z ∈ Metric.sphere 0 (m K *(1+ (r/q))))
--      (k : Fin n) (l₀ : Fin m) : m*r/q ≤ norm (z - l₀) := calc
--           _ = (m * (1 + r/q) - m : ℝ) := by {ring}
--           _ ≤ norm z - norm l₀ := by {
--           simp only [hz, norm_natCast]
--           have : (l₀ : ℝ) < m := by {
--             simp only [Nat.cast_lt, Fin.is_lt]
--             }
--           sorry
--           --rwa [sub_lt_sub_iff_left]
--           }
--           _ ≤ norm (z - l₀) := by {apply AbsoluteValue.le_sub}
--   have abs_z_k (k : Fin n) (l₀ : Fin m) (z : ℂ) (hz : z ∈ Metric.sphere 0 (m K *(1+ (r/q)))) :
--         m*r/q ≤ norm (z-k) := by
--     calc _ ≤ norm (z - l₀) := abs_hmrqzl₀ z hz k l₀
--          _ ≤ norm (z-k) := by { sorry
--           --aesop --          }
--   let c₁₁ : ℝ := sorry

--   have abs_denom (z : ℂ)(hz : z ∈ Metric.sphere 0 (m K *(1+ (r/q)))) (k : Fin n) (l₀ : Fin m) :
--     norm (((z - l₀)^(-r : ℤ))* ∏ k ∈ Finset.range (m + 1) \ {(l₀: ℕ)}, ((l₀ - k)/(z-k))^r)
--            ≤ (c₁₁)^r * (q/r)^(m*r) := sorry

--   let c₁₂ : ℝ := sorry

--   have (z : ℂ) (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--           norm (S (l₀, k) z) ≤ (c₁₂)^r*((3-m)/2 + 3 /2) := calc
--           _ = norm ((r.factorial) * (R (l₀, k) z) / ((z - l₀) ^ r) *
--               ∏ k in Finset.range ((r - 1)) \ {(l₀ : ℕ)}, ((l₀ - k) / (z - k)) ^ r) := rfl
--           _ = r.factorial * (norm ((R (l₀, k) z)) * norm ( (1/(z - l₀) ^ r)) *
--             norm (∏ k in Finset.range ((r - 1)) \
--                 {(l₀ : ℕ)}, ((l₀ - k) / (z - k)) ^ r)) := by {
--             simp only [_root_.map_mul]
--             simp only [map_div₀, _root_.map_mul, norm_natCast, map_pow, div_pow,
--               prod_div_distrib, map_prod, one_div, map_inv₀]
--             have : norm (R (l₀, k) z) / norm (z - ↑↑l₀) ^ r=
--              norm (R (l₀, k) z) * (1/  norm (z - ↑↑l₀) ^ r) := by {
--               rw [mul_one_div]
--              }
--             norm_cast at this
--             sorry
--             }
--           _ ≤  r.factorial*((c₁₀)^r*r^((r+3)/2)*(c₁₁)^r*(q/r)^(m*r)) := by {
--             rw [mul_le_mul_left]
--             · sorry
--             · simp only [Nat.cast_pos]
--               exact Nat.factorial_pos r
--           }
--           _ ≤ (c₁₂)^r*((3-m)/2 + 3 /2) := sorry
--   let c₁₃ : ℝ := sorry

--   let hρ (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--     σ (ρ t) = ((2 * Real.pi)⁻¹ * ∮ (z : ℂ) in
--         C(0, m* (1 + ↑r / ↑q)), (z - ↑l₀)⁻¹ * S  (l₀, k) z) := sorry

--   have eq8 (z : ℂ) (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--     norm (σ (ρ t))≤ (c₁₃)^r*r^(r*(3-m)/2 +3/2) := by
--       calc _ = norm ((2 * Real.pi)⁻¹ * ∮ (z : ℂ) in
--         C(0, m* (1 + ↑r / ↑q)), (z - ↑l₀)⁻¹ * S  (l₀, k) z) := by {rw [hρ k l₀ t]}
--            _≤ norm ((2 * Real.pi)⁻¹) *  norm (∮ (z : ℂ) in
--         C(0, m* (1 + ↑r / ↑q)),(z - ↑l₀)⁻¹ * S  (l₀, k) z) := by {
--           simp only [_root_.map_mul]
--           simp only [_root_.mul_inv_rev, ofReal_mul, ofReal_inv,
--            ofReal_ofNat, _root_.map_mul, map_inv₀, norm_ofReal, norm_ofNat,
--             le_refl]}
--            _ ≤ norm ((log (α)))^((-r : ℤ))*m K*(1+r/q)*
--         (c₁₂)^r*r^(r*(3-m)/2 +3/2)*q/(m*r) := by sorry
--            _ ≤ (c₁₃)^r*r^(r*(3-m)/2 +3/2)  := by sorry

--   let c₁₄ : ℝ := sorry

--   have use6and8 : (Algebra.norm ℚ ρ) ≤ (c₁₄)^r*r^((-r:ℤ)/2+3*h/2) := calc
--           _ ≤ (c₁₄)^r*r^((h-1)*(r+3/2)+(3-m)*r*1/2 +3/2) := sorry
--           _ = (c₁₄)^r*r^((-r : ℤ)/2+3*h/2) := sorry

--   have final_ineq : r^(r/2 - 3*h/2) ≥ c₁₅^r := sorry
--   exact ⟨r,  hr, final_ineq⟩
--   --sorry
-- include hα hβ
-- theorem hilbert7 : Transcendental ℚ (α ^ β) := fun hγ => by
--   obtain ⟨K, hK, hNK, σ, hd, α', β', γ', ha,hb, hc⟩ := getElemsInNF α β (α^β) hα hβ hγ
--   --have hq0 : 0 < q := sorry
--   rcases (main K α β σ α' β' γ' q) with ⟨r, ⟨hr, hs⟩⟩
--     -- only now you define t
--   have use5 : r^(r/2 - 3*h K/2) < c₁₅^r := calc
--     _ <  c₁₄^r * c₅^r := by sorry
--     _ = c₁₅^r := by {
--       rw [← mul_pow]
--       simp only [c₁₅]}
--   linarith
