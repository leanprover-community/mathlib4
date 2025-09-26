/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.H7.h7aux
import Mathlib.NumberTheory.H7.h7order
import Mathlib.NumberTheory.H7.House
import Mathlib.FieldTheory.Minpoly.IsConjRoot

set_option autoImplicit true
set_option linter.style.multiGoal false
set_option linter.style.cases false
set_option linter.unusedSectionVars true
set_option linter.style.longFile 0
set_option linter.unusedVariables false
set_option linter.style.commandStart false

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
  Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (α β : ℂ) (hirr : ∀ i j : ℤ, β ≠ i / j) (htriv : α ≠ 0 ∧ α ≠ 1)

open Complex

include htriv in
lemma γneq0 : α ^ β ≠ 0 := fun H => htriv.1 ((cpow_eq_zero_iff α β).mp H).1

include hirr in
lemma βneq0 : β ≠ 0 := fun H => hirr 0 1 (by simpa [div_one] using H)

variable (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β) (K : Type) [Field K]
  (σ : K →+* ℂ) (hd : DecidableEq (K →+* ℂ))
  (α' β' γ' : K)

def σ1 := canonicalEmbedding K

variable (habc : α = σ α' ∧ β = σ β' ∧ α ^ β = σ γ')

include habc htriv hirr in
lemma hneq0 : α' ≠ 0 ∧ β' ≠ 0 ∧ γ' ≠ 0 :=
  ⟨fun H => htriv.1 (habc.1 ▸ H ▸ RingHom.map_zero σ),
   ⟨fun H => βneq0 β hirr (habc.2.1 ▸ H ▸ RingHom.map_zero σ),
    fun H => γneq0 α β htriv (habc.2.2 ▸ H ▸ RingHom.map_zero σ)⟩⟩

include habc htriv in
lemma hneq1 : α' ≠ 1 := by
  intros H
  apply_fun σ at H
  rw [← habc.1,map_one] at H
  apply htriv.2 H

macro_rules | `(hneq0) => `(hneq0 α β hirr htriv K σ α' β' γ' habc)

include hirr htriv habc in
lemma β'ne_zero : β' ≠ 0 := (hneq0).2.1

variable [NumberField K]

abbrev c' (α : K) : ℤ := (c'_both α : ℤ)

macro_rules | `(c') => `(c' K)

lemma c'_IsIntegral (α : K) : IsIntegral ℤ ((c' ) α • α) := (c'_both α).2.2

lemma c'_neq0 (α : K) : (c'_both α : ℤ) ≠ 0 := (c'_both α).2.1

def c₁ : ℤ := abs ((((c') α') * ((c') β') * ((c') γ')))

macro_rules | `(c₁) => `(c₁ K α' β' γ')

lemma one_leq_c₁ : 1 ≤ c₁ :=
  (Int.one_le_abs (mul_ne_zero (mul_ne_zero (c'_neq0 K α') (c'_neq0 K β')) (c'_neq0 K γ')))

lemma c₁_neq_zero : c₁ K α' β' γ' ≠ 0 := by
  have := one_leq_c₁ K α' β' γ'
  exact Ne.symm (Int.ne_of_lt this)

lemma isIntegral_c₁α : IsIntegral ℤ (c₁ • α') := by
  have h := IsIntegral_assoc (x := (c') γ') (y := (c') β') K ((c') α') α'
    (c'_IsIntegral K α')
  conv => enter [2]; rw [c₁, mul_comm, mul_comm ((c') α') ((c') β'), ← mul_assoc]
  rcases abs_choice (( (c') γ' * (c') β' * (c') α'))
  rename_i H1
  · rw [H1]; exact h
  · rename_i H2; rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁β : IsIntegral ℤ (c₁ • β') := by
  have h := IsIntegral_assoc (x := (c') γ') (y := (c') α') K ((c') β') β'
    (c'_IsIntegral K β')
  rw [c₁, mul_comm, ← mul_assoc]
  rcases abs_choice ((c') γ' * (c') α' * (c') β' )
  · rename_i H1; rw [H1]; exact h
  · rename_i H2; rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁γ : IsIntegral ℤ (c₁ • γ') := by
  have h := IsIntegral_assoc (x := (c') α') (y := (c') β') K ((c') γ') γ'
    (c'_IsIntegral K γ')
  rw [c₁]
  rcases abs_choice (((c') α' * (c') β' * c' K γ'))
  · rename_i H1; rw [H1]; exact h
  · rename_i H2; rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma c₁b (n : ℕ) : 1 ≤ n → k ≤ n - 1 → 1 ≤ (a : ℕ) → 1 ≤ (b : ℕ) →
  IsIntegral ℤ (c₁ ^ (n - 1) • (a + b • β') ^ k) := by
  intros hn hkn ha hb
  have : c₁^(n - 1) = c₁^(n - 1 - k) * c₁^k := by
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
  exact isIntegral_c₁β K α' β' γ'

lemma c₁ac (u : K) (n k a l : ℕ) (hnk : a * l ≤ n * k) (H : IsIntegral ℤ (↑c₁ * u)) :
  IsIntegral ℤ (c₁^(n * k) • u ^ (a*l)) := by
  have : c₁ ^ (n * k) = c₁ ^ (n * k - a * l)*c₁^(a * l) := by
    rw [← pow_add]; rwa [Nat.sub_add_cancel]
  rw [this, zsmul_eq_mul]
  simp only [Int.cast_mul, Int.cast_pow]; rw [mul_assoc]
  apply IsIntegral.mul; apply IsIntegral.pow; apply IsIntegral.Cast
  rw [← mul_pow]; exact IsIntegral.pow H _

variable (q : ℕ)

abbrev h := Module.finrank ℚ K

macro_rules | `(h) => `(h K)

def m := 2 * h + 2

macro_rules | `(m) => `(m K)

def n := q^2 / (2 * m)

macro_rules | `(n) => `(n K q)

variable (u : Fin (m K * n K q)) (t : Fin (q * q)) (hq0 : 0 < q)

abbrev a : ℕ := (finProdFinEquiv.symm.1 t).1 + 1
abbrev b : ℕ := (finProdFinEquiv.symm.1 t).2 + 1
abbrev k : ℕ := (finProdFinEquiv.symm.1 u).2
abbrev l : ℕ := (finProdFinEquiv.symm.1 u).1 + 1

macro_rules | `(a) => `(a q t)
macro_rules | `(b) => `(b q t)
macro_rules | `(k) => `(k K q u)
macro_rules | `(l) => `(l K q u)

def shift {w : ℕ} (s : Fin w) : ℕ := s + 1

lemma foo'' {w : ℕ} (s : Fin w) : 1 ≤ s.val + 1 := by {
  simp_all only [le_add_iff_nonneg_left, zero_le]}

lemma bar' {w : ℕ} (s : Fin w) : s + 1 ≤ w := s.isLt

lemma fin_n_plus_1_le_n_plus1 {w} (s : Fin w) : s + 1 ≤ w + 1 := by
  simp only [add_le_add_iff_right, Fin.is_le']

lemma fin_le_val_last_u (u : Fin ((m * n) + 1)) : u ≤ (m * n) := by
  apply Fin.le_last

lemma b_le_q : b ≤ q := bar' (finProdFinEquiv.symm.toFun t).2

lemma l_le_n : l ≤ m := by
  exact bar' (finProdFinEquiv.symm.toFun u).1

lemma a_le_n : (finProdFinEquiv.symm.1 t).1 + 1 ≤ q := by
  exact bar' (finProdFinEquiv.symm.toFun t).1

lemma k_le_n_sub1 : (k : ℤ) ≤ (n - 1 : ℤ) := by
  rw [sub_eq_add_neg]
  have : k + (1 : ℤ) ≤ ↑n → k ≤ ↑n + (-1 : ℤ) := by {
    simp only [Int.reduceNeg, le_add_neg_iff_add_le, imp_self]}
  apply this
  norm_cast
  exact bar' (finProdFinEquiv.symm.toFun u).2

lemma al_leq_mq : a * l ≤ q * m := by
  apply mul_le_mul (bar' (finProdFinEquiv.symm.toFun t).1)
    (l_le_n K q u) (zero_le _) (zero_le _)

lemma bl_leq_mq : b * l ≤ q * m := by
  apply mul_le_mul (bar' (finProdFinEquiv.symm.toFun t).2)
    (l_le_n K q u) (zero_le _) (zero_le _)

lemma k_leq_n_sub_1 : k ≤ n := Fin.is_le'

abbrev c_coeffs0 := c₁^(k :ℕ) * c₁^ (a * l) * c₁^(b * l)

macro_rules | `(c_coeffs0) => `(c_coeffs0 K α' β' γ' q u t)

open Nat in include hq0 in omit hq0 in
lemma c1a0 :
 IsIntegral ℤ (c₁ ^ (a * l) • (α' ^ (a * l : ℕ))) := by
  apply c₁ac K α' β' γ' α' a l a l ?_ ?_
  · rw [mul_comm]
  · rw [← zsmul_eq_mul]; exact isIntegral_c₁α K α' β' γ'

open Nat in include hq0 in omit hq0 in
lemma c1c0 : IsIntegral ℤ (c₁ ^ (b * l) • (γ'^ (b * l : ℕ))) := by
  apply c₁ac K α' β' γ' γ' b  l b l ?_ ?_
  · rw [mul_comm]
  · rw [← zsmul_eq_mul]; exact isIntegral_c₁γ K α' β' γ'

open Nat in include hq0 in
lemma c1a :
 IsIntegral ℤ (c₁^(m * q) • (α' ^ (a * l : ℕ))) := by
  apply c₁ac K α' β' γ' α' (m) q (a) ((l)) ?_ ?_
  · rw [mul_comm]
    exact Nat.mul_le_mul
      (add_le_of_le_sub (le_of_ble_eq_true rfl)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).1.isLt))
      (add_le_of_le_sub hq0 (le_sub_one_of_lt ((finProdFinEquiv.symm.1 t).1).isLt))
  · rw [← zsmul_eq_mul]; exact isIntegral_c₁α K α' β' γ'

open Nat in include hq0 in
lemma c1c : IsIntegral ℤ (c₁ ^ (m * q) • (γ'^ (b * l : ℕ))) := by
  apply c₁ac K α' β' γ' γ' (m) q (b) (l) ?_ ?_
  · rw [mul_comm]
    exact Nat.mul_le_mul
      (add_le_of_le_sub (le_of_ble_eq_true rfl)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).1.isLt))
        (add_le_of_le_sub hq0 (le_sub_one_of_lt
        (finProdFinEquiv.symm.1 t).2.isLt))
  · rw [← zsmul_eq_mul]; exact isIntegral_c₁γ K α' β' γ'

abbrev sys_coe : Fin (q * q) → (Fin (m * n)) → K := fun i j => by
  exact (a + b • β')^k * α' ^(a * l) * γ' ^(b * l)

abbrev sys_coe' : K := (a + b • β')^k * α' ^(a * l) * γ' ^(b * l)

variable (h2mq : 2 * m K ∣ q ^ 2)

include h2mq in
lemma q_eq_2sqrtmn : q^2 = 2*m*n := by
  refine Eq.symm (Nat.mul_div_cancel' h2mq)

include h2mq in
lemma q_eq_sqrtmn : q = Real.sqrt (2*m*n) := by
  norm_cast
  rw [ ← q_eq_2sqrtmn K q h2mq]
  simp only [Nat.cast_pow, Nat.cast_nonneg, Real.sqrt_sq]

include hq0 h2mq in
lemma card_mn_pos : 0 < m * n := by
  simp only [CanonicallyOrderedAdd.mul_pos]
  constructor
  exact Nat.zero_lt_succ (2 * h + 1)
  unfold n
  simp only [Nat.div_pos_iff, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
  constructor
  exact Nat.zero_lt_succ (2 * h + 1)
  apply Nat.le_of_dvd
  simp_all only [pow_pos]
  exact h2mq

include hq0 h2mq in
lemma one_le_n : 1 ≤ n := by {
  simp only [n]
  rw [Nat.one_le_div_iff]
  · apply Nat.le_of_dvd (Nat.pow_pos hq0) h2mq
  · exact Nat.zero_lt_succ (Nat.mul 2 (2 * h + 1) + 1)}

include hq0 h2mq in
lemma n_neq_0 : n ≠ 0 := Nat.ne_zero_of_lt (one_le_n K q hq0 h2mq)

include hq0 h2mq in
lemma qsqrt_leq_2m : 2 * m ≤ q^2 := by {
  apply Nat.le_of_dvd
  simp_all only [pow_pos]
  simp_all only}

abbrev c_coeffs := c₁^(n - 1) * c₁^(m * q) * c₁^(m * q)

macro_rules | `(c_coeffs) => `(c_coeffs K α' β' γ' q)

open Nat in include hq0 h2mq in omit hq0 h2mq in
lemma c₁IsInt0 :
  IsIntegral ℤ (c_coeffs0 • sys_coe' K α' β' γ' q u t) := by
  unfold c_coeffs0
  rw [triple_comm K (c₁^(k) : ℤ) (c₁^(a*l) : ℤ) (c₁^(b*l) : ℤ)
    (((a : ℕ) + b • β')^(k : ℕ)) (α' ^ (a * l)) (γ' ^ (b * (l)))]
  rw [mul_assoc]
  apply IsIntegral.mul
  simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow]
  rw [Eq.symm (mul_pow (↑(c₁ K α' β' γ')) (↑a + ↑b * β') k)]
  apply IsIntegral.pow
  rw [mul_add]
  apply IsIntegral.add
  · exact mod_cast IsIntegral.Cast K (c₁ K α' β' γ' * ↑a)
  · rw [← mul_assoc]
    nth_rw 2 [mul_comm]
    rw [mul_assoc]
    apply IsIntegral.mul
    · exact IsIntegral.Nat K b
    · rw [← zsmul_eq_mul]
      exact isIntegral_c₁β K α' β' γ'
  exact IsIntegral.mul (c1a0 K α' β' γ' q u t) (c1c0 K α' β' γ' q u t)

open Nat in include hq0 h2mq in
lemma c₁IsInt :
  IsIntegral ℤ (c_coeffs • sys_coe' K α' β' γ' q u t) := by
  rw [triple_comm K
    (c₁^(n - 1) : ℤ)
    (c₁^(m * q) : ℤ)
    (c₁^(m * q) : ℤ)
    (((a : ℕ) + b • β')^(k : ℕ))
    (α' ^ (a * l))
    (γ' ^ (b * l))]
  rw [mul_assoc]
  apply IsIntegral.mul
  · exact c₁b K α' β' γ' n (one_le_n K q hq0 h2mq)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).2.isLt)
      (le_add_left 1 (finProdFinEquiv.symm.1 t).1)
      (le_add_left 1 (finProdFinEquiv.symm.1 t).2)
  · exact IsIntegral.mul (c1a K α' β' γ' q u t hq0) (c1c K α' β' γ' q u t hq0)

lemma c₁neq0 : c₁ ≠ 0 := by
  unfold c₁
  have hcα := (c'_both α').2.1
  have hcβ := (c'_both β').2.1
  have hcγ := (c'_both γ').2.1
  unfold c'
  intros H
  simp_all only [ne_eq, mem_setOf_eq, abs_eq_zero, mul_eq_zero, or_self]

include hirr htriv habc in
lemma c₁αneq0 : c₁ • α' ≠ 0 := by {
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  constructor
  · rw [← ne_eq]
    exact c₁neq0 K α' β' γ'
  · rw [← ne_eq]
    exact (hneq0).1}

include hirr htriv habc in
lemma c₁cneq0 : c₁ • γ' ≠ 0 := by {
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  constructor
  · rw [← ne_eq]
    exact c₁neq0 K α' β' γ'
  · rw [← ne_eq]
    exact (hneq0).2.2}

lemma c_coeffs_neq_zero : c_coeffs ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (c₁neq0 K α' β' γ'))
  (pow_ne_zero _ (c₁neq0 K α' β' γ'))) (pow_ne_zero _ (c₁neq0 K α' β' γ'))

def A : Matrix (Fin (m K * n)) (Fin (q * q)) (𝓞 K) :=
  fun i j => RingOfIntegers.restrict _ (fun _ => (c₁IsInt0 K α' β' γ' q i j)) ℤ

include hirr htriv habc in
lemma α'_neq_zero : α' ^ (a * l) ≠ 0 :=
  pow_ne_zero _ (hneq0).1

include hirr htriv habc in
lemma γ'_neq_zero : γ' ^ (b * l) ≠ 0 :=
  pow_ne_zero _ (hneq0).2.2

open Complex

include htriv in omit hirr in
lemma log_zero_zero : log α ≠ 0 := by
  intro H
  have := congr_arg exp H
  rw [exp_log, exp_zero] at this
  apply htriv.2; exact this; exact htriv.1

include hirr habc in
lemma β'_neq_zero (y : ℕ) : (↑↑a + (↑b) • β') ^ y ≠ 0 := by
  apply pow_ne_zero
  intro H
  have H1 : β' = (↑↑a)/(-(↑b)) := by
    rw [eq_div_iff_mul_eq]
    rw [← eq_neg_iff_add_eq_zero] at H
    rw [mul_neg, mul_comm, H]
    have : (↑↑b) ≠ 0 := by
      simp only [ne_eq]
      unfold b
      simp only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply, Fin.coe_modNat,
        AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
    unfold b
    simp only [Equiv.toFun_as_coe, nsmul_eq_mul]
    intros H
    norm_cast at H
  apply hirr (↑a) (-(↑b))
  rw [habc.2.1, H1]
  simp only [map_div₀, map_natCast, map_neg, Int.cast_natCast, Int.cast_neg]

include hirr
lemma sum_b
   (i1 i2 j1 j2 : ℕ) (Heq : ¬i2 = j2) : i1 + i2 • β ≠ j1 + j2 • β := by {
      intros H
      have hb := hirr (i1 - j1) (j2 - i2)
      apply hb
      have h1 : i1 + i2 • β = j1 + j2 • β  ↔
        (i1 + i2 • β) - (j1 + j2 • β) = 0 := Iff.symm sub_eq_zero
      rw [h1] at H
      have h2 : ↑i1 + ↑i2 • β - (↑j1 + ↑j2 • β) = 0 ↔
         ↑i1 + i2 • β - ↑j1 - ↑j2 • β = 0 := by
          simp_all only [ne_eq, Int.cast_sub, nsmul_eq_mul,
            iff_true, sub_self, add_sub_cancel_left]
      rw [h2] at H
      have h3 : ↑i1 + i2 • β - ↑j1 - j2 • β = 0 ↔
          ↑i1 - ↑j1 + ↑i2 • β - ↑j2 • β = 0 := by
        ring_nf
      rw [h3] at H
      have hij2 : i2 ≠ j2 := by
        by_contra HC
        apply Heq
        exact HC
      have h4 : ↑i1 - ↑j1 + ↑i2 • β - ↑j2 • β = 0 ↔
        ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • β = 0 := by {
        rw [sub_eq_add_neg]
        simp only [nsmul_eq_mul]
        rw [← neg_mul, add_assoc, ← add_mul]
        simp only [smul_eq_mul]
        rw [← sub_eq_add_neg]}
      rw [h4] at H
      have h5 : ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • β =0 ↔
       ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • β) := by
        rw [add_eq_zero_iff_eq_neg]
      rw [h5] at H
      have h6 : ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • β) ↔
          ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • β := by
        refine Eq.congr_right ?_
        simp only [smul_eq_mul]
        rw [← neg_mul]
        simp only [neg_sub]
      rw [h6] at H
      have h7 : ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • β ↔
         (↑i1 - ↑j1) /(↑j2 - ↑i2 : ℂ) =  β := by
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

include σ habc hirr hq0 in
lemma b_sum_neq_0 : ↑q + q • β' ≠ 0 := by
  have := sum_b (σ β')
  have qneq0 : q ≠ 0 := Nat.ne_zero_of_lt hq0
  have hirr' : ∀ (i j : ℤ), σ β' ≠ σ (↑i / ↑j) := by {
    intros i j
    simp only [map_div₀, map_intCast, ne_eq]
    intros H
    rw [← habc.2.1] at H
    apply hirr i j
    exact H}
  simp only [map_div₀, map_intCast, ne_eq] at hirr'
  have := this hirr' q q 0 0 qneq0
  simp only [nsmul_eq_mul] at this
  simp only [CharP.cast_eq_zero, zero_mul, add_zero] at this
  intros H
  apply this
  apply_fun σ at H
  simp only [nsmul_eq_mul, map_add, map_natCast, map_mul, map_zero] at H
  exact H

include hirr htriv habc in
lemma one_leq_house_c₁β : 1 ≤ house ((c₁ • β')) := by
  apply house_gt_one_of_isIntegral
  exact isIntegral_c₁β K α' β' γ'
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  rw [← ne_eq, ne_eq]
  exact ⟨c₁neq0 K α' β' γ', (hneq0).2.1⟩

include hirr htriv habc in
lemma one_leq_house_c₁α : 1 ≤ house ((c₁ • α')) := by
  apply house_gt_one_of_isIntegral
  exact isIntegral_c₁α K α' β' γ'
  apply c₁αneq0 α β hirr htriv K σ α' β' γ' habc

include hirr htriv habc in
lemma house_bound_c₁α : house (c₁ • α') ^ (a * l) ≤ house (c₁ • α')^(m * q) := by
    apply house_alg_int_leq_pow
    · rw [mul_comm m q]; exact al_leq_mq K q u t
    · apply c₁αneq0 α β hirr htriv K σ α' β' γ' habc
    · exact isIntegral_c₁α K α' β' γ'

omit hirr in
lemma isInt_β_bound : IsIntegral ℤ (c₁ • (↑q + q • β')) := by {
  simp only [nsmul_eq_mul, smul_add, zsmul_eq_mul]
  apply IsIntegral.add
  · apply IsIntegral.mul (IsIntegral.Cast K c₁) (IsIntegral.Nat K q)
  · rw [← mul_assoc]; nth_rw 2 [mul_comm]; rw [mul_assoc]
    apply IsIntegral.mul (IsIntegral.Nat K q)
    rw [← zsmul_eq_mul]
    exact isIntegral_c₁β K α' β' γ'}

omit hirr in
lemma isInt_β_bound_low : IsIntegral ℤ (c₁ • (↑a + b • β')) := by {
  simp only [nsmul_eq_mul, smul_add, zsmul_eq_mul]
  apply IsIntegral.add
  · apply IsIntegral.mul (IsIntegral.Cast K c₁) (IsIntegral.Nat K a)
  · rw [← mul_assoc]; nth_rw 2 [mul_comm]; rw [mul_assoc]
    apply IsIntegral.mul (IsIntegral.Nat K b) ?_
    · rw [← zsmul_eq_mul]; exact isIntegral_c₁β K α' β' γ'}

include hirr habc σ hq0 in
lemma bound_c₁β : 1 ≤ house ((c₁ • (q + q • β'))) := by
  apply house_gt_one_of_isIntegral
  exact isInt_β_bound K α' β' γ' q
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  constructor
  · rw [← ne_eq]; exact c₁neq0 K α' β' γ'
  · rw [← ne_eq]; apply b_sum_neq_0 α β  hirr K σ α' β' γ' habc q hq0

include hirr htriv habc in
lemma one_leq_house_c₁γ : 1 ≤ house (c₁ • γ') := by
  apply house_gt_one_of_isIntegral
  exact isIntegral_c₁γ K α' β' γ'
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  constructor
  · rw [← ne_eq]; exact c₁neq0 K α' β' γ'
  · rw [← ne_eq]; exact (hneq0).2.2

include hirr htriv habc in
lemma sys_coe_ne_zero : sys_coe' K α' β' γ' q u t ≠ 0 := by
  unfold sys_coe'
  rw [mul_assoc]
  apply mul_ne_zero
    (mod_cast β'_neq_zero α β hirr K σ α' β' γ' habc q t k)
  · exact mul_ne_zero (mod_cast α'_neq_zero α β hirr htriv K σ α' β' γ' habc q u t)
      (mod_cast γ'_neq_zero α β hirr htriv K σ α' β' γ' habc q u t)

include htriv habc hq0 h2mq in
lemma hM_neq0 : A K α' β' γ' q ≠ 0 := by
  simp (config := { unfoldPartialApp := true }) only [A]
  rw [Ne, funext_iff]
  simp only [zsmul_eq_mul]
  simp only [RingOfIntegers.restrict]
  intros H
  let u : Fin (m * n) := ⟨0, card_mn_pos K q hq0 h2mq⟩
  specialize H u
  rw [funext_iff] at H
  let t : Fin (q * q) := ⟨0, (mul_pos hq0 hq0)⟩
  specialize H t
  simp only [Int.cast_mul, Int.cast_pow, zero_apply] at H
  injection H with H
  simp only [mul_eq_zero, pow_eq_zero_iff', Int.cast_eq_zero, ne_eq, not_or] at H
  rcases H
  · rename_i H1; rcases H1;
    rename_i H1 ; rcases H1 with ⟨H1, H11⟩
    · apply c₁neq0 K α' β' γ'
      assumption
    · rename_i H11; apply c₁neq0 K α' β' γ'
      exact H11.1
    rename_i h
    simp_all only [ne_eq, map_eq_zero, t, u]
    obtain ⟨left, right⟩ := htriv
    obtain ⟨left_1, right_1⟩ := habc
    obtain ⟨left_2, right_2⟩ := h
    obtain ⟨left_3, right_1⟩ := right_1
    subst left_3 left_1
    apply c₁neq0 K α' β' γ'
    exact h.1
    apply c₁neq0 K α' β' γ'
    exact h.1
  · rename_i H2;
    simp only [Nat.cast_add, Nat.cast_one, nsmul_eq_mul, AddLeftCancelMonoid.add_eq_zero,
      one_ne_zero, and_false, not_false_eq_true] at H2
    rcases H2 with ⟨H2, H22⟩
    · have := β'_neq_zero α β hirr K σ α' β' γ' habc q t (k K q u)
      apply this
      simp_all only [ne_eq, map_eq_zero, Equiv.toFun_as_coe, finProdFinEquiv_symm_apply,
        Fin.coe_divNat, Nat.zero_div,
        CharP.cast_eq_zero, zero_add, Fin.coe_modNat, Nat.zero_mod, one_mul,
        Nat.cast_add, Nat.cast_one, nsmul_eq_mul,
        not_false_eq_true, zero_pow, not_true_eq_false, t, u]
    · simp_all only [ne_eq, map_zero, not_true_eq_false,
        zero_ne_one, not_false_eq_true, and_true]
    rename_i H2;
    simp_all only [ne_eq, map_eq_zero, map_zero, cpow_eq_zero_iff, and_self, and_true]
    subst H2
    obtain ⟨left, right⟩ := htriv
    obtain ⟨left_1, right_1⟩ := habc
    obtain ⟨left_2, right_1⟩ := right_1
    obtain ⟨left_3, right_1⟩ := right_1
    subst left_1 left_2
    simp_all only [zero_ne_one, not_false_eq_true, map_eq_zero]

omit hirr in
lemma cardmn : Fintype.card (Fin (m * n)) = m * n := by
  simp only [Fintype.card_fin]

omit hirr in
lemma cardqq : card (Fin (q*q)) = q * q := by
  simp only [Fintype.card_fin]

omit hirr in
lemma hm : 0 < m := Nat.zero_lt_succ (2 * h + 1)

include hq0 h2mq in
omit hirr in
lemma h0m : 0 < m * n := mul_pos (hm K) (one_le_n K q hq0 h2mq)

include hq0 h2mq in
omit hirr in
lemma hmn : m * n < q*q := by
  rw [← Nat.mul_div_eq_iff_dvd] at h2mq
  rw [← pow_two q, ← mul_lt_mul_left (Nat.zero_lt_two)]
  rw [← mul_assoc, n, h2mq, lt_mul_iff_one_lt_left]
  · exact one_lt_two
  · exact Nat.pow_pos hq0

include h2mq in
omit hirr in
lemma sq_le_two_mn : q^2 ≤ 2 * m * n := by
  dsimp [n]
  refine Nat.le_sqrt'.mp ?_
  rw [← Nat.mul_div_eq_iff_dvd] at h2mq
  refine Nat.le_sqrt'.mpr ?_
  nth_rw 1 [← h2mq]

omit hirr in
include h2mq in
lemma q_le_two_mn : q ≤ 2 * m * n := by
  calc q ≤ q^2 := Nat.le_pow (Nat.zero_lt_two)
       _ ≤ _ := (sq_le_two_mn K q h2mq)

omit hirr in
lemma housec1_gt_zero : 0 ≤ house.c₁ K := by
  apply mul_nonneg
  rw [le_iff_eq_or_lt]
  right
  simp only [Nat.cast_pos]
  exact Module.finrank_pos
  apply mul_nonneg
  simp only [le_sup_iff, zero_le_one, true_or]
  apply (le_trans zero_le_one (le_max_left ..))

omit hirr in
lemma n_sub_1_le_n : (n) - 1 ≤ (n) := Nat.sub_le (n) 1

def c₂ : ℤ := (c₁ ^ (1 + 2*(m) * (↑2*m)))

macro_rules | `(c₂) => `(c₂ K α' β' γ')

omit h2mq hirr in
lemma one_leq_c₂ : 1 ≤ c₂ := by
  apply le_trans (Int.cast_one_le_of_pos (one_leq_c₁ K α' β' γ'))
  · nth_rw 1 [← pow_one (a:= c₁)]
    refine pow_le_pow_right₀ (one_leq_c₁ K α' β' γ')
      (Nat.le_add_right 1 (2 * m * (↑2*m)))

omit hirr in
lemma zero_leq_c₂ : 0 ≤ c₂ :=
  le_trans Int.one_nonneg (one_leq_c₂ K α' β' γ')

include h2mq in
omit hirr in
lemma c_coeffs_le_c₂_pow_n :
    ↑(c₁^ (n - 1) * c₁  ^ (m * q) * c₁ ^ (m * q)) ≤ c₂ ^n := by
  calc _ = ↑c₁ ^ ((n - 1) + (m * q) + (m * q)) := ?_
       _ ≤ c₂ ^n := ?_
  · rw [← pow_add, ← pow_add]
  · dsimp [c₂]; rw [← pow_mul]
    refine pow_le_pow_right₀ (mod_cast one_leq_c₁ K α' β' γ') ?_
    · rw [add_mul,one_mul]
      rw [add_assoc]; rw [Eq.symm (Nat.two_mul (m * q))]; rw [mul_assoc]
      calc _ ≤ n - 1 + 2 * (m * (2 * m * n)) := ?_
           _ ≤ n + 2 * m * (2 * m * n) := ?_
      · simp only [add_le_add_iff_left, Nat.ofNat_pos, mul_le_mul_left]
        apply mul_le_mul (le_refl _) (q_le_two_mn K q h2mq) (Nat.zero_le q) (Nat.zero_le m)
      · have : 2 * (m * (2 * m * n) ) = 2 * m * (2 * m * n) := by simp only [mul_assoc]
        rw [this]; clear this
        simp only [add_le_add_iff_right, tsub_le_iff_right,
          le_add_iff_nonneg_right, zero_le]

def c₃ : ℝ := c₂ * (1 + house (β'))* Real.sqrt (2*m) *
  (max 1 (((house (α') ^ (2*m^2)) * house (γ') ^(2*m^2))^2*m))
-- (|c₂ K α' β' γ'| * Nat.sqrt (2*m K)* (1 + house (β'))*
--     (house (α') ^ (2*m K^2)) * house (γ') ^(2*m K^2))

macro_rules | `(c₃) => `(c₃ K α' β' γ')

omit hirr in
lemma one_leq_c₃ : 1 ≤ c₃ := by
  dsimp [c₃]
  trans
  · have := one_leq_c₂ K α' β' γ'
    norm_cast at this
  · simp only [mul_assoc]
    norm_cast
    refine one_le_mul_of_one_le_of_one_le ?_ ?_
    · norm_cast;
      exact one_leq_c₂ K α' β' γ'
    · have h1 : 1 ≤ (1 + house β') := by
        simp only [le_add_iff_nonneg_right]; apply house_nonneg
      have h2 : 1 ≤ (max 1 ((house α' ^ (2 * m ^ 2) *
        house γ' ^ (2 * m ^ 2)) ^ 2 * ↑(m))) := by
         apply le_max_left
      have h3 : 1 ≤ ((Real.sqrt ((2*m)))) := by
         rw [Real.one_le_sqrt]
         have h1 := hm K
         calc 1 ≤ (m : ℝ) := by exact mod_cast h1
              _ ≤ 2*m := by {
                refine le_mul_of_one_le_left ?_ ?_
                simp only [Nat.cast_nonneg]
                exact one_le_two
                }
         --exact Nat.le_of_ble_eq_true rfl
      calc 1 ≤ (1 + house β') := h1
           _ ≤ (1 + house β') * (Real.sqrt ((2*m))) := by
            nth_rw 1 [← mul_one (a:= (1 + house β'))]
            apply mul_le_mul (Preorder.le_refl (1 + house β')) (h3)
              (zero_le_one' ℝ) (zero_le_one.trans h1)
      nth_rw 1 [← mul_one (a:= (1 + house β')*(Real.sqrt ((2*m))))]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      simp only [mul_assoc]
      apply mul_le_mul
      · apply Preorder.le_refl
      · apply mul_le_mul
        · apply Preorder.le_refl
        · simp only [le_sup_left]
        · simp only [zero_le_one]
        · exact Real.sqrt_nonneg (2 * ↑(m K))
      · simp only [Nat.ofNat_nonneg, Real.sqrt_mul, mul_one, Real.sqrt_pos, Nat.ofNat_pos,
        mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
      · refine Left.add_nonneg ?_ ?_
        · simp only [zero_le_one]
        · exact house_nonneg β'

include h2mq in
omit hirr in
lemma house_leq_house : house (c_coeffs K α' β' γ' q : K) ≤ house ((c₂ ^ n :ℤ) : K) := by
    rw [house_intCast]
    rw [house_intCast (x := c₂ ^ (n : ℕ))]
    simp only [Int.cast_abs, Int.cast_mul, Int.cast_pow]
    have := c_coeffs_le_c₂_pow_n K α' β' γ' q h2mq
    apply abs_le_abs
    · norm_cast
    · norm_cast
      calc _ ≤ (c₁ ^ (n - 1) * c₁ ^ (m K * q) * c₁ ^ (m K * q)) := by {
        simp only [neg_le_self_iff]
        apply mul_nonneg
        · apply mul_nonneg
          · apply pow_nonneg
            · exact IsAbsoluteValue.abv_nonneg' (c' K α' * c' K β' * c' K γ')
          · apply pow_nonneg
            · exact IsAbsoluteValue.abv_nonneg' (c' K α' * c' K β' * c' K γ')
        · apply pow_nonneg
          exact IsAbsoluteValue.abv_nonneg' (c' K α' * c' K β' * c' K γ')}
           _ ≤ c₂ ^ (n : ℕ) := this

omit hirr in
lemma c2_abs_val : ↑|c₂| ≤ c₂ :=
  abs_le_of_sq_le_sq (le_refl _) (zero_leq_c₂ K α' β' γ')

include hq0 h2mq in
omit hirr in
lemma c2_abs_val_pow : ↑|(c₂ ^ n : ℤ)| ≤ (c₂ ^ n : ℤ) := by
  simp only [abs_pow]
  refine (pow_le_pow_iff_left₀ (abs_nonneg _)
    (zero_leq_c₂ K α' β' γ')
    (n_neq_0 K q hq0 h2mq)).mpr (c2_abs_val K α' β' γ')

omit hirr in
lemma house_muls (s t : ℕ) (h: s ≤ t ) (ht: 0 ≤ t) :
  ( s • house β') ≤ (t • house β') := by {
  simp only [nsmul_eq_mul]
  apply mul_le_mul
  simp only [Nat.cast_le]
  apply h
  simp only [le_refl]
  exact house_nonneg β'
  exact Nat.cast_nonneg' t}

omit hirr in
lemma house_add_mul_leq : house (c₁ •(↑a + b • β')) ≤
     (|c₁| * |(q : ℤ)|) * (1 + house (β')) := by
  calc _ ≤ house (c₁ • (a q t : ℤ) + c₁ • (b q t : ℤ) • β') := ?_
       _ ≤ house (c₁ • ((a q t : ℤ) : K)) + house (c₁ • ((b q t : ℤ) • β')) := ?_
       _ ≤ house (c₁ : K) * house ((a q t : ℤ) : K) +
         house (c₁ : K) * house ((b q t : ℤ) • β') := ?_
       _ ≤  house (c₁ : K) * house ((a q t : ℤ) : K) +
         house (c₁ : K) * (house ((b q t : ℤ) : K) * house ( β')) := ?_
       _ = |c₁| * |(a q t : ℤ)| + |c₁| * |((b q t) : ℤ)| * house (β') := ?_
       _ ≤ |c₁| * |(q : ℤ)| + |c₁| * |((q) : ℤ)| * house (β') := ?_
       _ ≤ (|c₁| * |(q : ℤ)|) * (1 + house (β')) := ?_
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
        (Int.cast_nonneg.mpr (abs_nonneg (c₁ K α' β' γ')))) ?_
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
    simp only [Int.cast_abs, mul_one, le_refl]

omit hirr htriv habc hq0 h2mq
lemma c₃_pow :  c₃  ^ ↑(n K q : ℝ) = c₂^ ↑(n K q) * ((1 + house (β'))^ ↑(n K q)) *
   (((Real.sqrt ((2*m)))) ^ ↑(n K q)) *
  (max 1 (((house (α') ^ (2*m^2)) * house (γ') ^(2*m^2))^2*m))^ ↑(n K q) := by
    unfold c₃
    simp only [Real.rpow_natCast]
    rw [mul_pow, mul_pow, mul_pow]

include h2mq in
lemma q_eq_n_etc : ↑q ^ (n K q - 1) ≤ (Real.sqrt (2*m)^(n-1))* (Real.sqrt n)^(n-1) := by
  have : (Real.sqrt ((2*m)*(n))) = Real.sqrt (2*m)* Real.sqrt n := by {
    rw [Real.sqrt_mul]
    simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg]}
  rw [← mul_pow]
  refine pow_le_pow_left₀ ?_ ?_ ((n K q - 1))
  · simp only [Nat.cast_nonneg]
  · rw [← this]
    rw [Real.le_sqrt]
    · norm_cast; apply sq_le_two_mn K q h2mq
    · simp only [Nat.cast_nonneg]
    · norm_cast;simp only [zero_le]

lemma sq_n : (Real.sqrt n)^((n K q : ℝ)-1) = (n : ℝ) ^ (((n K q : ℝ) - 1)/2) := by stop
  nth_rw 1 [Real.sqrt_eq_rpow, ← Real.rpow_mul, mul_comm, mul_div]
  simp only [mul_one]; simp only [Nat.cast_nonneg]

include hirr htriv habc hq0 h2mq in
lemma hAkl : --∀ (k : Fin (m K * n)) (l : Fin (q * q)),
  house ((algebraMap (𝓞 K) K) ((A K α' β' γ' q) u t)) ≤
      (c₃ ^ (n : ℝ) * (n : ℝ) ^ (((n : ℝ) - 1) / 2))  := by { stop
    --simp (config := { unfoldPartialApp := true }) only [A, sys_coe]
    unfold A sys_coe'
    simp only [RingOfIntegers.restrict, RingOfIntegers.map_mk]
    --intros u t
    let a : ℕ := (finProdFinEquiv.symm.1 t).1 + 1
    let b : ℕ := (finProdFinEquiv.symm.1 t).2 + 1
    let k : ℕ := (finProdFinEquiv.symm.1 u).2
    let l : ℕ := (finProdFinEquiv.symm.1 u).1 + 1

    calc _ = house
            (c₁ ^ k • (↑a + b • β') ^ k * c₁ ^ (a * l) • α' ^ (a * l) *
             c₁ ^ (b * l) • γ' ^ (b * l))  := ?_

         _ ≤ house (c₁ ^ k • (↑a + b • β') ^ k) *
             house (c₁ ^ (a * l) • α' ^ (a * l)) *
             house (c₁ ^ (b * l) • γ' ^ (b * l)) := ?_

         _ ≤ house (c₁ • (↑a + b • β')) ^ (k) *
             house (c₁ • α') ^ (a * l) *
             house (c₁ • γ') ^ (b * l) := ?_

         _ ≤ house (c₁ • (↑a + b • β')) ^ (n - 1) *
             house (c₁ • α') ^ (m * q) *
             house (c₁ • γ') ^ (m * q) := ?_

         _ ≤ (|c₁| * (|(q : ℤ)| * (1 + house (β')))) ^ (n - 1) *
             (|c₁| * house (α')) ^ (m * (2 * (m * n))) *
             (|c₁| * house (γ')) ^ (m * (2 * (m * n))) := ?_

         _= |c₁ ^ (n - 1)| • (↑|↑q| * (1 + house (β'))) ^ (n - 1) *
            |c₁ ^ (m * (2 * (m K * n K q)))| • house α' ^ (m * (2 * (m * n))) *
            |c₁ ^ (m * (2 * (m K * n K q)))| • house γ' ^ (m * (2 * (m * n))) := ?_

         _ = ↑|c₁| ^ ((n - 1) + (2 * m * (2 * (m * n))))
            * (↑|↑q| ^ (n - 1) * (1 + house β') ^ (n - 1) *
               house α' ^ (m * (2 * (m K * n K q))) * house γ' ^ (m K * (2 * (m K * n K q)))) := ?_

         _ ≤  ↑(c₂)^n * (↑|↑q| ^ (n - 1) * (1 + house β') ^ (n - 1) *
               house α' ^ (m * (2 * (m K * n K q))) * house γ' ^ (m * (2 * (m K * n K q)))) := ?_

         _ ≤ (c₃)^(n : ℝ) * ((Real.sqrt n)^((n  : ℝ)-1)) := ?_

         _ ≤ (c₃ ^ (n: ℝ) * (n : ℝ) ^ (((n  : ℝ) - 1) / 2)) := ?_

    · rw [triple_comm K (c₁^k : ℤ) (c₁^(a * l): ℤ) (c₁^(b * l) : ℤ)
        (((a : ℕ) + b • β')^(k : ℕ)) (α' ^ (a * l)) (γ' ^ (b * l))]
    · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow]
      trans
      apply house_mul_le
      · rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right
        · trans; rw [mul_assoc] ; apply house_mul_le
        · apply house_nonneg
    · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow]
      rw [← mul_pow]; rw [← mul_pow]; rw [← mul_pow]
      apply mul_le_mul
      · apply mul_le_mul (house_pow_le _ _) (house_pow_le _ _) (house_nonneg _)
          (by apply pow_nonneg (house_nonneg _))
      · apply house_pow_le
      · apply house_nonneg
      · apply mul_nonneg
        · apply pow_nonneg; apply house_nonneg
        · apply pow_nonneg; apply house_nonneg
    · apply mul_le_mul
      · apply mul_le_mul
        · apply house_alg_int_leq_pow
          · refine (Nat.le_sub_iff_add_le' ?_).mpr ?_
            · apply one_le_n K q hq0 h2mq
            · rw [add_comm]
              exact bar' (finProdFinEquiv.symm.toFun u).2
          · intros H
            rw [zsmul_eq_mul] at H
            simp only [mul_eq_zero, Int.cast_eq_zero] at H
            cases' H with h1 h2
            · apply c₁_neq_zero K α' β' γ'; exact h1
            · apply β'_neq_zero α β hirr K σ α' β' γ' habc q t 1
              rw [pow_one]; exact h2
          · apply isInt_β_bound_low
        · apply house_alg_int_leq_pow
          · rw [mul_comm m q]
            apply al_leq_mq K q u t
          · exact c₁αneq0 α β hirr htriv K σ α' β' γ' habc
          · exact isIntegral_c₁α K α' β' γ'
        · apply pow_nonneg; apply house_nonneg
        · apply pow_nonneg; apply house_nonneg
      · apply house_alg_int_leq_pow
        · rw [mul_comm m q]
          apply bl_leq_mq K q u t
        · exact c₁cneq0 α β hirr htriv K σ α' β' γ' habc
        · exact isIntegral_c₁γ K α' β' γ'
      · apply pow_nonneg; apply house_nonneg
      · apply mul_nonneg
        · apply pow_nonneg; apply house_nonneg
        · apply pow_nonneg; apply house_nonneg
    · apply mul_le_mul
      · apply mul_le_mul
        · refine pow_le_pow_left₀ ?_ ?_ (n - 1)
          · apply house_nonneg
          · rw [← mul_assoc]
            apply house_add_mul_leq
        · calc _ ≤ house (c₁ • α') ^ (m K * (2 * (m K * n K q))) := ?_
               _ ≤ (↑|c₁| * house α') ^ (m K * (2 * (m K * n K q))) := ?_
          · refine
            house_alg_int_leq_pow (c₁ K α' β' γ' • α') (m K * q) (m K * (2 * (m K * n K q))) ?_ ?_
              ?_
            · apply mul_le_mul
              · apply Preorder.le_refl
              · exact (by { have H := q_le_two_mn K q h2mq; rw [mul_assoc] at H; exact H })
              · simp only [zero_le]
              · simp only [zero_le]
            · exact c₁αneq0 α β hirr htriv K σ α' β' γ' habc
            · exact isIntegral_c₁α K α' β' γ'
          --· sorry
          · refine pow_le_pow_left₀ ?_ ?_ (m K * (2 * (m K * n K q)))
            · apply house_nonneg
            · calc _ ≤ house (c₁ : K)  * house (α') := ?_
                   _ ≤ _ := ?_
              · simp only [zsmul_eq_mul]
                apply house_mul_le
              · simp only [house_intCast, Int.cast_abs, le_refl]
        · apply pow_nonneg; apply house_nonneg
        · apply pow_nonneg;
          · apply mul_nonneg
            · simp only [Int.cast_abs, abs_nonneg]
            · apply mul_nonneg
              · simp only [Nat.abs_cast, Int.cast_natCast, Nat.cast_nonneg]
              · refine Left.add_nonneg ?_ ?_
                · simp only [zero_le_one]
                · exact house_nonneg β'
      · calc _ ≤ house (c₁ • γ') ^ (m K * (2 * (m K * n K q))) := ?_
             _ ≤ (↑|c₁| * house γ') ^ (m K * (2 * (m K * n K q))) := ?_
        · refine
            house_alg_int_leq_pow (c₁ K α' β' γ' • γ') (m K * q)
              (m K * (2 * (m K * n K q))) ?_ ?_ ?_
          · apply mul_le_mul
            · apply Preorder.le_refl
            · exact (by { have H := q_le_two_mn K q h2mq; rw [mul_assoc] at H; exact H })
            · simp only [zero_le]
            · simp only [zero_le]
          · exact c₁cneq0 α β hirr htriv K σ α' β' γ' habc
          · exact isIntegral_c₁γ K α' β' γ'
        refine pow_le_pow_left₀ ?_ ?_ (m K * (2 * (m K * n K q)))
        · apply house_nonneg
        · calc _ ≤ house (c₁ : K)  * house (γ') := ?_
               _ ≤ _ := ?_
          · simp only [zsmul_eq_mul]
            apply house_mul_le
          · simp only [house_intCast, Int.cast_abs, le_refl]
      · apply pow_nonneg; apply house_nonneg
      · apply mul_nonneg
        apply pow_nonneg;
        · apply mul_nonneg
          · simp only [Int.cast_abs, abs_nonneg]
          · apply mul_nonneg
            · simp only [Nat.abs_cast, Int.cast_natCast, Nat.cast_nonneg]
            · refine Left.add_nonneg ?_ ?_
              · simp only [zero_le_one]
              · exact house_nonneg β'
        · apply pow_nonneg;
          · apply mul_nonneg
            · simp only [Int.cast_abs, abs_nonneg]
            · apply house_nonneg
    · rw [zsmul_eq_mul]
      rw [zsmul_eq_mul]
      rw [zsmul_eq_mul]
      --rw [mul_add, mul_one]
      rw [mul_pow]
      rw [mul_pow]
      rw [mul_pow]
      rw [mul_pow]
      rw [mul_pow]
      rw [abs_pow]
      rw [abs_pow]
      congr
      simp only [Int.cast_abs, Int.cast_pow]
      simp only [Nat.abs_cast, Int.cast_natCast]
      simp only [Int.cast_abs, Int.cast_pow]
      simp only [Int.cast_abs, Int.cast_pow]
    · have := triple_comm ℝ
       |(c₁^(n - 1) : ℤ)|
       |(c₁^(m * (2 * (m K * n K q))) : ℤ)|
       |(c₁^(m * (2 * (m K * n K q))) : ℤ)|
       ((↑|↑q| * (1 + house (β')))^(n-1))
       ((house α') ^ (m * (2 * (m K * n K q))))
       ((house γ') ^ (m * (2 * (m K * n K q))))
      rw [← this]; clear this
      rw [abs_pow]
      rw [abs_pow]
      rw [← pow_add]
      rw [← pow_add]
      rw [zsmul_eq_mul]
      congr
      simp only [Int.cast_pow, Int.cast_abs]
      rw [add_assoc]
      congr
      ring
      rw [mul_pow]
    · unfold c₂
      rw [pow_mul]
      apply mul_le_mul
      · simp only [Int.cast_abs]
        calc _ ≤  ↑(c₁)^ (n - 1 + 2 * m * (2 * (m * n K q))) := ?_
             _ ≤ ((c₁ : ℝ) ^ (1 + 2 * m * (2 * m))) ^ n :=?_
        · refine (pow_le_pow_iff_left₀ ?_ ?_ ?_).mpr ?_
          · simp only [abs_nonneg]
          · simp only [Int.cast_nonneg]
            exact IsAbsoluteValue.abv_nonneg' (c' K α' * c' K β' * c' K γ')
          · simp only [ne_eq, Nat.add_eq_zero, mul_eq_zero,
              OfNat.ofNat_ne_zero, false_or, not_and, not_or]
            intros HN
            · constructor
              · sorry
              · simp_all only [ne_eq, map_eq_zero]
                obtain ⟨left, right⟩ := htriv
                obtain ⟨left_1, right_1⟩ := habc
                obtain ⟨left_2, right_1⟩ := right_1
                subst left_2 left_1
                sorry
          · apply abs_le_of_sq_le_sq (le_refl _) (sorry)
        · rw [← pow_mul]
          refine pow_le_pow_right₀ ?_ ?_
          · sorry
          · rw [add_mul]
            simp only [one_mul]
            refine Nat.add_le_add ?_ ?_
            · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
            · simp only [mul_assoc]
              apply Preorder.le_refl
        · simp only [Int.cast_pow]
          rfl
      · apply Preorder.le_refl
      · sorry
      · sorry
    · rw [c₃_pow K α' β' γ' q]
      simp only [mul_assoc]
      apply mul_le_mul
      · rfl
      · calc _ ≤ (Real.sqrt (2*m)^(n-1))* (Real.sqrt n)^(n-1)
                * ((1 + house β') ^ (n K q - 1) *
                  (house α' ^ (m K * (2 * (m K * n K q))) *
                    house γ' ^ (m K * (2 * (m K * n K q))))) := ?_

             _ ≤ (Real.sqrt (2*m)^(n-1))
                * ((1 + house β') ^ (n K q - 1) * (house α' ^ (m K * (2 * (m K * n K q)))
                * house γ' ^ (m K * (2 * (m K * n K q))))) * (Real.sqrt n)^((n  : ℝ)-1) := ?_

             _ ≤ √(2 * ↑(m K)) ^ (n K q - 1) *
                ((1 + house β') ^ (n K q - 1) * (house α' ^ (m K * 2 * m * n)
                * house γ' ^ (m K * 2 * m * n))) * (Real.sqrt n)^((n  : ℝ)-1) := ?_

             _ ≤ √(2 * ↑(m K)) ^ (n) *
               ((1 + house β') ^ (n) * (house α' ^ (m K * 2 * m)) ^ n
                * (house γ' ^ (m K * 2 * m)) ^ n) *  (Real.sqrt n)^((n  : ℝ)-1) := ?_

        · apply mul_le_mul
          · simp only [Nat.abs_cast]
            apply q_eq_n_etc K q h2mq
          · apply Preorder.le_refl
          · apply mul_nonneg
            · sorry
            · sorry
          · sorry
        · sorry
        · simp only [mul_assoc]
          apply mul_le_mul
          · apply Preorder.le_refl
          · apply mul_le_mul
            · apply Preorder.le_refl
            · apply mul_le_mul
              · sorry
              · sorry
              · sorry
              · sorry
            · sorry
            · sorry
          · sorry
          · sorry
        · simp only [mul_assoc]
          apply mul_le_mul
          · sorry--easy
          · apply mul_le_mul
            · sorry --easy
            · apply mul_le_mul
              · rw [← pow_mul]
                simp only [mul_assoc]
                apply Preorder.le_refl
              · rw [← pow_mul]
                simp only [mul_assoc]
                apply Preorder.le_refl
              · sorry
              · sorry
            · sorry
            · apply pow_nonneg; sorry
          · sorry
          · sorry
        · nth_rw 2 [← mul_assoc]
          rw [mul_comm  ((1 + house β') ^ n K q) (((Real.sqrt ((2*m)))) ^ n K q)]
          simp only [mul_assoc]
          apply mul_le_mul
          · refine pow_le_pow_left₀ ?_ ?_ n
            · sorry
            · apply Preorder.le_refl
          · apply mul_le_mul
            · apply Preorder.le_refl
            · simp only  [← mul_assoc]
              apply mul_le_mul
              · rw [← mul_pow]
                refine pow_le_pow_left₀ ?_ ?_ n
                · sorry
                · have : ((m K * 2) * m K) = ( 2 * m^2) := sorry
                  rw [this]; clear this
                  calc _ ≤ ((house α' ^ (2 * m K ^ 2) * house γ' ^ (2 * m K ^ 2)) ^ 2
                    * ↑(m K)) := ?_
                       _ ≤ max 1 ((house α' ^ (2 * m K ^ 2) * house γ' ^ (2 * m K ^ 2))
                        ^ 2 * ↑(m K)) := ?_
                  · sorry
                  · sorry
              · apply Preorder.le_refl
              · sorry
              · sorry
            · sorry
            · sorry
          · sorry
          · sorry
      · sorry
      · sorry
    · rw [le_iff_eq_or_lt]
      left
      rw [← sq_n]
}


def applylemma82 := NumberField.house.exists_ne_zero_int_vec_house_le K
  (A K α' β' γ' q)
  (hM_neq0 α β hirr htriv K σ α' β' γ' habc q hq0 h2mq)
  (h0m K q hq0 h2mq)
  (hmn K q hq0 h2mq)
  (cardqq q)
  (fun u t => hAkl α β hirr htriv K σ α' β' γ' habc q u t hq0 h2mq)
  (cardmn K q)

def η : Fin (q * q) → 𝓞 K :=
  (applylemma82 α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq).choose

macro_rules | `(η) => `(η α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)

abbrev c₄ := (max 1 ((house.c₁ K)* house.c₁ K * 2 * m )) * c₃

macro_rules | `(c₄) => `(c₄ K hd α' β' γ')

omit hirr in
lemma one_leq_c₄ : 1 ≤ c₄ := by
  dsimp [c₄]
  refine one_le_mul_of_one_le_of_one_le ?_ (one_leq_c₃ K α' β' γ')
  · exact le_max_left 1 (house.c₁ K * house.c₁ K * 2 * ↑(m K))

omit hirr in
lemma q_sq_real: (q * q : ℝ) = q^2 := by {
  norm_cast; exact Eq.symm (pow_two ↑q)}

omit hirr in
include h2mq in
lemma q_eq_2sqrtmn_real : (q^2 : ℝ) = 2*m*n := by
  norm_cast; refine Eq.symm (Nat.mul_div_cancel' h2mq)

omit hirr in
include h2mq hq0 in
lemma fracmqn : (↑(m K : ℝ) * ↑(n K q : ℝ) /
  (2 * ↑(m K : ℝ) * ↑(n K q : ℝ) - (m K * (n K q : ℝ))) : ℝ) = 1 := by
    have : 2 * ↑(m K : ℝ) * ↑(n K q : ℝ) - ↑(m K : ℝ) * ↑(n K q : ℝ)=
      ↑(m K : ℝ) * ↑(n K q : ℝ ) := by ring
    rw [this]
    norm_cast
    refine (div_eq_one_iff_eq ?_).mpr rfl
    simp only [Nat.cast_mul, ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
    constructor
    · rw [← ne_eq]; exact Ne.symm (Nat.zero_ne_add_one (2 * h K + 1))
    · rw [← ne_eq]; refine n_neq_0 K q hq0 h2mq

omit hirr in
include hq0 h2mq in
lemma hfrac : ↑(n K q : ℝ) * ↑(n K q : ℝ) ^ ((↑(n K q : ℝ) - 1) / 2) =
  ↑(n K q : ℝ) ^ ((↑(n K q : ℝ) + 1) / 2) := by {
    nth_rw 1 [← Real.rpow_one (x := ↑(n K q))]
    rw [← Real.rpow_add]
    · congr; ring
    · norm_cast
      have := one_le_n K q hq0 h2mq
      linarith}

open NumberField.house in
include hq0 h2mq hd hirr htriv habc in
lemma fromlemma82_bound :
  house (algebraMap (𝓞 K) K ((η) t)) ≤ c₄ ^ (n : ℝ) * ((n:ℝ) ^ (((n:ℝ)+ 1)/2)) := by
  unfold _root_.η
  calc _ ≤  house.c₁ K * (house.c₁ K * ↑(q * q) *
    (c₃ ^ (n : ℝ) * (n : ℝ) ^ (((n  : ℝ) - 1) / 2))) ^
      ((m K * n : ℝ) / (↑(q * q : ℝ) - ↑(m K * n ))) := ?_
       _ = (house.c₁ K * (house.c₁ K * 2 * m *
    (c₃ ^ (n  : ℝ)) * ((n  : ℝ) * (n : ℝ) ^ (((n  : ℝ) - 1) / 2)))) := ?_
       _ ≤ c₄ ^ (n  : ℝ) * ((n:ℝ) ^ (((n:ℝ) + 1)/2) : ℝ) := ?_
  · exact mod_cast ((applylemma82 α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq).choose_spec).2.2 t
  · rw [← pow_two q]
    rw [q_sq_real]
    rw [q_eq_2sqrtmn K q h2mq]
    rw [q_eq_2sqrtmn_real K q h2mq]
    have fracmqn := fracmqn K q hq0 h2mq
    nth_rw 2 [← Nat.cast_mul] at fracmqn
    rw [fracmqn]; clear fracmqn
    rw [Real.rpow_one]
    rw [hfrac K q hq0 h2mq]
    simp only [mul_eq_mul_left_iff]
    left
    rw [mul_assoc]; rw [mul_assoc]; rw [mul_assoc]; rw [mul_assoc]; rw [mul_assoc];
    refine (mul_right_inj' ?_).mpr ?_
    · have : 1 ≤ house.c₁ K := by {
      unfold house.c₁
      have : 0 < ↑(Module.finrank ℚ K) := Module.finrank_pos
      refine one_le_mul_of_one_le_of_one_le ?_ ?_
      · exact Nat.one_le_cast.mpr this
      · unfold house.c₂
        refine one_le_mul_of_one_le_of_one_le ?_ ?_
        apply le_max_left
        apply le_max_left}
      refine Ne.symm (ne_of_lt ?_)
      linarith
    · have : ↑(2 * (m K * n K q)) * (c₃ K α' β' γ' ^
        ↑(n K q : ℝ) * ↑(n K q) ^ ((↑(n K q: ℝ) - 1) / 2))=
        ↑(2 * m K) * (c₃ K α' β' γ' ^ ↑(n K q : ℝ) *
        (n K q * ↑(n K q) ^ ((↑(n K q : ℝ) - 1) / 2))) := by {
          nth_rw 4 [← mul_assoc]
          nth_rw 8 [← mul_comm]
          simp only [Nat.cast_mul, Nat.cast_ofNat, Real.rpow_natCast]
          simp only [mul_assoc]}
      rw [this]
      rw [hfrac K q hq0 h2mq]
      rw [← mul_assoc]
      rw [← mul_assoc]
      rw [← mul_assoc]
      simp only [Nat.cast_mul, Nat.cast_ofNat, Real.rpow_natCast]
  · rw [hfrac K q hq0 h2mq]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · unfold c₄
      rw [Real.mul_rpow]
      · refine mul_le_mul_of_nonneg_right ?_ ?_
        · trans
          · apply le_max_right 1 ((house.c₁ K * house.c₁ K * 2 * ↑(m K)))
          · nth_rw 1 [← Real.rpow_one (x := max 1 (house.c₁ K * house.c₁ K * 2 * ↑(m K)))]
            apply Real.rpow_le_rpow_of_exponent_le
            apply le_max_left
            · simp only [Nat.one_le_cast]
              exact one_le_n K q hq0 h2mq
        · simp only [Real.rpow_natCast]
          apply pow_nonneg
          · apply (le_trans zero_le_one (one_leq_c₃ ..))
      · apply (le_trans zero_le_one (le_max_left ..))
      · apply (le_trans zero_le_one (one_leq_c₃ ..))
    · apply Real.rpow_nonneg
      simp only [Nat.cast_nonneg]

omit h2mq hirr in
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

def ρ : ℂ := (a + (b • β)) * Complex.log α

include htriv hirr in
lemma hdist : ∀ (i j : Fin (q * q)), i ≠ j → ρ α β q i ≠ ρ α β q j := by
  intros i j hij
  rw [ne_eq, decompose_ij] at hij
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
      have hb := hirr (i1 - j1) (j2 - i2)
      rw [← ne_eq]
      change i1 + i2 • β ≠ j1 + j2 • β
      intros H
      have hb := hirr (i1 - j1) (j2 - i2)
      apply hb
      have h1 : i1 + i2 • β = j1 + j2 • β  ↔
        (i1 + i2 • β) - (j1 + j2 • β) = 0 := Iff.symm sub_eq_zero
      rw [h1] at H
      have h2 : ↑i1 + ↑i2 • β - (↑j1 + ↑j2 • β) = 0 ↔
         ↑i1 + i2 • β - ↑j1 - ↑j2 • β = 0 := by {
          simp_all only [ne_eq, Equiv.toFun_as_coe,
          finProdFinEquiv_symm_apply,
            nsmul_eq_mul, iff_true, sub_self,
            add_sub_cancel_left]}
      rw [h2] at H
      have h3 : ↑i1 + i2 • β - ↑j1 - j2 • β = 0 ↔
          ↑i1 - ↑j1 + ↑i2 • β - ↑j2 • β = 0 := by {
        ring_nf}
      rw [h3] at H
      have hij2 : i2 ≠ j2 := by {
        by_contra HC
        apply Heq
        refine Fin.eq_of_val_eq ?_
        exact Nat.succ_inj.mp HC
        }
      have h4 : ↑i1 - ↑j1 + ↑i2 • β - ↑j2 • β = 0 ↔
        ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • β = 0 := by {
        rw [sub_eq_add_neg]
        simp only [nsmul_eq_mul]
        rw [← neg_mul, add_assoc, ← add_mul]
        simp only [smul_eq_mul]
        rw [← sub_eq_add_neg]}
      rw [h4] at H
      have h5 : ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • β =0 ↔
       ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • β) := by {
        rw [add_eq_zero_iff_eq_neg]}
      rw [h5] at H
      have h6 : ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • β) ↔
          ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • β := by {
        refine Eq.congr_right ?_
        simp only [smul_eq_mul]
        rw [← neg_mul]
        simp only [neg_sub]}
      rw [h6] at H
      have h7 : ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • β ↔
         (↑i1 - ↑j1) /(↑j2 - ↑i2 : ℂ) =  β := by {
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
  · exact log_zero_zero α htriv

def V := vandermonde (fun t => ρ α β q t)

include hirr htriv in
lemma vandermonde_det_ne_zero : det (V α β q) ≠ 0 := by
  by_contra H
  rw [V, det_vandermonde_eq_zero_iff] at H
  rcases H with ⟨i, j, ⟨hij, hij'⟩⟩
  apply hdist α β hirr htriv q i j
  intros H'
  · apply hij' H'
  · exact hij

open Differentiable Complex

def R : ℂ → ℂ := fun x => ∑ t, (canonicalEmbedding K) ((algebraMap (𝓞 K) K) ((η) t)) σ
  * exp (ρ α β q t * x)

macro_rules | `(R) => `(R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)

def iteratedDeriv_of_R (k' : ℕ) : deriv^[k'] (fun x => (R) x) =
    fun x => ∑ t, (σ ((η) t)) * exp (ρ α β q t * x) * (ρ α β q t)^k' := by
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
    rw [cexp_mul, mul_assoc, (pow_succ' (ρ α β q t) k')]
    · rw [mul_comm, mul_assoc, mul_eq_mul_left_iff,
         Eq.symm (pow_succ' (ρ α β q t) k')]; left; rfl
    · intros i hi
      apply mul ?_ (differentiable_const (ρ α β q i ^ k'))
      · apply mul <| differentiable_const _
        apply Differentiable.cexp
        apply mul (differentiable_const _) (differentiable_fun_id)

include hirr htriv habc hq0 h2mq in
lemma iteratedDeriv_of_R_is_zero (hR : (R) = 0) :
  ∀ z k', deriv^[k'] (fun z => (R) z) z = 0 := by
intros z k'
rw [hR]
simp only [Pi.zero_apply]
rw [← iteratedDeriv_eq_iterate]
rw [iteratedDeriv]
simp_all only [iteratedFDeriv_zero_fun, Pi.zero_apply,
  ContinuousMultilinearMap.zero_apply]

include hirr htriv habc hq0 h2mq in
lemma vecMul_of_R_zero (hR : (R) = 0) : (V α β q).vecMul (fun t => σ ((η) t)) = 0 := by
  unfold V
  rw [funext_iff]
  intros t
  simp only [Pi.zero_apply]
  have : ∀ k', deriv^[k'] (fun x => (R) x) = 0 := by {
    intros k'
    rw [funext_iff]
    intros x
    simp only [Pi.zero_apply]
    apply iteratedDeriv_of_R_is_zero
    exact hR}
  simp only at this
  have deriv_eq : ∀ k', deriv^[k'] (fun x => ((R)) x) = fun x => ∑ t, (σ ((η) t)) *
    exp (ρ α β q t * x) * (ρ α β q t)^k' := by {
      intros k'
      exact iteratedDeriv_of_R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq k'}
  have deriv_eq_0 : ∀ k', deriv^[k'] (fun x => ((R)) x) 0 = 0 := by {
    intros k; simp_all only [Pi.zero_apply]}
  rw [← deriv_eq_0 t]
  rw [deriv_eq]
  simp only [mul_zero, exp_zero, mul_one]
  unfold vecMul dotProduct vandermonde
  simp only [of_apply]

include hirr htriv habc hq0 h2mq in
lemma ηvec_eq_zero (hVecMulEq0 : (V α β q).vecMul (fun t => σ ((η) t )) = 0) :
    (fun t => σ ((η) t )) = 0 := by {
  apply eq_zero_of_vecMul_eq_zero
    (vandermonde_det_ne_zero α β hirr htriv q) hVecMulEq0}

include α β hirr htriv K σ α' β' γ' habc hq0 h2mq in
lemma hbound_sigma : (η) ≠ 0 := by
  intros H
  have := (applylemma82 α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq).choose_spec.1
  apply this
  unfold η at H
  simp only [ne_eq] at H
  simp only [ne_eq]
  simp only [Nat.cast_mul, Real.rpow_natCast]
  simp_all only [Nat.cast_mul, Real.rpow_natCast, ne_eq, not_true_eq_false]

include α β hirr htriv σ α' β' γ' habc q hq0 h2mq in
lemma R_nonzero : (R) ≠ 0 := by
  by_contra H
  have HC := (ηvec_eq_zero α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)
    (vecMul_of_R_zero α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq H)
  simp only at HC
  apply hbound_sigma α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
  rw [funext_iff] at HC
  simp only [Pi.zero_apply, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff] at HC
  unfold η at *
  ext t
  specialize HC t
  simp only [ne_eq, Pi.zero_apply, map_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  exact HC

variable (hγ : γ = α ^ β)

include htriv habc in
omit hirr in
lemma sys_coe_bar :
  Complex.exp (ρ α β q t * l) * (ρ α β q t ^ (k : ℕ) *
  Complex.log α ^ (-(k) : ℤ)) = σ (sys_coe' K α' β' γ' q u t) := by {
  calc
      _ = cexp (ρ α β q t * l) *
          (((↑a + ↑b • β) * Complex.log α) ^ (k : ℕ) * Complex.log α ^ (-↑↑k : ℤ)) := ?_

      _ = cexp (ρ α β q t * (l)) * ( (↑a + ↑b • β)^ (k : ℕ) *
          (Complex.log α) ^ (k : ℕ) * Complex.log α ^ (-↑↑k : ℤ)) := ?_

      _ = cexp (ρ α β q t * l) * ( (↑a + ↑b • β)^ ((k) : ℕ) *
          ((Complex.log α) ^ (k : ℕ) * Complex.log α ^ (-↑↑k : ℤ))) := ?_

      _ = cexp (ρ α β q t * l) * ( (↑a + ↑b • β)^ (k : ℕ)) := ?_

      _ = σ (sys_coe' K α' β' γ' q u t) := ?_

  · nth_rw 2 [ρ]
  · rw [mul_pow]
  · rw [mul_assoc]
  ·  have  : (Complex.log α ^ (k) * Complex.log α ^ (-(k) : ℤ)) = 1 := by {
       simp only [zpow_neg, zpow_natCast]
       refine Complex.mul_inv_cancel ?_
       by_contra H
       apply log_zero_zero α htriv
       simp only [pow_eq_zero_iff', ne_eq] at H
       apply H.1}
     rw [this]
     rw [mul_one]
  · unfold sys_coe'
    have h1 : σ ((↑a+ ↑b • β') ^ ((k) : ℕ)) =
      (↑a + ↑b * β) ^ ((k) : ℕ) := by {
      simp only [nsmul_eq_mul, map_pow, map_add, map_natCast, map_mul]
      simp_all only [ne_eq, map_eq_zero, Equiv.toFun_as_coe, finProdFinEquiv_symm_apply,
        Fin.coe_divNat, Nat.cast_add, Nat.cast_one, Fin.coe_modNat, a, b]}
    rw [map_mul]
    rw [map_mul]
    unfold a b k at *
    rw [h1]; clear h1
    rw [mul_comm]
    rw [mul_assoc]
    simp only [nsmul_eq_mul, map_pow,
      mul_eq_mul_left_iff, pow_eq_zero_iff', ne_eq]
    left
    have : σ α' ^ (a * (l)) * σ γ' ^ (b * (l)) =
    α ^ (a * (l)) * (σ γ')^ (b * (l)) := by {rw [habc.1]}
    unfold a b l at *
    rw [this]
    have : σ γ' = α^β := by {rw [habc.2.2]}
    rw [this]
    rw [ρ]
    have : α ^ ((a * l)) * α ^ (↑(b * l) * β) =
      α ^ ((a * l) + (↑(b * l) * β)) := by {
        rw [cpow_add]
        · rw [cpow_nat_mul]
          simp only [mul_eq_mul_right_iff, pow_eq_zero_iff',
            cpow_eq_zero_iff, ne_eq, mul_eq_zero,
            not_or]
          left
          rw [cpow_nat_mul]
          simp only [cpow_natCast]
          exact pow_mul' α a (l)
        · exact htriv.1}
    rw [cpow_nat_mul] at this
    unfold a b l at *
    rw [this]; clear this
    rw [cpow_def_of_ne_zero]
    have : Complex.log α * (↑a * ↑(l) + ↑(b * (l)) * β) =
       (↑a + b • β) *
        Complex.log α * ↑(l) := by {
      nth_rw 4 [mul_comm]
      have : ( ↑((l) * b) * β) = ( ↑((b * β) * (l))) := by {
        simp only [Nat.cast_mul, mul_rotate (↑(l)) (↑b) β]}
      rw [this]
      have : (↑a * ↑(l) + ((b * β) * (l))) =
        ((↑a  + (b * β)) * (l)) :=
        Eq.symm (RightDistribClass.right_distrib
          (↑a) (↑b * β) ↑(l))
      rw [this]
      simp only [nsmul_eq_mul]
      nth_rw 1 [← mul_assoc]
      nth_rw 1 [mul_comm]
      nth_rw 1 [mul_comm]
      nth_rw 5 [mul_comm]}
    unfold a b l at *
    rw [this]
    · exact htriv.1}

include hirr htriv habc hq0 h2mq in
lemma sys_coe_foo : --
 (log α)^(-(k K q u) : ℤ) * deriv^[(k K q u)]
   (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) (l K q u) =
  ∑ t, σ ↑((η) t) * σ (sys_coe' K α' β' γ' q u t) := by
  rw [iteratedDeriv_of_R, mul_sum, Finset.sum_congr rfl]
  intros t ht
  rw [mul_assoc, mul_comm, mul_assoc]
  simp only [mul_eq_mul_left_iff, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  left
  have := sys_coe_bar α β htriv K σ α' β' γ' habc q u t
  unfold l at this
  rw [mul_assoc]
  unfold l
  exact this

lemma l_plus_one_lt_m : ∀ (l' : Fin (m K)), ↑l' + 1 < m K := sorry

include hirr htriv habc hq0 h2mq
lemma deriv_sum_blah : ∀ (l' : Fin (m K)) (k' : Fin (n)),
   σ (c_coeffs K α' β' γ' q) *
   ((log α)^ (-k' : ℤ) * deriv^[k']
      (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) (l' + 1)) =
      σ ((A K α' β' γ' q *ᵥ (η)) (finProdFinEquiv ⟨l',k'⟩)) := by {
    intros l' k'
    have := sys_coe_foo α β hirr htriv K σ hd α' β' γ' habc q (finProdFinEquiv ⟨⟨l'+1,
       l_plus_one_lt_m K l'⟩ ,k'⟩) hq0 h2mq
    simp only [Int.cast_mul, Int.cast_pow, map_mul, map_pow, map_intCast, zpow_neg, zpow_natCast]
    sorry
    --have : --wrong k in derin
    --  Complex.log α ^ (-↑(k K q (finProdFinEquiv (⟨↑l' + 1, ⋯⟩, k')) : ℤ)) *
    -- deriv^[k K q (finProdFinEquiv (⟨↑l' + 1, ⋯⟩, k'))]
    --    (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)
    --   ↑(l K q (finProdFinEquiv (⟨↑l' + 1, ⋯⟩, k')))=
    --  ((Complex.log α ^ ↑(k':ℤ))⁻¹ *
    --   deriv^[↑k'] (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) (↑↑l' + 1)) := sorry


    -- unfold mulVec
    -- unfold dotProduct
    -- simp only [← map_mul, ← map_sum]
    -- congr
    -- simp only [map_sum, map_mul]

    -- rw [mul_sum]
    -- rw [Finset.sum_congr rfl]
    -- intros x hx
    -- simp (config := { unfoldPartialApp := true }) only [A, sys_coe]
    -- simp only [RingOfIntegers.restrict, zsmul_eq_mul, RingOfIntegers.map_mk]
    -- nth_rw 2 [mul_assoc]
    -- rw [mul_eq_mul_left_iff]
    -- rw [mul_comm]
    -- simp only [mul_eq_mul_right_iff, FaithfulSMul.algebraMap_eq_zero_iff]
    -- left
    -- simp only
    }

include α β σ hq0 h2mq hd hirr htriv σ α' β' γ' habc h2mq  in
lemma iteratedDeriv_vanishes :
  ∀ (l' : Fin (m K)) (k' : Fin (n)), k' < n →
  deriv^[k'] (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) (l' + 1) = 0 := by
  intros l' k' hl
  have h1 := deriv_sum_blah α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l' k'
  have : (σ (c_coeffs K α' β' γ' q) * (log α)^(-k' : ℤ)) * deriv^[k']
    (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) (l' + 1) =
    (σ (c_coeffs K α' β' γ' q) * (log α)^(-k' : ℤ)) * 0 → deriv^[k']
    (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) (l' + 1) = 0 := by {
      apply mul_left_cancel₀
      by_contra H
      simp only [Int.cast_mul, Int.cast_pow, map_mul, map_pow, map_intCast, zpow_neg,
          zpow_natCast, mul_eq_zero, pow_eq_zero_iff', Int.cast_eq_zero, ne_eq, not_or,
          or_self_right, inv_eq_zero] at H
      cases' H with h1 h2
      · cases' h1 with h1 h3
        · apply c₁neq0 K α' β' γ'; exact h1.1
        · apply c₁neq0 K α' β' γ'; exact h3.1
      · apply (log_zero_zero α htriv); exact h2.1}
  rw [this]
  rw [mul_zero]
  rw [mul_assoc]
  rw [h1]
  simp only [map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  have hMt0 := (applylemma82 α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq).choose_spec.2.1
  rw [funext_iff] at hMt0
  unfold η
  simp only at this
  simp_all only [Fin.is_lt, Int.cast_mul, Int.cast_pow, map_mul, map_pow,
  map_intCast, zpow_neg, zpow_natCast, mul_zero, mul_eq_zero, pow_eq_zero_iff',
    Int.cast_eq_zero, ne_eq, not_or, or_self_right, inv_eq_zero, Nat.cast_mul,
  Real.rpow_natCast, Pi.zero_apply]

lemma R_analyt_at_point (point : ℕ) :
 AnalyticAt ℂ (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) point := by
  apply Differentiable.analyticAt
  unfold R
  apply Differentiable.fun_sum
  intros i hk
  apply Differentiable.fun_mul
  · apply differentiable_const
  · apply (differentiable_exp.comp ((differentiable_const _).mul differentiable_fun_id))

lemma analyticEverywhere : ∀ (z : ℂ),
  AnalyticAt ℂ (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) z := by
  intros z
  unfold R
  apply Differentiable.analyticAt
  apply Differentiable.fun_sum
  intros i hk
  exact
  (differentiable_const _).mul
    (differentiable_exp.comp ((differentiable_const _).mul differentiable_fun_id))

include htriv habc in
lemma order_neq_top : ∀ (l' : Fin (m K)),
  analyticOrderAt (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) (l' + 1) ≠ ⊤ := by {
  intros l' H
  rw [← zero_iff_order_inf] at H
  apply R_nonzero α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
  rw [funext_iff]
  intros z
  exact H z
  intros z
  exact analyticEverywhere α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq z}

include htriv habc in
lemma order_neq_top_min_one : ∀ z : ℂ,
  analyticOrderAt (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) z ≠ ⊤ := by {
  intros l' H
  rw [← zero_iff_order_inf] at H
  apply R_nonzero α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
  rw [funext_iff]
  intros z
  exact H z
  intros z
  exact analyticEverywhere α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq z}

lemma Rorder_exists (z : ℂ) :
  ∃ r, (analyticOrderAt (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) z) = some r := by
  have : (analyticOrderAt (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) z) ≠ ⊤ := by
   exact order_neq_top_min_one α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq z
  revert this
  cases'(analyticOrderAt (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) z) with r
  · intro this_1; simp_all only [ne_eq, not_true_eq_false]
  · intros hr; use r; rfl

def R_order (z : ℂ) : ℕ :=
  (Rorder_exists α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq z).choose

def R_order_prop {z : ℂ} :=
  (Rorder_exists α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq z).choose_spec

lemma R_order_eq (z) :
  (analyticOrderAt (R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) z)
    = R_order α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq z :=
    (Rorder_exists α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq z).choose_spec

omit hirr  htriv habc [NumberField K] hq0 h2mq in
lemma exists_mem_finset_min' {γ : Type _} {β : Type _} [LinearOrder γ]
    [DecidableEq γ] (s : Finset β) (f : β → γ) (Hs : s.Nonempty) :
  ∃ x ∈ s, ∃ y, y = f x ∧ ∀ x' ∈ s, y ≤ f x' := by
  let y := s.image f |>.min' (image_nonempty.mpr Hs)
  have : y ∈ Finset.image f s := min'_mem (image f s) (image_nonempty.mpr Hs)
  rw [Finset.mem_image] at this
  obtain ⟨x, hx, hy⟩ := this
  use x, hx, y
  constructor
  · exact id (Eq.symm hy)
  · intros x' hx'
    apply Finset.min'_le (image f s) (f x') (mem_image_of_mem _ hx')

lemma exists_min_order_at :
  let s : Finset (Fin (m K)) := Finset.univ
  ∃ l₀ ∈ s, (∃ y, (analyticOrderAt R l₀) = y ∧
   (∀ (l' : Fin (m K)), l' ∈ s → y ≤ (analyticOrderAt R l'))) := by
  intros s
  have Hs : s.Nonempty := by {
     refine univ_nonempty_iff.mpr ?_
     refine Fin.pos_iff_nonempty.mp ?_
     exact hm K}
  let f : (Fin (m K)) → ℕ∞ := fun x => (analyticOrderAt R x)
  have := exists_mem_finset_min' s f Hs
  obtain ⟨x, hx, ⟨r, h1, h2⟩⟩ := this
  use x
  constructor
  · exact hx
  · constructor
    · constructor
      · exact id (Eq.symm h1)
      · intros x hx
        subst h1
        simp_all only [Finset.mem_univ, forall_const, s, f]

def l₀ : Fin (m K) :=
  (exists_min_order_at α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq).choose

macro_rules | `(l₀) => `(l₀ α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)

def l₀_prop :=
  (exists_min_order_at α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq).choose_spec.2

def r' := (l₀_prop α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq).choose

macro_rules | `(r') => `(r' α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)

def r'_prop :
  let s : Finset (Fin (m K)) := Finset.univ
  analyticOrderAt (R) ↑↑(l₀) = r' ∧ ∀ l' ∈ s, r' ≤ analyticOrderAt (R) ↑↑l' :=
  let l₀_prop := l₀_prop α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
  (l₀_prop).choose_spec

lemma r_exists :
  ∃ r, r' = some r := by
  have := (r'_prop α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq).1
  have H := order_neq_top_min_one α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l₀
  have : r' ≠ ⊤ := by rw [this] at H; exact H
  revert this
  cases' r' with r
  · intro this_1; simp_all only [ne_eq, not_true_eq_false]
  · intros hr; use r; rfl

include α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq in
def r := (r_exists α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq).choose

macro_rules | `(r) => `(r α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)

def r_spec : r' = ↑r :=
  (r_exists α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq).choose_spec

def r_prop :
  let s : Finset (Fin (m K)) := Finset.univ
  analyticOrderAt R ↑↑l₀ = r ∧ ∀ l' ∈ s, r ≤ analyticOrderAt R ↑↑l' := by
  intros s
  rw [← (r_spec α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)]
  apply r'_prop

lemma r_div_q_geq_0 : 0 ≤ (r) / q := by {simp_all only [zero_le]}

lemma exists_nonzero_iteratedFDeriv : deriv^[r] R l₀ ≠ 0 := by {
  have Hrprop := (r_prop α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq).1
  obtain ⟨l₀, y, r, h1, h2⟩ :=
    (exists_min_order_at α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)
  have hA1 := R_analyt_at_point α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l₀
  exact ((iterated_deriv_eq_zero_if_order_eq_n l₀ r R hA1) Hrprop).2}

lemma foo' (l' : Fin (m K)) :
  (∀ k', k' < n → deriv^[k'] R (l' + 1) = 0) → n ≤ analyticOrderAt R (l' + 1) := by
  intros H
  apply iterated_deriv_eq_zero_imp_n_leq_order
  · exact analyticEverywhere α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq (l' + 1)
  · apply order_neq_top α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
  exact H

lemma order_geq_n : ∀ l' : Fin (m K), n ≤ analyticOrderAt R (l' + 1) := by
  intros l'
  apply foo'
  intros k'' hk
  let k' : Fin (n) := ⟨k'',hk⟩
  have := iteratedDeriv_vanishes α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l' k'
  have H : k'' = ↑k' := rfl
  rw [H]
  apply this hk

--yes, because deriv's are zero
lemma rneq0 : (r) ≠ 0 := by stop
  have := iteratedDeriv_vanishes α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l₀
  have Hrprop := (r_prop α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq).1
  have := (r_prop α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq).2
  have := foo' α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
  have H := order_geq_n α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l₀
  have HN := this l₀
  intros HH
  sorry
  --rw [AnalyticAt.analyticOrderAt_eq_zero] at H

lemma r_qeq_0 : 0 < (r) := by
  refine Nat.zero_lt_of_ne_zero ?_
  exact rneq0 α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq

def cρ : ℤ := abs (c₁ ^ ((r)) * c₁^(2*m K * q))

macro_rules | `(cρ) => `(cρ α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)

abbrev sys_coe_r : K := (a + b • β')^r * α' ^(a * l₀) * γ' ^(b * l₀)

macro_rules | `(sys_coe_r) =>`(sys_coe_r α β hirr htriv K σ hd α' β' γ' habc q t hq0 h2mq)

include u t in
lemma sys_coe'_ne_zero : sys_coe_r ≠ 0 := by
  unfold sys_coe_r
  intros H
  simp only [mul_eq_zero, pow_eq_zero_iff'] at H
  cases' H with H1 H2
  · cases' H1 with H1 H2
    · rcases H1 with ⟨h1, h2⟩
      have := β'_neq_zero α β hirr K σ α' β' γ' habc q t r
      apply this
      rw [h1]
      simp only [pow_eq_zero_iff', ne_eq, true_and]
      exact h2
    · apply α'_neq_zero α β hirr htriv K σ α' β' γ' habc q u t
      simp only [pow_eq_zero_iff', ne_eq]
      simp_all only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply,
        Fin.coe_divNat, ne_eq,
        mul_eq_zero, Nat.add_eq_zero, Nat.div_eq_zero_iff,
        one_ne_zero, and_false, false_or,
        or_self, not_false_eq_true, and_self]
  · apply γ'_neq_zero α β hirr htriv K σ α' β' γ' habc q u t
    simp only [pow_eq_zero_iff', ne_eq]
    simp_all only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply, Fin.coe_modNat, ne_eq,
      mul_eq_zero, Nat.add_eq_zero, one_ne_zero, and_false, false_or, Fin.coe_divNat,
      Nat.div_eq_zero_iff, or_self, not_false_eq_true, and_self]

def ρᵣ : ℂ := (log α)^(-r : ℤ) * deriv^[r] (R) (l₀)

macro_rules | `(ρᵣ) => `(ρᵣ α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)

include htriv habc in
lemma sys_coe'_bar :
  exp (ρ α β q t * l₀) * ρ α β q t ^ (r : ℕ) * log α ^ (-r : ℤ) = σ (sys_coe_r) := by {
    nth_rw 2 [ρ]
    rw [mul_pow, mul_assoc, mul_assoc]
    have : (Complex.log α ^ (r : ℕ) * Complex.log α ^ (-r : ℤ)) = 1 := by {
      simp only [zpow_neg, zpow_natCast]
      refine Complex.mul_inv_cancel ?_
      by_contra H
      apply log_zero_zero α htriv
      simp only [pow_eq_zero_iff', ne_eq] at H
      apply H.1}
    rw [this]
    rw [mul_one]
    unfold sys_coe_r
    rw [mul_comm]
    change _ = σ ((↑a + b • β') ^ (r : ℕ) * (α' ^ (a * (l₀))) * (γ' ^ (b * (l₀))))
    rw [map_mul]
    rw [map_mul]
    nth_rw 1 [mul_assoc]
    have : σ ((↑a + b • β') ^ (r)) = (↑a + ↑b * β) ^ (r) := by {
      simp only [nsmul_eq_mul, map_pow, map_add, map_natCast, map_mul]
      simp_all only [a, b]}
    rw [this]
    rw [map_pow]
    rw [map_pow]
    have : ((↑(finProdFinEquiv.symm.toFun t).1 + 1 : ℕ) +
        ((finProdFinEquiv.symm.toFun t).2 + 1 : ℕ) • β) ^
      (r) * cexp (ρ α β q t * (l₀)) = (↑a + ↑b * β)^(r) * cexp (ρ α β q t * (l₀)) := by {
      simp_all only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply,
        Fin.coe_modNat, zpow_neg,
        Fin.coe_divNat, Nat.cast_add, Nat.cast_one, nsmul_eq_mul,
        map_pow, map_add, map_natCast,
        map_one, map_mul, b, a]}
    rw [this]
    simp only [mul_eq_mul_left_iff, pow_eq_zero_iff']
    left
    rw [ρ]
    have : cexp ((↑(↑(finProdFinEquiv.symm.toFun t).1 + 1 : ℕ)
      + (↑(finProdFinEquiv.symm.toFun t).2 + 1 : ℕ ) • β) *
        Complex.log α * ↑(l₀)) = cexp ((↑a + ↑b • β) * Complex.log α * (l₀)) := by {
          simp_all only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply,
          Fin.coe_modNat, zpow_neg,
            Fin.coe_divNat, Nat.cast_add, Nat.cast_one,
            nsmul_eq_mul, map_pow, map_add, map_natCast,
            map_one, map_mul, b, a]}
    rw [this]
    have : σ α' ^ (a * (l₀)) * σ γ' ^ (b * (l₀)) = α ^ (a * (l₀ )) * (σ γ')^ (b * (l₀)) := by {
      simp_all only [zpow_neg, zpow_natCast, Equiv.toFun_as_coe,
        finProdFinEquiv_symm_apply, Fin.coe_divNat,
        Nat.cast_add, Nat.cast_one, Fin.coe_modNat, nsmul_eq_mul,
        map_pow, map_add, map_natCast, map_one, map_mul, a,
        b]}
    rw [this]
    have : σ γ' = α^β := by {rw [habc.2.2]}
    rw [this]
    have : Complex.exp (Complex.log α) = α := by {
      apply Complex.exp_log
      exact htriv.1}
    rw [← cpow_nat_mul]
    have : cexp ((↑a + b • β) *
      Complex.log α * ↑(l₀)) = α ^ (a * (l₀ )) * α ^ (↑(b * (l₀ )) * β) ↔
      cexp ((↑a + b • β) *
      Complex.log α * ↑(l₀ )) = α ^ ((a * (l₀ )) + (↑(b * (l₀)) * β)) := by {
        rw [cpow_add]
        simp only [nsmul_eq_mul, Nat.cast_mul]
        norm_cast
        exact htriv.1}
    rw [this]
    rw [cpow_def_of_ne_zero]
    have : Complex.log α * (↑a * ↑(l₀ ) + ↑(b * (l₀)) * β) =
        (↑a + b • β) * Complex.log α * ↑(l₀) := by {
      nth_rw 4 [mul_comm]
      have : ( ↑((l₀) * b) * β) = ( ↑((b * β) * (l₀))) := by {
          simp only [Nat.cast_mul]
          exact mul_rotate (↑(l₀)) (↑b) β}
      rw [this]
      have : (↑a * ↑(l₀) + ((b * β) * (l₀))) = ((↑a  + (b * β)) * (l₀)) :=
        Eq.symm (RightDistribClass.right_distrib (↑a) (↑b * β) ↑(l₀))
      rw [this, mul_comm, mul_assoc]
      nth_rw 3 [mul_comm]
      rw [← mul_assoc, nsmul_eq_mul]}
    rw [this]
    exact htriv.1}

lemma sys_coe'_foo :
 (log α)^(-r: ℤ) * deriv^[r] R (l₀) = ∑ t, σ ↑((η) t) * σ (sys_coe_r) := by {
  rw [iteratedDeriv_of_R, mul_sum, Finset.sum_congr rfl]
  intros t ht
  rw [mul_assoc, mul_comm, mul_assoc]
  unfold η
  simp only [mul_eq_mul_left_iff, map_eq_zero,
    FaithfulSMul.algebraMap_eq_zero_iff]
  left
  have := sys_coe'_bar α β hirr htriv K σ hd α' β' γ' habc q t hq0 h2mq
  rw [this]
  sorry
  }


def deriv_R_k_eval_at_l0' :
  deriv^[r] R l₀ = ∑ t, σ ((η) t) * cexp (ρ α β q t * l₀) * ρ α β q t ^ r := by
  rw [iteratedDeriv_of_R]

def rho := ∑ t, ((η) t) * ((sys_coe_r))

macro_rules | `(ρ) => `(rho α β hirr htriv K σ hd α' β' γ' habc q t hq0 h2mq)

def rho_eq_ρᵣ : σ ρ = ρᵣ := by
  unfold rho ρᵣ
  rw [sys_coe'_foo]
  simp only [map_sum, map_mul, nsmul_eq_mul, map_pow, map_add, map_natCast]
  · rfl

lemma ρᵣ_nonzero : ρᵣ ≠ 0 := by
  unfold ρᵣ
  simp only [zpow_neg, zpow_natCast, mul_eq_zero, inv_eq_zero,
    pow_eq_zero_iff', ne_eq, not_or, not_and, Decidable.not_not]
  constructor
  · intros hlog
    by_contra H
    apply log_zero_zero α htriv
    exact hlog
  · have := exists_nonzero_iteratedFDeriv
      α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
    simp_all only [ne_eq, not_false_eq_true]

lemma cρ_ne_zero : cρ α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq ≠ 0 := by
  unfold cρ
  apply abs_ne_zero.mpr <| mul_ne_zero _ _
  all_goals { apply pow_ne_zero _ (c₁neq0 K α' β' γ') }

-- IsIntegral ℤ (c₁ ^ (m K * q) • γ' ^ (b * l₀))
-- (c₁ ^ (m K * q - (b * l₀)) =
   --(c₁ ^ (b * l₀))
omit hirr  htriv
  habc
  hq0
  h2mq in
lemma c₁bρ (a b n : ℕ) : 1 ≤ n → k K q u ≤ n - 1 → 1 ≤ (a : ℕ) → 1 ≤ (b : ℕ) →
  IsIntegral ℤ (c₁^(n - 1) • (a + b • β') ^ (k K q u)) := by  {
  intros hn hkn ha hb
  have : c₁^(n - 1) = c₁ ^ (n - 1 - (k K q u))
    * c₁^(k K q u) := by {
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
  exact isIntegral_c₁β K α' β' γ'}

lemma ρ_is_int :
  IsIntegral ℤ (cρ α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq • ρ) := by
  unfold rho
  unfold cρ
  unfold sys_coe_r
  have : c₁ ^ (2 * m * q) = c₁ ^ (m K * q) * c₁ ^ (m K * q) := by {
      rw [← pow_add]; ring}
  rw [this]
  cases' abs_choice (c₁ ^ r * c₁ ^ (m K * q) * c₁ ^ (m K * q)) with H1 H2
  · rw [← mul_assoc, H1]
    rw [Finset.smul_sum]
    apply IsIntegral.sum
    intros x hx
    rw [zsmul_eq_mul]
    nth_rw 1 [mul_comm]
    rw [mul_assoc]
    apply IsIntegral.mul
    · exact RingOfIntegers.isIntegral_coe
       ((η) x)
    · rw [mul_comm]
      rw [← zsmul_eq_mul]
      have := triple_comm K
        (c₁^r : ℤ)
        (c₁^(m K * q) : ℤ)
        (c₁^(m K * q) : ℤ)
        (((a q t : ℕ) + b • β')^r)
        (α' ^ (a * l₀))
        (γ' ^ (b* l₀))
      have : IsIntegral ℤ
        (((c₁ ^ r * c₁ ^ (m K * q) * c₁ ^ (m K * q)) •
       let r := _root_.r α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq;
       let l₀ := l₀
      (a + b • β') ^ r * α' ^ (a * l₀ : ℕ) * γ' ^ (b * l₀))) =
         IsIntegral ℤ ((c₁ ^ r • (a + b • β') ^ r
           * c₁ ^ (m * q) • α' ^ (a * l₀) *
        c₁ ^ (m * q) • γ' ^ (b * l₀))) := by {
          rw [← this]
          }
      simp only at this
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
              have := isIntegral_c₁β K α' β' γ'
              simp only [zsmul_eq_mul] at this
              exact this
        · apply c₁ac K α' β' γ' α' (m K) q a l₀ ?_ ?_
          · rw [mul_comm]
            apply Nat.mul_le_mul
            · simp only [Fin.is_le']
            · exact bar' (finProdFinEquiv.symm.toFun t).1
          · rw [← zsmul_eq_mul]; exact isIntegral_c₁α K α' β' γ'
      · have : c₁ ^ (m K * q - (b * l₀)) *
           (c₁ ^ (b * l₀)) =
              (c₁ ^ ((m K * q))) := by
          rw [← pow_add,Nat.sub_add_cancel]
          nth_rw 1 [mul_comm]
          apply mul_le_mul
          · simp only [Fin.is_le']
          · change b ≤ q
            have : ↑(finProdFinEquiv.symm.toFun x).2 ≤ q := Fin.is_le'
            exact bar' (finProdFinEquiv.symm.toFun t).2
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
          · rw [← zsmul_eq_mul]; exact isIntegral_c₁γ K α' β' γ'
  · rw [Finset.smul_sum]
    apply IsIntegral.sum
    intros x hx
    rw [← mul_assoc, H2]
    rw [zsmul_eq_mul]
    nth_rw 1 [mul_comm]
    rw [mul_assoc]
    apply IsIntegral.mul
    · exact RingOfIntegers.isIntegral_coe ((η) x)
    · rw [mul_comm]
      --let l₀ : ℕ := (finProdFinEquiv.symm.1 u).1 + 1
      rw [← zsmul_eq_mul]
      have := triple_comm K
        (c₁^r : ℤ)
        (c₁^(m K * q) : ℤ)
        (c₁^(m K * q) : ℤ)
        (((a : ℕ) + b • β')^r)
        (α' ^ (a * ( (l₀))))
        (γ' ^ (b * ( (l₀))))
      have : IsIntegral ℤ
       (-(c₁ ^ r * c₁ ^ (m * q) * c₁ ^ (m * q)) •
       let a : ℕ := (finProdFinEquiv.symm.toFun x).1 + 1;
       let b : ℕ := (finProdFinEquiv.symm.toFun x).2 + 1;
       let r := _root_.r α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq;
      (↑a + b • β') ^ r * α' ^ (a * l₀) * γ' ^ (b * l₀)) =
         IsIntegral ℤ ((c₁ ^ r • (↑a + b • β') ^ r
           * c₁ ^ (m * q) • α' ^ (a * l₀) * c₁ ^ (m K * q) • γ' ^ (b * l₀))) := by
          rw [← this]
          rw [neg_smul]
          rw [IsIntegral.neg_iff]
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
             exact isIntegral_c₁β K α' β' γ'
        · apply c₁ac K α' β' γ' α' (m K) q a l₀ ?_ ?_
          · rw [mul_comm]
            apply Nat.mul_le_mul
            simp only [Fin.is_le']
            exact bar' (finProdFinEquiv.symm.toFun t).1
          · rw [← zsmul_eq_mul]; exact isIntegral_c₁α K α' β' γ'
      · have : c₁ ^ (m * q - (b * l₀)) * (c₁ ^ (b * l₀)) = (c₁ ^ ((m * q))) := by
          rw [← pow_add, Nat.sub_add_cancel]
          nth_rw 1 [mul_comm]
          apply mul_le_mul
          · exact Fin.is_le'
          · exact bar' (finProdFinEquiv.symm.toFun t).2
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
          · rw [← zsmul_eq_mul]; exact isIntegral_c₁γ K α' β' γ'

def c1ρ : 𝓞 K := RingOfIntegers.restrict _
  (fun _ => (ρ_is_int α β hirr htriv K σ hd α' β' γ' habc q t hq0 h2mq)) ℤ

macro_rules | `(c1ρ) => `(c1ρ α β hirr htriv K σ hd α' β' γ' habc q t hq0 h2mq)

lemma eq5zero : 1 ≤ norm (Algebra.norm ℚ ((algebraMap (𝓞 K) K) c1ρ)) := by {
  unfold c1ρ RingOfIntegers.restrict
  simp only [zsmul_eq_mul]
  simp only [RingOfIntegers.map_mk, map_mul, norm_mul]

  have := @Algebra.norm_algebraMap ℚ _ K _ _ (cρ)
  simp only [map_intCast] at this
  rw [this]
  simp only [norm_pow, Int.norm_cast_rat, ge_iff_le]

  have norm_neq_0 : ‖(Algebra.norm ℚ) (ρ)‖ ≠ 0 := by {
    rw [norm_ne_zero_iff, Algebra.norm_ne_zero_iff]
    intros H
    apply_fun σ at H
    rw [rho_eq_ρᵣ] at H
    simp only [map_zero] at H
    apply ρᵣ_nonzero α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
    exact H}

  have h0 : 0 < ‖cρ‖ := by {
    rw [norm_pos_iff]
    have := cρ_ne_zero α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
    unfold cρ at this
    exact this}

  have h1 : 1 ≤ ‖cρ‖ ^ Module.finrank ℚ K := by {
      rw [one_le_pow_iff_of_nonneg]
      · rw [Int.norm_eq_abs]
        rw [Int.norm_eq_abs] at h0
        unfold cρ
        simp only [Int.cast_abs, Int.cast_mul, Int.cast_pow, abs_abs]
        rw [← pow_add]
        simp only [abs_pow]
        have : 1 ≤ |↑(c₁ K α' β' γ')| := by {
          rw [le_abs']
          right
          exact one_leq_c₁ K α' β' γ'
        }
        refine one_le_pow₀ ?_
        exact mod_cast this
      · apply norm_nonneg
      · have : 0 < Module.finrank ℚ K  := Module.finrank_pos
        simp_all only [ne_eq, norm_eq_zero, Algebra.norm_eq_zero_iff,
          norm_pos_iff]
        intro a
        simp_all only [lt_self_iff_false]}

  have h2 : 0 < ‖(Algebra.norm ℚ) (ρᵣ)‖ := by {
    rw [norm_pos_iff]
    rw [← rho_eq_ρᵣ]
    have Hnorm_neq_0 := norm_neq_0
    have := ρᵣ_nonzero α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
    rw [← rho_eq_ρᵣ] at this
    simp only [ne_eq, norm_eq_zero, Algebra.norm_eq_zero_iff] at Hnorm_neq_0
    intros H
    sorry
    exact t
    exact t}

  calc 1 ≤ ‖cρ‖ ^ Module.finrank ℚ K := h1
       _ ≤ ‖cρ‖ ^ Module.finrank ℚ K * ‖(Algebra.norm ℚ) (ρ)‖ := ?_
  · nth_rw 1 [← mul_one (‖cρ‖ ^ Module.finrank ℚ K)]
    rw [mul_le_mul_left]
    · sorry
    · rw [le_iff_eq_or_lt] at h1
      sorry
      -- cases' h1 with h1 h1
      -- · rw [← h1]
      --   simp only [zero_lt_one]
      -- · trans
      --   · apply zero_lt_one
      --   · exact h1
          }
def c₅ : ℝ := (↑(c₁ K α' β' γ') ^ (((↑(h K) * (↑(r) + 2 * ↑(m K) * ↑q)) : ℤ)))

macro_rules | `(c₅) => `(c₅ α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)

include u t in
lemma eq5 : c₅ ^ (- r : ℤ) < norm (Algebra.norm ℚ ρ) := by

  simp only [zpow_neg, zpow_natCast]

  have h1 : 1 ≤ ‖(cρ) ^ Module.finrank ℚ K‖ * ‖(Algebra.norm ℚ) (ρ)‖ := by { stop

  have := eq5zero α β hirr htriv K σ hd α' β' γ' habc q t hq0 h2mq
  unfold c1ρ at this
  unfold RingOfIntegers.restrict at this
  simp only [zsmul_eq_mul] at this
  simp only [RingOfIntegers.map_mk, map_mul, norm_mul] at this

  have H := @Algebra.norm_algebraMap ℚ _ K _ _ (cρ)
  simp only [map_intCast] at H
  simp only [norm_pow, ge_iff_le]
  rw [H] at this
  simp only [norm_pow, Int.norm_cast_rat] at this
  exact this}

  have h2 : ‖(cρ) ^ Module.finrank ℚ K‖⁻¹ ≤ norm (Algebra.norm ℚ ρ) := by {
    have : 0 < ‖ (cρ)^ Module.finrank ℚ K‖ := by {
      rw [norm_pos_iff]
      simp only [ne_eq, pow_eq_zero_iff', not_and, Decidable.not_not]
      intros H
      by_contra H1
      apply cρ_ne_zero α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
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
          have : 0 < Module.finrank ℚ K := by {
            exact Module.finrank_pos}
          simp_all only [norm_zero, ne_eq]
          obtain ⟨left, right⟩ := htriv
          obtain ⟨left_1, right_1⟩ := habc
          obtain ⟨left_2, right_1⟩ := right_1
          subst left_2 left_1
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [pow_zero, zero_lt_one, lt_self_iff_false]}

  calc _ = _ := ?_
       c₅ ^ ((-r : ℤ)) < c₁^ ((- h : ℤ) * (r + 2 * m * q) ) := ?_
       _ < ‖(cρ) ^ Module.finrank ℚ K‖⁻¹ := ?_
       _ ≤ norm (Algebra.norm ℚ ρ) := ?_

  · simp only [zpow_neg, zpow_natCast]
  · simp only [zpow_neg, zpow_natCast, neg_mul]
    rw [inv_lt_inv₀]
    · rw [mul_add]
      have : (h : ℤ) * r + h * (2 * m * ↑q) = h * r + h * 2 * m * ↑q := by
        rw [mul_assoc, mul_assoc, mul_assoc]
      rw [this]
      have : ((h : ℤ) * r + ↑(h) * 2 * ↑(m K) * ↑q)  =
         ((h : ℤ) * (↑r + 2 * ↑(m K) * ↑q)) :=
         Eq.symm (Mathlib.Tactic.Ring.mul_add rfl rfl this)
      rw [this]
      dsimp [c₅]
      norm_cast
      rw [pow_mul]
      refine lt_self_pow₀ ?_ ?_
      sorry
      sorry
    · unfold c₅
      --unfold _root_.c₁
      trans
      · have : (0 : ℝ) < 1 := by {simp only [zero_lt_one]}
        apply this
      · apply one_lt_pow₀
        stop
        simp only [lt_sup_iff, Nat.one_lt_ofNat, true_or]
        exact rneq0 α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
    · have : 1 ≤ c₁ ^ (↑(h) * ((↑r) + 2 * ↑(m K) * (↑q))) := by {
        refine one_le_pow₀ ?_
        have : 1 ≤ c₁ K α' β' γ' := one_leq_c₁ K α' β' γ'
        exact this}
      calc (0 : ℝ) < 1 := by {simp only [zero_lt_one]}
       --needs the fact that 1 ≤ c₁
           (1 : ℝ) ≤ c₁ ^ (↑(h) * ((↑r) + 2 * ↑(m K) * (↑q))) := mod_cast this
  · unfold _root_.cρ
    rw [← pow_add]
    simp only [neg_mul, zpow_neg, abs_pow, norm_pow]
    rw [Int.norm_eq_abs]
    simp only [Int.cast_abs, abs_abs]
    rw [← pow_mul]
    rw [mul_comm]
    unfold h
    sorry
  · exact h2








































































lemma one_leq_c1rho : 1 ≤ ↑(cρ) := sorry

def c₆ : ℝ := house (1 + β')

macro_rules | `(c₆) => `(c₆ K β')

def c₇ : ℝ := house (α')^m * house (γ')^m

macro_rules | `(c₇) => `(c₇ K α' β')

def c₈ : ℝ := 2 * m * c₄* c₆ * 2* m * c₇^(2*m)

macro_rules | `(c₈) => `(c₈ K hd α' β' γ')

lemma eq6a : house ρ ≤ (q*q) * ((c₄ ^ (n : ℝ)) * ((n)^((1/2)*(n+1))) *
   (c₆* q) ^r * (c₇)^(q)) := by {
  calc _ ≤  house (cρ * ρ) := ?_

       _ ≤ ∑ t, house ( ((algebraMap (𝓞 K) K) ((η) t)) * (sys_coe_r)) := ?_

       _ ≤ (∑ t, house (algebraMap (𝓞 K) K ((η) t)) * house (sys_coe_r)) := ?_

       _ ≤ cρ * (∑ t, house (algebraMap (𝓞 K) K ((η) t)) * house (sys_coe_r)) := ?_

       _ ≤ (∑ t, house (algebraMap (𝓞 K) K ((η) t)) *
           (house ( c₁ • (a + b • β')) ^ r * house (c₁ • α') ^ (a * l₀) *
              house (c₁ • γ') ^ (b * l₀))) := ?_

       _ ≤ (∑ t, house (algebraMap (𝓞 K) K ((η) t)) *
           (house ( c₁ • (a + b • β')) ^ r * house (c₁ • α') ^ (m * q) *
              house (c₁ • γ') ^  (m * q))) := ?_

       _ ≤  (∑ t : Fin (q*q), (c₄ ^ (n : ℝ)) * ((n : ℝ)^(((n : ℝ)+ 1)/2) ) *
           ((Nat.sqrt (2*m K) * (1 + house (β')))^ r*
           (house (α') ^ (2*m K^2)) * house (γ') ^(2*m K^2))) := ?_

       _ ≤ (q*q) *((c₄ ^ (n : ℝ)) * ((n)^((1/2)*((n)+1))) * (c₆* q) ^r * (c₇)^(q : ℤ)) := ?_
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  -- · apply house_sum_le_sum_house
  -- · apply sum_le_sum
  --   intros i hi
  --   apply house_mul_le
  -- · nth_rw  1 [← one_mul ( a:= ∑ t_1,
  --   house ((algebraMap (𝓞 K) K) (η α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq t_1)) *
  --     house (sys_coe_r α β hirr htriv K σ hd α' β' γ' habc q t hq0 h2mq))]
  --   apply mul_le_mul
  --   · sorry
  --   · apply Preorder.le_refl
  --   · sorry
  --   · sorry
  -- · apply sum_le_sum
  --   intros i hi
  --   have := fromlemma82_bound α β hirr htriv K σ hd α' β' γ' habc q i hq0 h2mq
  --   apply mul_le_mul
  --   · exact this
  --   · apply Preorder.le_refl
  --   · apply house_nonneg
  --   · apply mul_nonneg
  --     · simp only [Real.rpow_natCast]
  --       apply pow_nonneg
  --       ·  apply (le_trans zero_le_one (one_leq_c₄ ..))
  --     · apply Real.rpow_nonneg
  --       simp only [Nat.cast_nonneg]
  -- · apply sum_le_sum
  --   intros i hi
  --   apply mul_le_mul
  --   · simp only [Real.rpow_natCast, le_refl]
  --   · unfold sys_coe_r
  --     trans
  --     · apply house_mul_le
  --     · rw [mul_comm]
  --       nth_rw 1 [mul_assoc]
  --       have : house (↑a + b • β') ^ r *
  --         (house α' ^ (a * l₀) * house γ' ^ (b * l₀)) =
  --         house γ' ^ (b * l₀) *
  --         (house (↑a + b • β') ^ r * (house α' ^ (a * l₀))) := by {
  --           rw [← mul_assoc]
  --           rw [mul_comm (house γ' ^ (b * l₀))]}
  --       rw [this]
  --       clear this
  --       apply mul_le_mul
  --       · trans
  --         · apply house_pow_le
  --         · apply Preorder.le_refl
  --       · trans
  --         · apply house_mul_le
  --         · apply mul_le_mul
  --           · trans
  --             · apply house_pow_le
  --             · apply Preorder.le_refl
  --           · trans
  --             · apply house_pow_le
  --             · apply Preorder.le_refl
  --           · apply house_nonneg
  --           · apply pow_nonneg
  --             apply house_nonneg
  --       · apply house_nonneg
  --       · apply pow_nonneg
  --         · apply house_nonneg
  --   · apply house_nonneg
  --   · apply mul_nonneg
  --     · simp only [Real.rpow_natCast]
  --       apply pow_nonneg
  --       · sorry
  --     · apply Real.rpow_nonneg
  --       simp only [Nat.cast_nonneg]
  -- · apply sum_le_sum
  --   intros i hi
  --   simp only [Real.rpow_natCast, nsmul_eq_mul]
  --   apply mul_le_mul
  --   · simp only [le_refl]
  --   · apply mul_le_mul
  --     · apply mul_le_mul
  --       · refine pow_le_pow_left₀ ?_ ?_ r
  --         sorry
  --         sorry
  --       · sorry
  --       · apply pow_nonneg
  --         · apply house_nonneg
  --       · sorry
  --     · sorry
  --     · apply pow_nonneg
  --       apply house_nonneg
  --     · apply mul_nonneg
  --       · apply pow_nonneg
  --         apply mul_nonneg
  --         · simp only [Nat.cast_nonneg]
  --         · trans
  --           · apply zero_le_one
  --           · simp only [le_add_iff_nonneg_right]
  --             apply house_nonneg
  --       · apply pow_nonneg
  --         apply house_nonneg
  --   · apply mul_nonneg
  --     · apply mul_nonneg
  --       · apply pow_nonneg
  --         apply house_nonneg
  --       · apply pow_nonneg
  --         apply house_nonneg
  --     · apply pow_nonneg
  --       apply house_nonneg
  --   · sorry
  -- · rw [sum_const, card_univ, Fintype.card_fin]
  --   simp only [Real.rpow_natCast, Nat.reduceDiv,
  --     zero_mul, pow_zero, mul_one, nsmul_eq_mul,
  --     Nat.cast_mul, zpow_natCast]
  --   apply mul_le_mul
  --   · simp only [le_refl]
  --   · apply mul_le_mul
  --     · sorry
  --     · sorry
  --     · apply mul_nonneg
  --       · apply mul_nonneg
  --         apply pow_nonneg
  --         · apply mul_nonneg
  --           · simp only [Nat.cast_nonneg]
  --           · trans
  --             · apply zero_le_one
  --             · simp only [le_add_iff_nonneg_right]
  --               apply house_nonneg
  --         · apply pow_nonneg
  --           apply house_nonneg
  --       · apply pow_nonneg
  --         apply house_nonneg
  --     · apply mul_nonneg
  --       · sorry
  --       · apply pow_nonneg
  --         apply mul_nonneg
  --         · sorry
  --         · exact Nat.cast_nonneg' q
  --   · apply mul_nonneg
  --     · sorry
  --     · apply mul_nonneg
  --       · apply mul_nonneg
  --         apply pow_nonneg
  --         apply mul_nonneg
  --         · simp only [Nat.cast_nonneg]
  --         · trans
  --           · apply zero_le_one
  --           · simp only [le_add_iff_nonneg_right]
  --             apply house_nonneg
  --         · apply pow_nonneg
  --           apply house_nonneg
  --       · apply pow_nonneg
  --         apply house_nonneg
  --   · simp_all only [Nat.cast_pos,
  --       mul_nonneg_iff_of_pos_left, Nat.cast_nonneg]
  -- · sorry
}

lemma eq6b : (q*q) *
  ((c₄ ^ (n : ℝ)) * ((n)^((1/2)*(n+1))) * (c₆* q) ^r * (c₇)^(q)) ≤ c₈^r * r^(r + 3/2) := sorry

lemma eq6 : house ρ ≤ c₈^r * r^(r + 3/2) := by sorry







































































































































/-
We formalize the existence of a function R' : ℂ → ℂ,
analytic in a neighborhood of l' + 1,
such that R(z) = (z - (l' + 1))^r * R'(z) in a neighborhood of l' + 1.
so this o is (I hope) R_order l' -/
lemma exists_R'_at_l'_plus_one (l' : Fin (m K))  :
  ∃ (R' : ℂ → ℂ) (U : Set ℂ), (U ∈ nhds (l' + 1 : ℂ)) ∧ (l' + 1 : ℂ) ∈ U ∧
    (∀ z ∈ U, (R) z = (z - (l' + 1))^r * R' z) ∧
    AnalyticOn ℂ R' U ∧ R' (l' + 1) ≠ 0 := by
  have hA := analyticEverywhere α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq (l' + 1)
  have (z : ℂ) := R_order_eq α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq z
  have := this (l' + 1)
  rw [AnalyticAt.analyticOrderAt_eq_natCast] at this
  obtain ⟨R'', ⟨horder, ⟨hRneq0, hfilter⟩⟩⟩ := this
  let o := R_order α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq (↑↑l' + 1)
  -- have h0or : 0 ≤ (o - r) := by {
  --   simp only [zero_le]
  -- }
  let R' (z : ℂ) := ((z - (l' + 1))^(o - r)) * R'' z
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
        have : (z - (l' + 1)) ^ (r) * (z - (l' + 1)) ^ (o - r) =
           (z - (l' + 1)) ^ (o) := by {
            rw [← pow_add]
            have : (r + (o - r) : ℤ) = o := by {
              simp only [add_sub_cancel]
            }
            rw [sub_eq_add_neg]
            congr
            sorry



            --simp only [add_sub_cancel] at this
            --rw [this]
            --rw [← this]
             }
        rw [← mul_assoc]
        rw [this]
        unfold R o
        simp only [smul_eq_mul] at hU_prop z hz
        exact  hU_prop z hz
      · constructor
        · unfold AnalyticOn
          intros x hx
          refine analyticWithinAt ?_
          unfold R'
          refine fun_mul ?_ ?_
          · apply Differentiable.analyticAt
            · apply Differentiable.pow ?_
              · simp only [differentiable_fun_id, differentiable_const, Differentiable.fun_sub]
          · refine Differentiable.analyticAt ?_ x
            refine analyticOn_univ_iff_differentiable.mp ?_
            refine analyticOn_of_locally_analyticOn ?_
            intros y hy
            use U
            constructor
            · sorry
            · constructor
              · sorry
              · simp only [Set.univ_inter]
                sorry
        · unfold R'
          by_contra H
          simp only [sub_self, mul_eq_zero, pow_eq_zero_iff', ne_eq, true_and] at H
          cases' H with H1 H2
          · sorry
          · apply hRneq0
            exact H2
  · exact hA

def R'U (l' : Fin (m K)) : ℂ → ℂ := (exists_R'_at_l'_plus_one
  α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l').choose

def U (l' : Fin (m K))  : Set ℂ :=
  (exists_R'_at_l'_plus_one α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l').choose_spec.choose

def R'prop (l' : Fin (m K)) :
  let R'U := R'U α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
  let U := U α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
  (U ∈ nhds (l' + 1 : ℂ)) ∧ ↑↑l' + 1 ∈ U ∧
  (∀ z ∈ U, (R) z = (z - (↑↑l' + 1)) ^ r * R'U z) ∧ AnalyticOn ℂ R'U U ∧ R'U (↑↑l' + 1) ≠ 0 := by
  intros R'U U
  have := (exists_R'_at_l'_plus_one
    α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l').choose_spec.choose_spec
  exact this

def R'R (l' : Fin (m K)) : ℂ → ℂ := fun z => (R) z * (z - (↑l' + 1))^(-r : ℤ)

def R' (l' : Fin (m K)) : ℂ → ℂ :=
  let R'U := R'U α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
  let R'R := R'R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
  let U := U α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
  letI : ∀ z, Decidable (z ∈ U) := by {
    intros z
    exact Classical.propDecidable (z ∈ U)}
  fun z =>
    if z = l' + 1 then
      R'U z
    else
      R'R z

-- lemma: R' is equal to R'_nhd on U
lemma R'_eq_R'U (l' : Fin (m K)) :
  let R' := R' α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
  let R'U := R'U α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
  let U := U α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
  ∀ z ∈ U, R' z = R'U z := by
    intros R' R'U U z hz
    unfold R' _root_.R'
    split_ifs
    · rfl
    · unfold R'R
      have R'prop := (R'prop α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l').2.2.1 z hz
      rw [R'prop]
      unfold R'U
      rw [mul_comm, ← mul_assoc]
      have : (z - (↑↑l' + 1)) ^ (-((r)) : ℤ) * (z - (↑↑l' + 1)) ^ (r) = 1 := by
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

lemma R'_eq_R'R (l' : Fin (m K)) :
  let R' := R' α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
  let R'R := R'R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
  ∀ z ∈ {z : ℂ | z ≠ l' + 1}, R' z = R'R z := by
    intros R' R'R z hz
    unfold R' _root_.R' R'R  _root_.R'R
    simp only [mem_setOf_eq] at hz
    split
    · rename_i h
      subst h
      simp_all only [ne_eq, not_true_eq_false]
    · rfl

lemma R'R_analytic (l' : Fin (m K)) :
  let R'R := R'R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
  AnalyticOn ℂ R'R {z : ℂ | z ≠ l' + 1} := by
    unfold R'R
    simp only
    refine AnalyticOn.mul ?_ ?_
    · apply AnalyticOnSubset _ _ univ
      simp only [Set.subset_univ]
      have := analyticEverywhere α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
      apply analyticOn_univ.mpr fun x a ↦ this x
    · apply AnalyticOn.fun_zpow ?_
      intros z hz
      simp only [mem_setOf_eq] at hz
      exact sub_ne_zero_of_ne hz
      apply AnalyticOn.sub analyticOn_id analyticOn_const

lemma R'analytic (l' : Fin (m K)) :
  let R' := R' α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
  ∀ z : ℂ, AnalyticAt ℂ R' z := by
    let U := U α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
    intros R' z
    by_cases H : z = l' + 1
    · have R'prop := (R'prop α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l')
      apply AnalyticOnAt _ _ U _
      have := R'_eq_R'U
        α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
      rw [AnalyticOnEquiv _ _ U this]
      exact R'prop.2.2.2.1
      rw [H]
      exact R'prop.1
    · apply AnalyticOnAt _ _ {z : ℂ | z ≠ l' + 1} _
      have := R'_eq_R'R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
      rw [AnalyticOnEquiv _ _ {z : ℂ | z ≠ l' + 1} this]
      apply R'R_analytic
      apply IsOpen.mem_nhds isOpen_ne
      simp only [ne_eq, mem_setOf_eq, H, not_false_eq_true]

lemma R'onC (l' : Fin (m K)) :
  let R' := R' α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l'
    ∀ z : ℂ, (R) z = (z - (l' + 1))^r * R' z := by
  intros R' z
  let U := (exists_R'_at_l'_plus_one
    α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l').choose_spec.choose
  unfold R'
  unfold _root_.R'
  split
  · have R'prop := (R'prop α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l')
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
    have : (z - (↑↑l' + 1)) ^ (-r : ℤ) * (z - (↑↑l' + 1)) ^ r = 1 := by
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

--#check EMetric.isOpen_iff

def ks : Finset ℂ := Finset.image (fun (k': ℕ) => (k' + 1 : ℂ)) (Finset.range (m K))

omit hirr   htriv
  habc
  hq0
  h2mq in
lemma z_in_ks : z ∈ (ks K) ↔ ∃ k': Fin (m K), z = k' + 1 := by
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

def S.U : Set ℂ := (ks K)ᶜ

omit hirr htriv
  habc
  hq0
  h2mq in
lemma S.U_ne_of_mem {z : ℂ} (hz : z ∈ (S.U K)) (k' : Fin (m K)) : z ≠ (k' + 1 : ℂ) := by
  dsimp [S.U, ks] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists, not_and] at hz
  intro H
  apply hz k' k'.isLt
  exact H.symm

omit h2mq hirr  htriv
  habc
  hq0 in
lemma S.U_is_open : IsOpen (S.U K) := by
  unfold S.U
  rw [EMetric.isOpen_iff]
  intros z hz
  have : (Finset.image (dist z) (ks K)).Nonempty := by
    dsimp [ks]
    simp only [Finset.image_nonempty, nonempty_range_iff, ne_eq]
    exact Nat.add_one_ne_zero (2 * h K + 1)
  let ε := Finset.min' (Finset.image (dist z) (ks K)) this
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

omit h2mq hirr htriv
  habc
  hq0 in
lemma S.U_nhds : z ∈ U K → (S.U K) ∈ nhds z :=
  IsOpen.mem_nhds (U_is_open K)

omit hirr htriv
  habc
  hq0
  h2mq in
lemma zneq0 : ∀ (h : z ∈ S.U K) (k' : Fin (m K)), (z - (k' + 1 : ℂ)) ≠ 0 := by
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

omit hirr htriv habc hq0 h2mq in
lemma z_in_ks' : z ∈ (ks K) ↔ ∃ k': Fin (m K), z = k' + 1 := by
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

omit hirr htriv habc hq0 h2mq in
lemma S.U_ne_of_mem' {z : ℂ} (hz : z ∈ (S.U K)) (k' : Fin (m K)) : z ≠ (k' + 1 : ℂ) := by
  dsimp [S.U, ks] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists, not_and] at hz
  intro H
  apply hz k' k'.isLt
  exact H.symm

def SR : ℂ → ℂ := fun z =>
  (R) z * ((r).factorial) * ((z - (l₀ : ℂ)) ^ (-r : ℤ)) *
    (∏ k' ∈ Finset.range (m K) \ {↑l₀}, ((l₀ - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ r)

macro_rules | `(SR) => `(SR α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)

lemma SR_analytic_S.U : AnalyticOn ℂ SR (S.U K) := by {
  unfold SR
  refine AnalyticOn.mul ?_ ?_
  · apply AnalyticOn.mul ?_ ?_
    · apply AnalyticOn.mul ?_ ?_
      · have := analyticEverywhere α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
        exact
          AnalyticOnSubset (R) (S.U K)
            (fun ⦃a⦄ ↦ True) (fun ⦃a⦄ a ↦ trivial) (analyticOn_univ.mpr fun x a ↦ this x)
      · exact analyticOn_const
    · apply AnalyticOn.fun_zpow
      · apply AnalyticOnSubset
        · have : S.U K ⊆ Set.univ := by {exact fun ⦃a⦄ a ↦ trivial}
          exact this
        · simp only [analyticOn_univ]
          sorry
      · intros z hz
        dsimp [S.U,ks] at hz
        simp only [coe_image, coe_range, mem_compl_iff,
          Set.mem_image, Set.mem_Iio, not_exists, not_and] at hz
        have := hz l₀
        intros HC
        apply this
        simp only [Fin.is_lt]
        rw [sub_eq_zero] at HC
        rw [HC]
        sorry
  · apply Finset.analyticOn_fun_prod
    intros u hu
    simp only [mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hu
    apply AnalyticOn.fun_pow
    · sorry

  }

-- functions are equal and both analytic are analytic

lemma SR_Analytic : ∀ z, AnalyticAt ℂ (SR) z := by {
  intros z
  apply AnalyticOnAt
  · apply S.U_nhds K
    sorry
    --bycases z as in def of SR
  · exact SR_analytic_S.U α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq}

def SRl0 : ℂ → ℂ := fun z =>
  (R' α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l₀) z * ((r).factorial)  *
    (∏ k' ∈ Finset.range (m K) \ {↑l₀}, ((l₀ - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ r)

macro_rules | `(SRl0) => `(SRl0 α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)

def SRl (l': Fin (m K)) : ℂ → ℂ := fun z =>
  (R' α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l') z *
      ((r).factorial) * ((z - (l₀ : ℂ)) ^ (-r : ℤ)) *
    (∏ k' ∈ Finset.range (m K) \ {↑l₀} ∪ {(↑l' + 1 : ℕ)},
     (((l₀ - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ r )) *((l₀ - (l' + 1)))^r

macro_rules | `(SRl) => `(SRl α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)

def S : ℂ → ℂ :=
  fun z =>
    let R' := R' α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
    if H : ∃ (k' : Fin (m K)), z = (k' : ℂ) + 1 then
      let k' := H.choose
      if k' = l₀ then
        (SRl0 α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq z)
          else
        (SRl α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq k' z)
    else
      (SR) z

macro_rules | `(S) => `(S α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq)

lemma S_eq_SRl0 : z ∈ (S.U K) → (SRl0) z = (SR) z := by
  intros hz
  unfold S.U at *
  unfold SRl0
  dsimp [SR]
  nth_rw 3 [mul_assoc]
  simp only [zpow_neg, zpow_natCast, mul_eq_mul_right_iff]
  dsimp [ks] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists,
    not_and] at hz
  left
  have := R'onC α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l₀
  rw [this]
  clear this
  nth_rw 3 [mul_comm]
  rw [mul_assoc]
  congr
  · rw [← mul_assoc]
    nth_rw 2 [mul_comm]
    have : (↑(r).factorial : ℂ) = ↑(r).factorial * 1 := by simp only [mul_one]
    nth_rw 1 [this]
    clear this
    rw [mul_assoc]
    refine (mul_right_inj' ?_).mpr ?_
    · simp only [ne_eq, Nat.cast_eq_zero]
      exact Nat.factorial_ne_zero r
    · have : ((z - ↑↑l₀) ^ r )⁻¹ = (z - ↑↑l₀) ^ (- r : ℤ) := by {
          simp only [zpow_neg, zpow_natCast]}
      rw [this]; clear this
      have : 1 = (z - ↑↑l₀) ^ (-↑(r : ℤ)) * (z - ↑↑l₀) ^ ↑r := by {
        simp only [zpow_neg, zpow_natCast]
        rw [mul_comm]
        symm
        apply Complex.mul_inv_cancel
        intros Hz
        simp only [pow_eq_zero_iff', ne_eq] at Hz
        have : l₀ < m := by {simp only [Fin.is_lt]}
        have H := hz  ↑(l₀) this
        apply H
        rw [sub_eq_add_neg] at Hz
        rw [add_eq_zero_iff_eq_neg] at Hz
        simp only [neg_neg] at Hz
        symm
        rw [Hz.1]-- l+1
        sorry
         }
      sorry -- l+1

lemma SR_eq_SRl(l' : Fin (m K)) (hl : l' ≠ l₀) : z ∈ (S.U K) → (SRl) (l') z = (SR) z := by
  intros hz
  unfold S.U at *
  dsimp [SR, SRl]
  nth_rw 3 [mul_assoc]
  simp only [zpow_neg, zpow_natCast]
  dsimp [ks] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists,
    not_and] at hz
  have := R'onC α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq l' z
  rw [this]
  clear this
  nth_rw 8 [mul_comm]
  simp only [mul_assoc]
  --congr
  sorry

  -- refine (mul_right_inj' ?_).mpr ?_
  -- · unfold R'
  --   split
  --   · rename_i H
  --     intros HF
  --     have : ↑↑l' < m := by {simp only [Fin.is_lt]}
  --     have := hz l' this
  --     apply this
  --     symm
  --     exact H
  --   · unfold R'R
  --     intros HR
  --     simp only [zpow_neg, zpow_natCast, mul_eq_zero,
  --       inv_eq_zero, pow_eq_zero_iff', ne_eq] at HR
  --     cases' HR with HR1 HR2
  --     ·
  --       have := R_nonzero α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
  --        --exact HR1
  --       apply this
  --       sorry
  --     · have : l' < m := by {simp only [Fin.is_lt]}
  --       have H := hz  ↑(l') this
  --       apply H
  --       rw [sub_eq_add_neg] at HR2
  --       rw [add_eq_zero_iff_eq_neg] at HR2
  --       simp only [neg_add_rev, neg_neg] at HR2
  --       symm
  --       exact HR2.1
  -- · nth_rw 4 [← mul_assoc]
  --   nth_rw 4 [mul_comm]
  --   simp only [mul_assoc]
  --   refine (mul_right_inj' ?_).mpr ?_
  --   · simp only [ne_eq, Nat.cast_eq_zero]
  --     intros HI
  --     apply Nat.factorial_ne_zero r
  --     exact HI
  --   · refine (mul_right_inj' ?_).mpr ?_
  --     · simp only [ne_eq, inv_eq_zero, pow_eq_zero_iff', not_and, Decidable.not_not]
  --       intros HI
  --       by_contra hr
  --       have : l₀ < m := by {simp only [Fin.is_lt]}
  --       have H := hz ↑(l₀) this
  --       rw [sub_eq_add_neg] at HI
  --       rw [add_eq_zero_iff_eq_neg] at HI
  --       simp only [neg_neg] at HI
  --       apply H
  --       rw [HI]
  --       sorry -- l₀ + 1 not l
  --     · sorry

lemma S_eq_SR (l : Fin (m K)) (hl : l ≠ l₀) : z ∈ (S.U K) → (SR) z = (S) z  := by
  intros hz
  unfold S.U at *
  unfold S
  simp only
  symm
  simp only [dite_eq_right_iff, forall_exists_index]
  intros x hx
  split
  · exact S_eq_SRl0 α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq hz
  · apply SR_eq_SRl
    subst hx
    simp_all only [ne_eq, mem_compl_iff, mem_coe,
      add_left_inj, Nat.cast_inj, not_false_eq_true]
    exact hz

-- #check AnalyticOnEquiv
 #check AnalyticOnEq
-- #check AnalyticOnAt
-- #check  AnalyticOnSubset

lemma holS :
  --∀ x ∈ Metric.ball 0 (m K *(1 + (r/q))) \ {(l₀ : ℂ)},
  ∀ z, AnalyticAt ℂ (S) z := by {
  intros z
  by_cases H : ∃ (k' : Fin (m K)), z = (k' : ℂ) + 1
  by_cases Hzl0 : z = l₀
  -- for all 3 cases show that S is equal to one of the other functions
  -- on a neigh and use the lemma that the other fun is analytic
  · refine AnalyticOnAt (S α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) z ?_ ?_ ?_
    · sorry
    · sorry
    · sorry
  · --have := S_eq_SRl α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq ?_ ?_ ?_ ?_
    refine AnalyticOnAt (S α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) z ?_ ?_ ?_
    · sorry
    · sorry
    apply AnalyticOnEq
    intros z HZ
    sorry
    sorry
    sorry
    --refine S_eq_SR α β hirr htriv K σ hd α' β' γ' habc q ?_ hq0 h2mq ?_ ?_ HZ
  · refine AnalyticOnAt (S α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq) z ?_ ?_ ?_
    exact (S.U K)
    apply S.U_nhds
    unfold S.U ks
    simp only [coe_image, coe_range, mem_compl_iff,
      Set.mem_image, Set.mem_Iio, not_exists, not_and]
    simp only [not_exists] at H
    intros x hx
    have := H ⟨x,hx⟩
    intros HC
    apply this
    simp only
    exact HC.symm
    apply AnalyticOnEq
    intros z HZ
    refine S_eq_SR α β hirr htriv K σ hd α' β' γ' habc q ?_ hq0 h2mq ?_ ?_ HZ
    · sorry
    · sorry
    · sorry
    · sorry
    }

lemma hcauchy (l' : Fin (m K)) :
  (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(0, m *(1 + (r / q))), (z - l₀)⁻¹ * (S) z) = (S) l₀ := by
  apply two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
  · exact countable_singleton (l₀ : ℂ)
  · have : (l₀ : ℂ) ∈ Metric.ball 0 (m K * (1 + ↑r / ↑q)) := by {
    simp only [Metric.mem_ball, dist_zero_right, norm_natCast]
    have : (l₀ : ℝ) < m := by {simp only [Nat.cast_lt, Fin.is_lt]}
    trans
    · exact this
    · apply lt_mul_right
      · exact mod_cast hm K
      · simp only [lt_add_iff_pos_right]
        apply div_pos
        · norm_cast
          exact r_qeq_0 α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
        · simp only [Nat.cast_pos]
          exact hq0}
    exact this
  · intros x hx
    apply @DifferentiableWithinAt.continuousWithinAt ℂ _ _ _ _ _ _ _ _ _
    refine DifferentiableAt.differentiableWithinAt ?_
    have : ∀ z, AnalyticAt ℂ S z :=
     fun z ↦ holS α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq z
    exact AnalyticAt.differentiableAt (this x)
  · intros x hx
    apply AnalyticAt.differentiableAt
    exact holS α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq x



--#check sys_coe'_bar
def sys_coeff_foo_S : ρᵣ = Complex.log α ^ (-↑(r : ℤ)) * (S) ↑↑(l₀) := by {
  unfold S
  simp only
  dsimp [ρᵣ]
  congr
  · sorry
    }

lemma eq7 (l' : Fin (m K)) :
  ρᵣ = log α ^ (-r : ℤ) * ((2 * ↑Real.pi * I)⁻¹ *
    (∮ z in C(0, m *(1+ (r/q))), (z - l₀)⁻¹ * (S) z)) := by
  calc _ = (log α)^(- r : ℤ) * (S) l₀ := ?_
       _ = (log α) ^ (-r : ℤ) * ((2 * ↑Real.pi * I)⁻¹ *
    (∮ z in C(0, m *(1 + (r/q))), (z - l₀)⁻¹ * (S) z)) := ?_
  · apply sys_coeff_foo_S
  · rw [hcauchy]
    exact l₀

def c₉ : ℝ := sorry

def c₁₀ : ℝ := sorry

lemma abs_R : norm ((R) z) ≤ (c₁₀)^r * r^(1/2*(r+3)) := by

  calc _ ≤ ∑ t, (‖(canonicalEmbedding K) ((algebraMap (𝓞 K) K) ((η) t)) σ‖ * ‖cexp (ρ α β q t * z)‖) := ?_

       _ ≤ ∑ t : Fin (q*q), ((c₄)^(n : ℝ) * (n) ^(((n:ℝ) +1)/2) *
         (Real.exp ((q+q*(norm β))* m *(1+r/q))*(norm α))) := ?_

       _ ≤ (q*q) * ((c₄)^(n : ℝ) * (n) ^((1/2)*(n +1))*(c₉)^(r+q)) := ?_

       _ ≤ (c₁₀)^r * r^(1/2*(r+3)) := ?_

  · unfold R
    apply norm_sum_le_of_le
    intros b hb
    simp only [Complex.norm_mul, le_refl]
  · apply sum_le_sum
    intros i hi
    apply mul_le_mul
    · have lemma82 := fromlemma82_bound
        α β hirr htriv K σ hd α' β' γ' habc q i hq0 h2mq
      unfold house at lemma82
      sorry
    · --unfold ρ
      have : ∀ i, ‖cexp (ρ α β q i * z)‖ ≤
         (Real.exp ((q+q*(norm β))* m *(1+r/q)) * (norm α)) := sorry
      apply this
    · apply norm_nonneg
    · unfold c₄
      simp only [Real.rpow_natCast]
      sorry
  · simp only [Real.rpow_natCast, Nat.reduceDiv, zero_mul, pow_zero,
    mul_one, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
    apply mul_le_mul
    · simp only [le_refl]
    · apply mul_le_mul
      · sorry
      · sorry
      · apply mul_nonneg
        · trans
          · apply zero_le_one
          · simp only [Real.one_le_exp_iff]
            apply mul_nonneg
            · apply mul_nonneg
              · have : (q : ℝ) = q * 1 := by {simp only [mul_one]}
                nth_rw 1 [this]
                rw [← mul_add]
                apply mul_nonneg
                · simp only [Nat.cast_nonneg]
                · trans
                  · apply zero_le_one
                  · simp only [le_add_iff_nonneg_right, norm_nonneg]
              · simp only [Nat.cast_nonneg]
            · trans
              · apply zero_le_one
              · simp only [le_add_iff_nonneg_right]
                apply div_nonneg
                · simp only [Nat.cast_nonneg]
                · simp only [Nat.cast_nonneg]
        · apply norm_nonneg
      · sorry
        -- simp only [Real.rpow_natCast,
        --   le_sup_iff, zero_le_one, true_or, pow_nonneg]
    · apply mul_nonneg
      · sorry
        -- simp only [Real.rpow_natCast, le_sup_iff,
        --   zero_le_one, true_or, pow_nonneg]
      · apply mul_nonneg
        · trans
          · apply zero_le_one
          · simp only [Real.one_le_exp_iff]
            apply mul_nonneg
            · apply mul_nonneg
              · have : (q : ℝ) = q * 1 := by {simp only [mul_one]}
                nth_rw 1 [this]
                rw [← mul_add]
                apply mul_nonneg
                · simp only [Nat.cast_nonneg]
                · trans
                  · apply zero_le_one
                  · simp only [le_add_iff_nonneg_right, norm_nonneg]
              · simp only [Nat.cast_nonneg]
            · trans
              · apply zero_le_one
              · simp only [le_add_iff_nonneg_right]
                have := r_div_q_geq_0
                  α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
                apply div_nonneg
                simp only [Nat.cast_nonneg]
                simp_all only [zero_le, Nat.cast_nonneg]
        · apply norm_nonneg
    · apply mul_nonneg
      · simp only [Nat.cast_nonneg]
      · simp only [Nat.cast_nonneg]
  · sorry

lemma abs_hmrqzl₀ : ∀ (hz : z ∈ Metric.sphere 0 (m K *(1+ (r/q)))),
    m *r/q ≤ norm (z - l₀ : ℂ) := by
  intros hz
  calc _ = (m K* (1 + r/q) - m : ℝ) := ?_
       _ ≤ norm z - norm (l₀ : ℂ) := ?_
       _ ≤ norm (z - l₀) := ?_
  · ring
  · simp only [norm_natCast]
    have hlm : (l₀ : ℝ) < m := by {
      simp only [Nat.cast_lt, Fin.is_lt]}
    simp only [mem_sphere_iff_norm, sub_zero] at hz
    rw [hz]
    simp only [tsub_le_iff_right, ge_iff_le]
    have : ↑(m K) * (1 + ↑r / ↑q) - ↑l₀ =
      ↑(m K) * (1 + ↑r / ↑q) + (- ↑l₀ : ℝ) := rfl
    rw [this]
    rw [add_assoc]
    simp only [le_add_iff_nonneg_right,
      le_neg_add_iff_add_le, add_zero, Nat.cast_le, ge_iff_le]
    rw [le_iff_lt_or_eq ]
    left
    simp only [Nat.cast_lt] at hlm
    exact hlm
  · exact norm_sub_norm_le z ↑l₀

lemma abs_z_k (k : Fin (m K)) :
  ∀ (hz : z ∈ Metric.sphere 0 (m K *(1 + (r/q)))), (m K) * r/q ≤ norm (z-k : ℂ) := by
  intros hz
  calc _ = (m K* (1 + r/q) - m : ℝ) := ?_
       _ ≤ norm z - norm (k : ℂ) := ?_
       _ ≤ norm (z - k) := ?_
  · ring
  · simp only [norm_natCast]
    simp only [mem_sphere_iff_norm, sub_zero] at hz
    rw [hz]
    simp only [tsub_le_iff_right]
    have : ↑(m K) * (1 + ↑r / ↑q) - ↑k =
      ↑(m K) * (1 + ↑r / ↑q) + (- ↑k : ℝ) := rfl
    rw [this]
    rw [add_assoc]
    simp only [le_add_iff_nonneg_right,
      le_neg_add_iff_add_le, add_zero, Nat.cast_le, ge_iff_le]
    unfold _root_.k
    sorry
  · exact norm_sub_norm_le z k

def c₁₁ : ℝ := sorry

def c₁₂ : ℝ := sorry

include u in
lemma blah (l' : Fin (m K)) : norm ((S) z) ≤ (c₁₂)^r * ((3 - m) / 2 + 3 / 2) := by
  calc
    _ = norm (((R) z) * ((r).factorial) * (((z - l₀) ^ (-r : ℤ)) *
        ∏ k ∈ Finset.range (m K) \ {(l₀ : ℕ)},
          ((l₀ - k) / (z - k)) ^ r) : ℂ) := ?_

    _ = (r).factorial * (norm ((R) z) * norm ( (1/(z - l₀ : ℂ) ^ r)) *
        norm (∏ k ∈ Finset.range ((m K)) \
          {(l₀ : ℕ)}, ((l₀ - k) / (z - k)) ^ r)) := ?_

    _ ≤ (r).factorial * ((c₁₀)^r * r^(1/2*(r+3)) * (c₁₁)^r * (q/r)^(m K *r)) := ?_

    _ ≤ (c₁₂)^r*((3-m K)/2 + 3 /2) := ?_

  · unfold S
    simp only
    sorry
  · simp only [zpow_neg, zpow_natCast, Complex.norm_mul,
      norm_natCast, norm_inv, norm_pow,
      norm_prod, Complex.norm_div, one_div]
    nth_rewrite 2 [mul_assoc]
    nth_rewrite 2 [← mul_assoc]
    simp only [mul_eq_mul_right_iff, mul_eq_zero, inv_eq_zero,
      pow_eq_zero_iff', norm_eq_zero, ne_eq]
    left
    exact Eq.symm (Nat.cast_comm (r).factorial ‖(R) z‖)
  · apply mul_le_mul
    · simp only [le_refl]
    · rw [mul_assoc]
      rw [mul_assoc]
      · apply mul_le_mul
        · have : norm ((R) z) ≤ (c₁₀)^r * r^(1/2*(r+3)) :=
            abs_R α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
          exact this
        · sorry
        · apply mul_nonneg
          · apply norm_nonneg
          · apply norm_nonneg
        · sorry
    · apply mul_nonneg
      · apply mul_nonneg
        · simp only [norm_nonneg]
        · simp only [norm_nonneg]
      · simp only [norm_nonneg]
    · simp only [Nat.cast_nonneg]
  · sorry

def c₁₃ : ℝ := sorry

-- #moogle "@zero_le_real_div?."
-- #check circleIntegral.norm_integral_le_of_norm_le_const'
--#check circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const

lemma eq8 : norm (ρᵣ) ≤ (c₁₃)^r*r^(r*(3-m K)/2 +3/2) := by
  let Cnum : ℝ := sorry
  have hR : 0 ≤ (m K * (1 + ↑r / ↑q) : ℝ) := by
    apply mul_nonneg
    · simp only [Nat.cast_nonneg]
    · trans
      · exact zero_le_one
      · simp only [le_add_iff_nonneg_right]
        have := r_div_q_geq_0 α β hirr htriv K σ hd α' β' γ' habc q hq0 h2mq
        have : 0 ≤ (r : ℝ) := by {simp only [Nat.cast_nonneg]}
        apply div_nonneg
        · simp only [Nat.cast_nonneg]
        · simp only [Nat.cast_nonneg]

  have hf : ∀ z ∈ Metric.sphere 0 (m K * (1 + ↑r / ↑q)),
    ‖(z - (↑l₀ : ℂ))⁻¹ * (S) z‖ ≤ Cnum := sorry

  have := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR hf

  calc _ = norm (Complex.log α ^ (-(r : ℤ)) * ((2 * Real.pi) * I)⁻¹ * ∮ (z : ℂ) in
           C(0, m* (1 + ↑r / ↑q)), (z - ↑l₀)⁻¹ * (S) z) := ?_

       _ = norm ((Complex.log α ^ (-(r : ℤ))) *
          norm ((2 * Real.pi * I)⁻¹)) * norm (∮ (z : ℂ) in
          C(0, m * (1 + ↑r / ↑q)), (z - ↑l₀)⁻¹ * (S) z) := ?_

       --_ ≤ norm ((2 * Real.pi)⁻¹) *
        -- (∮ (z : ℂ) in C(0, m * (1 + ↑r / ↑q)), ‖(z - ↑l₀)⁻¹ * ((S) z)‖) := ?_

       _ ≤ norm ((log α))^((-r : ℤ)) * m *(1+r/q)* (c₁₂)^r *
          r^(r*(3-m K)/2 + 3/2) * q/(m K * r) := ?_

       _ ≤ (c₁₃)^r * r^(r * (3- m)/2 + 3/2)  := ?_

  · rw [eq7]
    sorry
    exact l₀
  · simp only [zpow_neg, zpow_natCast, _root_.mul_inv_rev, ofReal_mul,
      ofReal_inv, ofReal_ofNat,
      norm_inv, norm_pow, norm_real, Real.norm_eq_abs,
      norm_ofNat, norm_mul, abs_abs]
    simp_all only
    simp only [norm_I, inv_one, one_mul, abs_one]
  · sorry
  · sorry

def c₁₄ : ℝ := sorry

lemma use6and8 :
  (Algebra.norm ℚ ρ) ≤ (c₁₄)^r * r^((-r : ℤ)/2 + 3 * h/2) := by

  have : (((h - 1) : ℤ) * (r + 3/2 : ℤ) + (3 - m) * r * 1/2 + 3/2) =
    ((-r : ℤ)/2 + 3 * h/2) := by {
      sorry
      }

  calc _ ≤ ((c₁₄)^r) * r^ ((h -1) * (r + 3/2 : ℤ)
    + (3-m K) * r * 1/2 + 3/2) := ?_
       _ = ((c₁₄)^r) * r^ ((-r : ℤ)/2 + 3 * h/2) := ?_
  · sorry
  · rw [← this]

def c₁₅ : ℝ := c₁₄ --* c₅

macro_rules | `(c₁₅) => `(c₁₅ K α' β' γ' q)

-- include α β σ hq0 h2mq hd hirr htriv K σ α' β' γ' habc h2mq u t in
-- theorem main : r ^ ((r - 3 * (h)) / 2) ≥ c₁₅ K α' β' γ' q ^ r := by
--   --have := rgeqn α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
--   sorry
--   --use r_geq_n K α β hirr htriv σ hd α' β' γ' habc q u t hq0 h2mq

-- lemma use5 : r^((r - 3 * (h)) / 2) < c₁₅ K α' β' γ' q ^r := by
--   calc _ < c₁₄^r * (c₅) ^r := ?_
--        _ = (c₁₅ K α' β' γ' q) ^r := ?_
--   · sorry
--   · rw [← mul_pow]
--     simp only [c₁₅]

--include hα hβ α β σ hq0 h2mq hd hirr htriv K σ h2mq t q in
theorem hilbert7 (α β : ℂ) (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
  (htriv : α ≠ 0 ∧ α ≠ 1) (hirr : ∀ i j : ℤ, β ≠ i / j) :
    Transcendental ℚ (α ^ β) := fun hγ => by

  obtain ⟨K, hK, hNK, σ, hd, α', β', γ', habc⟩ :=
    getElemsInNF α β (α^β) hα hβ hγ

  let q : ℕ := 5

  have hq0 : 0 < q := Nat.zero_lt_succ 4

  --have use5 := use5 α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq

  --simp only at use5

  -- apply absurd main
  -- simp only [ge_iff_le, not_le]
  --exact use5
  sorry






































































































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
