/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAnalytic
public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.AnalyticPart

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q))
 (t : Fin (q * q)) [DecidableEq (h7.K →+* ℂ)] (h2mq : 2 * h7.m ∣ q ^ 2)

open Set AnalyticAt AnalyticOnNhd


namespace Setup

lemma exists_nonzero_iteratedFDeriv : deriv^[h7.r q hq0 h2mq]
 (h7.R q hq0 h2mq) (h7.l₀' q hq0 h2mq + 1) ≠ 0 := by
  have Hrprop := (h7.r_prop q hq0 h2mq).1
  obtain ⟨l₀, y, r, h1, h2⟩ := (h7.exists_min_analyticOrderAt q hq0 h2mq)
  have hA1 : AnalyticAt ℂ (h7.R q hq0 h2mq) (↑↑(h7.l₀' q hq0 h2mq) + 1) := by fun_prop
  grind [analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero hA1]

lemma ρᵣ_nonzero : ρᵣ h7 q hq0 h2mq ≠ 0 := by
  unfold ρᵣ
  simp only [zpow_neg, zpow_natCast, mul_eq_zero, inv_eq_zero,
    pow_eq_zero_iff', ne_eq, not_or, not_and, Decidable.not_not]
  refine ⟨fun hlog => ?_, h7.exists_nonzero_iteratedFDeriv q hq0 h2mq⟩
  · by_contra H
    have : Complex.log h7.α ≠ 0 :=
      mt (fun h ↦ by simpa [exp_log h7.htriv.1, exp_zero] using congrArg exp h) h7.htriv.2
    apply this; exact hlog

lemma rho_nonzero : rho h7 q hq0 h2mq ≠ 0 := by
  intros H
  apply_fun h7.σ at H
  rw [rho_eq_ρᵣ] at H
  simp only [map_zero] at H
  apply h7.ρᵣ_nonzero
  exact H

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
  cases H1 with
  | inl hp => apply cρ_ne_zero h7 q hq0 h2mq; exact hp
  | inr hq =>
    apply_fun h7.σ at hq
    rw [rho_eq_ρᵣ] at hq
    simp only [map_zero] at hq
    apply ρᵣ_nonzero h7 q hq0 h2mq
    exact hq

lemma house_geq_1 : 1 ≤ house (h7.c1ρ q hq0 h2mq : h7.K) := by
  apply one_le_house_of_isIntegral (RingOfIntegers.isIntegral_coe (h7.c1ρ q hq0 h2mq))
  simp only [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  rw [← ne_eq]
  exact c1rho_neq_0 h7 q hq0 h2mq

lemma eq5zero : 1 ≤ norm
    (Algebra.norm ℚ ((algebraMap (𝓞 h7.K) h7.K) (h7.c1ρ q hq0 h2mq))) := by
  have := ρ_is_int h7 q hq0 h2mq
  have := Algebra.isIntegral_norm ℚ this
  have H1 : 0 ≤ ‖(Algebra.norm ℤ) (h7.c1ρ q hq0 h2mq)‖ := by
    positivity
  have H2 : 0 ≠ ‖(Algebra.norm ℤ) (h7.c1ρ q hq0 h2mq)‖ := by
    have := c1rho_neq_0 h7 q hq0 h2mq
    symm
    intros H
    apply this
    rw [norm_eq_zero] at H
    simp only [Algebra.norm_eq_zero_iff] at H
    exact H
  have : 0 < ‖(Algebra.norm ℤ) (h7.c1ρ q hq0 h2mq)‖ := by
    exact lt_of_le_of_ne H1 H2
  rw [← Algebra.coe_norm_int] at *
  simp only [Int.norm_cast_rat, ge_iff_le] at *
  rw [← Int.norm_cast_real] at *
  simp only [Real.norm_eq_abs] at *
  norm_cast at *

def c₅ : ℝ := ((abs (h7.c₁) + 1) ^ (((↑(h7.h) * (1+4 * h7.m^2)))))

omit [DecidableEq (h7.K →+* ℂ)] in
lemma c5nonneg : 0 < h7.c₅ := by
    unfold c₅
    apply pow_pos
    simp only [Int.cast_abs]
    refine add_pos_of_nonneg_of_pos ?_ ?_
    · simp only [abs_nonneg]
    · simp only [zero_lt_one]

------
lemma order_geq_n_foo (l' : Fin (h7.m)) :
  (∀ k', k' < h7.n q → deriv^[k'] (h7.R q hq0 h2mq) (l' + 1) = 0)
   → h7.n q ≤ analyticOrderAt (h7.R q hq0 h2mq) (l' + 1) := by
  intros H
  apply le_analyticOrderAt_iff_iteratedDeriv_eq_zero
  · fun_prop
  · apply order_neq_top h7 q hq0 h2mq l'
  exact H

lemma order_geq_n : ∀ l' : Fin (h7.m),
    h7.n q ≤ analyticOrderAt (h7.R q hq0 h2mq) (l' + 1) := by
  intros l'
  apply order_geq_n_foo
  intros k hk
  have H := h7.iteratedkDeriv_R_eq_zero q hq0 h2mq ⟨k,hk⟩ l'
  rw [H]

lemma n_le_r : h7.n q ≤ h7.r q hq0 h2mq := by
  have := h7.r_prop q hq0 h2mq
  obtain ⟨hr,hprop⟩ := this
  have := h7.order_geq_n q hq0 h2mq (h7.l₀' q hq0 h2mq)
  have H : h7.n q ≤ (h7.r q hq0 h2mq : ℕ∞) → h7.n q ≤ h7.r q hq0 h2mq := by
    simp only [Nat.cast_le, imp_self]
  apply H
  rw [← hr]
  apply this

lemma r_ne_zero : h7.r q hq0 h2mq ≠ 0 := by
  have H := n_le_r h7 q hq0 h2mq
  have : 0 < h7.n q := by
    unfold n; simp only [Nat.div_pos_iff, Nat.ofNat_pos,
    mul_pos_iff_of_pos_left]
    refine ⟨Nat.zero_lt_succ (2 * h7.h + 1), Nat.le_of_dvd (Nat.pow_pos hq0) h2mq⟩
  aesop

/-!so that

$$
|N(\rho)| > c_1^{-h(r+2mq)} > c_5^{-r}.
$$-/

lemma eq5 : h7.c₅ ^ (-(h7.r q hq0 h2mq) : ℝ) < norm (Algebra.norm ℚ (rho h7 q hq0 h2mq)) := by
  simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  have h1 : 1 ≤ ‖(h7.cρ q hq0 h2mq) ^ Module.finrank ℚ h7.K‖ *
      ‖(Algebra.norm ℚ) (rho h7 q hq0 h2mq)‖ := by
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
    exact this
  have h2 : ‖(h7.cρ q hq0 h2mq) ^ Module.finrank ℚ h7.K‖⁻¹
    ≤ norm (Algebra.norm ℚ (rho h7 q hq0 h2mq)) := by
    have : 0 < ‖ (h7.cρ q hq0 h2mq)^ Module.finrank ℚ h7.K‖ := by
      rw [norm_pos_iff]
      simp only [ne_eq, pow_eq_zero_iff', not_and, Decidable.not_not]
      intros H
      by_contra H1
      apply h7.cρ_ne_zero q hq0 h2mq
      exact H
    rw [← mul_le_mul_iff_right₀ this]
    · rw [mul_inv_cancel₀]
      · simp_all only [norm_pow]
      · simp only [norm_pow, ne_eq, pow_eq_zero_iff', norm_eq_zero,
          not_and, Decidable.not_not]
        intros H
        rw [H] at this
        simp only [norm_pow, norm_zero] at this
        rw [zero_pow] at this
        · by_contra H1
          simp_all only [norm_pow, lt_self_iff_false]
        · simp_all only [norm_pow]
          have : 0 < Module.finrank ℚ h7.K := by
            exact Module.finrank_pos
          simp_all only [norm_zero, ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [pow_zero, one_mul, zero_lt_one, lt_self_iff_false]
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
        ((abs (h7.c₁) + 1) ^ (h7.h * (1 + 4 * h7.m ^ 2) * h7.r q hq0 h2mq)) := by
          rw [pow_mul]
          rw [pow_mul]
      rw [this]; clear this
      calc _ ≤ abs (h7.c₁) ^ (h7.h * (h7.r q hq0 h2mq + 2 * h7.m * q^2)):= ?_
           _ ≤ abs (h7.c₁) ^ (h7.h * (h7.r q hq0 h2mq + 4 * h7.m ^ 2 * h7.n q)) := ?_
           _ ≤ abs (h7.c₁) ^( h7.h * (1 + 4 * h7.m ^ 2) * h7.r q hq0 h2mq) := ?_
           _ < (abs (h7.c₁) + 1) ^ (h7.h * (1 + 4 * h7.m ^ 2) * h7.r q hq0 h2mq) := ?_
      · refine pow_le_pow_right₀ ?_ ?_
        · exact one_le_abs_c₁ h7
        · simp only [mul_assoc]
          refine Nat.mul_le_mul (le_refl _) ?_
          · rw [q_sq_eq_two_mn h7 q h2mq]
            simp only [add_le_add_iff_left, Nat.ofNat_pos, mul_le_mul_iff_right₀]
            refine Nat.mul_le_mul (le_refl _) ?_
            · trans
              · have : q ≤ q^2 := by
                 refine Nat.le_pow ?_
                 simp only [Nat.ofNat_pos]
                apply this
              · rw [q_sq_eq_two_mn h7 q h2mq]
      · simp only [mul_assoc]
        refine pow_le_pow_right₀ ?_ ?_
        · exact one_le_abs_c₁ h7
        · refine Nat.mul_le_mul (le_refl _) ?_
          · rw [q_sq_eq_two_mn h7 q h2mq]
            simp only [add_le_add_iff_left]
            have : 2 * (h7.m * (2 * h7.m * h7.n q))=
              4 * h7.m ^ 2 * h7.n q := by
              rw [mul_assoc, mul_assoc]
              ring
            rw [this]
            simp only [mul_assoc,le_refl]
      · rw [mul_add]
        rw [mul_add]
        rw [add_mul]
        simp only [mul_one]
        refine pow_le_pow_right₀ ?_ ?_
        · exact one_le_abs_c₁ h7
        · simp only [add_le_add_iff_left]
          simp only [mul_assoc]
          refine Nat.mul_le_mul (le_refl _) ?_
          · simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
            refine Nat.mul_le_mul (le_refl _) ?_
            · exact n_le_r h7 q hq0 h2mq
      · refine pow_lt_pow_left₀ ?_ ?_ ?_
        · simp only [lt_add_iff_pos_right, zero_lt_one]
        · simp only [abs_nonneg]
        · intros H
          simp only [mul_eq_zero, Nat.add_eq_zero_iff,
            one_ne_zero, OfNat.ofNat_ne_zero,
            Nat.pow_eq_zero, ne_eq, not_false_eq_true, and_true,
             false_or, false_and, or_false] at H
          rcases H with h1 | h2
          · have : 0 ≠ h7.h := by
              symm ;apply Nat.pos_iff_ne_zero.mp
              dsimp [h]
              exact Module.finrank_pos
            apply this
            exact h1.symm
          · apply r_ne_zero h7 q hq0 h2mq
            exact h2
    · unfold c₅
      trans
      · have : (0 : ℝ) < 1 := by simp only [zero_lt_one]
        apply this
      · apply one_lt_pow₀
        · refine one_lt_pow₀ ?_ ?_
          · simp only [Int.cast_abs, lt_add_iff_pos_left, abs_pos, ne_eq, Int.cast_eq_zero]
            rw [← ne_eq]
            exact c₁_ne_zero h7
          · simp only [ne_eq, mul_eq_zero, Nat.add_eq_zero_iff, one_ne_zero, OfNat.ofNat_ne_zero,
            Nat.pow_eq_zero, not_false_eq_true, and_true, false_or, false_and, or_false]
            · unfold h
              have : 0 < Module.finrank ℚ h7.K := Module.finrank_pos
              simp_all only [norm_pow, ne_eq]
              apply Aesop.BuiltinRules.not_intro
              intro a
              simp_all only [pow_zero, one_mul, inv_one, lt_self_iff_false]
        · exact r_ne_zero h7 q hq0 h2mq
    · have : 1 ≤ abs (h7.c₁) ^ (↑(h7.h) *
       ((↑(h7.r q hq0 h2mq)) + 2 * ↑(h7.m) * (↑q))) := by
        refine one_le_pow₀ ?_
        have : 1 ≤ h7.c₁ := h7.one_le_c₁
        exact one_le_abs_c₁ h7
      calc (0 : ℝ) < 1 := by simp only [zero_lt_one]
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
    · rw [← Real.rpow_mul]
      · rw [mul_comm]
        norm_cast
        simp only [Int.cast_pow, Int.cast_abs, abs_pow]
        unfold h
        simp only [le_refl]
      · exact mod_cast (le_trans Int.one_nonneg (h7.one_le_c₁))
    · rw [lt_iff_le_and_ne]
      refine ⟨mod_cast (le_trans Int.one_nonneg (h7.one_le_c₁)), fun H ↦ ?_⟩
      · apply c₁_ne_zero h7
        symm
        exact mod_cast H
  · exact h2

lemma c_coeffspow_r :
  ((h7.c₁) ^ (h7.r q hq0 h2mq) * (h7.c₁) ^ (h7.m * q) * (h7.c₁) ^ (h7.m * q)) =
  ((h7.c₁) ^ ((h7.r q hq0 h2mq)) *
  (h7.c₁) ^ (h7.m * q - (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))) *
  (h7.c₁) ^ (h7.m * q - ((b q t * (↑(h7.l₀' q hq0 h2mq) + 1))))) •
  (h7.c₁) ^ (a q t * (↑(h7.l₀' q hq0 h2mq) + 1)) *
  (h7.c₁) ^ (b q t * (↑(h7.l₀' q hq0 h2mq) + 1)) := by
    rw [← one_mul (h7.c₁ ^ (a q t * (↑(h7.l₀' q hq0 h2mq : ℕ) + 1)))]
    have triple_comm_int (a b c : ℤ) (x y z : ℤ) :
      ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
     simp only [zsmul_eq_mul, Int.cast_mul]; ring
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
    rw [triple_comm_int]
    congr
    · simp only [Int.zsmul_eq_mul, mul_one]
    · simp only [smul_eq_mul]
      rw [← pow_add]
      have : (h7.m * q - (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))
      + (a q t * (↑(h7.l₀' q hq0 h2mq) + 1))) = (h7.m * q) := by
        rw [add_comm]
        refine add_tsub_cancel_of_le ?_
        rw [mul_comm h7.m]
        apply mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt) ?_ (zero_le _) (zero_le _)
        · exact (h7.l₀' q hq0 h2mq).isLt
      rw [this]
    · simp only [smul_eq_mul]
      rw [← pow_add]
      have : (h7.m * q - (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))
        + (b q t * (↑(h7.l₀' q hq0 h2mq) + 1))) = (h7.m * q) := by
        rw [add_comm]
        refine add_tsub_cancel_of_le ?_
        rw [mul_comm h7.m]
        apply mul_le_mul (((finProdFinEquiv.symm.toFun t).2).isLt) ?_ (zero_le _) (zero_le _)
        · exact (h7.l₀' q hq0 h2mq).isLt
      rw [this]

end Setup

end
