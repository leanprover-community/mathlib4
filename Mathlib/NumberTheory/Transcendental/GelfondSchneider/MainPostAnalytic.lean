/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAnalytic
public import Mathlib.Analysis.Analytic.Order

/-!
# Gelfond-Schneider Theorem: the algebraic lower bound

Having isolated the first non-vanishing derivative `R⁽ʳ⁾(ℓ₀)` of the auxiliary function, this
file scales it to a non-zero algebraic integer and bounds its norm from below. Since a non-zero
algebraic integer has norm at least one, this yields the lower bound
`|N(ρ)| > c₅ ^ (-r)`, which will contradict the analytic upper bound.

## Main results

* `order_geq_n`: the order of vanishing of `R` at each point is at least `n`.
* `n_le_r`: hence `n ≤ r` for the minimal non-vanishing order `r`.
* `eq5`: the lower bound `c₅ ^ (-r) < ‖N(ρ)‖`.

## References
* Loo-Keng Hua, Introduction to Number Theory, Springer, 1982. Chapter 17.9.
-/

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section


open Set AnalyticAt AnalyticOnNhd


namespace GelfondSchneider

variable {K : Type} [Field K] (α : ℂ) (β : ℂ) (σ : K →+* ℂ) (α' : K) (β' : K) (γ' : K)
  (hirr : ∀ i j : ℤ, β ≠ i / j) (htriv : α ≠ 0 ∧ α ≠ 1)
  (habc : α = σ α' ∧ β = σ β' ∧ α ^ β = σ γ')

variable [NumberField K]

variable (q : ℕ) (hq0 : 0 < q)

variable (u : Fin (m K * n K q)) (t : Fin (q * q))

variable (h2mq : 2 * m K ∣ q ^ 2)

variable [DecidableEq (K →+* ℂ)]

include α β σ α' β' γ' hirr htriv habc in
lemma exists_nonzero_iteratedFDeriv : deriv^[r α β σ α' β' γ' hirr htriv habc q hq0 h2mq]
 (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq +
     1) ≠ 0 := by
  have Hrprop := (rProp α β σ α' β' γ' hirr htriv habc q hq0 h2mq).1
  have hA1 : AnalyticAt ℂ (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
      (↑↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1) := by fun_prop
  rw [← iteratedDeriv_eq_iterate]
  exact ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hA1).mp Hrprop).2

include α β σ α' β' γ' hirr htriv habc in
lemma ρᵣ_nonzero : ρᵣ α β σ α' β' γ' hirr htriv habc q hq0 h2mq ≠ 0 := by
  unfold ρᵣ
  simp only [zpow_neg, zpow_natCast, mul_eq_zero, inv_eq_zero,
    pow_eq_zero_iff', ne_eq, not_or, not_and, Decidable.not_not]
  refine ⟨fun hlog => ?_, exists_nonzero_iteratedFDeriv α β σ α' β' γ' hirr htriv habc q hq0 h2mq⟩
  · by_contra H
    have : Complex.log α ≠ 0 :=
      mt (fun h ↦ by simpa [exp_log htriv.1, exp_zero] using congrArg exp h) htriv.2
    apply this; exact hlog

include α β σ α' β' γ' hirr htriv habc in
lemma rho_nonzero : rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq ≠ 0 := by
  intros H
  apply_fun σ at H
  rw [rho_eq_ρᵣ] at H
  simp only [map_zero] at H
  apply ρᵣ_nonzero α β σ α' β' γ' hirr htriv habc
  exact H

include α β σ α' β' γ' hirr htriv habc in
lemma norm_Algebra_norm_rho_nonzero :
  ‖(Algebra.norm ℚ) (rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq)‖ ≠ 0 := by
  rw [norm_ne_zero_iff, Algebra.norm_ne_zero_iff]
  intros H
  apply_fun σ at H
  rw [rho_eq_ρᵣ] at H
  simp only [map_zero] at H
  apply ρᵣ_nonzero α β σ α' β' γ' hirr htriv habc q hq0 h2mq
  exact H

include α β σ α' β' γ' hirr htriv habc in
lemma c1rho_neq_0 : c1ρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq ≠ 0 := by
  intros H
  injection H with H1
  simp only [zsmul_eq_mul, mul_eq_zero, Int.cast_eq_zero] at H1
  cases H1 with
  | inl hp => apply cρ_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq; exact hp
  | inr hq =>
    apply_fun σ at hq
    rw [rho_eq_ρᵣ] at hq
    simp only [map_zero] at hq
    apply ρᵣ_nonzero α β σ α' β' γ' hirr htriv habc q hq0 h2mq
    exact hq

include α β σ α' β' γ' hirr htriv habc in
lemma house_geq_1 : 1 ≤ house (c1ρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq : K) := by
  apply one_le_house_of_isIntegral (RingOfIntegers.isIntegral_coe (c1ρ α β σ α' β' γ' hirr htriv
      habc q hq0 h2mq))
  simp only [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  rw [← ne_eq]
  exact c1rho_neq_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq

include α β σ α' β' γ' hirr htriv habc in
lemma eq5zero : 1 ≤ norm
    (Algebra.norm ℚ ((algebraMap (𝓞 K) K) (c1ρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq))) := by
  have := ρ_is_int α β σ α' β' γ' hirr htriv habc q hq0 h2mq
  have := Algebra.isIntegral_norm ℚ this
  have H1 : 0 ≤ ‖(Algebra.norm ℤ) (c1ρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq)‖ := by
    positivity
  have H2 : 0 ≠ ‖(Algebra.norm ℤ) (c1ρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq)‖ := by
    have := c1rho_neq_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq
    symm
    intros H
    apply this
    rw [norm_eq_zero] at H
    simp only [Algebra.norm_eq_zero_iff] at H
    exact H
  have : 0 < ‖(Algebra.norm ℤ) (c1ρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq)‖ := by
    exact lt_of_le_of_ne H1 H2
  rw [← Algebra.coe_norm_int] at *
  simp only [Int.norm_cast_rat, ge_iff_le] at *
  rw [← Int.norm_cast_real] at *
  simp only [Real.norm_eq_abs] at *
  norm_cast at *

/-- The constant `c₅ = (|c₁| + 1) ^ (h * (1 + 4 * m ^ 2))` used for the lower bound on `ρ`. -/
def c₅ : ℝ := ((abs (c₁ α' β' γ') + 1) ^ (((↑(h K) * (1+4 * m K^2)))))

omit [DecidableEq (K →+* ℂ)] in
lemma c5nonneg : 0 < c₅ α' β' γ' := by
    unfold c₅
    apply pow_pos
    simp only [Int.cast_abs]
    refine add_pos_of_nonneg_of_pos ?_ ?_
    · simp only [abs_nonneg]
    · simp only [zero_lt_one]

------
include α β σ α' β' γ' hirr htriv habc in
lemma order_geq_n_foo (l' : Fin (m K)) :
  (∀ k', k' < n K q → deriv^[k'] (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (l' + 1) = 0)
   → n K q ≤ analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (l' + 1) := by
  intros H
  refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (by fun_prop)).mpr ?_
  intro i hi
  rw [iteratedDeriv_eq_iterate]
  exact H i hi

include α β σ α' β' γ' hirr htriv habc in
lemma order_geq_n : ∀ l' : Fin (m K),
    n K q ≤ analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (l' + 1) := by
  intros l'
  apply order_geq_n_foo
  intros k hk
  have H := iteratedkDeriv_R_eq_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq ⟨k,hk⟩ l'
  rw [H]

include α β σ α' β' γ' hirr htriv habc in
lemma n_le_r : n K q ≤ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq := by
  have := rProp α β σ α' β' γ' hirr htriv habc q hq0 h2mq
  obtain ⟨hr,hprop⟩ := this
  have := order_geq_n α β σ α' β' γ' hirr htriv habc q hq0 h2mq (l₀' α β σ α' β' γ' hirr htriv habc
      q hq0 h2mq)
  have H : n K q ≤ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq :
      ℕ∞) → n K q ≤ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq := by
    simp only [Nat.cast_le, imp_self]
  apply H
  rw [← hr]
  apply this

include α β σ α' β' γ' hirr htriv habc in
lemma r_ne_zero : r α β σ α' β' γ' hirr htriv habc q hq0 h2mq ≠ 0 := by
  have H := n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq
  have : 0 < n K q := by
    unfold n; simp only [Nat.div_pos_iff, Nat.ofNat_pos,
    mul_pos_iff_of_pos_left]
    refine ⟨Nat.zero_lt_succ (2 * h K + 1), Nat.le_of_dvd (Nat.pow_pos hq0) h2mq⟩
  aesop

/-!so that

$$
|N(\rho)| > c_1^{-h(r+2mq)} > c_5^{-r}.
$$-/

include α β σ α' β' γ' hirr htriv habc in
lemma eq5 : c₅ α' β' γ' ^ (-(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) : ℝ) < norm (Algebra.norm
    ℚ (rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq)) := by
  simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  have h1 : 1 ≤ ‖(cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq) ^ Module.finrank ℚ K‖ *
      ‖(Algebra.norm ℚ) (rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq)‖ := by
    have := eq5zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq
    unfold c1ρ at this
    unfold RingOfIntegers.restrict at this
    simp only [zsmul_eq_mul] at this
    simp only [RingOfIntegers.map_mk, map_mul, norm_mul] at this
    have H := Algebra.norm_algebraMap (S := K)
      ((cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℤ) : ℚ)
    simp only [map_intCast] at H
    simp only [norm_pow, ge_iff_le]
    rw [H] at this
    simp only [norm_pow, Int.norm_cast_rat] at this
    exact this
  have h2 : ‖(cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq) ^ Module.finrank ℚ K‖⁻¹
    ≤ norm (Algebra.norm ℚ (rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq)) := by
    have : 0 < ‖ (cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq)^ Module.finrank ℚ K‖ := by
      rw [norm_pos_iff]
      simp only [ne_eq, pow_eq_zero_iff', not_and, Decidable.not_not]
      intros H
      by_contra H1
      apply cρ_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq
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
          have : 0 < Module.finrank ℚ K := by
            exact Module.finrank_pos
          simp_all only [norm_zero, ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [pow_zero, one_mul, zero_lt_one, lt_self_iff_false]
  calc _ = _ := ?_
       c₅ α' β' γ' ^ ((-r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℤ)) <
        abs (c₁ α' β' γ')^ ((- h K : ℤ) * (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 2 * m K *
            q) ) := ?_
       _ ≤ ‖(cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq) ^ Module.finrank ℚ K‖⁻¹ := ?_
       _ ≤ norm (Algebra.norm ℚ (rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq)) := ?_
  · simp only [zpow_neg, zpow_natCast]
  · simp only [zpow_neg, zpow_natCast, neg_mul]
    rw [inv_lt_inv₀]
    · rw [mul_add]
      have : (h K : ℤ) * r α β σ α' β' γ' hirr htriv habc q hq0 h2mq + h K
        * (2 * m K * ↑q)
          = h K * r α β σ α' β' γ' hirr htriv habc q hq0 h2mq + h K * 2 * m K * ↑q := by
        rw [mul_assoc, mul_assoc, mul_assoc]
      rw [this]
      have : ((h K : ℤ) * r α β σ α' β' γ' hirr htriv habc q hq0 h2mq + ↑(h K) * 2 * ↑(m K) * ↑q)  =
         ((h K : ℤ) * (↑(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 2 * ↑(m K) * ↑q)) :=
         by ring
      rw [this]
      dsimp [c₅]
      norm_cast
      nth_rw 2 [pow_mul]
      have :  (((abs (c₁ α' β' γ') + 1) ^ h K) ^ (1 + 4 * m K ^
          2)) ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq=
        ((abs (c₁ α' β' γ') + 1) ^ (h K * (1 + 4 * m K ^ 2) * r α β σ α' β' γ' hirr htriv habc q hq0
            h2mq)) := by
          rw [pow_mul]
          rw [pow_mul]
      rw [this]; clear this
      calc _ ≤ abs (c₁ α' β' γ') ^ (h K * (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 2 * m K *
          q^2)):= ?_
           _ ≤ abs (c₁ α' β' γ') ^ (h K * (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 4 * m K ^ 2
               * n K q)) := ?_
           _ ≤ abs (c₁ α' β' γ') ^( h K * (1 + 4 * m K ^ 2) * r α β σ α' β' γ' hirr htriv habc q hq0
               h2mq) := ?_
           _ < (abs (c₁ α' β' γ') + 1) ^ (h K * (1 + 4 * m K ^ 2) * r α β σ α' β' γ' hirr htriv habc
               q hq0 h2mq) := ?_
      · refine pow_le_pow_right₀ ?_ ?_
        · exact one_le_abs_c₁ α' β' γ'
        · simp only [mul_assoc]
          refine Nat.mul_le_mul (le_refl _) ?_
          · rw [q_sq_eq_two_mn q h2mq]
            simp only [add_le_add_iff_left, Nat.ofNat_pos, mul_le_mul_iff_right₀]
            refine Nat.mul_le_mul (le_refl _) ?_
            · trans
              · have : q ≤ q^2 := by
                 refine Nat.le_pow ?_
                 simp only [Nat.ofNat_pos]
                apply this
              · rw [q_sq_eq_two_mn q h2mq]
      · simp only [mul_assoc]
        refine pow_le_pow_right₀ ?_ ?_
        · exact one_le_abs_c₁ α' β' γ'
        · refine Nat.mul_le_mul (le_refl _) ?_
          · rw [q_sq_eq_two_mn q h2mq]
            simp only [add_le_add_iff_left]
            have : 2 * (m K * (2 * m K * n K q))=
              4 * m K ^ 2 * n K q := by
              rw [mul_assoc, mul_assoc]
              ring
            rw [this]
            simp only [mul_assoc,le_refl]
      · rw [mul_add]
        rw [mul_add]
        rw [add_mul]
        simp only [mul_one]
        refine pow_le_pow_right₀ ?_ ?_
        · exact one_le_abs_c₁ α' β' γ'
        · simp only [add_le_add_iff_left]
          simp only [mul_assoc]
          refine Nat.mul_le_mul (le_refl _) ?_
          · simp only [Nat.ofNat_pos, mul_le_mul_iff_right₀]
            refine Nat.mul_le_mul (le_refl _) ?_
            · exact n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq
      · refine pow_lt_pow_left₀ ?_ ?_ ?_
        · simp only [lt_add_iff_pos_right, zero_lt_one]
        · simp only [abs_nonneg]
        · intros H
          simp only [mul_eq_zero, Nat.add_eq_zero_iff,
            one_ne_zero, OfNat.ofNat_ne_zero,
            Nat.pow_eq_zero, ne_eq, not_false_eq_true, and_true,
             false_or, false_and, or_false] at H
          rcases H with h1 | h2
          · have : 0 ≠ h K := by
              symm; apply Nat.pos_iff_ne_zero.mp
              dsimp [h]
              exact Module.finrank_pos
            apply this
            exact h1.symm
          · apply r_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq
            exact h2
    · unfold c₅
      trans
      · have : (0 : ℝ) < 1 := by simp only [zero_lt_one]
        apply this
      · apply one_lt_pow₀
        · refine one_lt_pow₀ ?_ ?_
          · simp only [Int.cast_abs, lt_add_iff_pos_left, abs_pos, ne_eq, Int.cast_eq_zero]
            rw [← ne_eq]
            exact c₁_ne_zero α' β' γ'
          · simp only [ne_eq, mul_eq_zero, Nat.add_eq_zero_iff, one_ne_zero, OfNat.ofNat_ne_zero,
            Nat.pow_eq_zero, not_false_eq_true, and_true, false_or, false_and, or_false]
            · unfold h
              have : 0 < Module.finrank ℚ K := Module.finrank_pos
              simp_all only [norm_pow, ne_eq]
              apply Aesop.BuiltinRules.not_intro
              intro a
              simp_all only [pow_zero, one_mul, inv_one, lt_self_iff_false]
        · exact r_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq
    · have : 1 ≤ abs (c₁ α' β' γ') ^ (↑(h K) *
       ((↑(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)) + 2 * ↑(m K) * (↑q))) := by
        refine one_le_pow₀ ?_
        have : 1 ≤ c₁ α' β' γ' := one_le_c₁ α' β' γ'
        exact one_le_abs_c₁ α' β' γ'
      calc (0 : ℝ) < 1 := by simp only [zero_lt_one]
           (1 : ℝ) ≤ abs (c₁ α' β' γ') ^ (↑(h K) *
           ((↑(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)) + 2 * ↑(m K) * (↑q))) := mod_cast this
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
      · exact mod_cast (le_trans Int.one_nonneg (one_le_c₁ α' β' γ'))
    · rw [lt_iff_le_and_ne]
      refine ⟨mod_cast (le_trans Int.one_nonneg (one_le_c₁ α' β' γ')), fun H ↦ ?_⟩
      · apply c₁_ne_zero α' β' γ'
        symm
        exact mod_cast H
  · exact h2

include α β σ α' β' γ' hirr htriv habc in
lemma c_coeffspow_r :
  ((c₁ α' β' γ') ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) * (c₁ α' β' γ') ^ (m K * q) * (c₁
      α' β' γ') ^ (m K * q)) =
  ((c₁ α' β' γ') ^ ((r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)) *
  (c₁ α' β' γ') ^ (m K * q - (a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1))) *
  (c₁ α' β' γ') ^ (m K * q - ((b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1))))) •
  (c₁ α' β' γ') ^ (a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1)) *
  (c₁ α' β' γ') ^ (b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1)) := by
    rw [← one_mul (c₁ α' β' γ' ^ (a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℕ) +
        1)))]
    have triple_comm_int (a b c : ℤ) (x y z : ℤ) :
      ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
     simp only [zsmul_eq_mul, Int.cast_mul]; ring
    simp only [mul_assoc]
    rw [ smul_mul_assoc
          (c₁ α' β' γ' ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq *
            (c₁ α' β' γ' ^ (m K * q - a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) +
                1)) *
              c₁ α' β' γ' ^ (m K * q - b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) +
                  1))))
          (1 * c₁ α' β' γ' ^ (a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1)))
          (c₁ α' β' γ' ^ (b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1)))]
    rw [Int.mul_assoc 1 (c₁ α' β' γ' ^ (a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) +
        1)))
          (c₁ α' β' γ' ^ (b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1)))]
    simp only [← mul_assoc]
    rw [triple_comm_int]
    congr
    · simp only [Int.zsmul_eq_mul, mul_one]
    · simp only [smul_eq_mul]
      rw [← pow_add]
      have : (m K * q - (a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1))
      + (a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1))) = (m K * q) := by
        rw [add_comm]
        refine add_tsub_cancel_of_le ?_
        rw [mul_comm (m K)]
        apply mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt) ?_ (Nat.zero_le _) (Nat.zero_le
            _)
        · exact (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq).isLt
      rw [this]
    · simp only [smul_eq_mul]
      rw [← pow_add]
      have : (m K * q - (b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1))
        + (b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1))) = (m K * q) := by
        rw [add_comm]
        refine add_tsub_cancel_of_le ?_
        rw [mul_comm (m K)]
        apply mul_le_mul (((finProdFinEquiv.symm.toFun t).2).isLt) ?_ (Nat.zero_le _) (Nat.zero_le
            _)
        · exact (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq).isLt
      rw [this]

end GelfondSchneider

end
