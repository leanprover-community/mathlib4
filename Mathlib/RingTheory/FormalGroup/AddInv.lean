/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic

/-! # Formal group laws over commutative ring

We define the additive inverse under the formal group $F$ sense, namely the power series $i(X)$
such that $F(X, i(X)) = F(i(X),X) = 0$.

## Main definitions/lemmas

* The power series `addInv_X`, which is the additive inverse of `X` under formal group $F$ sense,
namely, $F(X, i (X)) = 0$.

## References
* [Hazewinkel, Michiel. «Formal Groups and Applications»]

-/

@[expose] public section

noncomputable section

namespace FormalGroup

variable {R σ : Type*} [CommRing R] (f g : PowerSeries R) (F : FormalGroup R)
  (φ : MvPowerSeries (Fin 2) R) (n : ℕ)

open PowerSeries Finset Fin Finsupp

/-- Inductive definition of the power series $i(X)$ such that $F(X,i(X)) = 0$. -/
abbrev addInv_aux (F : FormalGroup R) : ℕ → R
  | 0 => 0
  | 1 => -1
  | n + 1 => - (coeff (n + 1) (F.toFun.subst
    ![X, (∑ i : Fin (n + 1), C (addInv_aux F i.1) * X ^ i.1)]))

@[simp]
lemma addInv_aux_zero : addInv_aux F 0 = 0 := rfl

@[simp]
lemma addInv_aux_one : addInv_aux F 1 = -1 := rfl

/-- Given a formal group law `F` over coefficient ring `R`, there exist unique power series `i(X)`,
such that `F(X, i(X)) = 0`. -/
def addInv_X : PowerSeries R := .mk (addInv_aux F ·)

@[simp]
lemma constantCoeff_addInv_X : constantCoeff (addInv_X F) = 0 := rfl

@[simp]
lemma coeff_one_addInv_X : coeff 1 (addInv_X F) = -1 := by
  simp only [addInv_X, coeff_mk]; rfl

lemma _root_.MvPowerSeries.HasSubst.addInv_aux : MvPowerSeries.HasSubst ![X, (addInv_X F)] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by fin_cases x <;> simp

lemma addInv_trunc_aux :
    trunc (n + 1) (addInv_X F) =
      ∑ i : Fin (n + 1), Polynomial.C (addInv_aux F i.1) * Polynomial.X ^ i.1 := by
  induction n with
  | zero => simp [addInv_X]
  | succ k ih =>
    simp only [trunc_apply, Nat.Ico_zero_eq_range, Fin.sum_univ_eq_sum_range
      (fun i => (Polynomial.C (R := R)) (addInv_aux F i) * Polynomial.X ^ i)] at ⊢ ih
    rw [Finset.sum_range_add, ih]
    conv_rhs => rw [Finset.sum_range_add]
    simp [Polynomial.C_mul_X_pow_eq_monomial, addInv_X]

lemma coeff_subst_addInv_trunc (hn : n ≠ 0) :
    coeff n (F.toFun.subst ![X, (addInv_X F)]) =
      coeff n (F.toFun.subst ![X, (trunc (n + 1) (addInv_X F))]) := by
  have : trunc (n + 1) X = Polynomial.X (R := R):= trunc_X_of <| by omega
  rw [trunc_subst_trunc_add_one (MvPowerSeries.HasSubst.addInv_aux F)]
  congr! 3 with i
  fin_cases i <;>  simp [this]

lemma _root_.MvPowerSeries.HasSubst.X_zero : MvPowerSeries.HasSubst ![X (R := R), 0] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by simp)

lemma _root_.MvPowerSeries.HasSubst.addInv_fin :
    MvPowerSeries.HasSubst ![X, (∑ (i ∈ range (n + 1)), Polynomial.C (F.addInv_aux i) *
      Polynomial.X (R := R) ^ i).toPowerSeries] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by simp)

lemma coeff_n_aux (n : ℕ) :
  (coeff n) (F.toFun.subst ![X, (∑ (i : Fin (n + 1)), Polynomial.C (F.addInv_aux i.1) *
    Polynomial.X (R := R) ^ i.1).toPowerSeries]) = 0 := by
  rw [sum_univ_eq_sum_range fun i => (Polynomial.C (F.addInv_aux i) * Polynomial.X (R := R) ^ i)]
  induction n with
  | zero =>
    simp [constantCoeff, MvPowerSeries.constantCoeff_subst_eq_zero MvPowerSeries.HasSubst.X_zero
      (by simp) F.zero_constantCoeff]
  | succ k ih =>
    by_cases hk : k = 0
    · rw [hk, show range 2 = {0, 1} by rfl, coeff, MvPowerSeries.coeff_subst
        (MvPowerSeries.hasSubst_of_constantCoeff_zero <| by simp)]
      · rw [finsum_eq_finset_sum_of_support_subset (s := {single 0 1, single 1 1}),
          sum_pair (ne_iff.mpr ⟨0, by simp⟩)]
        · simp [F.lin_coeff_X, F.lin_coeff_Y]
        have (x : Fin 2 →₀ ℕ) (h : ¬(MvPowerSeries.coeff x) F.toFun
          * (coeff 1) (X ^ x 0 * (-X) ^ x 1) = 0) : x = single 0 1 ∨ x = single 1 1 := by
          rw [neg_pow, coeff_X_pow_mul', coeff_mul_X_pow'] at h
          simp only [isValue, mul_ite, mul_zero, ite_eq_right_iff, Classical.not_imp] at h
          have : x 0 + x 1 ≤ 1 := by omega
          have x_one_le : x 1 ≤ 1 := Nat.le_of_add_left_le this
          by_cases hx₀ : x 0 = 0
          · by_cases hx₁ : x 1 = 0
            · have x_eq_zero : x = 0 := by ext n; fin_cases n <;> simpa
              simp [x_eq_zero] at h
            right; ext n; fin_cases n <;> grind
          · -- the cases x 0 ≠ 0
            have hx₀' : x 0 = 1 := by omega
            by_cases hx₁ : x 1 = 0
            · left; ext n; fin_cases n <;> simpa
            omega
        simpa
    simp_rw [coeff, MvPowerSeries.coeff_subst (MvPowerSeries.HasSubst.addInv_fin F (k + 1)),
      coeff_coe]
    generalize hB : (∑ i ∈ range (k + 1), Polynomial.C (F.addInv_aux i) * Polynomial.X ^ i) = B
    have coeff_B : B.coeff 0 = 0 := by simp [← hB]
    calc
      _ = ∑ᶠ (d : Fin 2 →₀ ℕ), (MvPowerSeries.coeff d) F.toFun * (coeff (k + 1))
          (X ^ d 0 * (↑B + C (F.addInv_aux (k + 1)) * X ^ (k + 1)) ^ d 1) := by
        simp [sum_range_add, hB]
      _ = _ := by
        have eq_aux {d : Fin 2 →₀ ℕ} : (coeff (k + 1)) (X ^ d 0 *
          (B.toPowerSeries + C (addInv_aux F (k + 1)) * X ^ (k + 1)) ^ d 1) =
            (coeff (k + 1)) (X ^ d 0 * B.toPowerSeries ^ d 1)
              + if d = single 1 1 then (addInv_aux F (k + 1)) else 0 := by
          rw [coeff_X_pow_mul', coeff_X_pow_mul']
          by_cases hd : d = single 1 1
          · simp [hd]
          rw [if_neg hd, add_zero]
          by_cases hd_le : d 0 ≤ k + 1
          · simp_rw [if_pos hd_le, add_pow, map_sum]
            rw [Finset.sum_eq_single (d 1) _ (by simp)]
            · simp
            · intro i hi_mem hi
              rw [mul_pow, mul_assoc, mul_assoc, mul_comm ((X ^ (k + 1)) ^ (d 1 - i)),
                ← mul_assoc, ← mul_assoc, ← pow_mul, coeff_mul_X_pow']
              by_cases! hd₀ : d 0 = 0 ∧ d 1 - i = 1
              · have i_ne_zero : i ≠ 0 := by grind
                simp [hd₀, coeff_B, zero_pow i_ne_zero]
              have : k + 1 ≤ (k + 1) * (d 1 - i) := by
                simp only [isValue, mem_range, Order.lt_add_one_iff, _root_.zero_le,
                  le_mul_iff_one_le_right] at ⊢ hi_mem
                omega
              rw [if_neg _]
              by_cases hd₀' : d 0 = 0
              · have aux : (k + 1) * 2 ≤ (k + 1) * (d 1 - i) :=
                  Nat.mul_le_mul_left _ (by grind only [= mem_range])
                omega
              omega
          simp_rw [if_neg hd_le]
        have Beq : B.toPowerSeries = ∑ i ∈ range (k + 1), C (F.addInv_aux i) * X ^ i := by
          ext n; simp [← hB]
        simp_rw [eq_aux, mul_add]
        rw [finsum_add_distrib]
        · nth_rw 2 [finsum_eq_single _ (single 1 1) fun d hd => by rw [if_neg hd, mul_zero]]
          · rw [if_pos rfl, F.lin_coeff_Y, one_mul, addInv_aux]
            · simp [sum_univ_eq_sum_range (fun i => (C (addInv_aux F i) * X ^ i)), ← Beq,
                coeff, MvPowerSeries.coeff_subst (hB ▸ MvPowerSeries.HasSubst.addInv_fin F k)]
            · exact hk
        · obtain h := MvPowerSeries.coeff_subst_finite
            (MvPowerSeries.HasSubst.addInv_fin F k) F.toFun
          simp only [Nat.succ_eq_add_one, Nat.reduceAdd, hB, Finsupp.prod_pow, prod_univ_two,
            isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
            smul_eq_mul] at h
          exact h _
        refine Set.Finite.subset (Set.finite_singleton (single 1 1))
          (Function.support_subset_iff'.mpr fun d hd => ?_)
        simp only [isValue, Set.mem_singleton_iff] at hd
        simp [hd]

/- Given a formal group law `F` over coefficient ring `R`, there exist a power series
`addInv_X F`, such that `F(X, (addInv_X F)) = 0`. -/
theorem subst_addInv_eq_zero : F.toFun.subst ![X, (addInv_X F)] = 0 := by
  ext n
  by_cases hn : n = 0
  · simp [hn, constantCoeff, MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.HasSubst.addInv_aux F) (by simp) F.zero_constantCoeff]
  rw [coeff_subst_addInv_trunc _ _ hn, addInv_trunc_aux, coeff_n_aux, map_zero]

end FormalGroup
