/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic

/-! # Formal group laws over commutative ring

We define the additive inverse under the formal group $F$ sense, namely the power series $i(X)$
such that $F(i(X), X) = F(X, i(X)) = 0$.

## Main definitions/lemmas

* The power series `addInvX`, which is the additive inverse of `X` under formal group $F$ sense,
namely, $F(i(X), X) = 0$.

## References
* [Hazewinkel, Michiel. «Formal Groups and Applications»]

-/

@[expose] public section

noncomputable section

namespace FormalGroup

variable {R σ : Type*} [CommRing R] (f g : PowerSeries R) (F : FormalGroup R) (n : ℕ)

open PowerSeries Finset Fin Finsupp

/-- Inductive definition of the power series $i(X)$ such that $F(i(X),X) = 0$. -/
abbrev addInvAux (F : FormalGroup R) : ℕ → R
  | 0 => 0
  | 1 => -1
  | n + 1 => - (coeff (n + 1) (F.toPowerSeries.subst
    ![(∑ i : Fin (n + 1), C (addInvAux F i.1) * X ^ i.1), X]))

@[simp]
lemma addInvAux_zero : addInvAux F 0 = 0 := rfl

@[simp]
lemma addInvAux_one : addInvAux F 1 = -1 := rfl

/-- The defining recursion for `addInvAux`, valid uniformly in `k` (including `k = 0`). -/
lemma addInvAux_succ (k : ℕ) : addInvAux F (k + 1) = -coeff (k + 1)
    (F.toPowerSeries.subst ![∑ i ∈ range (k + 1), C (addInvAux F i) * X ^ i, X]) := by
  obtain _ | k := k
  · simp [zeroX_eq_X]
  · rw [addInvAux, sum_univ_eq_sum_range fun i => C (addInvAux F i) * X ^ i]
    simp

/-- Given a formal group law `F` over coefficient ring `R`, there exist unique power series `i(X)`,
such that `F(i(X), X) = 0`. -/
def addInvX : PowerSeries R := .mk (addInvAux F ·)

@[simp]
lemma constantCoeff_addInvX : constantCoeff (addInvX F) = 0 := rfl

@[simp]
lemma coeff_one_addInvX : coeff 1 (addInvX F) = -1 := by
  simp only [addInvX, coeff_mk]; rfl

lemma _root_.MvPowerSeries.HasSubst.addInvAux : MvPowerSeries.HasSubst ![(addInvX F), X] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by fin_cases x <;> simp [← constantCoeff_eq]

lemma addInv_trunc_aux :
    trunc (n + 1) (addInvX F) =
      ∑ i : Fin (n + 1), Polynomial.C (addInvAux F i.1) * Polynomial.X ^ i.1 := by
  induction n with
  | zero => simp [addInvX]
  | succ k ih =>
    simp only [trunc_apply, Nat.Ico_zero_eq_range, Fin.sum_univ_eq_sum_range
      (fun i => (Polynomial.C (R := R)) (addInvAux F i) * Polynomial.X ^ i)] at ⊢ ih
    rw [Finset.sum_range_add, ih]
    conv_rhs => rw [Finset.sum_range_add]
    simp [Polynomial.C_mul_X_pow_eq_monomial, addInvX]

lemma coeff_subst_addInv_trunc (hn : n ≠ 0) :
    coeff n (F.toPowerSeries.subst ![(addInvX F), X]) =
      coeff n (F.toPowerSeries.subst ![(trunc (n + 1) (addInvX F)), X]) := by
  have : trunc (n + 1) X = Polynomial.X (R := R) := trunc_X_of <| by omega
  rw [trunc_subst_trunc_add_one (MvPowerSeries.HasSubst.addInvAux F)]
  congr! 3 with i
  fin_cases i <;> simp [this]

lemma _root_.MvPowerSeries.HasSubst.addInv_fin :
    MvPowerSeries.HasSubst ![(∑ (i ∈ range (n + 1)), Polynomial.C (F.addInvAux i) *
      Polynomial.X (R := R) ^ i).toPowerSeries, X] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by simp [← constantCoeff_eq])

/-- Substituting the degree `≤ n` truncation of `i(X)` into the first variable of `F` kills the
`n`-th coefficient: this is exactly what the recursion defining `addInvAux` was set up to do. -/
lemma coeff_subst_sum_C_addInvAux_mul_X_pow (n : ℕ) :
    (coeff n) (F.toPowerSeries.subst ![(∑ (i : Fin (n + 1)), Polynomial.C (F.addInvAux i.1) *
      Polynomial.X (R := R) ^ i.1).toPowerSeries, X]) = 0 := by
  rw [sum_univ_eq_sum_range fun i => (Polynomial.C (F.addInvAux i) * Polynomial.X (R := R) ^ i)]
  obtain _ | k := n
  · simp [zeroX_eq_X]
  · simp_rw [coeff, MvPowerSeries.coeff_subst (MvPowerSeries.HasSubst.addInv_fin F (k + 1)),
      coeff_coeToMvPowerSeries]
    generalize hB : (∑ i ∈ range (k + 1), Polynomial.C (F.addInvAux i) * Polynomial.X ^ i) = B
    have coeff_B : B.coeff 0 = 0 := by simp [← hB]
    calc
      _ = ∑ᶠ (d : Fin 2 →₀ ℕ), (MvPowerSeries.coeff d) F * (coeff (k + 1))
          ((↑B + C (F.addInvAux (k + 1)) * X ^ (k + 1)) ^ d 0 * X ^ d 1) := by
        simp [sum_range_add, hB]
      _ = _ := by
        have eq_aux {d : Fin 2 →₀ ℕ} : (coeff (k + 1))
          ((B.toPowerSeries + C (addInvAux F (k + 1)) * X ^ (k + 1)) ^ d 0 * X ^ d 1) =
            (coeff (k + 1)) (B.toPowerSeries ^ d 0 * X ^ d 1)
              + if d = single 0 1 then (addInvAux F (k + 1)) else 0 := by
          rw [coeff_mul_X_pow', coeff_mul_X_pow']
          by_cases hd : d = single 0 1
          · simp [hd]
          rw [ite_eq_right hd, _root_.add_zero]
          by_cases hd_le : d 1 ≤ k + 1
          · simp_rw [ite_eq_left hd_le, add_pow, map_sum]
            rw [Finset.sum_eq_single (d 0) _ (by simp)]
            · simp
            · intro i hi_mem hi
              rw [mul_pow, mul_assoc, mul_assoc, mul_comm ((X ^ (k + 1)) ^ (d 0 - i)),
                ← mul_assoc, ← mul_assoc, ← pow_mul, coeff_mul_X_pow']
              by_cases! hd₀ : d 1 = 0 ∧ d 0 - i = 1
              · have i_ne_zero : i ≠ 0 := by grind
                simp [hd₀, coeff_B, zero_pow i_ne_zero]
              have : k + 1 ≤ (k + 1) * (d 0 - i) :=
                Nat.le_mul_of_pos_right _ (by grind only [= mem_range])
              rw [ite_eq_right _]
              by_cases hd₀' : d 1 = 0
              · have aux : (k + 1) * 2 ≤ (k + 1) * (d 0 - i) :=
                  Nat.mul_le_mul_left _ (by grind only [= mem_range])
                omega
              omega
          simp_rw [ite_eq_right hd_le]
        have Beq : B.toPowerSeries = ∑ i ∈ range (k + 1), C (F.addInvAux i) * X ^ i := by
          ext n; simp [← hB]
        simp_rw [eq_aux, mul_add]
        rw [finsum_add_distrib]
        · nth_rw 2 [finsum_eq_single _ (single 0 1) fun d hd => by rw [ite_eq_right hd, mul_zero]]
          rw [ite_eq_left rfl, F.lin_coeff_X, one_mul, addInvAux_succ]
          simp [← Beq, coeff,
            MvPowerSeries.coeff_subst (hB ▸ MvPowerSeries.HasSubst.addInv_fin F k)]
        · obtain h := MvPowerSeries.coeff_subst_finite
            (MvPowerSeries.HasSubst.addInv_fin F k) F.toPowerSeries
          simp only [Nat.succ_eq_add_one, Nat.reduceAdd, hB, Finsupp.prod_pow, prod_univ_two,
            isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
            smul_eq_mul] at h
          exact h _
        refine Set.Finite.subset (Set.finite_singleton (single 0 1))
          (Function.support_subset_iff'.mpr fun d hd => ?_)
        simp only [isValue, Set.mem_singleton_iff] at hd
        simp [hd]

/-- Given a formal group law `F` over coefficient ring `R`, the power series `addInvX F`
satisfies `F(addInvX F, X) = 0`. -/
theorem subst_addInv_eq_zero : F.toPowerSeries.subst ![(addInvX F), X] = 0 := by
  ext n
  by_cases hn : n = 0
  · simp [hn, constantCoeff, MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.HasSubst.addInvAux F) (by simp [← constantCoeff_eq]) F.zero_constantCoeff]
  rw [coeff_subst_addInv_trunc _ _ hn, addInv_trunc_aux, coeff_subst_sum_C_addInvAux_mul_X_pow,
    map_zero]

variable (φ : MvPowerSeries σ R)

/-- For any multivariate power series `φ` with zero constant coefficient, `addInv F φ` is the
additive inverse of `φ` under formal group `F` sense. -/
def addInv : MvPowerSeries σ R := subst φ (addInvX F)

@[simp]
theorem addInv_apply : addInv F φ = subst φ (addInvX F) := rfl

instance : Neg (F.Point σ) where
  neg f := ⟨F.addInv f.val, MvPowerSeries.isNilpotent_constCoeff_subst_of_isNilpotent_constCoeff
    f.prop.const (HasSubst.of_constantCoeff_zero' rfl)⟩

@[simp]
lemma neg_apply {f : F.Point σ} : (-f).val = F.addInv f.val := rfl

/-- For any multivariate power series `φ` with zero constant coefficient, then the additive
inverse of `φ` (under `F` sense) plus `φ` (under `F` sense) equals zero. -/
theorem neg_add_cancel (f : F.Point σ) : (-f) + f = 0 := Subtype.ext <| by
  have h : (0 : MvPowerSeries σ R) = subst f.val (0 : PowerSeries R) := by
    simp [← coe_substAlgHom f.prop]
  rw [add_apply, zero_apply, h, ← subst_addInv_eq_zero, subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.addInvAux F) f.prop.const]
  congr! 2 with s
  fin_cases s <;> simp [subst, X, MvPowerSeries.subst_X f.prop.const]

instance : AddGroup (F.Point σ) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := F.neg_add_cancel

instance [F.IsComm] : AddCommGroup (F.Point σ) where
  add_comm x y := Subtype.ext <| F.comm' x.prop y.prop

end FormalGroup
