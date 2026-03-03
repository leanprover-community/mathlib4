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

* Definition of one dimensional formal group law.

* Properties: `F(X,0) = 0` and `F(0,X) = X`.

* Additive formal group laws and multiplicative formal group laws.

* Instance: Group instance defined by the formal group law `F` over the ideal
  `PowerSeries.hasEvalIdeal`.

## References
* [Hazewinkel, Michiel. «Formal Groups and Applications»]

-/

@[expose] public section

noncomputable section

namespace FormalGroup

variable {R σ : Type*} [CommRing R] (f g : PowerSeries R) (F : FormalGroup R)
  (φ : MvPowerSeries (Fin 2) R) (n : ℕ)

open PowerSeries Finset

/-- Inductive definition of the power series $i(X)$ such that $F(X,i(X)) = 0$. -/
abbrev addInv_aux (F : FormalGroup R) : ℕ → R
  | 0 => 0
  | 1 => -1
  | n + 1 => - (coeff (n + 1) (F.toFun.subst
    ![X, (∑ i : Fin (n + 1), C (addInv_aux F i.1) * X ^ i.1)]))

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
    trunc (n + 1) (addInv_X F)
      = ∑ i : Fin (n + 1), Polynomial.C (addInv_aux F i.1) * Polynomial.X ^ i.1 := by
  induction n with
  | zero => simp [addInv_X]
  | succ k ih =>
    simp only [trunc_apply, Nat.Ico_zero_eq_range, Fin.sum_univ_eq_sum_range
      (fun i => (Polynomial.C (R := R)) (addInv_aux F i) * Polynomial.X ^ i)] at ⊢ ih
    rw [Finset.sum_range_add, ih]
    conv_rhs => rw [Finset.sum_range_add]
    simp [Polynomial.C_mul_X_pow_eq_monomial, addInv_X]

lemma coeff_subst_addInv_trunc (hn : n ≠ 0) :
  coeff n (MvPowerSeries.subst ![X, (addInv_X F)] F.toFun) =
  coeff n (MvPowerSeries.subst ![X, (trunc (n + 1) (addInv_X F))] F.toFun) := by
  have trunc_X_aux : trunc (n + 1) X = Polynomial.X (R := R):= by
    refine trunc_X_of ?_
    omega
  have constant_aux : constantCoeff (addInv_X F) = 0 := by
    exact constantCoeff_addInv_X F
  rw [trunc_subst_trunc_add_one (MvPowerSeries.HasSubst.addInv_aux F)]

  sorry
