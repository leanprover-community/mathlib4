/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module data.mv_polynomial.funext
! leanprover-community/mathlib commit da01792ca4894d4f3a98d06b6c50455e5ed25da3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.RingDivision
import Mathbin.Data.MvPolynomial.Rename
import Mathbin.RingTheory.Polynomial.Basic

/-!
## Function extensionality for multivariate polynomials

In this file we show that two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variables.

# Main declaration

* `mv_polynomial.funext`: two polynomials `φ ψ : mv_polynomial σ R`
  over an infinite integral domain `R` are equal if `eval x φ = eval x ψ` for all `x : σ → R`.

-/


namespace MvPolynomial

variable {R : Type _} [CommRing R] [IsDomain R] [Infinite R]

private theorem funext_fin {n : ℕ} {p : MvPolynomial (Fin n) R}
    (h : ∀ x : Fin n → R, eval x p = 0) : p = 0 :=
  by
  induction' n with n ih generalizing R
  · let e := MvPolynomial.isEmptyRingEquiv R (Fin 0)
    apply e.injective
    rw [RingEquiv.map_zero]
    convert h finZeroElim
    suffices
      (eval₂_hom (RingHom.id _) (IsEmpty.elim' Fin.isEmpty)) p =
        (eval finZeroElim : MvPolynomial (Fin 0) R →+* R) p
      by
      rw [← this]
      simp only [coe_eval₂_hom, is_empty_ring_equiv_apply, RingEquiv.trans_apply,
        aeval_eq_eval₂_hom]
      congr
    exact eval₂_hom_congr rfl (Subsingleton.elim _ _) rfl
  · let e := (finSuccEquiv R n).toRingEquiv
    apply e.injective
    simp only [RingEquiv.map_zero]
    apply Polynomial.funext
    intro q
    rw [Polynomial.eval_zero]
    apply ih
    swap
    · infer_instance
    intro x
    dsimp [e]
    rw [fin_succ_equiv_apply]
    calc
      _ = eval _ p := _
      _ = 0 := h _
      
    · intro i
      exact Fin.cases (eval x q) x i
    apply induction_on p
    · intro r
      simp only [eval_C, Polynomial.eval_C, RingHom.coe_comp, eval₂_hom_C]
    · intros
      simp only [*, RingHom.map_add, Polynomial.eval_add]
    · intro φ i hφ
      simp only [*, eval_X, Polynomial.eval_mul, RingHom.map_mul, eval₂_hom_X']
      congr 1
      by_cases hi : i = 0
      · subst hi
        simp only [Polynomial.eval_X, Fin.cases_zero]
      · rw [← Fin.succ_pred i hi]
        simp only [eval_X, Polynomial.eval_C, Fin.cases_succ]
    · infer_instance
#align mv_polynomial.funext_fin mv_polynomial.funext_fin

/-- Two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variables. -/
theorem funext {σ : Type _} {p q : MvPolynomial σ R} (h : ∀ x : σ → R, eval x p = eval x q) :
    p = q :=
  by
  suffices ∀ p, (∀ x : σ → R, eval x p = 0) → p = 0
    by
    rw [← sub_eq_zero, this (p - q)]
    simp only [h, RingHom.map_sub, forall_const, sub_self]
  clear h p q
  intro p h
  obtain ⟨n, f, hf, p, rfl⟩ := exists_fin_rename p
  suffices p = 0 by rw [this, AlgHom.map_zero]
  apply funext_fin
  intro x
  classical
    convert h (Function.extend f x 0)
    simp only [eval, eval₂_hom_rename, Function.extend_comp hf]
#align mv_polynomial.funext MvPolynomial.funext

theorem funext_iff {σ : Type _} {p q : MvPolynomial σ R} :
    p = q ↔ ∀ x : σ → R, eval x p = eval x q :=
  ⟨by rintro rfl <;> simp only [forall_const, eq_self_iff_true], funext⟩
#align mv_polynomial.funext_iff MvPolynomial.funext_iff

end MvPolynomial

