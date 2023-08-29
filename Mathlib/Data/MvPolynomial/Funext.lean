/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Data.MvPolynomial.Rename
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.MvPolynomial.Polynomial

#align_import data.mv_polynomial.funext from "leanprover-community/mathlib"@"0b89934139d3be96f9dab477f10c20f9f93da580"

/-!
## Function extensionality for multivariate polynomials

In this file we show that two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variables.

# Main declaration

* `MvPolynomial.funext`: two polynomials `φ ψ : MvPolynomial σ R`
  over an infinite integral domain `R` are equal if `eval x φ = eval x ψ` for all `x : σ → R`.

-/

namespace MvPolynomial

variable {R : Type*} [CommRing R] [IsDomain R] [Infinite R]

private theorem funext_fin {n : ℕ} {p : MvPolynomial (Fin n) R}
    (h : ∀ x : Fin n → R, eval x p = 0) : p = 0 := by
  induction' n with n ih
  -- ⊢ p = 0
  · apply (MvPolynomial.isEmptyRingEquiv R (Fin 0)).injective
    -- ⊢ ↑(isEmptyRingEquiv R (Fin 0)) p = ↑(isEmptyRingEquiv R (Fin 0)) 0
    rw [RingEquiv.map_zero]
    -- ⊢ ↑(isEmptyRingEquiv R (Fin 0)) p = 0
    convert h finZeroElim
    -- 🎉 no goals
  · apply (finSuccEquiv R n).injective
    -- ⊢ ↑(finSuccEquiv R n) p = ↑(finSuccEquiv R n) 0
    simp only [AlgEquiv.map_zero]
    -- ⊢ ↑(finSuccEquiv R n) p = 0
    refine Polynomial.funext fun q => ?_
    -- ⊢ Polynomial.eval q (↑(finSuccEquiv R n) p) = Polynomial.eval q 0
    rw [Polynomial.eval_zero]
    -- ⊢ Polynomial.eval q (↑(finSuccEquiv R n) p) = 0
    apply ih fun x => ?_
    -- ⊢ ↑(eval x) (Polynomial.eval q (↑(finSuccEquiv R n) p)) = 0
    calc _ = _ := eval_polynomial_eval_finSuccEquiv p _
         _ = 0 := h _

/-- Two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variables. -/
theorem funext {σ : Type*} {p q : MvPolynomial σ R} (h : ∀ x : σ → R, eval x p = eval x q) :
    p = q := by
  suffices ∀ p, (∀ x : σ → R, eval x p = 0) → p = 0 by
    rw [← sub_eq_zero, this (p - q)]
    simp only [h, RingHom.map_sub, forall_const, sub_self]
  clear h p q
  -- ⊢ ∀ (p : MvPolynomial σ R), (∀ (x : σ → R), ↑(eval x) p = 0) → p = 0
  intro p h
  -- ⊢ p = 0
  obtain ⟨n, f, hf, p, rfl⟩ := exists_fin_rename p
  -- ⊢ ↑(rename f) p = 0
  suffices p = 0 by rw [this, AlgHom.map_zero]
  -- ⊢ p = 0
  apply funext_fin
  -- ⊢ ∀ (x : Fin n → R), ↑(eval x) p = 0
  intro x
  -- ⊢ ↑(eval x) p = 0
  classical
    convert h (Function.extend f x 0)
    simp only [eval, eval₂Hom_rename, Function.extend_comp hf]
#align mv_polynomial.funext MvPolynomial.funext

theorem funext_iff {σ : Type*} {p q : MvPolynomial σ R} :
    p = q ↔ ∀ x : σ → R, eval x p = eval x q :=
  ⟨by rintro rfl; simp only [forall_const, eq_self_iff_true], funext⟩
      -- ⊢ ∀ (x : σ → R), ↑(eval x) p = ↑(eval x) p
                  -- 🎉 no goals
#align mv_polynomial.funext_iff MvPolynomial.funext_iff

end MvPolynomial
