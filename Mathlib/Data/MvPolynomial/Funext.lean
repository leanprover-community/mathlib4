/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module data.mv_polynomial.funext
! leanprover-community/mathlib commit da01792ca4894d4f3a98d06b6c50455e5ed25da3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Data.MvPolynomial.Rename
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.LibrarySearch

/-!
## Function extensionality for multivariate polynomials

In this file we show that two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variables.

# Main declaration

* `MvPolynomial.funext`: two polynomials `φ ψ : MvPolynomial σ R`
  over an infinite integral domain `R` are equal if `eval x φ = eval x ψ` for all `x : σ → R`.

-/

-- TODO this needs a home
local macro "refine " e:term : conv => `(conv| tactic => refine $e)

namespace MvPolynomial

-- TODO move
theorem eval_eval₂ [CommSemiring R] [CommSemiring S]
    (f : R →+* Polynomial S) (g : σ → Polynomial S) (p : MvPolynomial σ R) :
    Polynomial.eval x (eval₂ f g p) =
      eval₂ ((Polynomial.evalRingHom x).comp f) (fun s => Polynomial.eval x (g s)) p := by
  apply induction_on p
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp [hp]

-- TODO move
theorem eval_eval₂' [CommSemiring R] [CommSemiring S]
    (f : R →+* MvPolynomial τ S) (g : σ → MvPolynomial τ S) (p : MvPolynomial σ R) :
    eval x (eval₂ f g p) = eval₂ ((eval x).comp f) (fun s => eval x (g s)) p := by
  apply induction_on p
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp [hp]

-- TODO move
@[simp]
theorem eval₂_id [CommSemiring R] (p : MvPolynomial σ R) : eval₂ (RingHom.id _) g p = eval g p :=
  rfl

-- TODO move
theorem eval_eval_finSuccEquiv
    [CommSemiring R] (f : MvPolynomial (Fin (n + 1)) R) (q : MvPolynomial (Fin n) R) :
    (eval x) (Polynomial.eval q (finSuccEquiv R n f)) = eval (Fin.cases (eval x q) x) f := by
  simp only [finSuccEquiv_apply, coe_eval₂Hom, eval_eval₂, eval_eval₂']
  conv in RingHom.comp _ _ =>
  { refine @RingHom.ext _ _ _ _ _ (RingHom.id _) fun r => ?_
    simp }
  simp only [eval₂_id]
  congr
  funext i
  refine Fin.cases (by simp) (by simp) i

variable {R : Type _} [CommRing R] [IsDomain R] [Infinite R]

private theorem funext_fin {n : ℕ} {p : MvPolynomial (Fin n) R}
    (h : ∀ x : Fin n → R, eval x p = 0) : p = 0 := by
  induction' n with n ih
  · apply (MvPolynomial.isEmptyRingEquiv R (Fin 0)).injective
    rw [RingEquiv.map_zero]
    convert h finZeroElim
  · apply (finSuccEquiv R n).injective
    simp only [AlgEquiv.map_zero]
    refine Polynomial.funext fun q => ?_
    rw [Polynomial.eval_zero]
    apply ih fun x => ?_
    calc _ = _ := eval_eval_finSuccEquiv p _
         _ = 0 := h _

/-- Two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variables. -/
theorem funext {σ : Type _} {p q : MvPolynomial σ R} (h : ∀ x : σ → R, eval x p = eval x q) :
    p = q := by
  suffices ∀ p, (∀ x : σ → R, eval x p = 0) → p = 0 by
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
    simp only [eval, eval₂Hom_rename, Function.extend_comp hf]
#align mv_polynomial.funext MvPolynomial.funext

theorem funext_iff {σ : Type _} {p q : MvPolynomial σ R} :
    p = q ↔ ∀ x : σ → R, eval x p = eval x q :=
  ⟨by rintro rfl; simp only [forall_const, eq_self_iff_true], funext⟩
#align mv_polynomial.funext_iff MvPolynomial.funext_iff

end MvPolynomial
