/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.MvPolynomial.Equiv
import Mathlib.Data.Polynomial.Eval

#align_import data.mv_polynomial.polynomial from "leanprover-community/mathlib"@"0b89934139d3be96f9dab477f10c20f9f93da580"

/-!
# Some lemmas relating polynomials and multivariable polynomials.
-/

set_option autoImplicit true

namespace MvPolynomial

theorem polynomial_eval_eval₂ [CommSemiring R] [CommSemiring S]
    (f : R →+* Polynomial S) (g : σ → Polynomial S) (p : MvPolynomial σ R) :
    Polynomial.eval x (eval₂ f g p) =
      eval₂ ((Polynomial.evalRingHom x).comp f) (fun s => Polynomial.eval x (g s)) p := by
  apply induction_on p
  · simp
    -- 🎉 no goals
  · intro p q hp hq
    -- ⊢ Polynomial.eval x (eval₂ f g (p + q)) = eval₂ (RingHom.comp (Polynomial.eval …
    simp [hp, hq]
    -- 🎉 no goals
  · intro p n hp
    -- ⊢ Polynomial.eval x (eval₂ f g (p * X n)) = eval₂ (RingHom.comp (Polynomial.ev …
    simp [hp]
    -- 🎉 no goals

theorem eval_polynomial_eval_finSuccEquiv
    [CommSemiring R] (f : MvPolynomial (Fin (n + 1)) R) (q : MvPolynomial (Fin n) R) :
    (eval x) (Polynomial.eval q (finSuccEquiv R n f)) = eval (Fin.cases (eval x q) x) f := by
  simp only [finSuccEquiv_apply, coe_eval₂Hom, polynomial_eval_eval₂, eval_eval₂]
  -- ⊢ eval₂ (RingHom.comp (eval x) (RingHom.comp (Polynomial.evalRingHom q) (RingH …
  conv in RingHom.comp _ _ =>
  { refine @RingHom.ext _ _ _ _ _ (RingHom.id _) fun r => ?_
    simp }
  simp only [eval₂_id]
  -- ⊢ ↑(eval fun s => ↑(eval x) (Polynomial.eval q (Fin.cases Polynomial.X (fun k  …
  congr
  -- ⊢ (fun s => ↑(eval x) (Polynomial.eval q (Fin.cases Polynomial.X (fun k => ↑Po …
  funext i
  -- ⊢ ↑(eval x) (Polynomial.eval q (Fin.cases Polynomial.X (fun k => ↑Polynomial.C …
  refine Fin.cases (by simp) (by simp) i
  -- 🎉 no goals
