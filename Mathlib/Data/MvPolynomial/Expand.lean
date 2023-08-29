/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.Data.MvPolynomial.Monad

#align_import data.mv_polynomial.expand from "leanprover-community/mathlib"@"5da451b4c96b4c2e122c0325a7fce17d62ee46c6"

/-!
## Expand multivariate polynomials

Given a multivariate polynomial `φ`, one may replace every occurrence of `X i` by `X i ^ n`,
for some natural number `n`.
This operation is called `MvPolynomial.expand` and it is an algebra homomorphism.

### Main declaration

* `MvPolynomial.expand`: expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/


open BigOperators

namespace MvPolynomial

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

See also `Polynomial.expand`. -/
noncomputable def expand (p : ℕ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  { (eval₂Hom C fun i ↦ X i ^ p : MvPolynomial σ R →+* MvPolynomial σ R) with
    commutes' := fun _ ↦ eval₂Hom_C _ _ _ }
#align mv_polynomial.expand MvPolynomial.expand

-- @[simp] -- Porting note: simp can prove this
theorem expand_C (p : ℕ) (r : R) : expand p (C r : MvPolynomial σ R) = C r :=
  eval₂Hom_C _ _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.expand_C MvPolynomial.expand_C

@[simp]
theorem expand_X (p : ℕ) (i : σ) : expand p (X i : MvPolynomial σ R) = X i ^ p :=
  eval₂Hom_X' _ _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.expand_X MvPolynomial.expand_X

@[simp]
theorem expand_monomial (p : ℕ) (d : σ →₀ ℕ) (r : R) :
    expand p (monomial d r) = C r * ∏ i in d.support, (X i ^ p) ^ d i :=
  bind₁_monomial _ _ _
#align mv_polynomial.expand_monomial MvPolynomial.expand_monomial

theorem expand_one_apply (f : MvPolynomial σ R) : expand 1 f = f := by
  simp only [expand, pow_one, eval₂Hom_eq_bind₂, bind₂_C_left, RingHom.toMonoidHom_eq_coe,
    RingHom.coe_monoidHom_id, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.id_apply]
#align mv_polynomial.expand_one_apply MvPolynomial.expand_one_apply

@[simp]
theorem expand_one : expand 1 = AlgHom.id R (MvPolynomial σ R) := by
  ext1 f
  -- ⊢ ↑(expand 1) (X f) = ↑(AlgHom.id R (MvPolynomial σ R)) (X f)
  rw [expand_one_apply, AlgHom.id_apply]
  -- 🎉 no goals
#align mv_polynomial.expand_one MvPolynomial.expand_one

theorem expand_comp_bind₁ (p : ℕ) (f : σ → MvPolynomial τ R) :
    (expand p).comp (bind₁ f) = bind₁ fun i ↦ expand p (f i) := by
  apply algHom_ext
  -- ⊢ ∀ (i : σ), ↑(AlgHom.comp (expand p) (bind₁ f)) (X i) = ↑(bind₁ fun i => ↑(ex …
  intro i
  -- ⊢ ↑(AlgHom.comp (expand p) (bind₁ f)) (X i) = ↑(bind₁ fun i => ↑(expand p) (f  …
  simp only [AlgHom.comp_apply, bind₁_X_right]
  -- 🎉 no goals
#align mv_polynomial.expand_comp_bind₁ MvPolynomial.expand_comp_bind₁

theorem expand_bind₁ (p : ℕ) (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    expand p (bind₁ f φ) = bind₁ (fun i ↦ expand p (f i)) φ := by
  rw [← AlgHom.comp_apply, expand_comp_bind₁]
  -- 🎉 no goals
#align mv_polynomial.expand_bind₁ MvPolynomial.expand_bind₁

@[simp]
theorem map_expand (f : R →+* S) (p : ℕ) (φ : MvPolynomial σ R) :
    map f (expand p φ) = expand p (map f φ) := by simp [expand, map_bind₁]
                                                  -- 🎉 no goals
#align mv_polynomial.map_expand MvPolynomial.map_expand

@[simp]
theorem rename_expand (f : σ → τ) (p : ℕ) (φ : MvPolynomial σ R) :
    rename f (expand p φ) = expand p (rename f φ) := by
  simp [expand, bind₁_rename, rename_bind₁, Function.comp]
  -- 🎉 no goals
#align mv_polynomial.rename_expand MvPolynomial.rename_expand

@[simp]
theorem rename_comp_expand (f : σ → τ) (p : ℕ) :
    (rename f).comp (expand p) =
      (expand p).comp (rename f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) := by
  ext1 φ
  -- ⊢ ↑(AlgHom.comp (rename f) (expand p)) (X φ) = ↑(AlgHom.comp (expand p) (renam …
  simp only [rename_expand, AlgHom.comp_apply]
  -- 🎉 no goals
#align mv_polynomial.rename_comp_expand MvPolynomial.rename_comp_expand

end MvPolynomial
