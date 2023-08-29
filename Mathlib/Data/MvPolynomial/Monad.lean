/-
Copyright (c) 2020 Johan Commelin, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.Data.MvPolynomial.Rename
import Mathlib.Data.MvPolynomial.Variables

#align_import data.mv_polynomial.monad from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

/-!

# Monad operations on `MvPolynomial`

This file defines two monadic operations on `MvPolynomial`. Given `p : MvPolynomial σ R`,

* `MvPolynomial.bind₁` and `MvPolynomial.join₁` operate on the variable type `σ`.
* `MvPolynomial.bind₂` and `MvPolynomial.join₂` operate on the coefficient type `R`.

- `MvPolynomial.bind₁ f φ` with `f : σ → MvPolynomial τ R` and `φ : MvPolynomial σ R`,
  is the polynomial `φ(f 1, ..., f i, ...) : MvPolynomial τ R`.
- `MvPolynomial.join₁ φ` with `φ : MvPolynomial (MvPolynomial σ R) R` collapses `φ` to
  a `MvPolynomial σ R`, by evaluating `φ` under the map `X f ↦ f` for `f : MvPolynomial σ R`.
  In other words, if you have a polynomial `φ` in a set of variables indexed by a polynomial ring,
  you evaluate the polynomial in these indexing polynomials.
- `MvPolynomial.bind₂ f φ` with `f : R →+* MvPolynomial σ S` and `φ : MvPolynomial σ R`
  is the `MvPolynomial σ S` obtained from `φ` by mapping the coefficients of `φ` through `f`
  and considering the resulting polynomial as polynomial expression in `MvPolynomial σ R`.
- `MvPolynomial.join₂ φ` with `φ : MvPolynomial σ (MvPolynomial σ R)` collapses `φ` to
  a `MvPolynomial σ R`, by considering `φ` as polynomial expression in `MvPolynomial σ R`.

These operations themselves have algebraic structure: `MvPolynomial.bind₁`
and `MvPolynomial.join₁` are algebra homs and
`MvPolynomial.bind₂` and `MvPolynomial.join₂` are ring homs.

They interact in convenient ways with `MvPolynomial.rename`, `MvPolynomial.map`,
`MvPolynomial.vars`, and other polynomial operations.
Indeed, `MvPolynomial.rename` is the "map" operation for the (`bind₁`, `join₁`) pair,
whereas `MvPolynomial.map` is the "map" operation for the other pair.

## Implementation notes

We add a `LawfulMonad` instance for the (`bind₁`, `join₁`) pair.
The second pair cannot be instantiated as a `Monad`,
since it is not a monad in `Type` but in `CommRing` (or rather `CommSemiRing`).

-/


open BigOperators

noncomputable section

namespace MvPolynomial

open Finsupp

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

/--
`bind₁` is the "left hand side" bind operation on `MvPolynomial`, operating on the variable type.
Given a polynomial `p : MvPolynomial σ R` and a map `f : σ → MvPolynomial τ R` taking variables
in `p` to polynomials in the variable type `τ`, `bind₁ f p` replaces each variable in `p` with
its value under `f`, producing a new polynomial in `τ`. The coefficient type remains the same.
This operation is an algebra hom.
-/
def bind₁ (f : σ → MvPolynomial τ R) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval f
#align mv_polynomial.bind₁ MvPolynomial.bind₁

/-- `bind₂` is the "right hand side" bind operation on `MvPolynomial`,
operating on the coefficient type.
Given a polynomial `p : MvPolynomial σ R` and
a map `f : R → MvPolynomial σ S` taking coefficients in `p` to polynomials over a new ring `S`,
`bind₂ f p` replaces each coefficient in `p` with its value under `f`,
producing a new polynomial over `S`.
The variable type remains the same. This operation is a ring hom.
-/
def bind₂ (f : R →+* MvPolynomial σ S) : MvPolynomial σ R →+* MvPolynomial σ S :=
  eval₂Hom f X
#align mv_polynomial.bind₂ MvPolynomial.bind₂

/--
`join₁` is the monadic join operation corresponding to `MvPolynomial.bind₁`. Given a polynomial `p`
with coefficients in `R` whose variables are polynomials in `σ` with coefficients in `R`,
`join₁ p` collapses `p` to a polynomial with variables in `σ` and coefficients in `R`.
This operation is an algebra hom.
-/
def join₁ : MvPolynomial (MvPolynomial σ R) R →ₐ[R] MvPolynomial σ R :=
  aeval id
#align mv_polynomial.join₁ MvPolynomial.join₁

/--
`join₂` is the monadic join operation corresponding to `MvPolynomial.bind₂`. Given a polynomial `p`
with variables in `σ` whose coefficients are polynomials in `σ` with coefficients in `R`,
`join₂ p` collapses `p` to a polynomial with variables in `σ` and coefficients in `R`.
This operation is a ring hom.
-/
def join₂ : MvPolynomial σ (MvPolynomial σ R) →+* MvPolynomial σ R :=
  eval₂Hom (RingHom.id _) X
#align mv_polynomial.join₂ MvPolynomial.join₂

@[simp]
theorem aeval_eq_bind₁ (f : σ → MvPolynomial τ R) : aeval f = bind₁ f :=
  rfl
#align mv_polynomial.aeval_eq_bind₁ MvPolynomial.aeval_eq_bind₁

@[simp]
theorem eval₂Hom_C_eq_bind₁ (f : σ → MvPolynomial τ R) : eval₂Hom C f = bind₁ f :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_polynomial.eval₂_hom_C_eq_bind₁ MvPolynomial.eval₂Hom_C_eq_bind₁

@[simp]
theorem eval₂Hom_eq_bind₂ (f : R →+* MvPolynomial σ S) : eval₂Hom f X = bind₂ f :=
  rfl
#align mv_polynomial.eval₂_hom_eq_bind₂ MvPolynomial.eval₂Hom_eq_bind₂

section

variable (σ R)

@[simp]
theorem aeval_id_eq_join₁ : aeval id = @join₁ σ R _ :=
  rfl
#align mv_polynomial.aeval_id_eq_join₁ MvPolynomial.aeval_id_eq_join₁

theorem eval₂Hom_C_id_eq_join₁ (φ : MvPolynomial (MvPolynomial σ R) R) :
    eval₂Hom C id φ = join₁ φ :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_polynomial.eval₂_hom_C_id_eq_join₁ MvPolynomial.eval₂Hom_C_id_eq_join₁

@[simp]
theorem eval₂Hom_id_X_eq_join₂ : eval₂Hom (RingHom.id _) X = @join₂ σ R _ :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_polynomial.eval₂_hom_id_X_eq_join₂ MvPolynomial.eval₂Hom_id_X_eq_join₂

end

-- In this file, we don't want to use these simp lemmas,
-- because we first need to show how these new definitions interact
-- and the proofs fall back on unfolding the definitions and call simp afterwards
attribute [-simp]
  aeval_eq_bind₁ eval₂Hom_C_eq_bind₁ eval₂Hom_eq_bind₂ aeval_id_eq_join₁ eval₂Hom_id_X_eq_join₂

@[simp]
theorem bind₁_X_right (f : σ → MvPolynomial τ R) (i : σ) : bind₁ f (X i) = f i :=
  aeval_X f i
set_option linter.uppercaseLean3 false in
#align mv_polynomial.bind₁_X_right MvPolynomial.bind₁_X_right

@[simp]
theorem bind₂_X_right (f : R →+* MvPolynomial σ S) (i : σ) : bind₂ f (X i) = X i :=
  eval₂Hom_X' f X i
set_option linter.uppercaseLean3 false in
#align mv_polynomial.bind₂_X_right MvPolynomial.bind₂_X_right

@[simp]
theorem bind₁_X_left : bind₁ (X : σ → MvPolynomial σ R) = AlgHom.id R _ := by
  ext1 i
  -- ⊢ ↑(bind₁ X) (X i) = ↑(AlgHom.id R (MvPolynomial σ R)) (X i)
  simp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.bind₁_X_left MvPolynomial.bind₁_X_left

variable (f : σ → MvPolynomial τ R)

@[simp]
theorem bind₁_C_right (f : σ → MvPolynomial τ R) (x) : bind₁ f (C x) = C x := by
  simp [bind₁, algebraMap_eq]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.bind₁_C_right MvPolynomial.bind₁_C_right

@[simp]
theorem bind₂_C_right (f : R →+* MvPolynomial σ S) (r : R) : bind₂ f (C r) = f r :=
  eval₂Hom_C f X r
set_option linter.uppercaseLean3 false in
#align mv_polynomial.bind₂_C_right MvPolynomial.bind₂_C_right

@[simp]
theorem bind₂_C_left : bind₂ (C : R →+* MvPolynomial σ R) = RingHom.id _ := by ext : 2 <;> simp
                                                                               -- ⊢ ↑(RingHom.comp (bind₂ C) C) x✝ = ↑(RingHom.comp (RingHom.id (MvPolynomial σ  …
                                                                                           -- 🎉 no goals
                                                                                           -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.bind₂_C_left MvPolynomial.bind₂_C_left

@[simp]
theorem bind₂_comp_C (f : R →+* MvPolynomial σ S) : (bind₂ f).comp C = f :=
  RingHom.ext <| bind₂_C_right _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.bind₂_comp_C MvPolynomial.bind₂_comp_C

@[simp]
theorem join₂_map (f : R →+* MvPolynomial σ S) (φ : MvPolynomial σ R) :
    join₂ (map f φ) = bind₂ f φ := by simp only [join₂, bind₂, eval₂Hom_map_hom, RingHom.id_comp]
                                      -- 🎉 no goals
#align mv_polynomial.join₂_map MvPolynomial.join₂_map

@[simp]
theorem join₂_comp_map (f : R →+* MvPolynomial σ S) : join₂.comp (map f) = bind₂ f :=
  RingHom.ext <| join₂_map _
#align mv_polynomial.join₂_comp_map MvPolynomial.join₂_comp_map

theorem aeval_id_rename (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    aeval id (rename f p) = aeval f p := by rw [aeval_rename, Function.comp.left_id]
                                            -- 🎉 no goals
#align mv_polynomial.aeval_id_rename MvPolynomial.aeval_id_rename

@[simp]
theorem join₁_rename (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    join₁ (rename f φ) = bind₁ f φ :=
  aeval_id_rename _ _
#align mv_polynomial.join₁_rename MvPolynomial.join₁_rename

@[simp]
theorem bind₁_id : bind₁ (@id (MvPolynomial σ R)) = join₁ :=
  rfl
#align mv_polynomial.bind₁_id MvPolynomial.bind₁_id

@[simp]
theorem bind₂_id : bind₂ (RingHom.id (MvPolynomial σ R)) = join₂ :=
  rfl
#align mv_polynomial.bind₂_id MvPolynomial.bind₂_id

theorem bind₁_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R)
    (φ : MvPolynomial σ R) : (bind₁ g) (bind₁ f φ) = bind₁ (fun i => bind₁ g (f i)) φ := by
  simp [bind₁, ← comp_aeval]
  -- 🎉 no goals
#align mv_polynomial.bind₁_bind₁ MvPolynomial.bind₁_bind₁

theorem bind₁_comp_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R) :
    (bind₁ g).comp (bind₁ f) = bind₁ fun i => bind₁ g (f i) := by
  ext1
  -- ⊢ ↑(AlgHom.comp (bind₁ g) (bind₁ f)) (X i✝) = ↑(bind₁ fun i => ↑(bind₁ g) (f i …
  apply bind₁_bind₁
  -- 🎉 no goals
#align mv_polynomial.bind₁_comp_bind₁ MvPolynomial.bind₁_comp_bind₁

theorem bind₂_comp_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* MvPolynomial σ T) :
    (bind₂ g).comp (bind₂ f) = bind₂ ((bind₂ g).comp f) := by ext : 2 <;> simp
                                                              -- ⊢ ↑(RingHom.comp (RingHom.comp (bind₂ g) (bind₂ f)) C) x✝ = ↑(RingHom.comp (bi …
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
#align mv_polynomial.bind₂_comp_bind₂ MvPolynomial.bind₂_comp_bind₂

theorem bind₂_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* MvPolynomial σ T)
    (φ : MvPolynomial σ R) : (bind₂ g) (bind₂ f φ) = bind₂ ((bind₂ g).comp f) φ :=
  RingHom.congr_fun (bind₂_comp_bind₂ f g) φ
#align mv_polynomial.bind₂_bind₂ MvPolynomial.bind₂_bind₂

theorem rename_comp_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → υ) :
    (rename g).comp (bind₁ f) = bind₁ fun i => rename g <| f i := by
  ext1 i
  -- ⊢ ↑(AlgHom.comp (rename g) (bind₁ f)) (X i) = ↑(bind₁ fun i => ↑(rename g) (f  …
  simp
  -- 🎉 no goals
#align mv_polynomial.rename_comp_bind₁ MvPolynomial.rename_comp_bind₁

theorem rename_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → υ) (φ : MvPolynomial σ R) :
    rename g (bind₁ f φ) = bind₁ (fun i => rename g <| f i) φ :=
  AlgHom.congr_fun (rename_comp_bind₁ f g) φ
#align mv_polynomial.rename_bind₁ MvPolynomial.rename_bind₁

theorem map_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* T) (φ : MvPolynomial σ R) :
    map g (bind₂ f φ) = bind₂ ((map g).comp f) φ := by
  simp only [bind₂, eval₂_comp_right, coe_eval₂Hom, eval₂_map]
  -- ⊢ eval₂ (RingHom.comp (map g) f) (↑(map g) ∘ X) φ = eval₂ (RingHom.comp (map g …
  congr 1 with : 1
  -- ⊢ (↑(map g) ∘ X) x✝ = X x✝
  simp only [Function.comp_apply, map_X]
  -- 🎉 no goals
#align mv_polynomial.map_bind₂ MvPolynomial.map_bind₂

theorem bind₁_comp_rename {υ : Type*} (f : τ → MvPolynomial υ R) (g : σ → τ) :
    (bind₁ f).comp (rename g) = bind₁ (f ∘ g) := by
  ext1 i
  -- ⊢ ↑(AlgHom.comp (bind₁ f) (rename g)) (X i) = ↑(bind₁ (f ∘ g)) (X i)
  simp
  -- 🎉 no goals
#align mv_polynomial.bind₁_comp_rename MvPolynomial.bind₁_comp_rename

theorem bind₁_rename {υ : Type*} (f : τ → MvPolynomial υ R) (g : σ → τ) (φ : MvPolynomial σ R) :
    bind₁ f (rename g φ) = bind₁ (f ∘ g) φ :=
  AlgHom.congr_fun (bind₁_comp_rename f g) φ
#align mv_polynomial.bind₁_rename MvPolynomial.bind₁_rename

theorem bind₂_map (f : S →+* MvPolynomial σ T) (g : R →+* S) (φ : MvPolynomial σ R) :
    bind₂ f (map g φ) = bind₂ (f.comp g) φ := by simp [bind₂]
                                                 -- 🎉 no goals
#align mv_polynomial.bind₂_map MvPolynomial.bind₂_map

@[simp]
theorem map_comp_C (f : R →+* S) : (map f).comp (C : R →+* MvPolynomial σ R) = C.comp f := by
  ext1
  -- ⊢ ↑(RingHom.comp (map f) C) x✝ = ↑(RingHom.comp C f) x✝
  apply map_C
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.map_comp_C MvPolynomial.map_comp_C

-- mixing the two monad structures
theorem hom_bind₁ (f : MvPolynomial τ R →+* S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    f (bind₁ g φ) = eval₂Hom (f.comp C) (fun i => f (g i)) φ := by
  rw [bind₁, map_aeval, algebraMap_eq]
  -- 🎉 no goals
#align mv_polynomial.hom_bind₁ MvPolynomial.hom_bind₁

theorem map_bind₁ (f : R →+* S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    map f (bind₁ g φ) = bind₁ (fun i : σ => (map f) (g i)) (map f φ) := by
  rw [hom_bind₁, map_comp_C, ← eval₂Hom_map_hom]
  -- ⊢ ↑(eval₂Hom C fun i => ↑(map f) (g i)) (↑(map f) φ) = ↑(bind₁ fun i => ↑(map  …
  rfl
  -- 🎉 no goals
#align mv_polynomial.map_bind₁ MvPolynomial.map_bind₁

@[simp]
theorem eval₂Hom_comp_C (f : R →+* S) (g : σ → S) : (eval₂Hom f g).comp C = f := by
  ext1 r
  -- ⊢ ↑(RingHom.comp (eval₂Hom f g) C) r = ↑f r
  exact eval₂_C f g r
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.eval₂_hom_comp_C MvPolynomial.eval₂Hom_comp_C

theorem eval₂Hom_bind₁ (f : R →+* S) (g : τ → S) (h : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    eval₂Hom f g (bind₁ h φ) = eval₂Hom f (fun i => eval₂Hom f g (h i)) φ := by
  rw [hom_bind₁, eval₂Hom_comp_C]
  -- 🎉 no goals
#align mv_polynomial.eval₂_hom_bind₁ MvPolynomial.eval₂Hom_bind₁

theorem aeval_bind₁ [Algebra R S] (f : τ → S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    aeval f (bind₁ g φ) = aeval (fun i => aeval f (g i)) φ :=
  eval₂Hom_bind₁ _ _ _ _
#align mv_polynomial.aeval_bind₁ MvPolynomial.aeval_bind₁

theorem aeval_comp_bind₁ [Algebra R S] (f : τ → S) (g : σ → MvPolynomial τ R) :
    (aeval f).comp (bind₁ g) = aeval fun i => aeval f (g i) := by
  ext1
  -- ⊢ ↑(AlgHom.comp (aeval f) (bind₁ g)) (X i✝) = ↑(aeval fun i => ↑(aeval f) (g i …
  apply aeval_bind₁
  -- 🎉 no goals
#align mv_polynomial.aeval_comp_bind₁ MvPolynomial.aeval_comp_bind₁

theorem eval₂Hom_comp_bind₂ (f : S →+* T) (g : σ → T) (h : R →+* MvPolynomial σ S) :
    (eval₂Hom f g).comp (bind₂ h) = eval₂Hom ((eval₂Hom f g).comp h) g := by ext : 2 <;> simp
                                                                             -- ⊢ ↑(RingHom.comp (RingHom.comp (eval₂Hom f g) (bind₂ h)) C) x✝ = ↑(RingHom.com …
                                                                                         -- 🎉 no goals
                                                                                         -- 🎉 no goals
#align mv_polynomial.eval₂_hom_comp_bind₂ MvPolynomial.eval₂Hom_comp_bind₂

theorem eval₂Hom_bind₂ (f : S →+* T) (g : σ → T) (h : R →+* MvPolynomial σ S)
    (φ : MvPolynomial σ R) : eval₂Hom f g (bind₂ h φ) = eval₂Hom ((eval₂Hom f g).comp h) g φ :=
  RingHom.congr_fun (eval₂Hom_comp_bind₂ f g h) φ
#align mv_polynomial.eval₂_hom_bind₂ MvPolynomial.eval₂Hom_bind₂

theorem aeval_bind₂ [Algebra S T] (f : σ → T) (g : R →+* MvPolynomial σ S) (φ : MvPolynomial σ R) :
    aeval f (bind₂ g φ) = eval₂Hom ((↑(aeval f : _ →ₐ[S] _) : _ →+* _).comp g) f φ :=
  eval₂Hom_bind₂ _ _ _ _
#align mv_polynomial.aeval_bind₂ MvPolynomial.aeval_bind₂

theorem eval₂Hom_C_left (f : σ → MvPolynomial τ R) : eval₂Hom C f = bind₁ f :=
  rfl
set_option linter.uppercaseLean3 false in
#align mv_polynomial.eval₂_hom_C_left MvPolynomial.eval₂Hom_C_left

theorem bind₁_monomial (f : σ → MvPolynomial τ R) (d : σ →₀ ℕ) (r : R) :
    bind₁ f (monomial d r) = C r * ∏ i in d.support, f i ^ d i := by
  simp only [monomial_eq, AlgHom.map_mul, bind₁_C_right, Finsupp.prod, AlgHom.map_prod,
    AlgHom.map_pow, bind₁_X_right]
#align mv_polynomial.bind₁_monomial MvPolynomial.bind₁_monomial

theorem bind₂_monomial (f : R →+* MvPolynomial σ S) (d : σ →₀ ℕ) (r : R) :
    bind₂ f (monomial d r) = f r * monomial d 1 := by
  simp only [monomial_eq, RingHom.map_mul, bind₂_C_right, Finsupp.prod, map_prod,
    map_pow, bind₂_X_right, C_1, one_mul]
#align mv_polynomial.bind₂_monomial MvPolynomial.bind₂_monomial

@[simp]
theorem bind₂_monomial_one (f : R →+* MvPolynomial σ S) (d : σ →₀ ℕ) :
    bind₂ f (monomial d 1) = monomial d 1 := by rw [bind₂_monomial, f.map_one, one_mul]
                                                -- 🎉 no goals
#align mv_polynomial.bind₂_monomial_one MvPolynomial.bind₂_monomial_one

section

theorem vars_bind₁ [DecidableEq τ] (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    (bind₁ f φ).vars ⊆ φ.vars.biUnion fun i => (f i).vars := by
  calc
    (bind₁ f φ).vars = (φ.support.sum fun x : σ →₀ ℕ => (bind₁ f) (monomial x (coeff x φ))).vars :=
      by rw [← AlgHom.map_sum, ← φ.as_sum]
    _ ≤ φ.support.biUnion fun i : σ →₀ ℕ => ((bind₁ f) (monomial i (coeff i φ))).vars :=
      (vars_sum_subset _ _)
    _ = φ.support.biUnion fun d : σ →₀ ℕ => vars (C (coeff d φ) * ∏ i in d.support, f i ^ d i) := by
      simp only [bind₁_monomial]
    _ ≤ φ.support.biUnion fun d : σ →₀ ℕ => d.support.biUnion fun i => vars (f i) := ?_
    -- proof below
    _ ≤ φ.vars.biUnion fun i : σ => vars (f i) := ?_
    -- proof below
  · apply Finset.biUnion_mono
    -- ⊢ ∀ (a : σ →₀ ℕ), a ∈ support φ → vars (↑C (coeff a φ) * ∏ i in a.support, f i …
    intro d _hd
    -- ⊢ vars (↑C (coeff d φ) * ∏ i in d.support, f i ^ ↑d i) ⊆ Finset.biUnion d.supp …
    calc
      vars (C (coeff d φ) * ∏ i : σ in d.support, f i ^ d i) ≤
          (C (coeff d φ)).vars ∪ (∏ i : σ in d.support, f i ^ d i).vars :=
        vars_mul _ _
      _ ≤ (∏ i : σ in d.support, f i ^ d i).vars := by
        simp only [Finset.empty_union, vars_C, Finset.le_iff_subset, Finset.Subset.refl]
      _ ≤ d.support.biUnion fun i : σ => vars (f i ^ d i) := (vars_prod _)
      _ ≤ d.support.biUnion fun i : σ => (f i).vars := ?_
    apply Finset.biUnion_mono
    -- ⊢ ∀ (a : σ), a ∈ d.support → vars (f a ^ ↑d a) ⊆ vars (f a)
    intro i _hi
    -- ⊢ vars (f i ^ ↑d i) ⊆ vars (f i)
    apply vars_pow
    -- 🎉 no goals
  · intro j
    -- ⊢ (j ∈ Finset.biUnion (support φ) fun d => Finset.biUnion d.support fun i => v …
    simp_rw [Finset.mem_biUnion]
    -- ⊢ (∃ a, a ∈ support φ ∧ ∃ a_1, a_1 ∈ a.support ∧ j ∈ vars (f a_1)) → ∃ a, a ∈  …
    rintro ⟨d, hd, ⟨i, hi, hj⟩⟩
    -- ⊢ ∃ a, a ∈ vars φ ∧ j ∈ vars (f a)
    exact ⟨i, (mem_vars _).mpr ⟨d, hd, hi⟩, hj⟩
    -- 🎉 no goals
#align mv_polynomial.vars_bind₁ MvPolynomial.vars_bind₁

end

theorem mem_vars_bind₁ (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) {j : τ}
    (h : j ∈ (bind₁ f φ).vars) : ∃ i : σ, i ∈ φ.vars ∧ j ∈ (f i).vars := by
  classical
  simpa only [exists_prop, Finset.mem_biUnion, mem_support_iff, Ne.def] using vars_bind₁ f φ h
#align mv_polynomial.mem_vars_bind₁ MvPolynomial.mem_vars_bind₁

instance monad : Monad fun σ => MvPolynomial σ R
    where
  map f p := rename f p
  pure := X
  bind p f := bind₁ f p
#align mv_polynomial.monad MvPolynomial.monad

instance lawfulFunctor : LawfulFunctor fun σ => MvPolynomial σ R
    where
  map_const := by intros; rfl
                  -- ⊢ Functor.mapConst = Functor.map ∘ Function.const β✝
                          -- 🎉 no goals
  -- porting note: I guess `map_const` no longer has a default implementation?
  id_map := by intros; simp [(· <$> ·)]
               -- ⊢ id <$> x✝ = x✝
                       -- 🎉 no goals
  comp_map := by intros; simp [(· <$> ·)]
                 -- ⊢ (h✝ ∘ g✝) <$> x✝ = h✝ <$> g✝ <$> x✝
                         -- 🎉 no goals
#align mv_polynomial.is_lawful_functor MvPolynomial.lawfulFunctor

instance lawfulMonad : LawfulMonad fun σ => MvPolynomial σ R
    where
  pure_bind := by intros; simp [pure, bind]
                  -- ⊢ pure x✝ >>= f✝ = f✝ x✝
                          -- 🎉 no goals
                   -- ⊢ (SeqLeft.seqLeft x✝ fun x => y✝) = Seq.seq (Function.const β✝ <$> x✝) fun x  …
                           -- ⊢ ↑(bind₁ fun a => ↑(bind₁ fun x => X a) y✝) x✝ = ↑(bind₁ ((fun y => ↑(rename  …
                                                                                     -- 🎉 no goals
  bind_assoc := by intros; simp [bind, ← bind₁_comp_bind₁]
                    -- ⊢ (SeqRight.seqRight x✝ fun x => y✝) = Seq.seq (Function.const α✝ id <$> x✝) f …
                            -- ⊢ ↑(bind₁ fun x => y✝) x✝ = ↑(bind₁ (Function.const α✝ y✝)) x✝
                                                                                        -- 🎉 no goals
                   -- ⊢ x✝ >>= f✝ >>= g✝ = x✝ >>= fun x => f✝ x >>= g✝
                 -- ⊢ (Seq.seq (pure g✝) fun x => x✝) = g✝ <$> x✝
                         -- 🎉 no goals
                           -- 🎉 no goals
                       -- 🎉 no goals
  seqLeft_eq := by intros; simp [SeqLeft.seqLeft, Seq.seq, (· <$> ·), bind₁_rename]; rfl
                 -- 🎉 no goals
  seqRight_eq := by intros; simp [SeqRight.seqRight, Seq.seq, (· <$> ·), bind₁_rename]; rfl
  pure_seq := by intros; simp [(· <$> ·), pure, Seq.seq]
  bind_pure_comp := by aesop
  bind_map := by aesop
#align mv_polynomial.is_lawful_monad MvPolynomial.lawfulMonad

/-
Possible TODO for the future:
Enable the following definitions, and write a lot of supporting lemmas.

def bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) :
    mv_polynomial σ R →+* mv_polynomial τ S :=
  eval₂_hom f g

def join (f : R →+* S) : mv_polynomial (mv_polynomial σ R) S →ₐ[S] mv_polynomial σ S :=
  aeval (map f)

def ajoin [algebra R S] : mv_polynomial (mv_polynomial σ R) S →ₐ[S] mv_polynomial σ S :=
  join (algebra_map R S)

-/
end MvPolynomial
