/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Data.MvPolynomial.Rename

#align_import data.mv_polynomial.comap from "leanprover-community/mathlib"@"aba31c938d3243cc671be7091b28a1e0814647ee"

/-!
# `comap` operation on `MvPolynomial`

This file defines the `comap` function on `MvPolynomial`.

`MvPolynomial.comap` is a low-tech example of a map of "algebraic varieties," modulo the fact that
`mathlib` does not yet define varieties.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

-/


namespace MvPolynomial

variable {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [CommSemiring R]

/-- Given an algebra hom `f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R`
and a variable evaluation `v : τ → R`,
`comap f v` produces a variable evaluation `σ → R`.
-/
noncomputable def comap (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) : (τ → R) → σ → R :=
  fun x i => aeval x (f (X i))
#align mv_polynomial.comap MvPolynomial.comap

@[simp]
theorem comap_apply (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (x : τ → R) (i : σ) :
    comap f x i = aeval x (f (X i)) :=
  rfl
#align mv_polynomial.comap_apply MvPolynomial.comap_apply

@[simp]
theorem comap_id_apply (x : σ → R) : comap (AlgHom.id R (MvPolynomial σ R)) x = x := by
  funext i
  -- ⊢ comap (AlgHom.id R (MvPolynomial σ R)) x i = x i
  simp only [comap, AlgHom.id_apply, id.def, aeval_X]
  -- 🎉 no goals
#align mv_polynomial.comap_id_apply MvPolynomial.comap_id_apply

variable (σ R)

theorem comap_id : comap (AlgHom.id R (MvPolynomial σ R)) = id := by
  funext x
  -- ⊢ comap (AlgHom.id R (MvPolynomial σ R)) x = id x
  exact comap_id_apply x
  -- 🎉 no goals
#align mv_polynomial.comap_id MvPolynomial.comap_id

variable {σ R}

theorem comap_comp_apply (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (g : MvPolynomial τ R →ₐ[R] MvPolynomial υ R) (x : υ → R) :
    comap (g.comp f) x = comap f (comap g x) := by
  funext i
  -- ⊢ comap (AlgHom.comp g f) x i = comap f (comap g x) i
  trans aeval x (aeval (fun i => g (X i)) (f (X i)))
  -- ⊢ comap (AlgHom.comp g f) x i = ↑(aeval x) (↑(aeval fun i => ↑g (X i)) (↑f (X  …
  · apply eval₂Hom_congr rfl rfl
    -- ⊢ ↑(AlgHom.comp g f) (X i) = ↑(aeval fun i => ↑g (X i)) (↑f (X i))
    rw [AlgHom.comp_apply]
    -- ⊢ ↑g (↑f (X i)) = ↑(aeval fun i => ↑g (X i)) (↑f (X i))
    suffices g = aeval fun i => g (X i) by rw [← this]
    -- ⊢ g = aeval fun i => ↑g (X i)
    exact aeval_unique g
    -- 🎉 no goals
  · simp only [comap, aeval_eq_eval₂Hom, map_eval₂Hom, AlgHom.comp_apply]
    -- ⊢ ↑(eval₂Hom (RingHom.comp (eval₂Hom (algebraMap R R) x) (algebraMap R (MvPoly …
    refine' eval₂Hom_congr _ rfl rfl
    -- ⊢ RingHom.comp (eval₂Hom (algebraMap R R) x) (algebraMap R (MvPolynomial υ R)) …
    ext r
    -- ⊢ ↑(RingHom.comp (eval₂Hom (algebraMap R R) x) (algebraMap R (MvPolynomial υ R …
    apply aeval_C
    -- 🎉 no goals
#align mv_polynomial.comap_comp_apply MvPolynomial.comap_comp_apply

theorem comap_comp (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (g : MvPolynomial τ R →ₐ[R] MvPolynomial υ R) : comap (g.comp f) = comap f ∘ comap g := by
  funext x
  -- ⊢ comap (AlgHom.comp g f) x = (comap f ∘ comap g) x
  exact comap_comp_apply _ _ _
  -- 🎉 no goals
#align mv_polynomial.comap_comp MvPolynomial.comap_comp

theorem comap_eq_id_of_eq_id (f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (hf : ∀ φ, f φ = φ)
    (x : σ → R) : comap f x = x := by
  convert comap_id_apply x
  -- ⊢ f = AlgHom.id R (MvPolynomial σ R)
  ext1 φ
  -- ⊢ ↑f (X φ) = ↑(AlgHom.id R (MvPolynomial σ R)) (X φ)
  simp [hf, AlgHom.id_apply]
  -- 🎉 no goals
#align mv_polynomial.comap_eq_id_of_eq_id MvPolynomial.comap_eq_id_of_eq_id

theorem comap_rename (f : σ → τ) (x : τ → R) : comap (rename f) x = x ∘ f := by
  funext
  -- ⊢ comap (rename f) x x✝ = (x ∘ f) x✝
  simp [rename_X, comap_apply, aeval_X]
  -- 🎉 no goals
#align mv_polynomial.comap_rename MvPolynomial.comap_rename

/-- If two polynomial types over the same coefficient ring `R` are equivalent,
there is a bijection between the types of functions from their variable types to `R`.
-/
noncomputable def comapEquiv (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) : (τ → R) ≃ (σ → R) where
  toFun := comap f
  invFun := comap f.symm
  left_inv := by
    intro x
    -- ⊢ comap (↑(AlgEquiv.symm f)) (comap (↑f) x) = x
    rw [← comap_comp_apply]
    -- ⊢ comap (AlgHom.comp ↑f ↑(AlgEquiv.symm f)) x = x
    apply comap_eq_id_of_eq_id
    -- ⊢ ∀ (φ : MvPolynomial τ R), ↑(AlgHom.comp ↑f ↑(AlgEquiv.symm f)) φ = φ
    intro
    -- ⊢ ↑(AlgHom.comp ↑f ↑(AlgEquiv.symm f)) φ✝ = φ✝
    simp only [AlgHom.id_apply, AlgEquiv.comp_symm]
    -- 🎉 no goals
  right_inv := by
    intro x
    -- ⊢ comap (↑f) (comap (↑(AlgEquiv.symm f)) x) = x
    rw [← comap_comp_apply]
    -- ⊢ comap (AlgHom.comp ↑(AlgEquiv.symm f) ↑f) x = x
    apply comap_eq_id_of_eq_id
    -- ⊢ ∀ (φ : MvPolynomial σ R), ↑(AlgHom.comp ↑(AlgEquiv.symm f) ↑f) φ = φ
    intro
    -- ⊢ ↑(AlgHom.comp ↑(AlgEquiv.symm f) ↑f) φ✝ = φ✝
    simp only [AlgHom.id_apply, AlgEquiv.symm_comp]
    -- 🎉 no goals
#align mv_polynomial.comap_equiv MvPolynomial.comapEquiv

@[simp]
theorem comapEquiv_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) :
    (comapEquiv f : (τ → R) → σ → R) = comap f :=
  rfl
#align mv_polynomial.comap_equiv_coe MvPolynomial.comapEquiv_coe

@[simp]
theorem comapEquiv_symm_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) :
    ((comapEquiv f).symm : (σ → R) → τ → R) = comap f.symm :=
  rfl
#align mv_polynomial.comap_equiv_symm_coe MvPolynomial.comapEquiv_symm_coe

end MvPolynomial
