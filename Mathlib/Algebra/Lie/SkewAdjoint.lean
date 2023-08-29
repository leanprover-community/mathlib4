/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Matrix
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic.NoncommRing

#align_import algebra.lie.skew_adjoint from "leanprover-community/mathlib"@"075b3f7d19b9da85a0b54b3e33055a74fc388dec"

/-!
# Lie algebras of skew-adjoint endomorphisms of a bilinear form

When a module carries a bilinear form, the Lie algebra of endomorphisms of the module contains a
distinguished Lie subalgebra: the skew-adjoint endomorphisms. Such subalgebras are important
because they provide a simple, explicit construction of the so-called classical Lie algebras.

This file defines the Lie subalgebra of skew-adjoint endomorphisms cut out by a bilinear form on
a module and proves some basic related results. It also provides the corresponding definitions and
results for the Lie algebra of square matrices.

## Main definitions

  * `skewAdjointLieSubalgebra`
  * `skewAdjointLieSubalgebraEquiv`
  * `skewAdjointMatricesLieSubalgebra`
  * `skewAdjointMatricesLieSubalgebraEquiv`

## Tags

lie algebra, skew-adjoint, bilinear form
-/


universe u v w w₁

section SkewAdjointEndomorphisms

open BilinForm

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

variable (B : BilinForm R M)

-- Porting note: Changed `(f g)` to `{f g}` for convenience in `skewAdjointLieSubalgebra`
theorem BilinForm.isSkewAdjoint_bracket {f g : Module.End R M} (hf : f ∈ B.skewAdjointSubmodule)
    (hg : g ∈ B.skewAdjointSubmodule) : ⁅f, g⁆ ∈ B.skewAdjointSubmodule := by
  rw [mem_skewAdjointSubmodule] at *
  -- ⊢ IsSkewAdjoint B ⁅f, g⁆
  have hfg : IsAdjointPair B B (f * g) (g * f) := by rw [← neg_mul_neg g f]; exact hf.mul hg
  -- ⊢ IsSkewAdjoint B ⁅f, g⁆
  have hgf : IsAdjointPair B B (g * f) (f * g) := by rw [← neg_mul_neg f g]; exact hg.mul hf
  -- ⊢ IsSkewAdjoint B ⁅f, g⁆
  change BilinForm.IsAdjointPair B B (f * g - g * f) (-(f * g - g * f)); rw [neg_sub]
  -- ⊢ IsAdjointPair B B (f * g - g * f) (-(f * g - g * f))
                                                                         -- ⊢ IsAdjointPair B B (f * g - g * f) (g * f - f * g)
  exact hfg.sub hgf
  -- 🎉 no goals
#align bilin_form.is_skew_adjoint_bracket BilinForm.isSkewAdjoint_bracket

/-- Given an `R`-module `M`, equipped with a bilinear form, the skew-adjoint endomorphisms form a
Lie subalgebra of the Lie algebra of endomorphisms. -/
def skewAdjointLieSubalgebra : LieSubalgebra R (Module.End R M) :=
  { B.skewAdjointSubmodule with
    lie_mem' := B.isSkewAdjoint_bracket }
#align skew_adjoint_lie_subalgebra skewAdjointLieSubalgebra

variable {N : Type w} [AddCommGroup N] [Module R N] (e : N ≃ₗ[R] M)

/-- An equivalence of modules with bilinear forms gives equivalence of Lie algebras of skew-adjoint
endomorphisms. -/
def skewAdjointLieSubalgebraEquiv :
    skewAdjointLieSubalgebra (B.comp (↑e : N →ₗ[R] M) ↑e) ≃ₗ⁅R⁆ skewAdjointLieSubalgebra B := by
  apply LieEquiv.ofSubalgebras _ _ e.lieConj
  -- ⊢ LieSubalgebra.map (LinearEquiv.lieConj e).toLieHom (skewAdjointLieSubalgebra …
  ext f
  -- ⊢ f ∈ LieSubalgebra.map (LinearEquiv.lieConj e).toLieHom (skewAdjointLieSubalg …
  simp only [LieSubalgebra.mem_coe, Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule,
    LinearEquiv.coe_coe]
  exact (BilinForm.isPairSelfAdjoint_equiv (-B) B e f).symm
  -- 🎉 no goals
#align skew_adjoint_lie_subalgebra_equiv skewAdjointLieSubalgebraEquiv

@[simp]
theorem skewAdjointLieSubalgebraEquiv_apply (f : skewAdjointLieSubalgebra (B.comp ↑e ↑e)) :
    ↑(skewAdjointLieSubalgebraEquiv B e f) = e.lieConj f := by
  simp [skewAdjointLieSubalgebraEquiv]
  -- 🎉 no goals
#align skew_adjoint_lie_subalgebra_equiv_apply skewAdjointLieSubalgebraEquiv_apply

@[simp]
theorem skewAdjointLieSubalgebraEquiv_symm_apply (f : skewAdjointLieSubalgebra B) :
    ↑((skewAdjointLieSubalgebraEquiv B e).symm f) = e.symm.lieConj f := by
  simp [skewAdjointLieSubalgebraEquiv]
  -- 🎉 no goals
#align skew_adjoint_lie_subalgebra_equiv_symm_apply skewAdjointLieSubalgebraEquiv_symm_apply

end SkewAdjointEndomorphisms

section SkewAdjointMatrices

open scoped Matrix

variable {R : Type u} {n : Type w} [CommRing R] [DecidableEq n] [Fintype n]

variable (J : Matrix n n R)

theorem Matrix.lie_transpose (A B : Matrix n n R) : ⁅A, B⁆ᵀ = ⁅Bᵀ, Aᵀ⁆ :=
  show (A * B - B * A)ᵀ = Bᵀ * Aᵀ - Aᵀ * Bᵀ by simp
                                               -- 🎉 no goals
#align matrix.lie_transpose Matrix.lie_transpose

-- Porting note: Changed `(A B)` to `{A B}` for convenience in `skewAdjointMatricesLieSubalgebra`
theorem Matrix.isSkewAdjoint_bracket {A B : Matrix n n R} (hA : A ∈ skewAdjointMatricesSubmodule J)
    (hB : B ∈ skewAdjointMatricesSubmodule J) : ⁅A, B⁆ ∈ skewAdjointMatricesSubmodule J := by
  simp only [mem_skewAdjointMatricesSubmodule] at *
  -- ⊢ IsSkewAdjoint J ⁅A, B⁆
  change ⁅A, B⁆ᵀ * J = J * (-⁅A, B⁆)
  -- ⊢ ⁅A, B⁆ᵀ * J = J * -⁅A, B⁆
  change Aᵀ * J = J * (-A) at hA
  -- ⊢ ⁅A, B⁆ᵀ * J = J * -⁅A, B⁆
  change Bᵀ * J = J * (-B) at hB
  -- ⊢ ⁅A, B⁆ᵀ * J = J * -⁅A, B⁆
  rw [Matrix.lie_transpose, LieRing.of_associative_ring_bracket,
    LieRing.of_associative_ring_bracket, sub_mul, mul_assoc, mul_assoc, hA, hB, ← mul_assoc,
    ← mul_assoc, hA, hB]
  noncomm_ring
  -- 🎉 no goals
#align matrix.is_skew_adjoint_bracket Matrix.isSkewAdjoint_bracket

/-- The Lie subalgebra of skew-adjoint square matrices corresponding to a square matrix `J`. -/
def skewAdjointMatricesLieSubalgebra : LieSubalgebra R (Matrix n n R) :=
  { skewAdjointMatricesSubmodule J with
    lie_mem' := J.isSkewAdjoint_bracket }
#align skew_adjoint_matrices_lie_subalgebra skewAdjointMatricesLieSubalgebra

@[simp]
theorem mem_skewAdjointMatricesLieSubalgebra (A : Matrix n n R) :
    A ∈ skewAdjointMatricesLieSubalgebra J ↔ A ∈ skewAdjointMatricesSubmodule J :=
  Iff.rfl
#align mem_skew_adjoint_matrices_lie_subalgebra mem_skewAdjointMatricesLieSubalgebra

/-- An invertible matrix `P` gives a Lie algebra equivalence between those endomorphisms that are
skew-adjoint with respect to a square matrix `J` and those with respect to `PᵀJP`. -/
def skewAdjointMatricesLieSubalgebraEquiv (P : Matrix n n R) (h : Invertible P) :
    skewAdjointMatricesLieSubalgebra J ≃ₗ⁅R⁆ skewAdjointMatricesLieSubalgebra (Pᵀ * J * P) :=
  LieEquiv.ofSubalgebras _ _ (P.lieConj h).symm <| by
    ext A
    -- ⊢ A ∈ LieSubalgebra.map (LieEquiv.symm (Matrix.lieConj P h)).toLieHom (skewAdj …
    suffices P.lieConj h A ∈ skewAdjointMatricesSubmodule J ↔
        A ∈ skewAdjointMatricesSubmodule (Pᵀ * J * P) by
      simp only [LieSubalgebra.mem_coe, Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule,
        LinearEquiv.coe_coe]
      exact this
    simp [Matrix.IsSkewAdjoint, J.isAdjointPair_equiv' _ _ P (isUnit_of_invertible P)]
    -- 🎉 no goals
#align skew_adjoint_matrices_lie_subalgebra_equiv skewAdjointMatricesLieSubalgebraEquiv

-- TODO(mathlib4#6607): fix elaboration so annotation on `A` isn't needed
theorem skewAdjointMatricesLieSubalgebraEquiv_apply (P : Matrix n n R) (h : Invertible P)
    (A : skewAdjointMatricesLieSubalgebra J) :
    ↑(skewAdjointMatricesLieSubalgebraEquiv J P h A) = P⁻¹ * (A : Matrix n n R) * P := by
  simp [skewAdjointMatricesLieSubalgebraEquiv]
  -- 🎉 no goals
#align skew_adjoint_matrices_lie_subalgebra_equiv_apply skewAdjointMatricesLieSubalgebraEquiv_apply

/-- An equivalence of matrix algebras commuting with the transpose endomorphisms restricts to an
equivalence of Lie algebras of skew-adjoint matrices. -/
def skewAdjointMatricesLieSubalgebraEquivTranspose {m : Type w} [DecidableEq m] [Fintype m]
    (e : Matrix n n R ≃ₐ[R] Matrix m m R) (h : ∀ A, (e A)ᵀ = e Aᵀ) :
    skewAdjointMatricesLieSubalgebra J ≃ₗ⁅R⁆ skewAdjointMatricesLieSubalgebra (e J) :=
  LieEquiv.ofSubalgebras _ _ e.toLieEquiv <| by
    ext A
    -- ⊢ A ∈ LieSubalgebra.map (AlgEquiv.toLieEquiv e).toLieHom (skewAdjointMatricesL …
    suffices J.IsSkewAdjoint (e.symm A) ↔ (e J).IsSkewAdjoint A by
      -- Porting note: Originally `simpa [this]`
      simpa [- LieSubalgebra.mem_map, LieSubalgebra.mem_map_submodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, ← h,
      ← Function.Injective.eq_iff e.injective, map_mul, AlgEquiv.apply_symm_apply, map_neg]
#align skew_adjoint_matrices_lie_subalgebra_equiv_transpose skewAdjointMatricesLieSubalgebraEquivTranspose

@[simp]
theorem skewAdjointMatricesLieSubalgebraEquivTranspose_apply {m : Type w} [DecidableEq m]
    [Fintype m] (e : Matrix n n R ≃ₐ[R] Matrix m m R) (h : ∀ A, (e A)ᵀ = e Aᵀ)
    (A : skewAdjointMatricesLieSubalgebra J) :
    (skewAdjointMatricesLieSubalgebraEquivTranspose J e h A : Matrix m m R) = e A :=
  rfl
#align skew_adjoint_matrices_lie_subalgebra_equiv_transpose_apply skewAdjointMatricesLieSubalgebraEquivTranspose_apply

theorem mem_skewAdjointMatricesLieSubalgebra_unit_smul (u : Rˣ) (J A : Matrix n n R) :
    A ∈ skewAdjointMatricesLieSubalgebra (u • J) ↔ A ∈ skewAdjointMatricesLieSubalgebra J := by
  change A ∈ skewAdjointMatricesSubmodule (u • J) ↔ A ∈ skewAdjointMatricesSubmodule J
  -- ⊢ A ∈ skewAdjointMatricesSubmodule (u • J) ↔ A ∈ skewAdjointMatricesSubmodule J
  simp only [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  -- ⊢ Aᵀ * u • J = u • J * -A ↔ Aᵀ * J = J * -A
  constructor <;> intro h
  -- ⊢ Aᵀ * u • J = u • J * -A → Aᵀ * J = J * -A
                  -- ⊢ Aᵀ * J = J * -A
                  -- ⊢ Aᵀ * u • J = u • J * -A
  · simpa using congr_arg (fun B => u⁻¹ • B) h
    -- 🎉 no goals
  · simp [h]
    -- 🎉 no goals
#align mem_skew_adjoint_matrices_lie_subalgebra_unit_smul mem_skewAdjointMatricesLieSubalgebra_unit_smul

end SkewAdjointMatrices
