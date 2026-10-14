/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Lifting linear maps from base-changed modules

This file defines the lift of an `R`-linear map from `M` to an `A`-module `N` to an `A`-linear
map from `A ⊗[R] M` to `N`.
-/

@[expose] public section

open scoped TensorProduct

open TensorProduct

namespace LinearMap

variable {R M N} (A) [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
variable [AddCommMonoid N] [Module R M] [Module R N] [Module A N] [IsScalarTower R A N]

/-- If `M` is an `R`-module and `N` is an `A`-module, then `A`-linear maps
`A ⊗[R] M →ₗ[A] N` correspond to `R`-linear maps `M →ₗ[R] N` by composing with
`M → A ⊗[R] M`, `x ↦ 1 ⊗ₜ x`. -/
def liftBaseChangeEquiv : (M →ₗ[R] N) ≃ₗ[A] (A ⊗[R] M →ₗ[A] N) :=
  (LinearMap.ringLmapEquivSelf _ _ _).symm.trans (AlgebraTensorModule.lift.equiv _ _ _ _ _ _)

/-- If `N` is an `A`-module, lift a linear map `M →ₗ[R] N` to `A ⊗[R] M →ₗ[A] N`. -/
abbrev liftBaseChange (l : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] N :=
  LinearMap.liftBaseChangeEquiv A l

@[simp]
lemma liftBaseChange_tmul (l : M →ₗ[R] N) (x y) : l.liftBaseChange A (x ⊗ₜ y) = x • l y := rfl

lemma liftBaseChange_one_tmul (l : M →ₗ[R] N) (y) : l.liftBaseChange A (1 ⊗ₜ y) = l y := by
  simp

@[simp]
lemma liftBaseChangeEquiv_symm_apply (l : A ⊗[R] M →ₗ[A] N) (x) :
    (liftBaseChangeEquiv A).symm l x = l (1 ⊗ₜ x) := rfl

lemma liftBaseChange_comp {P} [AddCommMonoid P] [Module A P] [Module R P] [IsScalarTower R A P]
    (l : M →ₗ[R] N) (l' : N →ₗ[A] P) :
      l' ∘ₗ l.liftBaseChange A = (l'.restrictScalars R ∘ₗ l).liftBaseChange A := by
  ext
  simp

@[simp]
lemma range_liftBaseChange (l : M →ₗ[R] N) :
    LinearMap.range (l.liftBaseChange A) = Submodule.span A (LinearMap.range l) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn
    · rw [LinearMap.liftBaseChange_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [map_add]
      exact add_mem ‹_› ‹_›
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp⟩

end LinearMap
