/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Colimit.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

/-!
# Tensor product with direct limit of finitely generated submodules

We show that if `M` and `P` are arbitrary modules and `N` is a finitely generated submodule
of a module `P`, then two elements of `N ⊗ M` have the same image in `P ⊗ M` if and only if
they already have the same image in `N' ⊗ M` for some finitely generated submodule `N' ≥ N`.
This is the theorem `Submodule.FG.exists_rTensor_fg_inclusion_eq`. The key facts used are
that every module is the direct limit of its finitely generated submodules and that tensor
product preserves colimits.
-/

open TensorProduct

variable {R M P : Type*} [CommSemiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid P] [Module R P]

theorem Submodule.FG.exists_rTensor_fg_inclusion_eq {N : Submodule R P} (hN : N.FG)
    {x y : N ⊗[R] M} (eq : N.subtype.rTensor M x = N.subtype.rTensor M y) :
    ∃ N', N'.FG ∧ ∃ h : N ≤ N', (N.inclusion h).rTensor M x = (N.inclusion h).rTensor M y := by
  classical
  lift N to {N : Submodule R P // N.FG} using hN
  apply_fun (Module.fgSystem.equiv R P).symm.toLinearMap.rTensor M at eq
  apply_fun directLimitLeft _ _ at eq
  simp_rw [← LinearMap.rTensor_comp_apply, ← (LinearEquiv.eq_toLinearMap_symm_comp _ _).mpr
    (Module.fgSystem.equiv_comp_of N), directLimitLeft_rTensor_of] at eq
  have ⟨N', le, eq⟩ := Module.DirectLimit.exists_eq_of_of_eq eq
  exact ⟨_, N'.2, le, eq⟩
