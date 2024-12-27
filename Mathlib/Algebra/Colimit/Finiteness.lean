/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Colimit.Module
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Modules as direct limits of finitely generated submodules

We show that every module is the direct limit of its finitely generated submodules.

As a consequence of this and the fact that tensor products preserves colimits,
we show that if `M` and `P` are arbitrary modules and `N` is a finitely generated submodule
of a module `P`, then two elements of `N ⊗ M` have the same image in `P ⊗ M` if and only if
they already have the same image in `N' ⊗ M` for some finitely generated submodule `N' ≥ N`.
This is the theorem `Submodule.FG.exists_rTensor_fg_inclusion_eq`.

## Main definition

* `Module.fgSystem`: the directed system of finitely generated submodules of a module.
-/

namespace Module

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

/-- The directed system of finitely generated submodules of a module. -/
def fgSystem (N₁ N₂ : {N : Submodule R M // N.FG}) (le : N₁ ≤ N₂) : N₁ →ₗ[R] N₂ :=
  Submodule.inclusion le

open DirectLimit

namespace fgSystem

instance : IsDirected {N : Submodule R M // N.FG} (· ≤ ·) where
  directed N₁ N₂ :=
    ⟨⟨_, N₁.2.sup N₂.2⟩, Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩

instance : DirectedSystem _ (fgSystem R M · · · ·) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

variable [DecidableEq (Submodule R M)]

open Submodule in
/-- Every module is the direct limit of its finitely generated submodules. -/
noncomputable def equiv : DirectLimit _ (fgSystem R M) ≃ₗ[R] M :=
  .ofBijective (lift _ _ _ _ (fun _ ↦ Submodule.subtype _) fun _ _ _ _ ↦ rfl)
    ⟨lift_injective _ _ fun _ ↦ Subtype.val_injective, fun x ↦
      ⟨of _ _ _ _ ⟨_, fg_span_singleton x⟩ ⟨x, subset_span <| by rfl⟩, lift_of ..⟩⟩

variable {R M}

lemma equiv_comp_of (N : {N : Submodule R M // N.FG}) :
    (equiv R M).toLinearMap ∘ₗ of _ _ _ _ N = N.1.subtype := by
  ext; simp [equiv]

end fgSystem

end Module

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
