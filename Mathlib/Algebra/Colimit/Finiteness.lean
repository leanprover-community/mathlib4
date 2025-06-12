/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Colimit.Module
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Modules as direct limits of finitely generated submodules

We show that every module is the direct limit of its finitely generated submodules.

## Main definitions

* `Module.fgSystem`: the directed system of finitely generated submodules of a module.

* `Module.fgSystem.equiv`: the isomorphism between a module and the direct limit of its
  finitely generated submodules.
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
