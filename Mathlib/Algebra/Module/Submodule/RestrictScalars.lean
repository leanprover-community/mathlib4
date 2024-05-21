/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Andrew Yang,
  Johannes Hölzl, Kevin Buzzard, Yury Kudryashov
-/
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Order.Hom.CompleteLattice

/-!

# Restriction of scalars for submodules

If semiring `S` acts on a semiring `R` and `M` is a module over both (compatibly with this action)
then we can turn an `R`-submodule into an `S`-submodule by forgetting the action of `R`. We call
this restriction of scalars for submodules.

## Main definitions:
 * `Submodule.restrictScalars`: regard an `R`-submodule as an `S`-submodule if `S` acts on `R`

-/

namespace Submodule

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

/-- `V.restrictScalars S` is the `S`-submodule of the `S`-module given by restriction of scalars,
corresponding to `V`, an `R`-submodule of the original `R`-module.
-/
def restrictScalars (V : Submodule R M) : Submodule S M where
  carrier := V
  zero_mem' := V.zero_mem
  smul_mem' c _ h := V.smul_of_tower_mem c h
  add_mem' hx hy := V.add_mem hx hy
#align submodule.restrict_scalars Submodule.restrictScalars

@[simp]
theorem coe_restrictScalars (V : Submodule R M) : (V.restrictScalars S : Set M) = V :=
  rfl
#align submodule.coe_restrict_scalars Submodule.coe_restrictScalars

@[simp]
theorem toAddSubmonoid_restrictScalars (V : Submodule R M) :
    (V.restrictScalars S).toAddSubmonoid = V.toAddSubmonoid :=
  rfl

@[simp]
theorem restrictScalars_mem (V : Submodule R M) (m : M) : m ∈ V.restrictScalars S ↔ m ∈ V :=
  Iff.refl _
#align submodule.restrict_scalars_mem Submodule.restrictScalars_mem

@[simp]
theorem restrictScalars_self (V : Submodule R M) : V.restrictScalars R = V :=
  SetLike.coe_injective rfl
#align submodule.restrict_scalars_self Submodule.restrictScalars_self

variable (R M)

theorem restrictScalars_injective :
    Function.Injective (restrictScalars S : Submodule R M → Submodule S M) := fun _ _ h =>
  ext <| Set.ext_iff.1 (SetLike.ext'_iff.1 h : _)
#align submodule.restrict_scalars_injective Submodule.restrictScalars_injective

@[simp]
theorem restrictScalars_inj {V₁ V₂ : Submodule R M} :
    restrictScalars S V₁ = restrictScalars S V₂ ↔ V₁ = V₂ :=
  (restrictScalars_injective S _ _).eq_iff
#align submodule.restrict_scalars_inj Submodule.restrictScalars_inj

/-- Even though `p.restrictScalars S` has type `Submodule S M`, it is still an `R`-module. -/
instance restrictScalars.origModule (p : Submodule R M) : Module R (p.restrictScalars S) :=
  (by infer_instance : Module R p)
#align submodule.restrict_scalars.orig_module Submodule.restrictScalars.origModule

instance restrictScalars.isScalarTower (p : Submodule R M) :
    IsScalarTower S R (p.restrictScalars S) where
  smul_assoc r s x := Subtype.ext <| smul_assoc r s (x : M)
#align submodule.restrict_scalars.is_scalar_tower Submodule.restrictScalars.isScalarTower

/-- `restrictScalars S` is an embedding of the lattice of `R`-submodules into
the lattice of `S`-submodules. -/
@[simps]
def restrictScalarsEmbedding : Submodule R M ↪o Submodule S M where
  toFun := restrictScalars S
  inj' := restrictScalars_injective S R M
  map_rel_iff' := by simp [SetLike.le_def]
#align submodule.restrict_scalars_embedding Submodule.restrictScalarsEmbedding
#align submodule.restrict_scalars_embedding_apply Submodule.restrictScalarsEmbedding_apply

/-- Turning `p : Submodule R M` into an `S`-submodule gives the same module structure
as turning it into a type and adding a module structure. -/
@[simps (config := { simpRhs := true })]
def restrictScalarsEquiv (p : Submodule R M) : p.restrictScalars S ≃ₗ[R] p :=
  { AddEquiv.refl p with
    map_smul' := fun _ _ => rfl }
#align submodule.restrict_scalars_equiv Submodule.restrictScalarsEquiv
#align submodule.restrict_scalars_equiv_symm_apply Submodule.restrictScalarsEquiv_symm_apply

@[simp]
theorem restrictScalars_bot : restrictScalars S (⊥ : Submodule R M) = ⊥ :=
  rfl
#align submodule.restrict_scalars_bot Submodule.restrictScalars_bot

@[simp]
theorem restrictScalars_eq_bot_iff {p : Submodule R M} : restrictScalars S p = ⊥ ↔ p = ⊥ := by
  simp [SetLike.ext_iff]
#align submodule.restrict_scalars_eq_bot_iff Submodule.restrictScalars_eq_bot_iff

@[simp]
theorem restrictScalars_top : restrictScalars S (⊤ : Submodule R M) = ⊤ :=
  rfl
#align submodule.restrict_scalars_top Submodule.restrictScalars_top

@[simp]
theorem restrictScalars_eq_top_iff {p : Submodule R M} : restrictScalars S p = ⊤ ↔ p = ⊤ := by
  simp [SetLike.ext_iff]
#align submodule.restrict_scalars_eq_top_iff Submodule.restrictScalars_eq_top_iff

/-- If ring `S` acts on a ring `R` and `M` is a module over both (compatibly with this action) then
we can turn an `R`-submodule into an `S`-submodule by forgetting the action of `R`. -/
def restrictScalarsLatticeHom : CompleteLatticeHom (Submodule R M) (Submodule S M) where
  toFun := restrictScalars S
  map_sInf' s := by ext; simp
  map_sSup' s := by rw [← toAddSubmonoid_eq, toAddSubmonoid_sSup, ← Set.image_comp]; simp

end Submodule
