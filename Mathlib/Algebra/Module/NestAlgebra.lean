/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Order.CompleteSublattice
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Nest algebras
-/

variable (R M N : Type*)

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

instance test : CompleteLattice (Submodule R M) := Submodule.completeLattice

--variable (N : CompleteSublattice (Submodule R M)) [LinearOrder N]

/-
structure Nest (N : CompleteSublattice (Submodule R M)) [LinearOrder N] where
  mem_bot: ⊥ ∈ N
  mem_top: ⊤ ∈ N
-/

/--
The nest algebra of a nest
-/
def NestAlg (N : CompleteSublattice (Submodule R M)) : Subalgebra R (M →ₗ[R] M) where
  carrier := { T | ∀ (n : N), T '' n ⊆ n}
  add_mem' S T := by
    intro n x hx
    obtain ⟨y, ⟨hy₁, hy₂⟩⟩ := hx
    rw [← hy₂, LinearMap.add_apply]
    exact AddMemClass.add_mem (S _ (Set.mem_image_of_mem _ hy₁))  (T _ (Set.mem_image_of_mem _ hy₁))
  mul_mem' S T := by
    intro n h hx
    obtain ⟨y, hy₁, hy₂⟩ := hx
    rw [← hy₂, LinearMap.mul_apply]
    exact S _ (Set.mem_image_of_mem _ (T _ (Set.mem_image_of_mem _ hy₁)))
  one_mem' := by
    intro n
    simp only [LinearMap.one_apply, Set.image_id', subset_refl]
  zero_mem' := by
    intro n
    simp only [LinearMap.zero_apply, Set.image_subset_iff, SetLike.mem_coe, Submodule.zero_mem,
      Set.preimage_const_of_mem, Set.subset_univ]
  algebraMap_mem' := by
    intro r n x hx
    obtain ⟨y, hy₁, hy₂⟩ := hx
    rw [← hy₂, Module.algebraMap_end_apply]
    exact SMulMemClass.smul_mem _ hy₁
