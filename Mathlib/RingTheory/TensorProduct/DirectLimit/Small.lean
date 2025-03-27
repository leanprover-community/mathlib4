/-
Copyright (c) 2025 Antoine Chambert-Loir, María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Maria-Inés de Frutos-Fernandez
-/
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Small

/-! # Tensor products and small submodules

* `DirectedSystem.Submodules_small`: the directed system of small submodules of a module

* `Submodules_small_equiv` proves that a module is the direct limit
of its finitely generated submodules, with respect to the inclusion maps

* `rTensor_smallEquiv` deduces that a tensor product `M ⊗[R] N`
is the direct limit of the modules `P ⊗[R] N`, for all finitely generated
submodules `P` of `M`, with respect to the maps deduced from the inclusions

* `lTensor_smallEquiv` deduces that a tensor product `M ⊗[R] N`
is the direct limit of the modules `M ⊗[R] Q`, for all finitely generated
submodules `Q` of `N`, with respect to the maps deduced from the inclusions

## TODO

* Fix namespaces, add docstrings

* Provide the analogous result both sides at the same time.

-/

open Submodule LinearMap

section Semiring

universe u v
variable {R : Type u} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

-- The directed system of small submodules of `M`
theorem DirectedSystem.Submodules_small :
    DirectedSystem (ι := {P : Submodule R M // Small.{v} P}) (F := fun P ↦ P.val)
    (f := fun ⦃P Q⦄ (h : P ≤ Q) ↦ Submodule.inclusion h) where
  map_self := fun _ _ ↦ rfl
  map_map  := fun _ _ _ _ _ _ ↦ rfl

variable (R M) in
/-- Any module is the direct limit of its finitely generated submodules -/
noncomputable def Submodules_small_equiv
    [Small.{v} R] [DecidableEq {P : Submodule R M // Small.{v} P}] :
    Module.DirectLimit (ι := {P : Submodule R M // Small.{v} P})
      (G := fun P ↦ P.val)
      (fun ⦃P Q⦄ (h : P ≤ Q) ↦ Submodule.inclusion h) ≃ₗ[R] M :=
  LinearEquiv.ofBijective
    (Module.DirectLimit.lift _ _ _ _ (fun P ↦ P.val.subtype) (fun _ _ _ _ ↦ rfl))
    ⟨Module.DirectLimit.lift_injective _ _ (fun P ↦ Submodule.injective_subtype P.val),
      fun x ↦ ⟨Module.DirectLimit.of _ {P : Submodule R M // Small.{v} P} _ _
          ⟨Submodule.span R {x}, Submodule.FG.small _ (fg_span_singleton x)⟩
          ⟨x, Submodule.mem_span_singleton_self x⟩, by simp⟩⟩

end Semiring

open TensorProduct

universe v

variable (R : Type*) (M N : Type*)
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

variable {R M N}

/-- A tensor product `M ⊗[R] N` is the direct limit of the modules `P ⊗[R] N`,
where `P` ranges over all small submodules of `M`. -/
noncomputable def rTensor_small_equiv
    [Small.{v} R]  [DecidableEq {P : Submodule R M // Small.{v} P}] :
    Module.DirectLimit (R := R) (ι := {P : Submodule R M // Small.{v} P}) (fun P ↦ P.val ⊗[R] N)
      (fun ⦃P Q⦄ (h : P ≤ Q)  ↦ (Submodule.inclusion h).rTensor N) ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitLeft _ N).symm.trans ((Submodules_small_equiv R M).rTensor N)

/-- A tensor product `M ⊗[R] N` is the direct limit of the modules `M ⊗[R] Q`,
where `Q` ranges over all small submodules of `N`. -/
noncomputable def lTensor_small_equiv
    [Small.{v} R]  [DecidableEq {Q : Submodule R N // Small.{v} Q}] :
    Module.DirectLimit (R := R) (ι := {Q : Submodule R N // Small.{v} Q}) (fun Q ↦ M ⊗[R] Q.val)
      (fun ⦃P Q⦄ (h : P ≤ Q)  ↦ (Submodule.inclusion h).lTensor M) ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitRight _ M).symm.trans ((Submodules_small_equiv R N).lTensor M)
