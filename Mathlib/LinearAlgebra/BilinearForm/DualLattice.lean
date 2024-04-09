/-
Copyright (c) 2018 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.SesquilinearForm.DualLattice

/-!

# Dual submodule with respect to a bilinear form.

## Main definitions and results
- `BilinForm.dualSubmodule`: The dual submodule with respect to a bilinear form.
- `BilinForm.dualSubmodule_span_of_basis`: The dual of a lattice is spanned by the dual basis.

## TODO
Properly develop the material in the context of lattices.
-/

open LinearMap (BilinForm)

variable {R S M} [CommRing R] [Field S] [AddCommGroup M]
variable [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]

namespace LinearMap

namespace BilinForm

variable (B : BilinForm S M)

/-- The dual submodule of a submodule with respect to a bilinear form. -/
def dualSubmodule (N : Submodule R M) : Submodule R M :=
  LinearMap.BilinForm.dualSubmodule (BilinForm.toLin B) N

lemma mem_dualSubmodule {N : Submodule R M} {x} :
    x ∈ B.dualSubmodule N ↔ ∀ y ∈ N, B x y ∈ (1 : Submodule R S) := Iff.rfl

lemma le_flip_dualSubmodule {N₁ N₂ : Submodule R M} :
    N₁ ≤ B.flip.dualSubmodule N₂ ↔ N₂ ≤ B.dualSubmodule N₁ :=
  LinearMap.BilinForm.le_flip_dualSubmodule (BilinForm.toLin B)

/-- The natural paring of `B.dualSubmodule N` and `N`.
This is bundled as a bilinear map in `BilinForm.dualSubmoduleToDual`. -/
noncomputable
def dualSubmoduleParing {N : Submodule R M} (x : B.dualSubmodule N) (y : N) : R :=
  LinearMap.BilinForm.dualSubmoduleParing (BilinForm.toLin B) x y

@[simp]
lemma dualSubmoduleParing_spec {N : Submodule R M} (x : B.dualSubmodule N) (y : N) :
    algebraMap R S (B.dualSubmoduleParing x y) = B x y :=
  LinearMap.BilinForm.dualSubmoduleParing_spec (BilinForm.toLin B) x y

/-- The natural paring of `B.dualSubmodule N` and `N`. -/
-- TODO: Show that this is perfect when `N` is a lattice and `B` is nondegenerate.
@[simps!]
noncomputable
def dualSubmoduleToDual [NoZeroSMulDivisors R S] (N : Submodule R M) :
    B.dualSubmodule N →ₗ[R] Module.Dual R N :=
  LinearMap.BilinForm.dualSubmoduleToDual (BilinForm.toLin B) N

lemma dualSubmoduleToDual_injective (hB : B.Nondegenerate) [NoZeroSMulDivisors R S]
    (N : Submodule R M) (hN : Submodule.span S (N : Set M) = ⊤) :
    Function.Injective (B.dualSubmoduleToDual N) :=
  LinearMap.BilinForm.dualSubmoduleToDual_injective (BilinForm.toLin B) hB N hN

lemma dualSubmodule_span_of_basis {ι} [Finite ι] [DecidableEq ι]
    (hB : B.Nondegenerate) (b : Basis ι S M) :
    B.dualSubmodule (Submodule.span R (Set.range b)) =
      Submodule.span R (Set.range <| B.dualBasis hB b) :=
  LinearMap.BilinForm.dualSubmodule_span_of_basis (BilinForm.toLin B) hB b

lemma dualSubmodule_dualSubmodule_flip_of_basis {ι : Type*} [Finite ι]
    (hB : B.Nondegenerate) (b : Basis ι S M) :
    B.dualSubmodule (B.flip.dualSubmodule (Submodule.span R (Set.range b))) =
      Submodule.span R (Set.range b) :=
  LinearMap.BilinForm.dualSubmodule_dualSubmodule_flip_of_basis (BilinForm.toLin B) hB b

lemma dualSubmodule_flip_dualSubmodule_of_basis {ι : Type*} [Finite ι]
    (hB : B.Nondegenerate) (b : Basis ι S M) :
    B.flip.dualSubmodule (B.dualSubmodule (Submodule.span R (Set.range b))) =
      Submodule.span R (Set.range b) :=
  LinearMap.BilinForm.dualSubmodule_flip_dualSubmodule_of_basis (BilinForm.toLin B) hB b

lemma dualSubmodule_dualSubmodule_of_basis
    {ι} [Finite ι] (hB : B.Nondegenerate) (hB' : B.IsSymm) (b : Basis ι S M) :
    B.dualSubmodule (B.dualSubmodule (Submodule.span R (Set.range b))) =
      Submodule.span R (Set.range b) :=
  LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis (BilinForm.toLin B) hB hB' b
