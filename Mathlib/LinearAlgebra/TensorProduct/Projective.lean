/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor products of projective modules

The tensor product of projective modules is projective.
-/

public section

namespace Module

variable {R : Type*} [Semiring R]
variable {R₀ M N} [CommSemiring R₀] [Algebra R₀ R] [AddCommMonoid M] [Module R₀ M] [Module R M]
variable [IsScalarTower R₀ R M] [AddCommMonoid N] [Module R₀ N]

open TensorProduct in
instance Projective.tensorProduct [hM : Module.Projective R M] [hN : Module.Projective R₀ N] :
    Module.Projective R (M ⊗[R₀] N) := by
  obtain ⟨sM, hsM⟩ := hM
  obtain ⟨sN, hsN⟩ := hN
  have : Module.Projective R (M ⊗[R₀] (N →₀ R₀)) := by
    fapply Projective.of_split (R := R) (M := ((M →₀ R) ⊗[R₀] (N →₀ R₀)))
    · exact (AlgebraTensorModule.map sM (LinearMap.id (R := R₀) (M := N →₀ R₀)))
    · exact (AlgebraTensorModule.map
        (Finsupp.linearCombination R id) (LinearMap.id (R := R₀) (M := N →₀ R₀)))
    · ext; simp [hsM _]
  fapply Projective.of_split (R := R) (M := (M ⊗[R₀] (N →₀ R₀)))
  · exact (AlgebraTensorModule.map (LinearMap.id (R := R) (M := M)) sN)
  · exact (AlgebraTensorModule.map (LinearMap.id (R := R) (M := M))
      (Finsupp.linearCombination R₀ id))
  · ext; simp [hsN _]

end Module
