/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!

# Nontriviality of tensor product of algebras

This file contains some more results on nontriviality of tensor product of algebras.

-/

open TensorProduct

namespace Algebra.TensorProduct

/-- If `A`, `B` are nontrivial algebras over a field `F`, then `A ⊗[F] B` is nontrivial. -/
theorem nontrivial_of_field
    (F A B : Type*) [Field F] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    [Nontrivial A] [Nontrivial B] : Nontrivial (A ⊗[F] B) :=
  nontrivial_of_algebraMap_injective_of_flat_left F A B (RingHom.injective _)

/-- If `A`, `B` are `R`-algebras, `R` injects into `A` and `B`,
and all of them are domains, then `A ⊗[R] B` is nontrivial. -/
theorem nontrivial_of_algebraMap_injective_of_isDomain
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (ha : Function.Injective (algebraMap R A)) (hb : Function.Injective (algebraMap R B))
    [IsDomain R] [IsDomain A] [IsDomain B] : Nontrivial (A ⊗[R] B) := by
  let FR := FractionRing R
  let FA := FractionRing A
  let FB := FractionRing B
  let fa : FR →ₐ[R] FA := IsFractionRing.liftAlgHom (g := Algebra.ofId R FA)
    ((IsFractionRing.injective A FA).comp ha)
  let fb : FR →ₐ[R] FB := IsFractionRing.liftAlgHom (g := Algebra.ofId R FB)
    ((IsFractionRing.injective B FB).comp hb)
  algebraize_only [fa.toRingHom, fb.toRingHom]
  have := nontrivial_of_field FR FA FB
  exact Algebra.TensorProduct.mapOfCompatibleSMul FR R FA FB |>.comp
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A FA) (IsScalarTower.toAlgHom R B FB))
    |>.toRingHom.domain_nontrivial

end Algebra.TensorProduct
