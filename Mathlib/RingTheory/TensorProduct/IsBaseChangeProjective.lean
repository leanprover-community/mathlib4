/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change of projective modules

Extension of scalars preserves projectivity. The tensor product case is already provided by
`Module.Projective.tensorProduct`. This file treats other presentations of base change relying on
`IsTensorProduct`.

## Main results

* `IsBaseChange.projective`: a base change of a projective module is projective.
* `Algebra.IsPushout.projective`: projectivity is preserved by a pushout of algebras.
-/

public section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable {M N : Type*} [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- A base change of a projective module is projective. -/
theorem IsBaseChange.projective {f : M →ₗ[R] N} (h : IsBaseChange S f)
    [Module.Projective R M] : Module.Projective S N :=
  Module.Projective.of_equiv' h.equiv

variable {A B : Type*} [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
variable [IsScalarTower R S B] [IsScalarTower R A B]

/-- Projectivity is preserved by a pushout of algebras. -/
theorem Algebra.IsPushout.projective [h : Algebra.IsPushout R S A B]
    [Module.Projective R A] : Module.Projective S B :=
  h.out.projective
