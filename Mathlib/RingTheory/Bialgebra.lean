/-
Copyright (c) 2024 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey
-/
import Mathlib.RingTheory.Coalgebra
import Mathlib.RingTheory.TensorProduct

/-!
# Bialgebras

In this file we define `Bialgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toBialgebra`

## References

* <https://en.wikipedia.org/wiki/Bialgebra>
-/

suppress_compilation

universe u v

open scoped TensorProduct

/-- A bialgebra over a commutative (semi)ring `R` is both an algebra and a coalgebra over `R`, such
that the counit and comultiplication are algebra morphisms. -/
class Bialgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    Algebra R A, Coalgebra R A where
  -- The counit is an algebra morphism
  /-- The counit on a bialgebra preserves 1. -/
  counit_one : counit 1 = 1
  /-- The counit on a bialgebra preserves multiplication. -/
  counit_mul : ∀ a₁ a₂ : A, counit (a₁ * a₂) = counit a₁ * counit a₂
  -- The comultiplication is an algebra morphism
  /-- The comultiplication on a bialgebra preserves `1`. -/
  comul_one : comul 1 = 1
  /-- The comultiplication on a bialgebra preserves multiplication. -/
  comul_mul : ∀ a₁ a₂ : A, comul (a₁ * a₂) = comul a₁ * comul a₂

namespace Bialgebra
variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Semiring A] [B : Bialgebra R A]

attribute [simp] counit_one counit_mul comul_one comul_mul

/-- The counit of a bialgebra, as an R-algebra map. -/
def counitAlgHom : A →ₐ[R] R where
  toFun := B.counit
  map_one' := B.counit_one
  map_mul' := B.counit_mul
  map_zero' := B.counit.map_zero
  map_add' := B.counit.map_add
  commutes' := by simp [Algebra.algebraMap_eq_smul_one]

/-- The comultiplication of a bialgebra, as an R-algebra map. -/
def comulAlgHom : A →ₐ[R] A ⊗[R] A where
  toFun := B.comul
  map_one' := B.comul_one
  map_mul' := B.comul_mul
  map_zero' := B.comul.map_zero
  map_add' := B.comul.map_add
  commutes' := by simp [Algebra.algebraMap_eq_smul_one]

end Bialgebra

section CommSemiring
variable (R : Type u) [CommSemiring R]

open Bialgebra

namespace CommSemiring

/-- Every commutative (semi)ring is a bialgebra over itself -/
noncomputable
instance toBialgebra : Bialgebra R R where
  counit_mul := by simp
  counit_one := rfl
  comul_mul := by simp
  comul_one := rfl

end CommSemiring
