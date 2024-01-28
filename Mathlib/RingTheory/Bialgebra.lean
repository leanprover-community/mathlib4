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

universe u v

open scoped TensorProduct

/-- A bialgebra over a commutative (semi)ring `R` is both an algebra and a coalgebra over `R`, such
that the counit and comultiplication are algebra morphisms. -/
class Bialgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    Algebra R A, Coalgebra R A where
  /-- The counit is an algebra morphism -/
  counit_mul : ∀ a₁ a₂ : A, counit (a₁ * a₂) = counit a₁ * counit a₂
  counit_unit : counit 1 = 1
  /-- The comultiplication is an algebra morphism -/
  comul_mul : ∀ a₁ a₂ : A, comul (a₁ * a₂) = Algebra.TensorProduct.mul (comul a₁) (comul a₂)
  comul_unit : comul 1 = 1

namespace Bialgebra
variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Semiring A] [B : Bialgebra R A]

@[simp]
theorem counit_mul_apply (a₁ a₂ : A) : B.counit (a₁ * a₂) = B.counit a₁ * B.counit a₂ :=
  counit_mul a₁ a₂

@[simp]
theorem counit_unit_apply : B.counit 1 = 1 :=
  counit_unit

@[simp]
theorem comul_mul_apply (a₁ a₂ : A) :
    B.comul (a₁ * a₂) = Algebra.TensorProduct.mul (B.comul a₁) (B.comul a₂) :=
  comul_mul a₁ a₂

@[simp]
theorem comul_unit_apply : B.comul 1 = 1 :=
  comul_unit

end Bialgebra

section CommSemiring
variable (R : Type u) [CommSemiring R]

open Bialgebra

namespace CommSemiring

/-- Every commutative (semi)ring is a bialgebra over itself -/
noncomputable
instance toBialgebra : Bialgebra R R where
  counit_mul := by simp
  counit_unit := rfl
  comul_mul := by simp
  comul_unit := rfl

end CommSemiring
