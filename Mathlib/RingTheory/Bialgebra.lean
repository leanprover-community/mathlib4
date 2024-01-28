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

@[simp]
theorem counit_mul_apply (a₁ a₂ : A) : B.counit (a₁ * a₂) = B.counit a₁ * B.counit a₂ :=
  counit_mul a₁ a₂

@[simp]
theorem comul_mul_apply (a₁ a₂ : A) :
    B.comul (a₁ * a₂) = B.comul a₁ * B.comul a₂ :=
  comul_mul a₁ a₂

attribute [simp] counit_one comul_one

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
