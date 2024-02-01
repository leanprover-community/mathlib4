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
  /-- The counit on a bialgebra preserves multiplication. Note that this is written
  in a rather obscure way: it says that two curried maps `A →ₗ[R] A →ₗ[R]` are equal.
  The two corresponding uncurried maps `A ⊗[R] A →ₗ[R]` which are hence also equal,
  are the following: the first factors through `A` and is is multiplication on `A` followed
  by `counit`. The second factors through `R ⊗[R] R` is `counit ⊗ counit` followed by
  multiplication on `R`. -/
  mul_compr₂_counit : (LinearMap.mul R A).compr₂ counit = (LinearMap.mul R R).compl₁₂ counit counit
  -- The comultiplication is an algebra morphism
  /-- The comultiplication on a bialgebra preserves `1`. -/
  comul_one : comul 1 = 1
  /-- The comultiplication on a bialgebra preserves multiplication. This is written in
  a rather obscure way: it says that two curried maps `A →ₗ[R] A →ₗ[R] (A ⊗[R] A)`
  are equal. The corresponding equal uncurried maps `A ⊗[R] A →ₗ[R] A ⊗[R] A`
  are firstly multiplcation followed by `comul`, and secondly `comul ⊗ comul` followed
  by multiplication on `A ⊗[R] A`. -/
  mul_compr₂_comul :
    (LinearMap.mul R A).compr₂ comul = (LinearMap.mul R (A ⊗[R] A)).compl₁₂ comul comul

namespace Bialgebra

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Semiring A] [B : Bialgebra R A]

lemma counit_mul {a b : A} : B.counit (a * b) = B.counit a * B.counit b :=
  DFunLike.congr_fun (DFunLike.congr_fun (B.mul_compr₂_counit) a) b

lemma comul_mul {a b : A} : B.comul (a * b) = B.comul a * B.comul b :=
  DFunLike.congr_fun (DFunLike.congr_fun (B.mul_compr₂_comul) a) b

-- should `mul_compr₂_counit` and `mul_compr₂_comul` be simp?
attribute [simp] counit_one comul_one counit_mul comul_mul

variable (R A)

/-- `counitAlgHom R A` is the counit of the `R`-bialgebra `A`, as an `R`-algebra map. -/
def counitAlgHom : A →ₐ[R] R where
  toFun := B.counit
  map_one' := B.counit_one
  map_mul' x y := counit_mul
  map_zero' := B.counit.map_zero
  map_add' := B.counit.map_add
  commutes' := by simp [Algebra.algebraMap_eq_smul_one]

/-- `comulAlgHom R A` is the comultiplication of the `R`-bialgebra `A`, as an `R`-algebra map. -/
def comulAlgHom : A →ₐ[R] A ⊗[R] A where
  toFun := B.comul
  map_one' := B.comul_one
  map_mul' x y := comul_mul
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
  mul_compr₂_counit := by ext; simp
  counit_one := rfl
  mul_compr₂_comul := by ext; simp
  comul_one := rfl

end CommSemiring
