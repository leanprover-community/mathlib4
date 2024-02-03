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

## TODO

* Uniqueness of Hopf algebra structure on a bialgebra (i.e. if the algebra and coalgebra structures agree then the antipodes must also agree).

* S(1)=1 and S(ab)=S(b)S(a), so in particular if A is commutative then S is an algebra homomorphism.

* If H is commutative then S is necessarily a bijection (and I think its square must be the identity?)

References for these facts: Christian Kassel "Quantum Groups" (Springer GTM), around Prop III.3.1, Theorem III.3.4 etc.

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
  The two corresponding uncurried maps `A ⊗[R] A →ₗ[R]` (also equal)
  are the following: the first factors through `A` and is is multiplication on `A` followed
  by `counit`. The second factors through `R ⊗[R] R` is `counit ⊗ counit` followed by
  multiplication on `R`.

  See `Bialgebra.mk'` for a constructor for bialgebras which uses
  the more familiar `counit (a * b) = counit a * counit b`. -/
  mul_compr₂_counit : (LinearMap.mul R A).compr₂ counit = (LinearMap.mul R R).compl₁₂ counit counit
  -- The comultiplication is an algebra morphism
  /-- The comultiplication on a bialgebra preserves `1`. -/
  comul_one : comul 1 = 1
  /-- The comultiplication on a bialgebra preserves multiplication. This is written in
  a rather obscure way: it says that two curried maps `A →ₗ[R] A →ₗ[R] (A ⊗[R] A)`
  are equal. The corresponding equal uncurried maps `A ⊗[R] A →ₗ[R] A ⊗[R] A`
  are firstly multiplcation followed by `comul`, and secondly `comul ⊗ comul` followed
  by multiplication on `A ⊗[R] A`.

  See `Bialgebra.mk'` for a constructor for bialgebras which uses
  the more familiar `comul (a * b) = comul a * comul b`. -/
  mul_compr₂_comul :
    (LinearMap.mul R A).compr₂ comul = (LinearMap.mul R (A ⊗[R] A)).compl₁₂ comul comul

namespace Bialgebra

open Coalgebra

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Semiring A] [Bialgebra R A]

lemma counit_mul (a b : A) : counit (R := R) (a * b) = counit a * counit b :=
  DFunLike.congr_fun (DFunLike.congr_fun mul_compr₂_counit a) b

lemma comul_mul (a b : A) : comul (R := R) (a * b) = comul a * comul b :=
  DFunLike.congr_fun (DFunLike.congr_fun mul_compr₂_comul a) b

-- should `mul_compr₂_counit` and `mul_compr₂_comul` be simp?
attribute [simp] counit_one comul_one counit_mul comul_mul

/-- If `R` is a field (or even a commutative semiring) and `A`
is an `R`-algebra with a coalgebra structure, then `Bialgebra.mk'`
consumes proofs that the counit and comultiplication preserve
the identity and multiplication, and produces a bialgebra
structure on `A`. -/
def mk' (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    [Algebra R A] [C : Coalgebra R A] (counit_one : C.counit 1 = 1)
    (counit_mul : ∀ {a b}, C.counit (a * b) = C.counit a * C.counit b)
    (comul_one : C.comul 1 = 1)
    (comul_mul : ∀ {a b}, C.comul (a * b) = C.comul a * C.comul b) :
    Bialgebra R A where
      counit_one := counit_one
      mul_compr₂_counit := by ext; exact counit_mul
      comul_one := comul_one
      mul_compr₂_comul := by ext; exact comul_mul

variable (R A)

/-- `counitAlgHom R A` is the counit of the `R`-bialgebra `A`, as an `R`-algebra map. -/
@[simps!]
def counitAlgHom : A →ₐ[R] R :=
  .ofLinearMap counit counit_one counit_mul

/-- `comulAlgHom R A` is the comultiplication of the `R`-bialgebra `A`, as an `R`-algebra map. -/
@[simps!]
def comulAlgHom : A →ₐ[R] A ⊗[R] A :=
  .ofLinearMap comul comul_one comul_mul

variable {R A}

@[simp] lemma counit_algebraMap (r : R) : counit (R := R) (algebraMap R A r) = r :=
  (counitAlgHom R A).commutes r

@[simp] lemma comul_algebraMap (r : R) :
    comul (R := R) (algebraMap R A r) = algebraMap R (A ⊗[R] A) r :=
  (comulAlgHom R A).commutes r

@[simp] lemma counit_natCast (n : ℕ) : counit (R := R) (n : A) = n :=
  map_natCast (counitAlgHom R A) _

@[simp] lemma comul_natCast (n : ℕ) : comul (R := R) (n : A) = n :=
  map_natCast (comulAlgHom R A) _

@[simp] lemma counit_pow (a : A) (n : ℕ) : counit (R := R) (a ^ n) = counit a ^ n :=
  (counitAlgHom R A).map_pow a n

@[simp] lemma comul_pow (a : A) (n : ℕ) : comul (R := R) (a ^ n) = comul a ^ n :=
  (comulAlgHom R A).map_pow a n

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
