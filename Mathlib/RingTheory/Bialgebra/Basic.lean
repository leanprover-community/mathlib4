/-
Copyright (c) 2024 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey, Kevin Buzzard
-/
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bialgebras

In this file we define `Bialgebra`s.

## Main definitions

* `Bialgebra R A`: the structure of a bialgebra on the `R`-algebra `A`;
* `CommSemiring.toBialgebra`: a commutative semiring is a bialgebra over itself.

## Implementation notes

Rather than the "obvious" axiom `∀ a b, counit (a * b) = counit a * counit b`, the far
more convoluted `mul_compr₂_counit` is used as a structure field; this says that
the corresponding two maps `A →ₗ[R] A →ₗ[R] R` are equal; a similar trick is
used for comultiplication as well. An alternative constructor `Bialgebra.mk'` is provided
with the more easily-readable axioms. The argument for using the more convoluted axioms
is that in practice there is evidence that they will be easier to prove (especially
when dealing with things like tensor products of bialgebras). This does make the definition
more surprising to mathematicians, however mathlib is no stranger to definitions which
are surprising to mathematicians -- see for example its definition of a group.
Note that this design decision is also compatible with that of `Coalgebra`. The lengthy
docstring for these convoluted fields attempts to explain what is going on.

The constructor `Bialgebra.ofAlgHom` is dual to the default constructor: For `R` is a commutative
semiring and `A` a `R`-algebra, it consumes the counit and comultiplication as algebra homomorphisms
that satisfy the coalgebra axioms to define a bialgebra structure on `A`.

## References

* <https://en.wikipedia.org/wiki/Bialgebra>

## Tags

bialgebra
-/

universe u v w

open Function
open scoped TensorProduct

/-- A bialgebra over a commutative (semi)ring `R` is both an algebra and a coalgebra over `R`, such
that the counit and comultiplication are algebra morphisms. -/
class Bialgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    Algebra R A, Coalgebra R A where
  -- The counit is an algebra morphism
  /-- The counit on a bialgebra preserves 1. -/
  counit_one : counit 1 = 1
  /-- The counit on a bialgebra preserves multiplication. Note that this is written
  in a rather obscure way: it says that two bilinear maps `A →ₗ[R] A →ₗ[R]` are equal.
  The two corresponding equal linear maps `A ⊗[R] A →ₗ[R]`
  are the following: the first factors through `A` and is multiplication on `A` followed
  by `counit`. The second factors through `R ⊗[R] R`, and is `counit ⊗ counit` followed by
  multiplication on `R`.

  See `Bialgebra.mk'` for a constructor for bialgebras which uses
  the more familiar but mathematically equivalent `counit (a * b) = counit a * counit b`. -/
  mul_compr₂_counit : (LinearMap.mul R A).compr₂ counit = (LinearMap.mul R R).compl₁₂ counit counit
  -- The comultiplication is an algebra morphism
  /-- The comultiplication on a bialgebra preserves `1`. -/
  comul_one : comul 1 = 1
  /-- The comultiplication on a bialgebra preserves multiplication. This is written in
  a rather obscure way: it says that two bilinear maps `A →ₗ[R] A →ₗ[R] (A ⊗[R] A)`
  are equal. The corresponding equal linear maps `A ⊗[R] A →ₗ[R] A ⊗[R] A`
  are firstly multiplication followed by `comul`, and secondly `comul ⊗ comul` followed
  by multiplication on `A ⊗[R] A`.

  See `Bialgebra.mk'` for a constructor for bialgebras which uses the more familiar
  but mathematically equivalent `comul (a * b) = comul a * comul b`. -/
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

@[simp] lemma toLinearMap_counitAlgHom : (counitAlgHom R A).toLinearMap = counit := rfl
@[simp] lemma toLinearMap_comulAlgHom : (comulAlgHom R A).toLinearMap = comul := rfl

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
  map_pow (counitAlgHom R A) a n

@[simp] lemma comul_pow (a : A) (n : ℕ) : comul (R := R) (a ^ n) = comul a ^ n :=
  map_pow (comulAlgHom R A) a n

end Bialgebra

namespace CommSemiring
variable (R : Type u) [CommSemiring R]

open Bialgebra

/-- Every commutative (semi)ring is a bialgebra over itself -/
instance toBialgebra : Bialgebra R R where
  mul_compr₂_counit := by ext; simp
  counit_one := rfl
  mul_compr₂_comul := by ext; simp
  comul_one := rfl

end CommSemiring

namespace Bialgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- If `R` is a commutative semiring and `A` is an `R`-algebra,
then `Bialgebra.ofAlgHom` consumes the counit and comultiplication
as algebra homomorphisms that satisfy the coalgebra axioms to define
a bialgebra structure on `A`. -/
abbrev ofAlgHom (comul : A →ₐ[R] (A ⊗[R] A)) (counit : A →ₐ[R] R)
    (h_coassoc : (Algebra.TensorProduct.assoc R R A A A).toAlgHom.comp
      ((Algebra.TensorProduct.map comul (.id R A)).comp comul)
      = (Algebra.TensorProduct.map (.id R A) comul).comp comul)
    (h_rTensor : (Algebra.TensorProduct.map counit (.id R A)).comp comul
      = (Algebra.TensorProduct.lid R A).symm)
    (h_lTensor : (Algebra.TensorProduct.map (.id R A) counit).comp comul
      = (Algebra.TensorProduct.rid R R A).symm) :
    Bialgebra R A :=
  letI : Coalgebra R A := {
    comul := comul
    counit := counit
    coassoc := congr(($h_coassoc).toLinearMap)
    rTensor_counit_comp_comul := congr(($h_rTensor).toLinearMap)
    lTensor_counit_comp_comul := congr(($h_lTensor).toLinearMap)
  }
  .mk' _ _ (map_one counit) (map_mul counit _ _) (map_one comul) (map_mul comul _ _)

end Bialgebra

namespace Bialgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

variable (A) in
lemma algebraMap_injective : Injective (algebraMap R A) := RightInverse.injective counit_algebraMap

lemma counit_surjective : Surjective (Coalgebra.counit : A →ₗ[R] R) :=
  RightInverse.surjective counit_algebraMap

include R in
variable (R) in
/-- A bialgebra over a nontrivial ring is nontrivial. -/
lemma nontrivial [Nontrivial R] : Nontrivial A := (algebraMap_injective (R := R) _).nontrivial

end Bialgebra
