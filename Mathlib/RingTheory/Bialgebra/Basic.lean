/-
Copyright (c) 2024 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey, Kevin Buzzard
-/
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.TensorProduct

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

## References

* <https://en.wikipedia.org/wiki/Bialgebra>

## Tags

bialgebra
-/

suppress_compilation

open scoped TensorProduct
set_option autoImplicit false

/-- A bialgebra over a commutative (semi)ring `R` is both an algebra and a coalgebra over `R`, such
that the counit and comultiplication are algebra morphisms. -/
class Bialgebra (R A : Type*) [CommSemiring R] [Semiring A] extends
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
  are firstly multiplcation followed by `comul`, and secondly `comul ⊗ comul` followed
  by multiplication on `A ⊗[R] A`.

  See `Bialgebra.mk'` for a constructor for bialgebras which uses the more familiar
  but mathematically equivalent `comul (a * b) = comul a * comul b`. -/
  mul_compr₂_comul :
    (LinearMap.mul R A).compr₂ comul = (LinearMap.mul R (A ⊗[R] A)).compl₁₂ comul comul

namespace Bialgebra

open Coalgebra

variable {R A : Type*}
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
def mk' (R A : Type*) [CommSemiring R] [Semiring A]
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

instance MonoidAlgebra.instCoalgebra {G : Type*} : Coalgebra R (MonoidAlgebra A G) :=
  inferInstanceAs (Coalgebra R (G →₀ A))

lemma ffs {G : Type*} : MonoidAlgebra A G = (G →₀ A) := rfl

instance MonoidAlgebra.instBialgebra {G : Type*} [Monoid G] : Bialgebra R (MonoidAlgebra A G) :=
{ counit_one := by
    simp only [MonoidAlgebra.one_def, MonoidAlgebra.single, MonoidAlgebra,
      Finsupp.counit_single, counit_one]
  mul_compr₂_counit := Finsupp.lhom_ext' fun g =>
    LinearMap.ext fun x => Finsupp.lhom_ext' fun h => by
      ext y
      simp_rw [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
        ffs, LinearMap.compr₂_apply, LinearMap.mul, ← ffs, LinearMap.mk₂_apply,
        MonoidAlgebra.single_mul_single,ffs, Finsupp.counit_single, counit_mul,
        LinearMap.compl₁₂_apply, Finsupp.counit_single, LinearMap.mk₂_apply]
  comul_one := by
    simp only [ffs, MonoidAlgebra.one_def, MonoidAlgebra.single, Finsupp.comul_single, comul_one]
    rfl
  mul_compr₂_comul := Finsupp.lhom_ext' fun g =>
    LinearMap.ext fun x => Finsupp.lhom_ext' fun h => by
      ext y
      simp_rw [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
        ffs, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, Finsupp.comul_single,
        ← ffs, LinearMap.mul_apply', MonoidAlgebra.single_mul_single, MonoidAlgebra.single,
        ffs, Finsupp.comul_single, comul_mul, ← ffs]
      show (LinearMap.mul R (A ⊗[R] A)).compr₂ (TensorProduct.map _ _) _ _
        = (LinearMap.mul R _).compl₁₂ _ _ _ _
      -- not sure if worth factoring out the rest
      congr
      ext a b c d
      simp only [ffs, TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
        LinearMap.coe_restrictScalars, LinearMap.compr₂_apply, LinearMap.mul_apply',
        Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul, Finsupp.lsingle_apply,
        LinearMap.compl₁₂_apply]
      simp only [← ffs, LinearMap.mul_apply', Algebra.TensorProduct.tmul_mul_tmul,
        MonoidAlgebra.single_mul_single]
         }

lemma ffs2 {G : Type*} : AddMonoidAlgebra A G = (G →₀ A) := rfl

instance AddMonoidAlgebra.instBialgebra {G : Type*} [AddMonoid G] :
  Bialgebra R (AddMonoidAlgebra A G) :=
{ Finsupp.instCoalgebra R G A with
  counit_one := by
    simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.single, AddMonoidAlgebra,
      Finsupp.counit_single, counit_one]
  mul_compr₂_counit := Finsupp.lhom_ext' fun g =>
    LinearMap.ext fun x => Finsupp.lhom_ext' fun h => by
      ext y
      simp_rw [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
        ffs2, LinearMap.compr₂_apply, LinearMap.mul, ← ffs2, LinearMap.mk₂_apply,
        AddMonoidAlgebra.single_mul_single, ffs2, Finsupp.counit_single, counit_mul,
        LinearMap.compl₁₂_apply, Finsupp.counit_single, LinearMap.mk₂_apply]
  comul_one := by
    simp only [ffs2, AddMonoidAlgebra.one_def, AddMonoidAlgebra.single, Finsupp.comul_single, comul_one]
    rfl
  mul_compr₂_comul := Finsupp.lhom_ext' fun g =>
    LinearMap.ext fun x => Finsupp.lhom_ext' fun h => by
      ext y
      simp_rw [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
        ffs2, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, Finsupp.comul_single,
        ← ffs2, LinearMap.mul_apply', AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single,
        ffs2, Finsupp.comul_single, comul_mul, ← ffs2]
      show (LinearMap.mul R (A ⊗[R] A)).compr₂ (TensorProduct.map _ _) _ _
        = (LinearMap.mul R _).compl₁₂ _ _ _ _
      -- not sure if worth factoring out the rest
      congr
      ext a b c d
      simp only [ffs2, TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
        LinearMap.coe_restrictScalars, LinearMap.compr₂_apply, LinearMap.mul_apply',
        Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul, Finsupp.lsingle_apply,
        LinearMap.compl₁₂_apply]
      simp only [← ffs2, LinearMap.mul_apply', Algebra.TensorProduct.tmul_mul_tmul,
        AddMonoidAlgebra.single_mul_single]
         }

def ofAlgEquiv {B : Type*} [Semiring B] [Algebra R B] (f : A ≃ₐ[R] B)
    [CoalgebraStruct R B] (hcounit : counit (R := R) (A := B) ∘ₗ f.toLinearEquiv
      = counit (R := R) (A := A))
    (hcomul : TensorProduct.map f.toLinearEquiv f.toLinearEquiv ∘ₗ comul (R := R) (A := A)
      = comul (R := R) (A := B) ∘ₗ f.toLinearEquiv) :
    Bialgebra R B := by
  refine' Bialgebra.mk' (C := Coalgebra.ofLinearEquiv f.toLinearEquiv hcounit hcomul) _ _ _ _
  <;> simp only [(f.toLinearEquiv.eq_comp_toLinearMap_symm _ _).2 hcounit,
      ← (f.toLinearEquiv.comp_toLinearMap_symm_eq _ _).2 hcomul]
  · simp only [AlgEquiv.toLinearEquiv_symm,
    AlgEquiv.toLinearEquiv_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, map_one, counit_one]
  · intros
    simp only [AlgEquiv.toLinearEquiv_symm,
      AlgEquiv.toLinearEquiv_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgEquiv.toLinearMap_apply, map_mul, counit_mul, forall_const]
  · simp only [AlgEquiv.toLinearEquiv_toLinearMap,
    AlgEquiv.toLinearEquiv_symm, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, map_one, comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.map_tmul]
  · intros
    show Algebra.TensorProduct.map f.toAlgHom f.toAlgHom _ = _
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toLinearEquiv_symm,
      AlgEquiv.toLinearEquiv_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgEquiv.toLinearMap_apply, map_mul, comul_mul]
    rfl

@[simp] lemma AddMonoidAlgebra.toMultiplicative_apply {k G : Type*} [Semiring k] [Add G] :
  (AddMonoidAlgebra.toMultiplicative k G :
    AddMonoidAlgebra k G → MonoidAlgebra k (Multiplicative G))
    = Finsupp.equivMapDomain Multiplicative.ofAdd := by
  rfl

@[simp] lemma AddMonoidAlgebra.toMultiplicative_symm_apply {k G : Type*} [Semiring k] [Add G] :
  ((AddMonoidAlgebra.toMultiplicative k G).symm :
    MonoidAlgebra k (Multiplicative G) → AddMonoidAlgebra k G)
    = Finsupp.equivMapDomain Multiplicative.ofAdd.symm := by
  rfl

@[simp] lemma AddMonoidAlgebra.toMultiplicativeAlgEquiv_apply {k G : Type*}
  [Semiring k] [Algebra R k] [AddMonoid G] :
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv k G (R := R) :
    AddMonoidAlgebra k G → MonoidAlgebra k (Multiplicative G))
    = Finsupp.equivMapDomain Multiplicative.ofAdd := by
  rfl

@[simp] lemma AddMonoidAlgebra.toMultiplicativeAlgEquiv_symm_apply {k G : Type*}
  [Semiring k] [Algebra R k] [AddMonoid G] :
  ((AddMonoidAlgebra.toMultiplicativeAlgEquiv k G (R := R)).symm :
    MonoidAlgebra k (Multiplicative G) → AddMonoidAlgebra k G)
    = Finsupp.equivMapDomain Multiplicative.ofAdd.symm := by
  rfl


-- dismal, i give up

#check Finsupp.domLCongr
/-lemma hmmm {G : Type*} [AddMonoid G] :
    Coalgebra.comul (R := R) (A := AddMonoidAlgebra A G)
      = Coalgebra.comul (R := R) (A := G →₀ A) := Finsupp.lhom_ext fun a b => by
  simp only [ofLinearEquivStruct_comul, AlgEquiv.toLinearEquiv_toLinearMap,
    AlgEquiv.toLinearEquiv_symm, AlgEquiv.symm_symm, LinearMap.coe_comp, Function.comp_apply]
  simp only [ffs]
  erw [Finsupp.comul_single]
  erw [AddMonoidAlgebra.toMultiplicative_apply]
  simp only [Finsupp.equivMapDomain_single, Finsupp.comul_single]
  rw [← TensorProduct.map_comp]
  simp only [ofLinearEquivStruct_comul, ffs, LinearMap.coe_comp, Function.comp_apply]
  erw [Finsupp.comul_single]
  --show TensorProduct.map (Finsupp.lmapDomain _) _ (comul (Finsupp.domCongr _ _)) = _
  simp only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_single, Finsupp.comul_single]
  simp only [AddMonoidAlgebra.toMultiplicativeAlgEquiv, RingEquiv.toEquiv_eq_coe]

  simp only [ofLinearEquivStruct_comul, AlgEquiv.toLinearEquiv_toLinearMap,
    AlgEquiv.toLinearEquiv_symm, AlgEquiv.symm_symm]-/

end Bialgebra

section CommSemiring
variable (R : Type*) [CommSemiring R]

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
