/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Towers of algebras

We set up the basic theory of algebra towers.
An algebra tower A/S/R is expressed by having instances of `Algebra A S`,
`Algebra R S`, `Algebra R A` and `IsScalarTower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

In `FieldTheory/Tower.lean` we use this to prove the tower law for finite extensions,
that if `R` and `S` are both fields, then `[A:R] = [A:S] [S:A]`.

In this file we prepare the main lemma:
if `{bi | i ∈ I}` is an `R`-basis of `S` and `{cj | j ∈ J}` is an `S`-basis
of `A`, then `{bi cj | i ∈ I, j ∈ J}` is an `R`-basis of `A`. This statement does not require the
base rings to be a field, so we also generalize the lemma to rings in this file.
-/


open Pointwise

variable (R S A B : Type*)

namespace IsScalarTower

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra S B] [Algebra R A] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]

/-- Suppose that `R → S → A` is a tower of algebras.
If an element `r : R` is invertible in `S`, then it is invertible in `A`. -/
def Invertible.algebraTower (r : R) [Invertible (algebraMap R S r)] :
    Invertible (algebraMap R A r) :=
  Invertible.copy (Invertible.map (algebraMap S A) (algebraMap R S r)) (algebraMap R A r)
    (IsScalarTower.algebraMap_apply R S A r)

/-- A natural number that is invertible when coerced to `R` is also invertible
when coerced to any `R`-algebra. -/
def invertibleAlgebraCoeNat (n : ℕ) [inv : Invertible (n : R)] : Invertible (n : A) :=
  haveI : Invertible (algebraMap ℕ R n) := inv
  Invertible.algebraTower ℕ R A n

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

end CommSemiring

end IsScalarTower

section AlgebraMapCoeffs

variable {R} {ι M : Type*} [CommSemiring R] [Semiring A] [AddCommMonoid M]
variable [Algebra R A] [Module A M] [Module R M] [IsScalarTower R A M]
variable (b : Basis ι R M) (h : Function.Bijective (algebraMap R A))

/-- If `R` and `A` have a bijective `algebraMap R A` and act identically on `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module. -/
@[simps! repr_apply_toFun]
noncomputable def Basis.algebraMapCoeffs : Basis ι A M :=
  b.mapCoeffs (RingEquiv.ofBijective _ h) fun c x => by simp

@[simp]
theorem Basis.algebraMapCoeffs_repr (m : M) :
    (b.algebraMapCoeffs A h).repr m = (b.repr m).mapRange (algebraMap R A) (map_zero _) := by
  rfl

theorem Basis.algebraMapCoeffs_apply (i : ι) : b.algebraMapCoeffs A h i = b i :=
  b.mapCoeffs_apply _ _ _

@[simp]
theorem Basis.coe_algebraMapCoeffs : (b.algebraMapCoeffs A h : ι → M) = b :=
  b.coe_mapCoeffs _ _

end AlgebraMapCoeffs

section Semiring

open Finsupp

variable {R S A}
variable [Semiring R] [Semiring S] [AddCommMonoid A]
variable [Module R S] [Module S A] [Module R A] [IsScalarTower R S A]

theorem linearIndependent_smul {ι : Type*} {b : ι → S} {ι' : Type*} {c : ι' → A}
    (hb : LinearIndependent R b) (hc : LinearIndependent S c) :
    LinearIndependent R fun p : ι × ι' ↦ b p.1 • c p.2 := by
  classical
  rw [← linearIndependent_equiv' (.prodComm ..) (g := fun p : ι' × ι ↦ b p.2 • c p.1) rfl,
    LinearIndependent, linearCombination_smul]
  simpa using Function.Injective.comp hc
    ((mapRange_injective _ (map_zero _) hb).comp <| Equiv.injective _)

variable (R)

-- LinearIndependent is enough if S is a ring rather than semiring.
theorem Basis.isScalarTower_of_nonempty {ι} [Nonempty ι] (b : Basis ι S A) : IsScalarTower R S S :=
  (b.repr.symm.comp <| lsingle <| Classical.arbitrary ι).isScalarTower_of_injective R
    (b.repr.symm.injective.comp <| single_injective _)

theorem Basis.isScalarTower_finsupp {ι} (b : Basis ι S A) : IsScalarTower R S (ι →₀ S) :=
  b.repr.symm.isScalarTower_of_injective R b.repr.symm.injective

variable {R} {ι ι' : Type*} [DecidableEq ι'] (b : Basis ι R S) (c : Basis ι' S A)

/-- `Basis.smulTower (b : Basis ι R S) (c : Basis ι S A)` is the `R`-basis on `A`
where the `(i, j)`th basis vector is `b i • c j`. -/
noncomputable
def Basis.smulTower : Basis (ι × ι') R A :=
  haveI := c.isScalarTower_finsupp R
  .ofRepr
    (c.repr.restrictScalars R ≪≫ₗ
      (Finsupp.lcongr (Equiv.refl _) b.repr ≪≫ₗ
        ((finsuppProdLEquiv R).symm ≪≫ₗ
          Finsupp.lcongr (Equiv.prodComm ι' ι) (LinearEquiv.refl _ _))))

@[simp]
theorem Basis.smulTower_repr (x ij) :
    (b.smulTower c).repr x ij = b.repr (c.repr x ij.2) ij.1 := by
  simp [smulTower, Finsupp.uncurry_apply]

theorem Basis.smulTower_repr_mk (x i j) : (b.smulTower c).repr x (i, j) = b.repr (c.repr x j) i :=
  b.smulTower_repr c x (i, j)

@[simp]
theorem Basis.smulTower_apply (ij) : (b.smulTower c) ij = b ij.1 • c ij.2 := by
  classical
  obtain ⟨i, j⟩ := ij
  rw [Basis.apply_eq_iff]
  ext ⟨i', j'⟩
  rw [Basis.smulTower_repr, LinearEquiv.map_smul, Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  dsimp only
  split_ifs with hi
  · simp [hi, Finsupp.single_apply]
  · simp [hi]

/-- `Basis.smulTower (b : Basis ι R S) (c : Basis ι S A)` is the `R`-basis on `A`
where the `(i, j)`th basis vector is `b j • c i`. -/
noncomputable def Basis.smulTower' : Basis (ι' × ι) R A :=
  (b.smulTower c).reindex (.prodComm ..)

theorem Basis.smulTower'_repr (x ij) :
    (b.smulTower' c).repr x ij = b.repr (c.repr x ij.1) ij.2 := by
  rw [smulTower', repr_reindex_apply, smulTower_repr]; rfl

theorem Basis.smulTower'_repr_mk (x i j) : (b.smulTower' c).repr x (i, j) = b.repr (c.repr x i) j :=
  b.smulTower'_repr c x (i, j)

theorem Basis.smulTower'_apply (ij) : b.smulTower' c ij = b ij.2 • c ij.1 := by
  rw [smulTower', reindex_apply, smulTower_apply]; rfl

end Semiring

section Ring

variable {R S}
variable [CommRing R] [Ring S] [Algebra R S]

-- Porting note: Needed to add Algebra.toModule below
theorem Basis.algebraMap_injective {ι : Type*} [NoZeroDivisors R] [Nontrivial S]
    (b : @Basis ι R S _ _ Algebra.toModule) : Function.Injective (algebraMap R S) :=
  have : NoZeroSMulDivisors R S := b.noZeroSMulDivisors
  FaithfulSMul.algebraMap_injective R S

end Ring

section AlgHomTower

variable {A} {C D : Type*} [CommSemiring A] [CommSemiring C] [CommSemiring D] [Algebra A C]
  [Algebra A D]

variable [CommSemiring B] [Algebra A B] [Algebra B C] [IsScalarTower A B C] (f : C →ₐ[A] D)

/-- Restrict the domain of an `AlgHom`. -/
def AlgHom.restrictDomain : B →ₐ[A] D :=
  f.comp (IsScalarTower.toAlgHom A B C)

-- Porting note: definition below used to be
--  { f with commutes' := fun _ => rfl }
-- but it complains about not finding (Algebra B D), despite it being given in the header of the thm

/-- Extend the scalars of an `AlgHom`. -/
def AlgHom.extendScalars : @AlgHom B C D _ _ _ _ (f.restrictDomain B).toRingHom.toAlgebra where
  toFun := f.toFun
  map_one' := by simp only [toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    map_one]
  map_mul' := by simp only [toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, map_mul, MonoidHom.coe_coe, RingHom.coe_coe, forall_const]
  map_zero' := by simp only [toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe, map_zero]
  map_add' := by simp only [toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe, map_add, RingHom.coe_coe, forall_const]
  commutes' := fun _ ↦ rfl
  __ := (f.restrictDomain B).toRingHom.toAlgebra

variable {B}

/-- `AlgHom`s from the top of a tower are equivalent to a pair of `AlgHom`s. -/
def algHomEquivSigma :
    (C →ₐ[A] D) ≃ Σf : B →ₐ[A] D, @AlgHom B C D _ _ _ _ f.toRingHom.toAlgebra where
  toFun f := ⟨f.restrictDomain B, f.extendScalars B⟩
  invFun fg :=
    let _ := fg.1.toRingHom.toAlgebra
    fg.2.restrictScalars A
  left_inv f := by
    dsimp only
    ext
    rfl
  right_inv := by
    rintro ⟨⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩, ⟨⟨⟨⟨g, _⟩, _⟩, _⟩, hg⟩⟩
    obtain rfl : f = fun x => g (algebraMap B C x) := by
      ext x
      exact (hg x).symm
    rfl

end AlgHomTower
