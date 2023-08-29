/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Invertible
import Mathlib.Algebra.Module.BigOperators
import Mathlib.LinearAlgebra.Basis

#align_import ring_theory.algebra_tower from "leanprover-community/mathlib"@"94825b2b0b982306be14d891c4f063a1eca4f370"

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

universe u v w u₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

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
#align is_scalar_tower.invertible.algebra_tower IsScalarTower.Invertible.algebraTower

/-- A natural number that is invertible when coerced to `R` is also invertible
when coerced to any `R`-algebra. -/
def invertibleAlgebraCoeNat (n : ℕ) [inv : Invertible (n : R)] : Invertible (n : A) :=
  haveI : Invertible (algebraMap ℕ R n) := inv
  Invertible.algebraTower ℕ R A n
#align is_scalar_tower.invertible_algebra_coe_nat IsScalarTower.invertibleAlgebraCoeNat

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
@[simps! repr_apply_support_val repr_apply_toFun]
noncomputable def Basis.algebraMapCoeffs : Basis ι A M :=
  b.mapCoeffs (RingEquiv.ofBijective _ h) fun c x => by simp
                                                        -- 🎉 no goals
#align basis.algebra_map_coeffs Basis.algebraMapCoeffs
#noalign Basis.algebraMapCoeffs_repr_symm_apply -- failed simpNF linter

theorem Basis.algebraMapCoeffs_apply (i : ι) : b.algebraMapCoeffs A h i = b i :=
  b.mapCoeffs_apply _ _ _
#align basis.algebra_map_coeffs_apply Basis.algebraMapCoeffs_apply

@[simp]
theorem Basis.coe_algebraMapCoeffs : (b.algebraMapCoeffs A h : ι → M) = b :=
  b.coe_mapCoeffs _ _
#align basis.coe_algebra_map_coeffs Basis.coe_algebraMapCoeffs

end AlgebraMapCoeffs

section Semiring

open Finsupp

open BigOperators Classical

universe v₁ w₁

variable {R S A}

variable [CommSemiring R] [Semiring S] [AddCommMonoid A]

variable [Algebra R S] [Module S A] [Module R A] [IsScalarTower R S A]

theorem linearIndependent_smul {ι : Type v₁} {b : ι → S} {ι' : Type w₁} {c : ι' → A}
    (hb : LinearIndependent R b) (hc : LinearIndependent S c) :
    LinearIndependent R fun p : ι × ι' => b p.1 • c p.2 := by
  rw [linearIndependent_iff'] at hb hc; rw [linearIndependent_iff'']; rintro s g hg hsg ⟨i, k⟩
  -- ⊢ LinearIndependent R fun p => b p.fst • c p.snd
                                        -- ⊢ ∀ (s : Finset (ι × ι')) (g : ι × ι' → R), (∀ (i : ι × ι'), ¬i ∈ s → g i = 0) …
                                                                      -- ⊢ g (i, k) = 0
  by_cases hik : (i, k) ∈ s
  -- ⊢ g (i, k) = 0
  · have h1 : ∑ i in s.image Prod.fst ×ˢ s.image Prod.snd, g i • b i.1 • c i.2 = 0 := by
      rw [← hsg]
      exact
        (Finset.sum_subset Finset.subset_product fun p _ hp =>
            show g p • b p.1 • c p.2 = 0 by rw [hg p hp, zero_smul]).symm
    rw [Finset.sum_product_right] at h1
    -- ⊢ g (i, k) = 0
    simp_rw [← smul_assoc, ← Finset.sum_smul] at h1
    -- ⊢ g (i, k) = 0
    exact hb _ _ (hc _ _ h1 k (Finset.mem_image_of_mem _ hik)) i (Finset.mem_image_of_mem _ hik)
    -- 🎉 no goals
  exact hg _ hik
  -- 🎉 no goals
#align linear_independent_smul linearIndependent_smul

/-- `Basis.SMul (b : Basis ι R S) (c : Basis ι S A)` is the `R`-basis on `A`
where the `(i, j)`th basis vector is `b i • c j`. -/
noncomputable def Basis.smul {ι : Type v₁} {ι' : Type w₁} (b : Basis ι R S) (c : Basis ι' S A) :
    Basis (ι × ι') R A :=
  .ofRepr
    (c.repr.restrictScalars R ≪≫ₗ
      (Finsupp.lcongr (Equiv.refl _) b.repr ≪≫ₗ
        ((finsuppProdLEquiv R).symm ≪≫ₗ
          Finsupp.lcongr (Equiv.prodComm ι' ι) (LinearEquiv.refl _ _))))
#align basis.smul Basis.smul

@[simp]
theorem Basis.smul_repr {ι : Type v₁} {ι' : Type w₁} (b : Basis ι R S) (c : Basis ι' S A) (x ij) :
    (b.smul c).repr x ij = b.repr (c.repr x ij.2) ij.1 := by simp [Basis.smul]
                                                             -- 🎉 no goals
#align basis.smul_repr Basis.smul_repr

theorem Basis.smul_repr_mk {ι : Type v₁} {ι' : Type w₁} (b : Basis ι R S) (c : Basis ι' S A)
    (x i j) : (b.smul c).repr x (i, j) = b.repr (c.repr x j) i :=
  b.smul_repr c x (i, j)
#align basis.smul_repr_mk Basis.smul_repr_mk

@[simp]
theorem Basis.smul_apply {ι : Type v₁} {ι' : Type w₁} (b : Basis ι R S) (c : Basis ι' S A) (ij) :
    (b.smul c) ij = b ij.1 • c ij.2 := by
  obtain ⟨i, j⟩ := ij
  -- ⊢ ↑(smul b c) (i, j) = ↑b (i, j).fst • ↑c (i, j).snd
  rw [Basis.apply_eq_iff]
  -- ⊢ ↑(smul b c).repr (↑b (i, j).fst • ↑c (i, j).snd) = single (i, j) 1
  ext ⟨i', j'⟩
  -- ⊢ ↑(↑(smul b c).repr (↑b (i, j).fst • ↑c (i, j).snd)) (i', j') = ↑(single (i,  …
  rw [Basis.smul_repr, LinearEquiv.map_smul, Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  dsimp only
  -- ⊢ ↑(↑b.repr (↑b i • if j = j' then 1 else 0)) i' = ↑(single (i, j) 1) (i', j')
  split_ifs with hi
  -- ⊢ ↑(↑b.repr (↑b i • 1)) i' = ↑(single (i, j) 1) (i', j')
  · simp [hi, Finsupp.single_apply]
    -- 🎉 no goals
  · simp [hi]
    -- 🎉 no goals
#align basis.smul_apply Basis.smul_apply

end Semiring

section Ring

variable {R S}

variable [CommRing R] [Ring S] [Algebra R S]

-- Porting note: Needed to add Algebra.toModule below
theorem Basis.algebraMap_injective {ι : Type*} [NoZeroDivisors R] [Nontrivial S]
    (b : @Basis ι R S _ _ Algebra.toModule) : Function.Injective (algebraMap R S) :=
  have : NoZeroSMulDivisors R S := b.noZeroSMulDivisors
  NoZeroSMulDivisors.algebraMap_injective R S
#align basis.algebra_map_injective Basis.algebraMap_injective

end Ring

section AlgHomTower

variable {A} {C D : Type*} [CommSemiring A] [CommSemiring C] [CommSemiring D] [Algebra A C]
  [Algebra A D]

variable (f : C →ₐ[A] D) [CommSemiring B] [Algebra A B] [Algebra B C] [IsScalarTower A B C]


/-- Restrict the domain of an `AlgHom`. -/
def AlgHom.restrictDomain : B →ₐ[A] D :=
  f.comp (IsScalarTower.toAlgHom A B C)
#align alg_hom.restrict_domain AlgHom.restrictDomain

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
#align alg_hom.extend_scalars AlgHom.extendScalars

variable {B}

/-- `AlgHom`s from the top of a tower are equivalent to a pair of `AlgHom`s. -/
def algHomEquivSigma : (C →ₐ[A] D) ≃ Σf : B →ₐ[A] D, @AlgHom B C D _ _ _ _ f.toRingHom.toAlgebra
    where
  toFun f := ⟨f.restrictDomain B, f.extendScalars B⟩
  invFun fg :=
    let _ := fg.1.toRingHom.toAlgebra
    fg.2.restrictScalars A
  left_inv f := by
    dsimp only
    -- ⊢ AlgHom.restrictScalars A (AlgHom.extendScalars B f) = f
    ext
    -- ⊢ ↑(AlgHom.restrictScalars A (AlgHom.extendScalars B f)) x✝ = ↑f x✝
    rfl
    -- 🎉 no goals
  right_inv := by
    rintro ⟨⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩, ⟨⟨⟨⟨g, _⟩, _⟩, _⟩, hg⟩⟩
    -- ⊢ (fun f => { fst := AlgHom.restrictDomain B f, snd := AlgHom.extendScalars B  …
    obtain rfl : f = fun x => g (algebraMap B C x) := by
      ext x
      exact (hg x).symm
    rfl
    -- 🎉 no goals
#align alg_hom_equiv_sigma algHomEquivSigma

end AlgHomTower
