/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Frobenius algebras

A Frobenius algebra is an algebra equipped with a `dual : Dual R A` such that the bilinear form
`(mul R a).compr₂ dual` is bijective and nondegenerate.
This means `A ≃ₗ[R] Module.Dual R A` and so over fields, a Frobenius algebra is finite-dimensional.

We also define the Nakayama automorphism `A ≃ₐ[R] A` such that
for all `a` and `b`, we have `dual (nakayamaAlgEquiv R A b * a) = dual (a * b)`.

## Main definitions and results



-/

variable {R A : Type*} [CommSemiring R]

open scoped RingTheory.LinearMap
open LinearMap Module TensorProduct

public section

variable (R A) in
/-- A **Frobenius algebra** is an algebra equipped with a dual such that
`mul.compr₂ dual` is bijective.

The bilinear form `mul.compr₂ dual` is nondegenerate. -/
class FrobeniusAlgebra [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A]
    [IsScalarTower R A A] where
  /-- The dual of a Frobenius algebra. -/
  dual : Dual R A
  bijective_compr₂_mul : Function.Bijective ((mul R A).compr₂ dual)

namespace FrobeniusAlgebra

section NonUnital
variable [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [FrobeniusAlgebra R A]

variable (R A) in
/-- The isomorphism of a Frobenius algebra with its dual, induced by the linear functional. -/
@[expose]
noncomputable def equivDual : A ≃ₗ[R] Module.Dual R A := .ofBijective _ bijective_compr₂_mul

@[simp] lemma equivDual_apply (a b : A) : equivDual R A a b = dual (a * b) := rfl
@[simp] lemma toLinearMap_equivDual : (equivDual R A).toLinearMap = (mul R A).compr₂ dual := rfl

@[simp] lemma dual_apply_symm_equivDual_mul (f : Dual R A) (a : A) :
    dual ((equivDual R A).symm f * a) = f a := by simp [← equivDual_apply]

@[simp] lemma symm_equivDual_compr₂_mul_dual (a : A) :
    (equivDual R A).symm (((mul R A).compr₂ dual) a) = a := by simp [equivDual]

lemma forall_dual_mul_left_eq_zero_iff {a : A} : (∀ b : A, dual (R := R) (a * b) = 0) ↔ a = 0 :=
  ⟨fun h ↦ (equivDual R A).injective (by ext; simp [h]), fun h ↦ by simp [h]⟩

lemma forall_dual_mul_right_eq_zero_iff {a : A} : (∀ b : A, dual (R := R) (b * a) = 0) ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  simp_rw [← forall_dual_mul_left_eq_zero_iff (R := R)]
  intro x
  simpa using h ((equivDual R A).symm (dual ∘ₗ (mul R A).flip x))

lemma nondegenerate_equivDual : ((mul R A).compr₂ dual).Nondegenerate := by
  simp [Nondegenerate, SeparatingLeft, SeparatingRight, forall_dual_mul_left_eq_zero_iff,
    forall_dual_mul_right_eq_zero_iff]

instance : FrobeniusAlgebra R R where
  dual := .id
  bijective_compr₂_mul := ⟨fun _ _ h ↦ by simpa using congr($h 1), fun f ↦ ⟨f 1, by ext; simp⟩⟩

end NonUnital

section NonAssoc
variable [NonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

/-- An algebra with an isomorphism `σ : A ≃ₗ[R] A →ₗ[R] R` such that
`σ (a * b) c = σ a (b * c)` induces a Frobenius algebra, where its dual will be `σ.flip 1`. -/
abbrev ofLinearEquiv (σ : A ≃ₗ[R] A →ₗ[R] R) (hσ : ∀ a b c : A, σ (a * b) c = σ a (b * c)) :
    FrobeniusAlgebra R A where
  dual := σ.flip 1
  bijective_compr₂_mul := by
    convert σ.bijective
    ext; simp [hσ]

/-- A finite-dimensional algebra with a separating left bilinear form `σ` such that
`σ (a * b) c = σ a (b * c)` induces a Frobenius algebra, where its dual will be `σ.flip 1`. -/
noncomputable abbrev ofBilinForm {K A : Type*} [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] (σ : LinearMap.BilinForm K A) (hσ : σ.SeparatingLeft)
    (hσ₂ : ∀ a b c : A, σ (a * b) c = σ a (b * c)) : FrobeniusAlgebra K A :=
  .ofLinearEquiv
    (.ofBijective σ (by simp [Function.Bijective, ← injective_iff_surjective_of_finrank_eq_finrank,
      ker_eq_bot.mp (separatingLeft_iff_ker_eq_bot.mp hσ)]))
    hσ₂

/-- A Frobenius algebra over a field is finite-dimensional. -/
instance instFiniteDimensional {K A : Type*} [Field K] [Ring A] [Algebra K A]
    [FrobeniusAlgebra K A] : FiniteDimensional K A :=
  Basis.linearEquiv_dual_iff_finiteDimensional.mp ⟨equivDual K A⟩

variable [FrobeniusAlgebra R A]

lemma flip_compr₂_mul_dual :
    ((mul R A).compr₂ (dual (R := R))).flip =
      (equivDual R A).dualMap ∘ₗ Module.Dual.eval R A := rfl

-- move
lemma _root_.Module.Dual.eval_injective (R M : Type*) [CommSemiring R] [AddCommMonoid M]
    [Module R M] : Function.Injective (Module.Dual.eval R (Module.Dual R M)) :=
  Function.LeftInverse.injective (g := (Module.Dual.eval R M).dualMap) fun _ ↦ by ext; simp

variable [Module.IsReflexive R A]

theorem bijective_flip_compr₂_mul :
    Function.Bijective ((mul R A).compr₂ (dual (R := R))).flip := by
  rw [flip_compr₂_mul_dual]
  exact (equivDual R A).dualMap.bijective.comp (Module.bijective_dual_eval R A)

end NonAssoc

section Semiring
variable [Semiring A] [Algebra R A] [Module.IsReflexive R A] [FrobeniusAlgebra R A]

variable (R A) in
/-- The Nakayama automorphism: `nakayamaAlgEquiv R A b` is the unique
element with `dual (nakayamaAlgEquiv R A b * a) = dual (a * b)` for all `a`. -/
noncomputable def nakayamaAlgEquiv : A ≃ₐ[R] A :=
  .ofLinearEquiv
    (.trans (.ofBijective _ bijective_flip_compr₂_mul) (equivDual R A).symm)
    ((equivDual R A).injective (by ext a; simp))
    (by simp [← (equivDual R A).injective.eq_iff, LinearMap.ext_iff, equivDual_apply, mul_assoc])

@[simp] theorem dual_nakayamaAlgEquiv_mul (a b : A) :
    dual (R := R) (nakayamaAlgEquiv R A b * a) = dual (a * b) := by
  simp [nakayamaAlgEquiv, AlgEquiv.ofLinearEquiv]

end Semiring

open Matrix
/-- Matrices over fields induces a natural Frobenius algebra, where the dual is the trace. -/
noncomputable abbrev _root_.Matrix.frobeniusAlgebra (K n : Type*) [Field K] [Fintype n]
    [DecidableEq n] : FrobeniusAlgebra K (Matrix n n K) :=
  .ofBilinForm ((mul K _).compr₂ (traceLinearMap n K K))
    (by simp [LinearMap.SeparatingLeft, ext_iff_trace_mul_right])
    (by simp [mul_assoc])

attribute [local instance] Matrix.frobeniusAlgebra in
lemma _root_.Matrix.frobeniusAlgebraDual_eq_traceLinearMap (K n : Type*) [Field K] [Fintype n]
    [DecidableEq n] : dual (R := K) (A := Matrix n n K) = traceLinearMap n K K := by
  ext; simp [dual]

end FrobeniusAlgebra
