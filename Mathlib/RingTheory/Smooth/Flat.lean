/-
Copyright (c) 2022 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.RingOfDefinition

universe u v

namespace Algebra

section

variable {R : Type*} [CommRing R]
variable (I : Ideal R) (J : Ideal R) (h : I ≤ J)

def Ideal.Quotient.factorₐ : R ⧸ I →ₐ[R] R ⧸ J := by
  fapply AlgHom.mk
  · exact Ideal.Quotient.factor I J h
  · intro r
    simp

end

section

variable (A : Type*) [CommRing A]
variable (B : Type*) [CommRing B] [Algebra A B]
variable (C : Type*) [CommRing C] [Algebra A C]

-- the unique algebra map to the zero algebra
def AlgHom.toTrivialAlgebra (h : Subsingleton C) : B →ₐ[A] C where
  toFun _ := 1
  map_one' := rfl
  map_mul' := by
    intro _ _
    simp
  map_zero' := by
    simp
    symm
    rwa [subsingleton_iff_zero_eq_one]
  map_add' := by
    simp
    symm
    rwa [subsingleton_iff_zero_eq_one]
  commutes' := by
    intro r
    simp
    apply eq_of_zero_eq_one
    rwa [subsingleton_iff_zero_eq_one]

@[simp]
lemma AlgHom.toTrivialAlgebra_apply_eq_one (h : Subsingleton C) (b : B) :
    AlgHom.toTrivialAlgebra A B C h b = 1 :=
  rfl

end

variable {A : Type u} [CommRing A]
variable {B : Type u} [CommRing B] [Algebra A B] [FormallySmooth A B]
variable {k : ℕ}

local notation "R" => MvPolynomial (Fin k) A

variable (f : MvPolynomial (Fin k) A →ₐ[A] B) (hf : Function.Surjective f)

local notation "I" => RingHom.ker f

noncomputable def transitionMap (n m : ℕ) (h : n ≤ m) : R ⧸ (I ^ m) →ₐ[A] R ⧸ (I ^ n) := by
  apply Ideal.quotientMapₐ (I ^ n) (AlgHom.id A _)
  change I ^ m ≤ I ^ n
  apply Ideal.pow_le_pow_right
  exact h

@[simp]
lemma transitionMap_mk (n m : ℕ) (h : n ≤ m) (p : R) :
    (transitionMap f n m h) p = p := by
  simp [transitionMap]

noncomputable def sectionAuxEquiv (m : ℕ) :
    ((R ⧸ I ^ (m + 1)) ⧸ (I ^ m).map (Ideal.Quotient.mk (I ^ (m + 1)))) ≃ₐ[A] R ⧸ (I ^ m) := by
  apply DoubleQuot.quotQuotEquivQuotOfLEₐ _
  apply Ideal.pow_le_pow_right
  exact Nat.le_succ m

@[simp]
lemma sectionAuxEquiv_mk (m : ℕ) (p : R) :
    sectionAuxEquiv f m p = p := by
  simp only [sectionAuxEquiv]
  change (DoubleQuot.quotQuotEquivQuotOfLEₐ A _) (DoubleQuot.quotQuotMk _ _ p) = p
  simp

lemma sectionAuxEquiv_comp (m : ℕ) :
    AlgHom.comp (sectionAuxEquiv f m).toAlgHom
      (Ideal.Quotient.mkₐ A <| (I ^ m).map (Ideal.Quotient.mk (I ^ (m + 1))))
    = transitionMap f m (m + 1) (by omega) := by
  apply AlgHom.cancel_surjective (Ideal.Quotient.mkₐ A (I ^ (m + 1)))
  · apply Ideal.Quotient.mkₐ_surjective
  · ext i
    simp

/-- Lift `B →ₐ[A] R ⧸ I` inductively to `B →ₐ[A] R ⧸ (I ^ m)` using formal smoothness.

Note that, since `B ≃ₐ[A] R ⧸ I ≃ₐ[A] R ⧸ (I ^ m) ⧸ (I ⧸ (I ^ m))`, we could also
lift this directly, but then we don't have compatibility with the canonical transition maps.
-/
noncomputable def sectionAux' : (m : ℕ) → B →ₐ[A] R ⧸ (I ^ (m + 1))
  | Nat.zero => by
      letI e : (R ⧸ I) ≃ₐ[A] R ⧸ (I ^ 1) := by
        apply Ideal.quotientEquivAlgOfEq A
        simp
      letI f' : (R ⧸ I) ≃ₐ[A] B := Ideal.quotientKerAlgEquivOfSurjective hf
      exact (AlgEquiv.trans f'.symm e).toAlgHom
  | Nat.succ m => by
      letI T := R ⧸ (I ^ (m + 2))
      letI J : Ideal T := Ideal.map (Ideal.Quotient.mk (I ^ (m + 2))) (I ^ (m + 1))
      letI q : B →ₐ[A] T ⧸ J := AlgHom.comp (sectionAuxEquiv f (m + 1)).symm (sectionAux' m)
      refine FormallySmooth.lift J ⟨m + 2, ?_⟩ q
      rw [← Ideal.map_pow, Submodule.zero_eq_bot, ← pow_mul]
      refine eq_bot_mono (Ideal.map_mono ?_) (Ideal.map_quotient_self _)
      apply Ideal.pow_le_pow_right
      simp

lemma sectionAux'_comp_transitionMap (m : ℕ) :
    AlgHom.comp (transitionMap f (m + 1) (m + 2) (Nat.succ_le_succ_iff.mpr (by omega))) (sectionAux' f hf (m + 1))
      = sectionAux' f hf m := by
  cases m <;> (
    simp only [sectionAux', ← sectionAuxEquiv_comp]
    ext
    simp
  )

/-- Extends `sectionAux` with the zero map in degree zero. -/
noncomputable def sectionAux : (m : ℕ) → B →ₐ[A] R ⧸ (I ^ m)
  | Nat.zero => by
      apply AlgHom.toTrivialAlgebra
      rw [Ideal.Quotient.subsingleton_iff]
      simp
  | Nat.succ m => sectionAux' f hf m

@[simp]
lemma sectionAux_comp_transitionMap (m : ℕ) :
    AlgHom.comp (transitionMap f m (m + 1) (by omega)) (sectionAux f hf (m + 1))
      = sectionAux f hf m := by
  cases m with
  | zero =>
      ext b
      apply eq_of_zero_eq_one
      rw [subsingleton_iff_zero_eq_one, Ideal.Quotient.subsingleton_iff]
      simp
  | succ m => exact sectionAux'_comp_transitionMap f hf m
