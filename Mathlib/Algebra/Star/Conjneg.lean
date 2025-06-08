/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Star.Pi
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Conjugation-negation operator

This file defines the conjugation-negation operator, useful in Fourier analysis.

The way this operator enters the picture is that the adjoint of convolution with a function `f` is
convolution with `conjneg f`.
-/

open Function
open scoped ComplexConjugate

variable {ι G R : Type*} [AddGroup G]

section CommSemiring
variable [CommSemiring R] [StarRing R] {f g : G → R}

/-- Conjugation-negation. Sends `f` to `fun x ↦ conj (f (-x))`. -/
def conjneg (f : G → R) : G → R := conj fun x ↦ f (-x)

@[simp] lemma conjneg_apply (f : G → R) (x : G) : conjneg f x = conj (f (-x)) := rfl
@[simp] lemma conjneg_conjneg (f : G → R) : conjneg (conjneg f) = f := by ext; simp

lemma conjneg_involutive : Involutive (conjneg : (G → R) → G → R) := conjneg_conjneg
lemma conjneg_bijective : Bijective (conjneg : (G → R) → G → R) := conjneg_involutive.bijective
lemma conjneg_injective : Injective (conjneg : (G → R) → G → R) := conjneg_involutive.injective
lemma conjneg_surjective : Surjective (conjneg : (G → R) → G → R) := conjneg_involutive.surjective

@[simp] lemma conjneg_inj : conjneg f = conjneg g ↔ f = g := conjneg_injective.eq_iff
lemma conjneg_ne_conjneg : conjneg f ≠ conjneg g ↔ f ≠ g := conjneg_injective.ne_iff

@[simp] lemma conjneg_conj (f : G → R) : conjneg (conj f) = conj (conjneg f) := rfl

@[simp] lemma conjneg_zero : conjneg (0 : G → R) = 0 := by ext; simp
@[simp] lemma conjneg_one : conjneg (1 : G → R) = 1 := by ext; simp
@[simp] lemma conjneg_add (f g : G → R) : conjneg (f + g) = conjneg f + conjneg g := by ext; simp
@[simp] lemma conjneg_mul (f g : G → R) : conjneg (f * g) = conjneg f * conjneg g := by ext; simp

@[simp] lemma conjneg_sum (s : Finset ι) (f : ι → G → R) :
    conjneg (∑ i ∈ s, f i) = ∑ i ∈ s, conjneg (f i) := by ext; simp

@[simp] lemma conjneg_prod (s : Finset ι) (f : ι → G → R) :
    conjneg (∏ i ∈ s, f i) = ∏ i ∈ s, conjneg (f i) := by ext; simp

@[simp] lemma conjneg_eq_zero : conjneg f = 0 ↔ f = 0 := by
  rw [← conjneg_inj, conjneg_conjneg, conjneg_zero]

@[simp] lemma conjneg_eq_one : conjneg f = 1 ↔ f = 1 := by
  rw [← conjneg_inj, conjneg_conjneg, conjneg_one]

lemma conjneg_ne_zero : conjneg f ≠ 0 ↔ f ≠ 0 := conjneg_eq_zero.not
lemma conjneg_ne_one : conjneg f ≠ 1 ↔ f ≠ 1 := conjneg_eq_one.not

lemma sum_conjneg [Fintype G] (f : G → R) : ∑ a, conjneg f a = ∑ a, conj (f a) :=
  Fintype.sum_equiv (Equiv.neg _) _ _ fun _ ↦ rfl

@[simp] lemma support_conjneg (f : G → R) : support (conjneg f) = -support f := by
  ext; simp [starRingEnd_apply]

/-- `conjneg` bundled as a ring homomorphism. -/
@[simps] def conjnegRingHom : (G → R) →+* (G → R) where
  toFun := conjneg
  map_zero' := conjneg_zero
  map_one' := conjneg_one
  map_add' := conjneg_add
  map_mul' := conjneg_mul

end CommSemiring

section CommRing
variable [CommRing R] [StarRing R]

@[simp] lemma conjneg_sub (f g : G → R) : conjneg (f - g) = conjneg f - conjneg g := by ext; simp
@[simp] lemma conjneg_neg (f : G → R) : conjneg (-f) = -conjneg f := by ext; simp

end CommRing
