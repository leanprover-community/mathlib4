/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Weight spaces of Lie modules of nilpotent Lie algebras

Just as a key tool when studying the behaviour of a linear operator is to decompose the space on
which it acts into a sum of (generalised) eigenspaces, a key tool when studying a representation `M`
of Lie algebra `L` is to decompose `M` into a sum of simultaneous eigenspaces of `x` as `x` ranges
over `L`. These simultaneous eigenspaces are known as the weight spaces of `M`.

Basic definitions of the above ideas are provided in this file.

## Main definitions

  * `LieModule.Weight`
  * `LieModule.weightSpace`

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 7--9*](bourbaki1975b)

## Tags

lie character, eigenvalue, eigenspace, weight, weight vector, root, root vector
-/

variable {R L M : Type*} [CommRing R] [LieRing L]
  [AddCommGroup M] [Module R M] [LieRingModule L M]

namespace LieModule

open Set Function TensorProduct LieModule

variable (R L M) in
/-- A weight of a Lie module is a map `L → R` such that the corresponding weight space is
non-trivial. -/
structure Weight where
  /-- The family of eigenvalues corresponding to a weight. -/
  toFun : L → R
  exists_lie_eq_smul' : ∃ m : M, m ≠ 0 ∧ ∀ x : L, ⁅x, m⁆ = toFun x • m

namespace Weight

instance instFunLike : FunLike (Weight R L M) L R where
  coe χ := χ.1
  coe_injective' χ₁ χ₂ h := by cases χ₁; cases χ₂; simp_all

@[simp] lemma coe_weight_mk (χ : L → R) (h) :
    (↑(⟨χ, h⟩ : Weight R L M) : L → R) = χ :=
  rfl

@[ext] lemma ext {χ₁ χ₂ : Weight R L M} (h : ∀ x, χ₁ x = χ₂ x) : χ₁ = χ₂ := by
  cases' χ₁ with f₁ _; cases' χ₂ with f₂ _; aesop

lemma ext_iff' {χ₁ χ₂ : Weight R L M} : (χ₁ : L → R) = χ₂ ↔ χ₁ = χ₂ := by aesop

/-- The proposition that a weight of a Lie module is zero.

We make this definition because we cannot define a `Zero (Weight R L M)` instance since the weight
space of the zero function can be trivial. -/
def IsZero (χ : Weight R L M) := (χ : L → R) = 0

@[simp] lemma IsZero.eq {χ : Weight R L M} (hχ : χ.IsZero) : (χ : L → R) = 0 := hχ

@[simp] lemma coe_eq_zero_iff (χ : Weight R L M) : (χ : L → R) = 0 ↔ χ.IsZero := Iff.rfl

variable (R L M) in
/-- The set of weights is equivalent to a subtype. -/
def equivSetOf : Weight R L M ≃ {χ : L → R | ∃ m : M, m ≠ 0 ∧ ∀ x : L, ⁅x, m⁆ = χ x • m} where
  toFun w := ⟨w.1, w.2⟩
  invFun w := ⟨w.1, w.2⟩
  left_inv w := by simp
  right_inv w := by simp

end Weight

variable [LieAlgebra R L] [LieModule R L M]

variable (M) in
/-- If `M` is a representation of a Lie algebra `L` and `χ : L → R` is a family of scalars,
then `weightSpace M χ` is the intersection of the `χ x`-eigenspaces
of the action of `x` on `M` as `x` ranges over `L`. -/
def weightSpace (χ : L → R) : LieSubmodule R L M where
  __ := ⨅ x : L, (toEnd R L M x).eigenspace (χ x)
  lie_mem {x m} hm := by simp_all [smul_comm (χ x)]

lemma mem_weightSpace (χ : L → R) (m : M) : m ∈ weightSpace M χ ↔ ∀ x, ⁅x, m⁆ = χ x • m := by
  simp [weightSpace]

variable (R L M) in
/-- A Lie module `M` of a Lie algebra `L` is triangularizable if the endomorphism of `M` defined by
any `x : L` is triangularizable. -/
class IsTriangularizable : Prop where
  maxGenEigenspace_eq_top : ∀ x, ⨆ φ, (toEnd R L M x).maxGenEigenspace φ = ⊤

end LieModule
