/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
import Mathlib.LinearAlgebra.SesquilinearForm

/-!
# Bilinear form and linear maps

This file describes the relation between bilinear forms and linear maps.

## Notations

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, ie. `B x y = B.bilin x y`.

In this file we use the following type variables:
 - `M`, `M'`, ... are modules over the semiring `R`,
 - `M₁`, `M₁'`, ... are modules over the ring `R₁`,
 - `M₂`, `M₂'`, ... are modules over the commutative semiring `R₂`,
 - `M₃`, `M₃'`, ... are modules over the commutative ring `R₃`,
 - `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

open LinearMap (BilinForm)

namespace LinearMap

namespace BilinForm

variable {R R₁ R₂ R₃ M M₁ M₂ M₃ Mₗ₁ Mₗ₁' Mₗ₂ Mₗ₂' K K₁ K₂ V V₁ V₂ n : Type*}

variable [CommRing R₁]

variable [AddCommGroup M₁] [Module R₁ M₁]

variable [CommSemiring R]

variable [AddCommMonoid M] [Module R M]

/-- Apply a linear map to the left argument of a bilinear form. -/
def compLeft (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.compl₁₂ f LinearMap.id

/-- Apply a linear map to the right argument of a bilinear form. -/
def compRight (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.compl₁₂ LinearMap.id f

@[simp]
theorem compLeft_apply (B : BilinForm R M) (f : M →ₗ[R] M) (v w) : B.compLeft f v w = B (f v) w :=
  rfl

theorem compLeft_injective (B : BilinForm R₁ M₁) (b : B.SeparatingLeft) :
    Function.Injective (B.compLeft) := fun φ ψ h => by
  ext w
  refine' eq_of_sub_eq_zero (b _ _)
  intro v
  rw [map_sub, sub_apply, ← compLeft_apply, ← compLeft_apply, ← h, sub_self]
#align bilin_form.comp_left_injective LinearMap.BilinForm.compLeft_injective

theorem isAdjointPair_unique_of_separatingLeft (B : BilinForm R₁ M₁) (b : B.SeparatingLeft)
    (φ ψ₁ ψ₂ : M₁ →ₗ[R₁] M₁) (hψ₁ : IsAdjointPair B B ψ₁ φ) (hψ₂ : IsAdjointPair B B ψ₂ φ) :
    ψ₁ = ψ₂ := by
  apply B.compLeft_injective b
  ext v w
  rw [compLeft_apply, compLeft_apply, hψ₁, hψ₂]
#align bilin_form.is_adjoint_pair_unique_of_nondegenerate LinearMap.BilinForm.isAdjointPair_unique_of_separatingLeft

end BilinForm

end LinearMap
