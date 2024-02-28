/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying, Christopher Hoskin
-/
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Bilinear form and linear maps

This file describes the relation between bilinear forms and linear maps.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

open LinearMap (BilinForm)

namespace LinearMap

namespace BilinForm

variable {R M : Type*}

variable [CommSemiring R]

variable [AddCommMonoid M] [Module R M]

/-- Apply a linear map to the left argument of a bilinear form. -/
def compLeft (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.compl₁₂ f LinearMap.id
#align bilin_form.comp_left LinearMap.BilinForm.compLeft

/-- Apply a linear map to the right argument of a bilinear form. -/
def compRight (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.compl₁₂ LinearMap.id f

@[simp]
theorem compLeft_apply (B : BilinForm R M) (f : M →ₗ[R] M) (v w) : B.compLeft f v w = B (f v) w :=
  rfl

end BilinForm

end LinearMap
