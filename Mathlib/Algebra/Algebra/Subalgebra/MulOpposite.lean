/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!

# Opposite of subalgebras

This file defines some equivalences between subalgebras and their opposite.

-/

namespace Subalgebra

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A] (S : Subalgebra R A)

/-- The ordered set of subalgebras of the opposite algebra is isomorphic to the
ordered set of subalgebras. -/
def equivOpposite : Subalgebra R Aᵐᵒᵖ ≃o Subalgebra R A where
  toFun S := { MulOpposite.unop (Submodule.equivOpposite (toSubmodule S)) with
    mul_mem' := fun ha hb ↦ S.mul_mem hb ha
    algebraMap_mem' := S.algebraMap_mem }
  invFun S := { Submodule.equivOpposite.symm (MulOpposite.op (toSubmodule S)) with
    mul_mem' := fun ha hb ↦ S.mul_mem hb ha
    algebraMap_mem' := S.algebraMap_mem }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' {_} {_} :=
    Submodule.comap_le_comap_iff_of_surjective (MulOpposite.opLinearEquiv R).surjective _ _

/-- There is a natural linear isomorphism from a subalgebra `S` to
its `Subalgebra.equivOpposite`. -/
def opLinearEquiv : S ≃ₗ[R] equivOpposite.symm S :=
  ((MulOpposite.opLinearEquiv R).symm.ofSubmodule' (toSubmodule S)).symm

/-- There is a natural algebra isomorphism from a subalgebra `S` to
the opposite of its `Subalgebra.equivOpposite`. -/
def opAlgEquiv : S ≃ₐ[R] (equivOpposite.symm S)ᵐᵒᵖ where
  __ := opLinearEquiv S ≪≫ₗ MulOpposite.opLinearEquiv _
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- There is a natural algebra isomorphism from the opposite of a subalgebra `S` to
the its `Subalgebra.equivOpposite`. -/
def opAlgEquiv' : Sᵐᵒᵖ ≃ₐ[R] equivOpposite.symm S where
  __ := (MulOpposite.opLinearEquiv _).symm ≪≫ₗ opLinearEquiv S
  map_mul' _ _ := rfl
  commutes' _ := rfl

end Subalgebra
