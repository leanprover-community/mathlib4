/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.RingTheory.TensorProduct.Basic

/-!

# Some results on tensor product of subalgebras

## Linear maps induced by multiplication for subalgebras

Let `R` be a commutative ring, `S` be a commutative `R`-algebra.
Let `A` and `B` be `R`-subalgebras in `S` (`Subalgebra R S`). We define some linear maps
induced by the multiplication in `S`, which are
mainly used in the definition of linearly disjointness.

- `Subalgebra.mulMap`: the natural `R`-algebra homomorphism `A ⊗[R] B →ₐ[R] S`
  induced by the multiplication in `S`, whose image is `A ⊔ B` (`Subalgebra.mulMap_range`).

- `Subalgebra.mulMap'`: the natural `R`-algebra homomorphism `A ⊗[R] B →ₗ[R] A ⊔ B`
  induced by multiplication in `S`, which is surjective (`Subalgebra.mulMap'_surjective`).

-/

open scoped Classical TensorProduct

noncomputable section

universe u v w

namespace Subalgebra

variable {R : Type u} {S : Type v}

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable (A B : Subalgebra R S)

/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, there is the natural map
`A ⊗[R] B →ₐ[R] S` induced by multiplication in `S`. -/
def mulMap : A ⊗[R] B →ₐ[R] S := Algebra.TensorProduct.productMap A.val B.val

@[simp]
theorem mulMap_tmul (a : A) (b : B) : mulMap A B (a ⊗ₜ[R] b) = a.1 * b.1 := rfl

theorem mulMap_toLinearMap : (A.mulMap B).toLinearMap = (toSubmodule A).mulMap (toSubmodule B) :=
  rfl

theorem mulMap_comm : mulMap B A = (mulMap A B).comp (Algebra.TensorProduct.comm R B A) := by
  ext <;> simp

theorem mulMap_range : (A.mulMap B).range = A ⊔ B := by
  simp_rw [mulMap, Algebra.TensorProduct.productMap_range, Subalgebra.range_val]

/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, there is the natural map
`A ⊗[R] B →ₐ[R] A ⊔ B` induced by multiplication in `S`,
which is surjective (`Subalgebra.mulMap'_surjective`). -/
def mulMap' : A ⊗[R] B →ₐ[R] ↥(A ⊔ B) :=
  (equivOfEq _ _ (mulMap_range A B)).toAlgHom.comp (mulMap A B).rangeRestrict

@[simp]
theorem val_mulMap'_tmul (a : A) (b : B) : (mulMap A B (a ⊗ₜ[R] b) : S) = a.1 * b.1 := rfl

theorem mulMap'_surjective : Function.Surjective (mulMap' A B) := by
  simp_rw [mulMap', AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe,
    EquivLike.comp_surjective, AlgHom.rangeRestrict_surjective]

end Subalgebra
