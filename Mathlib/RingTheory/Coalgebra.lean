/-
Copyright (c) 2023 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey
-/
import Mathlib.RingTheory.TensorProduct

/-!
# Coalgebras

In this file we define `Coalgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toCoalgebra`
* Finitely supported functions: `Finsupp.instCoalgebra`

## References

* <https://en.wikipedia.org/wiki/Coalgebra>
-/

suppress_compilation

universe u v

open scoped TensorProduct

/-- A coalgebra over a commutative (semi)ring `R` is an `R`-module equipped with a coassociative
comultiplication `Δ` and a counit `ε` obeying the left and right conunitality laws. -/
class Coalgebra (R : Type u) (A : Type v) [CommSemiring R] [AddCommMonoid A] [Module R A] where
  /-- The comultiplication of the coalgebra -/
  comul : A →ₗ[R] A ⊗[R] A
  /-- The counit of the coalgebra -/
  counit : A →ₗ[R] R
  /-- The comultiplication is coassociative -/
  coassoc : TensorProduct.assoc R A A A ∘ₗ comul.rTensor A ∘ₗ comul = comul.lTensor A ∘ₗ comul
  /-- The counit satisfies the left counitality law -/
  rTensor_counit_comp_comul : counit.rTensor A ∘ₗ comul = TensorProduct.mk R _ _ 1
  /-- The counit satisfies the right counitality law -/
  lTensor_counit_comp_comul : counit.lTensor A ∘ₗ comul = (TensorProduct.mk R _ _).flip 1

namespace Coalgebra
variable {R : Type u} {A : Type v}
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

@[simp]
theorem coassoc_apply (a : A) :
    TensorProduct.assoc R A A A (comul.rTensor A (comul a)) = comul.lTensor A (comul a) :=
  LinearMap.congr_fun coassoc a

@[simp]
theorem coassoc_symm_apply (a : A) :
    (TensorProduct.assoc R A A A).symm (comul.lTensor A (comul a)) = comul.rTensor A (comul a) := by
  rw [(TensorProduct.assoc R A A A).symm_apply_eq, coassoc_apply a]

@[simp]
theorem coassoc_symm :
    (TensorProduct.assoc R A A A).symm ∘ₗ comul.lTensor A ∘ₗ comul =
    comul.rTensor A ∘ₗ (comul (R := R)) :=
  LinearMap.ext coassoc_symm_apply

@[simp]
theorem rTensor_counit_comul (a : A) : counit.rTensor A (comul a) = 1 ⊗ₜ[R] a :=
  LinearMap.congr_fun rTensor_counit_comp_comul a

@[simp]
theorem lTensor_counit_comul (a : A) : counit.lTensor A (comul a) = a ⊗ₜ[R] 1 :=
  LinearMap.congr_fun lTensor_counit_comp_comul a

end Coalgebra
section CommSemiring
variable (R : Type u) [CommSemiring R]

open Coalgebra

namespace CommSemiring

/-- Every commutative (semi)ring is a coalgebra over itself, with `Δ r = 1 ⊗ₜ r`. -/
instance toCoalgebra : Coalgebra R R where
  comul := (TensorProduct.mk R R R) 1
  counit := .id
  coassoc := rfl
  rTensor_counit_comp_comul := by ext; rfl
  lTensor_counit_comp_comul := by ext; rfl

@[simp]
theorem comul_apply (r : R) : comul r = 1 ⊗ₜ[R] r := rfl

@[simp]
theorem counit_apply (r : R) : counit r = r := rfl

end CommSemiring

namespace Finsupp
variable (ι : Type v)

/-- The `R`-module whose elements are functions `ι → R` which are zero on all but finitely many
elements of `ι` has a coalgebra structure. The coproduct `Δ` is given by `Δ(fᵢ) = fᵢ ⊗ fᵢ` and the
counit `ε` by `ε(fᵢ) =  1`, where `fᵢ` is the function sending `i` to `1` and all other elements of
`ι` to zero. -/
noncomputable
instance instCoalgebra : Coalgebra R (ι →₀ R) where
  comul := Finsupp.total ι ((ι →₀ R) ⊗[R] (ι →₀ R)) R (fun i ↦ .single i 1 ⊗ₜ .single i 1)
  counit := Finsupp.total ι R R (fun _ ↦ 1)
  coassoc := by ext; simp
  rTensor_counit_comp_comul := by ext; simp
  lTensor_counit_comp_comul := by ext; simp

@[simp]
theorem comul_single (i : ι) (r : R) :
    comul (Finsupp.single i r) = (Finsupp.single i r) ⊗ₜ[R] (Finsupp.single i 1) := by
  unfold comul instCoalgebra
  rw [total_single, TensorProduct.smul_tmul', smul_single_one i r]

@[simp]
theorem counit_single (i : ι) (r : R) : counit (Finsupp.single i r) = r := by
  unfold counit instCoalgebra; simp

end Finsupp

end CommSemiring
