/-
Copyright (c) 2023 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey
-/
import Mathlib.RingTheory.TensorProduct

/-!
# Coalgebras

In this file we define `Coalgebra`, and provide instances for:

* Commutative rings: `CommRing.toCoalgebra`
* Finitely supported functions: `Finsupp.instCoalgebra`

## References

* <https://en.wikipedia.org/wiki/Coalgebra>
-/

suppress_compilation

universe u v

open scoped TensorProduct

/-- A coalgebra over a commutative ring `R` is a module over `R` equipped with a coassociative
comultiplication `Δ` and a counit `ε` obeying the left and right conunitality laws. -/
class Coalgebra (R : Type u) (A : Type v) [CommRing R] [AddCommGroup A] [Module R A] where
  /-- The comultiplication of the coalgebra -/
  comul : A →ₗ[R] A ⊗[R] A
  /-- The counit of the coalgebra -/
  counit : A →ₗ[R] R
  /-- The comultiplication is coassociative -/
  coassoc : TensorProduct.assoc R A A A ∘ₗ comul.rTensor A ∘ₗ comul = comul.lTensor A ∘ₗ comul
  /-- The counit satisfies the left counitality law -/
  counit_id : TensorProduct.lid R A ∘ₗ counit.rTensor A ∘ₗ comul = .id
  /-- The counit satisfies the right counitality law -/
  id_counit : TensorProduct.rid R A ∘ₗ counit.lTensor A ∘ₗ comul = .id

namespace Coalgebra

section CommRingAddCommGroup

variable {R : Type u} {A : Type v}
variable [CommRing R] [AddCommGroup A] [Module R A] [Coalgebra R A]

@[simp]
theorem coassoc_apply (a : A) :
    TensorProduct.assoc R A A A (comul.rTensor A (comul a)) = comul.lTensor A (comul a) :=
  LinearMap.congr_fun coassoc a

@[simp]
theorem counit_id_apply (a : A) : TensorProduct.lid R A (counit.rTensor A (comul a)) = a :=
  LinearMap.congr_fun counit_id a

@[simp]
theorem id_counit_apply (a : A) : TensorProduct.rid R A (counit.lTensor A (comul a)) = a :=
  LinearMap.congr_fun id_counit a

end CommRingAddCommGroup

end Coalgebra

open Coalgebra

section CommRing

variable (R : Type u) [CommRing R]

namespace CommRing

instance toCoalgebra : Coalgebra R R where
  comul := (TensorProduct.mk R R R) 1
  counit := .id
  coassoc := rfl
  counit_id := by ext; simp
  id_counit := by ext; simp

@[simp]
theorem comul_apply (r : R) : comul r = 1 ⊗ₜ[R] r := rfl

@[simp]
theorem counit_apply (r : R) : counit r = r := rfl

end CommRing

namespace Finsupp

variable (ι : Type v)

/-- The `R`-module whose elements are functions `ι → R` which are zero on all but finitely many
elements of `ι` has a coalgebra structure. The coproduct `Δ` is given by `Δ(fᵢ) = fᵢ ⊗ fᵢ` and the
counit `ε` by `ε(fᵢ) =  1`, where `fᵢ` is the function sending `i` to `1` and all other elements of
`ι` to zero. -/
noncomputable
instance instCoalgebra : Coalgebra R (ι →₀ R) where
  comul := Finsupp.total ι ((ι →₀ R) ⊗[R] (ι →₀ R)) R
    (fun i ↦ Finsupp.single i 1 ⊗ₜ Finsupp.single i 1)
  counit := Finsupp.total ι R R (fun _ ↦ 1)
  coassoc := by
    ext; simp
  counit_id := by
    ext; simp
  id_counit := by
    ext; simp

@[simp]
theorem comul_single (i : ι) (r : R) : comul (Finsupp.single i r) =
    (Finsupp.single i r) ⊗ₜ[R] (Finsupp.single i 1) := by
  unfold comul instCoalgebra
  rw [total_single, TensorProduct.smul_tmul', smul_single_one i r]

@[simp]
theorem counit_single (i : ι) (r : R) : counit (Finsupp.single i r) = r := by
  unfold counit instCoalgebra; simp

end Finsupp

end CommRing
