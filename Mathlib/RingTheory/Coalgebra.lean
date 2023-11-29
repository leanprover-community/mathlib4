/-
Copyright (c) 2023 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey
-/
import Mathlib.RingTheory.TensorProduct

/-!
# Definition and example of a coalgebra
-/

suppress_compilation

universe u v

open scoped TensorProduct

/-- A coalgebra over a commutative ring `R` is a module over `R` equipped with a coassociative
comultiplication `Δ` and a counit `ε` obeying the left and right conunitality laws. -/
class Coalgebra (R : Type u) (A : Type v) [CommRing R] [AddCommGroup A] [Module R A] where
  /-- The comultiplication of the coalgebra -/
  Δ : A →ₗ[R] A ⊗[R] A
  /-- The counit of the coalgebra -/
  ε : A →ₗ[R] R
  /-- The comultiplication is coassociative -/
  coassoc : TensorProduct.assoc R A A A ∘ₗ TensorProduct.map Δ .id ∘ₗ Δ =
    TensorProduct.map .id Δ ∘ₗ Δ
  /-- The counit satisfies the left counitality law -/
  ε_id : TensorProduct.lid R A ∘ₗ TensorProduct.map ε .id ∘ₗ Δ = .id
  /-- The counit satisfies the right counitality law -/
  id_ε : TensorProduct.rid R A ∘ₗ TensorProduct.map .id ε ∘ₗ Δ = .id

namespace Coalgebra

section CommRingAddCommGroup

variable {R : Type u} {A : Type v}
variable [CommRing R] [AddCommGroup A] [Module R A] [Coalgebra R A]

@[simp]
theorem coassoc_apply (a : A) : TensorProduct.assoc R A A A (TensorProduct.map Δ .id (Δ a)) =
    TensorProduct.map .id Δ (Δ a) := LinearMap.congr_fun coassoc a

@[simp]
theorem ε_id_apply (a : A) : TensorProduct.lid R A (TensorProduct.map ε .id (Δ a)) = a :=
    LinearMap.congr_fun ε_id a

@[simp]
theorem id_ε_apply (a : A) : TensorProduct.rid R A (TensorProduct.map .id ε (Δ a)) = a :=
    LinearMap.congr_fun id_ε a

end CommRingAddCommGroup

end Coalgebra

open Coalgebra

section CommRing

variable (R : Type u) [CommRing R]

namespace CommRing

instance toCoalgebra : Coalgebra R R where
  Δ := (TensorProduct.mk R R R) 1
  ε := .id
  coassoc := rfl
  ε_id := by ext; simp
  id_ε := by ext; simp

@[simp]
theorem Δ_apply (r : R) : Δ r = 1 ⊗ₜ[R] r := rfl

@[simp]
theorem ε_apply (r : R) : ε r = r := rfl

end CommRing

namespace Finsupp

variable (ι : Type v)

/-- The `R`-module whose elements are functions `ι → R` which are zero on all but finitely many
elements of `ι` has a coalgebra structure. The coproduct is given by `Δ(fᵢ) = fᵢ ⊗ fᵢ` and the
counit by `ε(fᵢ) =  1`, where `fᵢ` is the function sending `i` to `1` and all other elements of `ι`
to zero. -/
noncomputable
instance instCoalgebra : Coalgebra R (ι →₀ R) where
  Δ := Finsupp.total ι ((ι →₀ R) ⊗[R] (ι →₀ R)) R
    (fun i ↦ Finsupp.single i 1 ⊗ₜ Finsupp.single i 1)
  ε := Finsupp.total ι R R (fun _ ↦ 1)
  coassoc := by
    ext; simp
  ε_id := by
    ext; simp
  id_ε := by
    ext; simp

@[simp]
theorem Δ_single (i : ι) (r : R) : Δ (Finsupp.single i r) =
    (Finsupp.single i r) ⊗ₜ[R] (Finsupp.single i 1) := by
  unfold Δ; unfold instCoalgebra; simp
  rw [TensorProduct.smul_tmul', smul_single_one i r]

@[simp]
theorem ε_single (i : ι) (r : R) : ε (Finsupp.single i r) = r := by
  unfold ε; unfold instCoalgebra; simp

end Finsupp

end CommRing
