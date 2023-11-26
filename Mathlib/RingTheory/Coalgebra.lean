/-
Copyright (c) 2023 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey
-/
import Mathlib.RingTheory.TensorProduct

/-!
# Definition and example of a coalgebra
-/

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

/-- The `R`-module whose elements are functions `S → R` which are zero on all but finitely many
elements of `S` has a coalgebra structure. The coproduct is given by `Δ(fₛ) = fₛ ⊗ fₛ` and the
counit by `ε(fₛ) =  1`, where `fₛ` is the function sending `s` to `1` and all other elements of `S`
to zero. -/
noncomputable
instance Finsupp.instCoalgebra (R : Type u) (S : Type v) [CommRing R] : Coalgebra R (S →₀ R) where
  Δ := Finsupp.total S ((S →₀ R) ⊗[R] (S →₀ R)) R
    (fun s ↦ Finsupp.single s 1 ⊗ₜ Finsupp.single s 1)
  ε := Finsupp.total S R R (fun _ ↦ 1)
  coassoc := by
    ext; simp
  ε_id := by
    ext; simp
  id_ε := by
    ext; simp
