/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!

# Base change of exterior algebra

In this file, we proved that exterior algebra commutes with arbitrary base change.

# Main Results

* `ExteriorAlgebra.baseChangeEquiv`: for `R`-algebra `S`, the base change isomorphism
  `S ⊗[R] (⋀[R]^i M) ≃ₗ[S] ⋀[S]^i (S ⊗[R] M)`

-/

public noncomputable section

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

variable (S : Type*) [CommRing S] [Algebra R S]

open TensorProduct

namespace ExteriorAlgebra

/-- Abbreviation of base change of `ExteriorAlgebra.ι`. -/
abbrev baseChangeι : S ⊗[R] M →ₗ[S] S ⊗[R] ExteriorAlgebra R M :=
  (ExteriorAlgebra.ι R).baseChange S

lemma baseChangeι_mul_add_swap (x y : S ⊗[R] M) :
    baseChangeι R M S x * baseChangeι R M S y + baseChangeι R M S y * baseChangeι R M S x = 0 := by
  -- Reduce the anticommutation relation to pure tensors in each variable.
  refine TensorProduct.inductionOn x ?_ (fun a b ha hb ↦ ?_)
  · refine TensorProduct.inductionOn y ?_ (fun c d hc hd ↦ ?_)
    · simp [Algebra.TensorProduct.tmul_mul_tmul, ExteriorAlgebra.ι_add_mul_swap, mul_comm,
        ← TensorProduct.tmul_add]
    · intro u v
      simpa [map_add, add_mul, mul_add, add_assoc, add_left_comm, add_comm] using
        congrArg₂ (· + ·) (hc u v) (hd u v)
  · simpa [map_add, add_mul, mul_add, add_assoc, add_left_comm, add_comm] using
      congrArg₂ (· + ·) ha hb

lemma baseChangeι_sq_zero (x : S ⊗[R] M) : baseChangeι R M S x * baseChangeι R M S x = 0 := by
  refine TensorProduct.inductionOn x ?_ (fun a b ha hb ↦ ?_)
  · simp [ExteriorAlgebra.baseChangeι, Algebra.TensorProduct.tmul_mul_tmul]
  · simp only [map_add, mul_add, add_mul, add_left_comm, add_assoc]
    simp [ha, hb, ExteriorAlgebra.baseChangeι_mul_add_swap R M S a b]

/-- The exterior algebra map from `ExteriorAlgebra S (S ⊗[R] M)` to `S ⊗[R] ExteriorAlgebra R M`,
lift from `ExteriorAlgebra.baseChangeι`. -/
def baseChangeExteriorAlgebraToTensor :
    ExteriorAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] ExteriorAlgebra R M :=
  ExteriorAlgebra.lift S
    ⟨ExteriorAlgebra.baseChangeι R M S, ExteriorAlgebra.baseChangeι_sq_zero R M S⟩

lemma baseChangeExteriorAlgebraToTensor_apply (s : S) (m : M) :
    baseChangeExteriorAlgebraToTensor R M S (ι S (s ⊗ₜ[R] m)) = s ⊗ₜ[R] ι R m := by
  simp [baseChangeExteriorAlgebraToTensor]

/-- The auxiliary construction for `ExteriorAlgebra.baseChangeEquivForward`. -/
def baseChangeEquivForwardAux : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra S (S ⊗[R] M) :=
  ExteriorAlgebra.lift R
    ⟨((ExteriorAlgebra.ι S).restrictScalars R).comp (TensorProduct.mk R S M 1), fun m ↦ by simp⟩

/-- The forward map of `ExteriorAlgebra.baseChangeEquiv`, lift from universal property of
tensor product and `ExteriorAlgebra`. -/
def baseChangeEquivForward : S ⊗[R] ExteriorAlgebra R M →ₐ[S] ExteriorAlgebra S (S ⊗[R] M) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (baseChangeEquivForwardAux R M S) (fun s y ↦ by
    simp [Algebra.commute_algebraMap_left])

lemma baseChangeEquiv_leftInverse :
    (baseChangeExteriorAlgebraToTensor R M S).comp (baseChangeEquivForward R M S) =
      AlgHom.id S _ := by
  ext m
  simp [baseChangeEquivForward, baseChangeEquivForwardAux, baseChangeExteriorAlgebraToTensor]

lemma baseChangeEquivForward_rightInverse :
    (baseChangeEquivForward R M S).comp (baseChangeExteriorAlgebraToTensor R M S) =
      AlgHom.id S _ := by
  ext m
  simp [baseChangeEquivForward, baseChangeEquivForwardAux, baseChangeExteriorAlgebraToTensor]

/-- The commute of `ExteriorAlgebra` and base change. -/
def baseChangeEquiv : S ⊗[R] ExteriorAlgebra R M ≃ₐ[S] ExteriorAlgebra S (S ⊗[R] M) where
  __ := baseChangeEquivForward R M S
  invFun := baseChangeExteriorAlgebraToTensor R M S
  left_inv x := AlgHom.congr_fun (baseChangeEquiv_leftInverse R M S) x
  right_inv x := AlgHom.congr_fun (baseChangeEquivForward_rightInverse R M S) x

lemma baseChangeEquiv_apply (m : M) : baseChangeEquiv R M S (1 ⊗ₜ[R] ι R m) = ι S (1 ⊗ₜ[R] m) := by
  simp [baseChangeEquiv, baseChangeEquivForward, baseChangeEquivForwardAux]

end ExteriorAlgebra
