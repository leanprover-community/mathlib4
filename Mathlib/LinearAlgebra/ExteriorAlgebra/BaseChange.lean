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

* `ExteriorAlgebra.baseChangeIso`: for `R`-algebra `S`, the base change isomorphism
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

lemma baseChangeExteriorAlgebraToTensor_apply (m : M) :
    baseChangeExteriorAlgebraToTensor R M S (ι S (1 ⊗ₜ[R] m)) = 1 ⊗ₜ[R] ι R m := by
  simp [baseChangeExteriorAlgebraToTensor]

def baseChangeIsoForwardAux : ExteriorAlgebra R M →ₐ[R]ExteriorAlgebra S (S ⊗[R] M) :=
  ExteriorAlgebra.lift R
    ⟨((ExteriorAlgebra.ι S).restrictScalars R).comp (TensorProduct.mk R S M 1), fun m ↦ by simp⟩

def baseChangeIsoForward : S ⊗[R] ExteriorAlgebra R M →ₐ[S] ExteriorAlgebra S (S ⊗[R] M) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (baseChangeIsoForwardAux R M S) (fun s y ↦ by
    simp [Algebra.commute_algebraMap_left])

lemma baseChangeIso_leftInverse :
    (baseChangeExteriorAlgebraToTensor R M S).comp (baseChangeIsoForward R M S) =
      AlgHom.id S _ := by
  ext m
  simp [baseChangeIsoForward, baseChangeIsoForwardAux, baseChangeExteriorAlgebraToTensor]

lemma baseChangeIsoForward_rightInverse :
    (baseChangeIsoForward R M S).comp (baseChangeExteriorAlgebraToTensor R M S) =
      AlgHom.id S _ := by
  ext m
  simp [baseChangeIsoForward, baseChangeIsoForwardAux, baseChangeExteriorAlgebraToTensor]

def baseChangeIso : S ⊗[R] ExteriorAlgebra R M ≃ₐ[S] ExteriorAlgebra S (S ⊗[R] M) where
  __ := baseChangeIsoForward R M S
  invFun := baseChangeExteriorAlgebraToTensor R M S
  left_inv x := AlgHom.congr_fun (baseChangeIso_leftInverse R M S) x
  right_inv x := AlgHom.congr_fun (baseChangeIsoForward_rightInverse R M S) x

lemma baseChangeIso_apply (m : M) : baseChangeIso R M S (1 ⊗ₜ[R] ι R m) = ι S (1 ⊗ₜ[R] m) := by
  simp [baseChangeIso, baseChangeIsoForward, baseChangeIsoForwardAux]

end ExteriorAlgebra
