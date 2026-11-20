/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Interaction between quotients and tensor products for modules with torsion

This file strengthens quotient equivalences from
`Mathlib.LinearAlgebra.TensorProduct.Quotient` from `R`-linear ones to `R ⧸ I`-linear ones.
They are separated from that file because they rely on the `R ⧸ I`-module structure,
which requires additional torsion API.
-/

@[expose] public section

namespace TensorProduct

variable {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] (I : Ideal R)

/-- Left tensoring with `R ⧸ I` identifies the base change with `M / IM` as an `R ⧸ I`-module. -/
noncomputable def quotTensorEquivQuotSMul' :
    ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I] (M ⧸ (I • (⊤ : Submodule R M))) :=
  (quotTensorEquivQuotSMul M I).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

@[simp]
lemma quotTensorEquivQuotSMul'_mk_tmul (r : R) (x : M) :
    quotTensorEquivQuotSMul' M I (Ideal.Quotient.mk I r ⊗ₜ[R] x) =
      Submodule.Quotient.mk (r • x) :=
  quotTensorEquivQuotSMul_mk_tmul I r x

@[simp]
lemma quotTensorEquivQuotSMul'_mk_one_tmul (x : M) :
    quotTensorEquivQuotSMul' M I (1 ⊗ₜ[R] x) = Submodule.Quotient.mk x :=
  quotTensorEquivQuotSMul_mk_one_tmul I x

@[simp]
lemma quotTensorEquivQuotSMul'_symm_mk (x : M) :
    (quotTensorEquivQuotSMul' M I).symm (Submodule.Quotient.mk x) = 1 ⊗ₜ[R] x :=
  quotTensorEquivQuotSMul_symm_mk I x

end TensorProduct
