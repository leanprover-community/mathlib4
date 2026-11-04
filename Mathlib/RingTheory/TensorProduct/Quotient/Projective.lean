/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.RingTheory.TensorProduct.Quotient.Algebra
public import Mathlib.RingTheory.TensorProduct.Quotient.Torsion

/-!
# Projectivity over quotient scalar rings

-/

public section

variable {R : Type*} [CommRing R]

/-- If `M` is projective over `R`, then `M / IM` is projective over `R / I`. -/
instance Module.Projective.quotient_smul {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R) [Module.Projective R M] :
    Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
  Module.Projective.of_equiv' (TensorProduct.quotTensorEquivQuotSMul' M I)

/-- If an `R`-algebra `S` is projective over `R`, then `S / IS` is projective over `R / I`. -/
instance QuotientMapQuotient.projective {S : Type*} [CommRing S] [Algebra R S]
    (I : Ideal R) [Module.Projective R S] :
    Module.Projective (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  Module.Projective.of_equiv'
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toLinearEquiv
