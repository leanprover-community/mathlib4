/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Semisimple

/-!
# Semisimplicity of the adjoint action

This file proves that the adjoint action of a semisimple endomorphism is semisimple.
This is the semisimple analogue of `LieAlgebra.ad_nilpotent_of_nilpotent`.
-/

@[expose] public section

open Polynomial in
private lemma aeval_mulRight_apply {R : Type*} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M]
    (a : Module.End R M) (p : R[X]) (T : Module.End R M) :
    (aeval (LinearMap.mulRight R a) p) T = T * aeval a p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, mul_add]
  | monomial n c =>
    simp only [aeval_monomial, ← Algebra.smul_def, LinearMap.smul_apply,
      mul_smul_comm, LinearMap.pow_mulRight, LinearMap.mulRight_apply]

private theorem isSemisimple_mulLeft_of_isSemisimple {R : Type*} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {a : Module.End R M} (ha : a.IsSemisimple) :
    Module.End.IsSemisimple (LinearMap.mulLeft R a) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
  have : Polynomial.aeval (Algebra.lmul R (Module.End R M) a) (minpoly R a) = 0 := by
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  simpa using this

private theorem isSemisimple_mulRight_of_isSemisimple {R : Type*} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {a : Module.End R M} (ha : a.IsSemisimple) :
    Module.End.IsSemisimple (LinearMap.mulRight R a) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
  ext1 T
  simp only [LinearMap.zero_apply, aeval_mulRight_apply, minpoly.aeval, mul_zero]

/-- The adjoint of a semisimple endomorphism is semisimple. -/
theorem LieAlgebra.ad_isSemisimple_of_isSemisimple {R : Type*} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M] [PerfectField R]
    {a : Module.End R M} (ha : a.IsSemisimple) :
    (LieAlgebra.ad R (Module.End R M) a).IsSemisimple := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  exact (isSemisimple_mulLeft_of_isSemisimple ha).sub_of_commute
    (LinearMap.commute_mulLeft_right a a)
    (isSemisimple_mulRight_of_isSemisimple ha)
