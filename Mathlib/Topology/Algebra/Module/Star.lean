/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis

! This file was ported from Lean 3 source module topology.algebra.module.star
! leanprover-community/mathlib commit aa6669832974f87406a3d9d70fc5707a60546207
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Star.Module
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Star

/-!
# The star operation, bundled as a continuous star-linear equiv
-/


set_option linter.uppercaseLean3 false

/-- If `A` is a topological module over a commutative `R` with compatible actions,
then `star` is a continuous semilinear equivalence. -/
@[simps!]
def starL (R : Type _) {A : Type _} [CommSemiring R] [StarRing R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] [TopologicalSpace A] [ContinuousStar A] :
    A ≃L⋆[R] A where
  toLinearEquiv := starLinearEquiv R
  continuous_toFun := continuous_star
  continuous_invFun := continuous_star
#align starL starL

variable (R : Type _) (A : Type _) [Semiring R] [StarSemigroup R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A] [Invertible (2 : R)] [TopologicalSpace A]

theorem continuous_selfAdjointPart [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A] :
    Continuous (@selfAdjointPart R A _ _ _ _ _ _ _ _) :=
  ((continuous_const_smul _).comp <| continuous_id.add continuous_star).subtype_mk _
#align continuous_self_adjoint_part continuous_selfAdjointPart

theorem continuous_skewAdjointPart [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A] :
    Continuous (@skewAdjointPart R A _ _ _ _ _ _ _ _) :=
  ((continuous_const_smul _).comp <| continuous_id.sub continuous_star).subtype_mk _
#align continuous_skew_adjoint_part continuous_skewAdjointPart

theorem continuous_decomposeProdAdjoint [TopologicalAddGroup A] [ContinuousStar A]
    [ContinuousConstSMul R A] : Continuous (@StarModule.decomposeProdAdjoint R A _ _ _ _ _ _ _ _) :=
  (continuous_selfAdjointPart R A).prod_mk (continuous_skewAdjointPart R A)
#align continuous_decompose_prod_adjoint continuous_decomposeProdAdjoint

theorem continuous_decomposeProdAdjoint_symm [TopologicalAddGroup A] :
    Continuous (@StarModule.decomposeProdAdjoint R A _ _ _ _ _ _ _ _).symm :=
  (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
#align continuous_decompose_prod_adjoint_symm continuous_decomposeProdAdjoint_symm

/-- The self-adjoint part of an element of a star module, as a continuous linear map. -/
@[simps!]
def selfAdjointPartL [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A] :
    A →L[R] selfAdjoint A where
  toLinearMap := selfAdjointPart R
  cont := continuous_selfAdjointPart _ _
#align self_adjoint_partL selfAdjointPartL

-- Porting note: `simp only [selfAdjointPartL_toFun_coe]` proves this projection
attribute [nolint simpNF] selfAdjointPartL_apply_coe

/-- The skew-adjoint part of an element of a star module, as a continuous linear map. -/
@[simps!]
def skewAdjointPartL [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A] :
    A →L[R] skewAdjoint A where
  toLinearMap := skewAdjointPart R
  cont := continuous_skewAdjointPart _ _
#align skew_adjoint_partL skewAdjointPartL

/-- The decomposition of elements of a star module into their self- and skew-adjoint parts,
as a continuous linear equivalence. -/
@[simps!]
def StarModule.decomposeProdAdjointL [TopologicalAddGroup A] [ContinuousStar A]
    [ContinuousConstSMul R A] : A ≃L[R] selfAdjoint A × skewAdjoint A where
  toLinearEquiv := StarModule.decomposeProdAdjoint R A
  continuous_toFun := continuous_decomposeProdAdjoint _ _
  continuous_invFun := continuous_decomposeProdAdjoint_symm _ _
#align star_module.decompose_prod_adjointL StarModule.decomposeProdAdjointL
