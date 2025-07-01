/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
import Mathlib.Algebra.Star.Module
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Star

/-!
# The star operation, bundled as a continuous star-linear equiv
-/



@[inherit_doc]
notation:25 M " →L⋆[" R "] " M₂ => ContinuousLinearMap (starRingEnd R) M M₂

@[inherit_doc]
notation:50 M " ≃L⋆[" R "] " M₂ => ContinuousLinearEquiv (starRingEnd R) M M₂

/-- If `A` is a topological module over a commutative `R` with compatible actions,
then `star` is a continuous semilinear equivalence. -/
@[simps!]
def starL (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] [TopologicalSpace A] [ContinuousStar A] :
    A ≃L⋆[R] A where
  toLinearEquiv := starLinearEquiv R
  continuous_toFun := continuous_star
  continuous_invFun := continuous_star

-- TODO: this could be replaced with something like `(starL R).restrict_scalarsₛₗ h` if we
-- implemented the idea in
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Star-semilinear.20maps.20are.20semilinear.20when.20star.20is.20trivial/near/359557835
/-- If `A` is a topological module over a commutative `R` with trivial star and compatible actions,
then `star` is a continuous linear equivalence. -/
@[simps!]
def starL' (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [TrivialStar R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] [TopologicalSpace A] [ContinuousStar A] :
    A ≃L[R] A :=
  (starL R : A ≃L⋆[R] A).trans
    ({ AddEquiv.refl A with
        map_smul' := fun r a => by simp [starRingEnd_apply]
        continuous_toFun := continuous_id
        continuous_invFun := continuous_id } :
      A ≃L⋆[R] A)

variable (R : Type*) (A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A] [Invertible (2 : R)] [TopologicalSpace A]

theorem continuous_selfAdjointPart [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A] :
    Continuous (selfAdjointPart R (A := A)) :=
  ((continuous_const_smul _).comp <| continuous_id.add continuous_star).subtype_mk _

theorem continuous_skewAdjointPart [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A] :
    Continuous (skewAdjointPart R (A := A)) :=
  ((continuous_const_smul _).comp <| continuous_id.sub continuous_star).subtype_mk _

theorem continuous_decomposeProdAdjoint [IsTopologicalAddGroup A] [ContinuousStar A]
    [ContinuousConstSMul R A] : Continuous (StarModule.decomposeProdAdjoint R A) :=
  (continuous_selfAdjointPart R A).prodMk (continuous_skewAdjointPart R A)

theorem continuous_decomposeProdAdjoint_symm [ContinuousAdd A] :
    Continuous (StarModule.decomposeProdAdjoint R A).symm :=
  (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

/-- The self-adjoint part of an element of a star module, as a continuous linear map. -/
@[simps! -isSimp]
def selfAdjointPartL [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A] :
    A →L[R] selfAdjoint A where
  toLinearMap := selfAdjointPart R
  cont := continuous_selfAdjointPart _ _

/-- The skew-adjoint part of an element of a star module, as a continuous linear map. -/
@[simps!]
def skewAdjointPartL [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A] :
    A →L[R] skewAdjoint A where
  toLinearMap := skewAdjointPart R
  cont := continuous_skewAdjointPart _ _

/-- The decomposition of elements of a star module into their self- and skew-adjoint parts,
as a continuous linear equivalence. -/
@[simps!]
def StarModule.decomposeProdAdjointL [IsTopologicalAddGroup A] [ContinuousStar A]
    [ContinuousConstSMul R A] : A ≃L[R] selfAdjoint A × skewAdjoint A where
  toLinearEquiv := StarModule.decomposeProdAdjoint R A
  continuous_toFun := continuous_decomposeProdAdjoint _ _
  continuous_invFun := continuous_decomposeProdAdjoint_symm _ _
