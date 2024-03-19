/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Moritz Doll
-/
--import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Topology.Algebra.Module.Dual

#align_import topology.algebra.module.weak_dual from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Weak dual topology

This file defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`𝕜` and a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `fun x => B x y` is continuous.

In the case that `F = E →L[𝕜] 𝕜` and `B` being the canonical pairing, we obtain the weak-* topology,
`WeakDual 𝕜 E := (E →L[𝕜] 𝕜)`. Interchanging the arguments in the bilinear form yields the
weak topology `WeakSpace 𝕜 E := E`.

## Main definitions

The main definitions are the types `WeakBilin B` for the general case and the two special cases
`WeakDual 𝕜 E` and `WeakSpace 𝕜 E` with the respective topology instances on it.

* Given `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, the type `WeakBilin B` is a type synonym for `E`.
* The instance `WeakBilin.instTopologicalSpace` is the weak topology induced by the bilinear form
  `B`.
* `WeakDual 𝕜 E` is a type synonym for `Dual 𝕜 E`: both are equal to the type `E →L[𝕜] 𝕜` of
  continuous linear maps from a module `E` over `𝕜` to the ring `𝕜`.
* The instance `WeakDual.instTopologicalSpace` is the weak-* topology on `WeakDual 𝕜 E`, i.e., the
  coarsest topology making the evaluation maps at all `z : E` continuous.
* `WeakSpace 𝕜 E` is a type synonym for `E`.
* The instance `WeakSpace.instTopologicalSpace` is the weak topology on `E`, i.e., the
  coarsest topology such that all `v : Dual 𝕜 E` remain continuous.

## Main results

We establish that `WeakBilin B` has the following structure:
* `WeakBilin.instContinuousAdd`: The addition in `WeakBilin B` is continuous.
* `WeakBilin.instContinuousSMul`: The scalar multiplication in `WeakBilin B` is continuous.

We prove the following results characterizing the weak topology:
* `evalCLM`: For any `y : F`, the evaluation mapping `x ↦ B x y` is continuous.
* `continuous_of_continuous_eval`: For a mapping to `WeakBilin B` to be continuous,
  it suffices that its compositions with pairing with `B` at all points `y : F` is continuous.
* `tendsto_iff_forall_eval_tendsto`: Convergence in `WeakBilin B` can be characterized
  in terms of convergence of the evaluations at all points `y : F`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

weak-star, weak dual, duality

-/


noncomputable section

open Filter

open Topology

variable {α 𝕜 𝕝 R E F M : Type*}

/-- The space `E` equipped with the weak topology induced by the bilinear form `B`. -/
@[nolint unusedArguments]
def WeakBilin [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    (_ : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) := E
#align weak_bilin WeakBilin

namespace WeakBilin

instance instAddCommMonoid [CommSemiring 𝕜] [a : AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : AddCommMonoid (WeakBilin B) := a

instance instModule [CommSemiring 𝕜] [AddCommMonoid E] [m : Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : Module 𝕜 (WeakBilin B) := m

instance instAddCommGroup [CommSemiring 𝕜] [a : AddCommGroup E] [Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : AddCommGroup (WeakBilin B) := a

instance (priority := 100) instModule' [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommGroup E]
    [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [m : Module 𝕝 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    Module 𝕝 (WeakBilin B) := m
#align weak_bilin.module' WeakBilin.instModule'

instance instIsScalarTower [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [SMul 𝕝 𝕜] [Module 𝕝 E] [s : IsScalarTower 𝕝 𝕜 E]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : IsScalarTower 𝕝 𝕜 (WeakBilin B) := s

section Semiring

variable [TopologicalSpace 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]
variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

instance instTopologicalSpace : TopologicalSpace (WeakBilin B) :=
  TopologicalSpace.induced (B · ·) Pi.topologicalSpace

/-- The coercion `B : E → (F → 𝕜)` as a continuous linear map. -/
def coeFnCLM : WeakBilin B →L[𝕜] (F → 𝕜) where
  toFun := (B · ·)
  map_add' := fun _ _ ↦ by ext; simp
  map_smul' := fun _ _ ↦ by ext; simp
  cont := continuous_induced_dom
#align weak_bilin.coe_fn_continuous WeakBilin.coeFnCLM

@[simp]
theorem coeFnCLM_apply (x : WeakBilin B) : coeFnCLM B x = B x := rfl

/-- The map `x ↦ B x y` for fixed `y : F` as a continuous linear map. -/
def evalCLM (y : F) : WeakBilin B →L[𝕜] 𝕜 where
  toLinearMap := B.flip y
  cont := (continuous_pi_iff.mp (coeFnCLM B).continuous) y
#align weak_bilin.eval_continuous WeakBilin.evalCLM

@[simp]
theorem evalCLM_apply (y : F) (x : WeakBilin B) : evalCLM B y x = B x y := rfl

theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakBilin B}
    (h : ∀ y, Continuous fun a => B (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)
#align weak_bilin.continuous_of_continuous_eval WeakBilin.continuous_of_continuous_eval

/-- The coercion `(x y ↦ B x y) : E → (F → 𝕜)` is an embedding. -/
theorem embedding {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (hB : Function.Injective B) :
    Embedding fun (x : WeakBilin B) y ↦ B x y :=
  Function.Injective.embedding_induced <| LinearMap.coe_injective.comp hB
#align weak_bilin.embedding WeakBilin.embedding

theorem tendsto_iff_forall_eval_tendsto {l : Filter α} {f : α → WeakBilin B} {x : WeakBilin B}
    (hB : Function.Injective B) :
    Tendsto f l (𝓝 x) ↔ ∀ y, Tendsto (fun i => B (f i) y) l (𝓝 (B x y)) := by
  rw [← tendsto_pi_nhds, Embedding.tendsto_nhds_iff (embedding hB)]
  rfl
#align weak_bilin.tendsto_iff_forall_eval_tendsto WeakBilin.tendsto_iff_forall_eval_tendsto

/-- Addition in `WeakBilin B` is continuous. -/
instance instContinuousAdd [ContinuousAdd 𝕜] : ContinuousAdd (WeakBilin B) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine cast (congr_arg _ ?_)
    (((coeFnCLM B).continuous.comp continuous_fst).add
      ((coeFnCLM B).continuous.comp continuous_snd))
  ext
  simp

/-- Scalar multiplication by `𝕜` on `WeakBilin B` is continuous. -/
instance instContinuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (WeakBilin B) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine cast (congr_arg _ ?_) (continuous_fst.smul ((coeFnCLM B).continuous.comp continuous_snd))
  ext
  simp

end Semiring

section Ring

variable [TopologicalSpace 𝕜] [CommRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- `WeakBilin B` is a `TopologicalAddGroup`, meaning that addition and negation are
continuous. -/
instance instTopologicalAddGroup [ContinuousAdd 𝕜] : TopologicalAddGroup (WeakBilin B) where
  toContinuousAdd := by infer_instance
  continuous_neg := by
    apply continuous_of_continuous_eval
    intro y
    convert (evalCLM B (-y)).continuous
    simp

end Ring

end WeakBilin

section WeakStarTopology

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [AddCommMonoid E] [Module 𝕜 E]
  [TopologicalSpace E] [ContinuousConstSMul 𝕜 𝕜]

variable (𝕜 E) in
/-- The weak-* topology is the topology coarsest topology on `Dual 𝕜 E` such that all
functionals `v ↦ v x` are continuous. -/
@[reducible]
def WeakDual : Type _ := WeakBilin (dualPairing 𝕜 E)
#align weak_dual WeakDual

namespace WeakDual

instance instInhabited : Inhabited (WeakDual 𝕜 E) :=
  ContinuousLinearMap.inhabited

instance instFunLike : FunLike (WeakDual 𝕜 E) E 𝕜 :=
  ContinuousLinearMap.funLike

instance instContinuousLinearMapClass : ContinuousLinearMapClass (WeakDual 𝕜 E) 𝕜 E 𝕜 :=
  ContinuousLinearMap.continuousSemilinearMapClass
#align weak_dual.weak_dual.continuous_linear_map_class WeakDual.instContinuousLinearMapClass

/-- Helper instance for when there's too many metavariables to apply `DFunLike.hasCoeToFun`
directly. -/
instance instCoeFun : CoeFun (WeakDual 𝕜 E) fun _ => E → 𝕜 :=
  DFunLike.hasCoeToFun

variable (𝕜 E) in
/-- The coercion `WeakDual 𝕜 E → (E → 𝕜)` as a continuous linear map. -/
def coeFnCLM : WeakDual 𝕜 E →L[𝕜] (E → 𝕜) := WeakBilin.coeFnCLM (dualPairing 𝕜 E)
#align weak_dual.coe_fn_continuous WeakDual.coeFnCLM

@[simp]
theorem coeFnCLM_apply (x : WeakDual 𝕜 E) : coeFnCLM 𝕜 E x = dualPairing 𝕜 E x := rfl

variable (𝕜) in
/-- The map `x ↦ x y` for fixed `y : E` as a continuous linear map. -/
def evalCLM (y : E) : WeakDual 𝕜 E →L[𝕜] 𝕜 := WeakBilin.evalCLM (dualPairing 𝕜 E) y
#align weak_dual.eval_continuous WeakDual.evalCLM

@[simp]
theorem evalCLM_apply (y : E) (x : WeakDual 𝕜 E) : evalCLM 𝕜 y x = x y := rfl

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts on `WeakDual 𝕜 E`. -/
instance instMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : MulAction M (WeakDual 𝕜 E) :=
  ContinuousLinearMap.mulAction

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts distributively on `WeakDual 𝕜 E`. -/
instance instDistribMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : DistribMulAction M (WeakDual 𝕜 E) :=
  ContinuousLinearMap.distribMulAction

/-- If `𝕜` is a topological module over a semiring `R` and scalar multiplication commutes with the
multiplication on `𝕜`, then `WeakDual 𝕜 E` is a module over `R`. -/
instance instModule' (R) [Semiring R] [Module R 𝕜] [SMulCommClass 𝕜 R 𝕜] [ContinuousConstSMul R 𝕜] :
    Module R (WeakDual 𝕜 E) :=
  ContinuousLinearMap.module
#align weak_dual.module' WeakDual.instModule'

instance instContinuousConstSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : ContinuousConstSMul M (WeakDual 𝕜 E) :=
  ⟨(continuous_induced_rng.2 <| (WeakDual.coeFnCLM 𝕜 E).continuous.const_smul ·)⟩

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it continuously acts on `WeakDual 𝕜 E`. -/
instance instContinuousSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [TopologicalSpace M] [ContinuousSMul M 𝕜] : ContinuousSMul M (WeakDual 𝕜 E) :=
  ⟨continuous_induced_rng.2 <|
      continuous_fst.smul ((WeakDual.coeFnCLM 𝕜 E).continuous.comp continuous_snd)⟩

theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakDual 𝕜 E}
    (h : ∀ y, Continuous fun a => (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)
#align weak_dual.continuous_of_continuous_eval WeakDual.continuous_of_continuous_eval

variable (𝕜 E) in
/-- The coercion `WeakDual 𝕜 E → (E → 𝕜)` is an embedding. -/
theorem embedding :
    Embedding fun (x : WeakDual 𝕜 E) y ↦ x y :=
  Function.Injective.embedding_induced <| LinearMap.coe_injective.comp
    ContinuousLinearMap.coe_injective

theorem tendsto_iff_forall_eval_tendsto_dualPairing {l : Filter α} {f : α → WeakDual 𝕜 E}
    {x : WeakDual 𝕜 E} : Tendsto f l (𝓝 x) ↔ ∀ y, Tendsto (f · y) l (𝓝 (x y)) :=
  WeakBilin.tendsto_iff_forall_eval_tendsto _ ContinuousLinearMap.coe_injective
#align tendsto_iff_forall_eval_tendsto_top_dual_pairing WeakDual.tendsto_iff_forall_eval_tendsto_dualPairing

instance instT2Space [T2Space 𝕜] : T2Space (WeakDual 𝕜 E) :=
  Embedding.t2Space <|
    WeakBilin.embedding <|
      show Function.Injective (dualPairing 𝕜 E) from ContinuousLinearMap.coe_injective

end WeakDual

/-- The weak topology is the topology coarsest topology on `E` such that all functionals
`fun x ↦ v x` are continuous. -/
@[reducible]
def WeakSpace (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (dualPairing 𝕜 E).flip
#align weak_space WeakSpace

namespace WeakSpace

variable (𝕜 E) in
/-- The coercion `E → Dual 𝕜 E` as a continuous linear map in the weak topology. -/
def coeFnCLM : WeakSpace 𝕜 E →L[𝕜] (Dual 𝕜 E → 𝕜) := WeakBilin.coeFnCLM (dualPairing 𝕜 E).flip

@[simp]
theorem coeFnCLM_apply (x : WeakSpace 𝕜 E) : coeFnCLM 𝕜 E x = (dualPairing 𝕜 E).flip x := rfl

/-- The map `x ↦ y x` for fixed `y : Dual 𝕜 E` as a continuous linear map. -/
def evalCLM (y : Dual 𝕜 E) : WeakSpace 𝕜 E →L[𝕜] 𝕜 := WeakBilin.evalCLM (dualPairing 𝕜 E).flip y

@[simp]
theorem evalCLM_apply (y : Dual 𝕜 E) (x : WeakSpace 𝕜 E) : evalCLM y x = y x := rfl

variable [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

/-- A continuous linear map from `E` to `F` is still continuous when `E` and `F` are equipped with
their weak topologies. -/
def map (f : E →L[𝕜] F) : WeakSpace 𝕜 E →L[𝕜] WeakSpace 𝕜 F :=
  { f with
    cont :=
      WeakBilin.continuous_of_continuous_eval _ fun l ↦ (WeakBilin.evalCLM _ (l ∘L f)).continuous }
#align weak_space.map WeakSpace.map

theorem map_apply (f : E →L[𝕜] F) (x : E) : WeakSpace.map f x = f x :=
  rfl
#align weak_space.map_apply WeakSpace.map_apply

@[simp]
theorem coe_map (f : E →L[𝕜] F) : (WeakSpace.map f : E → F) = f :=
  rfl
#align weak_space.coe_map WeakSpace.coe_map

end WeakSpace

end WeakStarTopology
