/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Moritz Doll

! This file was ported from Lean 3 source module topology.algebra.module.weak_dual
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Module.Basic
import Mathbin.LinearAlgebra.BilinearMap

/-!
# Weak dual topology

This file defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`𝕜` and a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `λ x, B x y` is continuous.

In the case that `F = E →L[𝕜] 𝕜` and `B` being the canonical pairing, we obtain the weak-* topology,
`weak_dual 𝕜 E := (E →L[𝕜] 𝕜)`. Interchanging the arguments in the bilinear form yields the
weak topology `weak_space 𝕜 E := E`.

## Main definitions

The main definitions are the types `weak_bilin B` for the general case and the two special cases
`weak_dual 𝕜 E` and `weak_space 𝕜 E` with the respective topology instances on it.

* Given `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, the type `weak_bilin B` is a type synonym for `E`.
* The instance `weak_bilin.topological_space` is the weak topology induced by the bilinear form `B`.
* `weak_dual 𝕜 E` is a type synonym for `dual 𝕜 E` (when the latter is defined): both are equal to
  the type `E →L[𝕜] 𝕜` of continuous linear maps from a module `E` over `𝕜` to the ring `𝕜`.
* The instance `weak_dual.topological_space` is the weak-* topology on `weak_dual 𝕜 E`, i.e., the
  coarsest topology making the evaluation maps at all `z : E` continuous.
* `weak_space 𝕜 E` is a type synonym for `E` (when the latter is defined).
* The instance `weak_dual.topological_space` is the weak topology on `E`, i.e., the
  coarsest topology such that all `v : dual 𝕜 E` remain continuous.

## Main results

We establish that `weak_bilin B` has the following structure:
* `weak_bilin.has_continuous_add`: The addition in `weak_bilin B` is continuous.
* `weak_bilin.has_continuous_smul`: The scalar multiplication in `weak_bilin B` is continuous.

We prove the following results characterizing the weak topology:
* `eval_continuous`: For any `y : F`, the evaluation mapping `λ x, B x y` is continuous.
* `continuous_of_continuous_eval`: For a mapping to `weak_bilin B` to be continuous,
  it suffices that its compositions with pairing with `B` at all points `y : F` is continuous.
* `tendsto_iff_forall_eval_tendsto`: Convergence in `weak_bilin B` can be characterized
  in terms of convergence of the evaluations at all points `y : F`.

## Notations

No new notation is introduced.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

weak-star, weak dual, duality

-/


noncomputable section

open Filter

open Topology

variable {α 𝕜 𝕝 R E F M : Type _}

section WeakTopology

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] 𝕜 -/
/-- The space `E` equipped with the weak topology induced by the bilinear form `B`. -/
@[nolint has_nonempty_instance unused_arguments]
def WeakBilin [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :=
  E deriving AddCommMonoid,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] 𝕜»
#align weak_bilin WeakBilin

namespace WeakBilin

instance [CommSemiring 𝕜] [a : AddCommGroup E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : AddCommGroup (WeakBilin B) :=
  a

instance (priority := 100) module' [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [m : Module 𝕝 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    Module 𝕝 (WeakBilin B) :=
  m
#align weak_bilin.module' WeakBilin.module'

instance [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F]
    [Module 𝕜 F] [SMul 𝕝 𝕜] [Module 𝕝 E] [s : IsScalarTower 𝕝 𝕜 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    IsScalarTower 𝕝 𝕜 (WeakBilin B) :=
  s

section Semiring

variable [TopologicalSpace 𝕜] [CommSemiring 𝕜]

variable [AddCommMonoid E] [Module 𝕜 E]

variable [AddCommMonoid F] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

instance : TopologicalSpace (WeakBilin B) :=
  TopologicalSpace.induced (fun x y => B x y) Pi.topologicalSpace

/-- The coercion `(λ x y, B x y) : E → (F → 𝕜)` is continuous. -/
theorem coeFn_continuous : Continuous fun (x : WeakBilin B) y => B x y :=
  continuous_induced_dom
#align weak_bilin.coe_fn_continuous WeakBilin.coeFn_continuous

theorem eval_continuous (y : F) : Continuous fun x : WeakBilin B => B x y :=
  (continuous_pi_iff.mp (coeFn_continuous B)) y
#align weak_bilin.eval_continuous WeakBilin.eval_continuous

theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakBilin B}
    (h : ∀ y, Continuous fun a => B (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)
#align weak_bilin.continuous_of_continuous_eval WeakBilin.continuous_of_continuous_eval

/-- The coercion `(λ x y, B x y) : E → (F → 𝕜)` is an embedding. -/
theorem embedding {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (hB : Function.Injective B) :
    Embedding fun (x : WeakBilin B) y => B x y :=
  Function.Injective.embedding_induced <| LinearMap.coe_injective.comp hB
#align weak_bilin.embedding WeakBilin.embedding

theorem tendsto_iff_forall_eval_tendsto {l : Filter α} {f : α → WeakBilin B} {x : WeakBilin B}
    (hB : Function.Injective B) :
    Tendsto f l (𝓝 x) ↔ ∀ y, Tendsto (fun i => B (f i) y) l (𝓝 (B x y)) := by
  rw [← tendsto_pi_nhds, Embedding.tendsto_nhds_iff (Embedding hB)]
#align weak_bilin.tendsto_iff_forall_eval_tendsto WeakBilin.tendsto_iff_forall_eval_tendsto

/-- Addition in `weak_space B` is continuous. -/
instance [ContinuousAdd 𝕜] : ContinuousAdd (WeakBilin B) :=
  by
  refine' ⟨continuous_induced_rng.2 _⟩
  refine'
    cast (congr_arg _ _)
      (((coe_fn_continuous B).comp continuous_fst).add ((coe_fn_continuous B).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.add_apply, map_add, LinearMap.add_apply]

/-- Scalar multiplication by `𝕜` on `weak_bilin B` is continuous. -/
instance [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (WeakBilin B) :=
  by
  refine' ⟨continuous_induced_rng.2 _⟩
  refine' cast (congr_arg _ _) (continuous_fst.smul ((coe_fn_continuous B).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.smul_apply, LinearMap.map_smulₛₗ, RingHom.id_apply,
    LinearMap.smul_apply]

end Semiring

section Ring

variable [TopologicalSpace 𝕜] [CommRing 𝕜]

variable [AddCommGroup E] [Module 𝕜 E]

variable [AddCommGroup F] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- `weak_space B` is a `topological_add_group`, meaning that addition and negation are
continuous. -/
instance [ContinuousAdd 𝕜] : TopologicalAddGroup (WeakBilin B)
    where
  to_continuousAdd := by infer_instance
  continuous_neg :=
    by
    refine' continuous_induced_rng.2 (continuous_pi_iff.mpr fun y => _)
    refine' cast (congr_arg _ _) (eval_continuous B (-y))
    ext
    simp only [map_neg, Function.comp_apply, LinearMap.neg_apply]

end Ring

end WeakBilin

end WeakTopology

section WeakStarTopology

/-- The canonical pairing of a vector space and its topological dual. -/
def topDualPairing (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 𝕜] : (E →L[𝕜] 𝕜) →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  ContinuousLinearMap.coeLM 𝕜
#align top_dual_pairing topDualPairing

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]

variable [ContinuousConstSMul 𝕜 𝕜]

variable [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

theorem dual_pairing_apply (v : E →L[𝕜] 𝕜) (x : E) : topDualPairing 𝕜 E v x = v x :=
  rfl
#align dual_pairing_apply dual_pairing_apply

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] 𝕜 -/
/-- The weak star topology is the topology coarsest topology on `E →L[𝕜] 𝕜` such that all
functionals `λ v, top_dual_pairing 𝕜 E v x` are continuous. -/
def WeakDual (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E)deriving AddCommMonoid,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] 𝕜»,
  TopologicalSpace, ContinuousAdd
#align weak_dual WeakDual

namespace WeakDual

instance : Inhabited (WeakDual 𝕜 E) :=
  ContinuousLinearMap.inhabited

instance WeakDual.continuousLinearMapClass : ContinuousLinearMapClass (WeakDual 𝕜 E) 𝕜 E 𝕜 :=
  ContinuousLinearMap.continuousSemilinearMapClass
#align weak_dual.weak_dual.continuous_linear_map_class WeakDual.WeakDual.continuousLinearMapClass

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (WeakDual 𝕜 E) fun _ => E → 𝕜 :=
  FunLike.hasCoeToFun

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts on `weak_dual 𝕜 E`. -/
instance (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜] [ContinuousConstSMul M 𝕜] :
    MulAction M (WeakDual 𝕜 E) :=
  ContinuousLinearMap.mulAction

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts distributively on `weak_dual 𝕜 E`. -/
instance (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜] [ContinuousConstSMul M 𝕜] :
    DistribMulAction M (WeakDual 𝕜 E) :=
  ContinuousLinearMap.distribMulAction

/-- If `𝕜` is a topological module over a semiring `R` and scalar multiplication commutes with the
multiplication on `𝕜`, then `weak_dual 𝕜 E` is a module over `R`. -/
instance module' (R) [Semiring R] [Module R 𝕜] [SMulCommClass 𝕜 R 𝕜] [ContinuousConstSMul R 𝕜] :
    Module R (WeakDual 𝕜 E) :=
  ContinuousLinearMap.module
#align weak_dual.module' WeakDual.module'

instance (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜] [ContinuousConstSMul M 𝕜] :
    ContinuousConstSMul M (WeakDual 𝕜 E) :=
  ⟨fun m =>
    continuous_induced_rng.2 <| (WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).const_smul m⟩

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it continuously acts on `weak_dual 𝕜 E`. -/
instance (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜] [TopologicalSpace M]
    [ContinuousSMul M 𝕜] : ContinuousSMul M (WeakDual 𝕜 E) :=
  ⟨continuous_induced_rng.2 <|
      continuous_fst.smul ((WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).comp continuous_snd)⟩

theorem coeFn_continuous : Continuous fun (x : WeakDual 𝕜 E) y => x y :=
  continuous_induced_dom
#align weak_dual.coe_fn_continuous WeakDual.coeFn_continuous

theorem eval_continuous (y : E) : Continuous fun x : WeakDual 𝕜 E => x y :=
  continuous_pi_iff.mp coeFn_continuous y
#align weak_dual.eval_continuous WeakDual.eval_continuous

theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakDual 𝕜 E}
    (h : ∀ y, Continuous fun a => (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)
#align weak_dual.continuous_of_continuous_eval WeakDual.continuous_of_continuous_eval

instance [T2Space 𝕜] : T2Space (WeakDual 𝕜 E) :=
  Embedding.t2Space <|
    WeakBilin.embedding <|
      show Function.Injective (topDualPairing 𝕜 E) from ContinuousLinearMap.coe_injective

end WeakDual

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] 𝕜 -/
/-- The weak topology is the topology coarsest topology on `E` such that all
functionals `λ x, top_dual_pairing 𝕜 E v x` are continuous. -/
@[nolint has_nonempty_instance]
def WeakSpace (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E).flip deriving AddCommMonoid,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] 𝕜»,
  TopologicalSpace, ContinuousAdd
#align weak_space WeakSpace

namespace WeakSpace

variable {𝕜 E F} [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

/-- A continuous linear map from `E` to `F` is still continuous when `E` and `F` are equipped with
their weak topologies. -/
def map (f : E →L[𝕜] F) : WeakSpace 𝕜 E →L[𝕜] WeakSpace 𝕜 F :=
  { f with
    cont :=
      WeakBilin.continuous_of_continuous_eval _ fun l => WeakBilin.eval_continuous _ (l ∘L f) }
#align weak_space.map WeakSpace.map

theorem map_apply (f : E →L[𝕜] F) (x : E) : WeakSpace.map f x = f x :=
  rfl
#align weak_space.map_apply WeakSpace.map_apply

@[simp]
theorem coe_map (f : E →L[𝕜] F) : (WeakSpace.map f : E → F) = f :=
  rfl
#align weak_space.coe_map WeakSpace.coe_map

end WeakSpace

theorem tendsto_iff_forall_eval_tendsto_topDualPairing {l : Filter α} {f : α → WeakDual 𝕜 E}
    {x : WeakDual 𝕜 E} :
    Tendsto f l (𝓝 x) ↔
      ∀ y, Tendsto (fun i => topDualPairing 𝕜 E (f i) y) l (𝓝 (topDualPairing 𝕜 E x y)) :=
  WeakBilin.tendsto_iff_forall_eval_tendsto _ ContinuousLinearMap.coe_injective
#align tendsto_iff_forall_eval_tendsto_top_dual_pairing tendsto_iff_forall_eval_tendsto_topDualPairing

end WeakStarTopology

