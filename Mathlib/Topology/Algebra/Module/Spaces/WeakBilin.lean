/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Moritz Doll
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.IsWeak
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Weak dual topology

This file defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`𝕜` and a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `fun x => B x y` is continuous.

## Main definitions

The main definition is the type `WeakBilin B`.

* Given `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, the type `WeakBilin B` is a type synonym for `E`.
* The instance `WeakBilin.instTopologicalSpace` is the weak topology induced by the bilinear form
  `B`.

## Main results

We establish that `WeakBilin B` has the following structure:
* `WeakBilin.instContinuousAdd`: The addition in `WeakBilin B` is continuous.
* `WeakBilin.instContinuousSMul`: The scalar multiplication in `WeakBilin B` is continuous.

We prove the following results characterizing the weak topology:
* `eval_continuous`: For any `y : F`, the evaluation mapping `fun x => B x y` is continuous.
* `continuous_of_continuous_eval`: For a mapping to `WeakBilin B` to be continuous,
  it suffices that its compositions with pairing with `B` at all points `y : F` is continuous.
* `tendsto_iff_forall_eval_tendsto`: Convergence in `WeakBilin B` can be characterized
  in terms of convergence of the evaluations at all points `y : F`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

weak-star, weak dual, duality

-/

@[expose] public section


noncomputable section

open Filter

open Topology

variable {α 𝕜 𝕝 E F : Type*}

section WeakTopology

/-- The space `E` equipped with the weak topology induced by the bilinear form `B`. -/
@[nolint unusedArguments]
def WeakBilin [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    (_ : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) := E
deriving AddCommMonoid, Module 𝕜

namespace WeakBilin

instance instAddCommGroup [CommSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : AddCommGroup (WeakBilin B) :=
  inferInstanceAs <| AddCommGroup E

instance (priority := 100) instModule' [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommMonoid E]
    [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] [Module 𝕝 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    Module 𝕝 (WeakBilin B) :=
  inferInstanceAs <| Module 𝕝 E

instance instIsScalarTower [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommMonoid E] [Module 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F] [SMul 𝕝 𝕜] [Module 𝕝 E] [s : IsScalarTower 𝕝 𝕜 E]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : IsScalarTower 𝕝 𝕜 (WeakBilin B) :=
  inferInstanceAs <| IsScalarTower 𝕝 𝕜 E

section LinearEquiv

variable [CommSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]
variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- The canonical linear equivalence (over `𝕝`) between `WeakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)`
and `E`. -/
noncomputable def linearEquiv (𝕝 : Type*) [CommSemiring 𝕝] [Module 𝕝 E] :
    WeakBilin B ≃ₗ[𝕝] E :=
  LinearEquiv.refl ..

/-- The dual pairing between `WeakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)` and `F`. In order to avoid abuse
of the definitional equality between `E` and `WeakBilin B`, it is necessary to use this pairing
instead of `B` itself when considering statements involving the weak topology induced by the
pairing, such as the bipolar theorem. -/
noncomputable def pairing : WeakBilin B →ₗ[𝕜] F →ₗ[𝕜] 𝕜 :=
  (linearEquiv B 𝕜).symm.arrowCongr (.refl _ _) B

variable {B}

lemma pairing_apply (x : WeakBilin B) :
    pairing B x = B (linearEquiv B 𝕜 x) :=
  rfl

lemma pairing_injective (hB : Function.Injective B) : Function.Injective (pairing B) :=
  hB.comp (linearEquiv B 𝕜).symm.injective

lemma pairing_surjective (hB : Function.Surjective B) : Function.Surjective (pairing B) :=
  hB.comp (linearEquiv B 𝕜).symm.surjective

end LinearEquiv

section Semiring

variable [TopologicalSpace 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]
variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

instance instTopologicalSpace : TopologicalSpace (WeakBilin B) :=
  TopologicalSpace.induced (pairing B · ·) Pi.topologicalSpace

instance isWeak : (pairing B).IsWeak where eq_induced := rfl

open LinearMap

/-- The coercion `(fun x y => B x y) : E → (F → 𝕜)` is continuous. -/
@[deprecated IsWeak.coeFn_continuous (since := "2026-06-15")]
theorem coeFn_continuous : Continuous (pairing B · ·) :=
  IsWeak.coeFn_continuous (pairing B)

@[deprecated IsWeak.continuous_eval (since := "2026-06-15")]
theorem eval_continuous (y : F) : Continuous (pairing B · y) := by
  fun_prop

@[fun_prop]
theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakBilin B}
    (h : ∀ y, Continuous fun a => pairing B (g a) y) : Continuous g :=
  IsWeak.continuous_of_continuous_eval (pairing B) h

/-- The coercion `(fun x y => B x y) : E → (F → 𝕜)` is an embedding. -/
@[deprecated IsWeak.isEmbedding (since := "2026-06-15")]
theorem isEmbedding {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (hB : Function.Injective B) :
    IsEmbedding (pairing B · ·) :=
  IsWeak.isEmbedding hB

@[deprecated IsWeak.tendsto_iff_forall_eval_tendsto (since := "2026-06-15")]
theorem tendsto_iff_forall_eval_tendsto {l : Filter α} {f : α → WeakBilin B} {x : WeakBilin B}
    (hB : Function.Injective B) :
    Tendsto f l (𝓝 x) ↔ ∀ y, Tendsto (fun i => pairing B (f i) y) l (𝓝 (pairing B x y)) :=
  IsWeak.tendsto_iff_forall_eval_tendsto (pairing_injective hB)

/-- Addition in `WeakBilin B` is continuous. -/
instance instContinuousAdd [ContinuousAdd 𝕜] : ContinuousAdd (WeakBilin B) :=
  IsWeak.continuousAdd (pairing B)

/-- Scalar multiplication by `𝕜` on `WeakBilin B` is continuous. -/
instance instContinuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (WeakBilin B) :=
  IsWeak.continuousSMul (pairing B)

/--
Map `F` into the topological dual of `E` with the weak topology induced by `F`
-/
@[deprecated IsWeak.eval (since := "2026-06-15")]
def eval [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] :
    F →ₗ[𝕜] StrongDual 𝕜 (WeakBilin B) :=
  IsWeak.eval (pairing B)

end Semiring

section Ring

variable [TopologicalSpace 𝕜] [CommRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]


variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- `WeakBilin B` is a `IsTopologicalAddGroup`, meaning that addition and negation are
continuous. -/
instance instIsTopologicalAddGroup [ContinuousAdd 𝕜] : IsTopologicalAddGroup (WeakBilin B) :=
  LinearMap.IsWeak.isTopologicalAddGroup (pairing B)

end Ring

end WeakBilin

end WeakTopology
