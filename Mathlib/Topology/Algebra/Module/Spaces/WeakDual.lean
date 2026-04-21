/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Moritz Doll
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin

/-!
# Weak dual topology

This file defines the weak-* (weak dual) topology on the continuous dual `E →L[𝕜] 𝕜`.
It is the coarsest topology such that for all `z : E` every evaluation map
`fun v => v z` is continuous.

## Main definitions

* `WeakDual 𝕜 E` is a type synonym for `E →L[𝕜] 𝕜` (equal to `Dual 𝕜 E`).
* The instance `WeakDual.instTopologicalSpace` is the weak-* topology on `WeakDual 𝕜 E`, i.e., the
  coarsest topology making the evaluation maps at all `z : E` continuous.

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

/-- The weak star topology is the topology coarsest topology on `E →L[𝕜] 𝕜` such that all
functionals `fun v => v x` are continuous. -/
def WeakDual (𝕜 E : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E)
deriving AddCommMonoid, TopologicalSpace, ContinuousAdd, Inhabited,
  FunLike, ContinuousLinearMapClass

namespace WeakDual

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts on `WeakDual 𝕜 E`. -/
instance instMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : MulAction M (WeakDual 𝕜 E) :=
  inferInstanceAs <| MulAction M (E →L[𝕜] 𝕜)

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts distributively on `WeakDual 𝕜 E`. -/
instance instDistribMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : DistribMulAction M (WeakDual 𝕜 E) :=
  inferInstanceAs <| DistribMulAction M (E →L[𝕜] 𝕜)

instance instContinuousConstSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : ContinuousConstSMul M (WeakDual 𝕜 E) :=
  ⟨fun m =>
    continuous_induced_rng.2 <| (WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).const_smul m⟩

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it continuously acts on `WeakDual 𝕜 E`. -/
instance instContinuousSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [TopologicalSpace M] [ContinuousSMul M 𝕜] : ContinuousSMul M (WeakDual 𝕜 E) :=
  ⟨continuous_induced_rng.2 <|
      continuous_fst.smul ((WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).comp continuous_snd)⟩

/-- If `𝕜` is a topological module over a semiring `R` and scalar multiplication commutes with the
multiplication on `𝕜`, then `WeakDual 𝕜 E` is a module over `R`. -/
instance (priority := 950) instModule'
    (R : Type*) [Semiring R] [Module R 𝕜] [SMulCommClass 𝕜 R 𝕜] [ContinuousConstSMul R 𝕜] :
    Module R (WeakDual 𝕜 E) :=
  inferInstanceAs <| Module R (E →L[𝕜] 𝕜)

instance instModule : Module 𝕜 (WeakDual 𝕜 E) := inferInstance

end WeakDual

namespace StrongDual

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- For vector spaces `E`, there is a canonical map `StrongDual 𝕜 E → WeakDual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. -/
def toWeakDual : StrongDual 𝕜 E ≃ₗ[𝕜] WeakDual 𝕜 E :=
  LinearEquiv.refl 𝕜 (StrongDual 𝕜 E)

theorem coe_toWeakDual (x' : StrongDual 𝕜 E) : (toWeakDual x' : E → 𝕜) = x' := rfl

@[simp]
theorem toWeakDual_apply (x' : StrongDual 𝕜 E) (y : E) : (toWeakDual x') y = x' y := rfl

theorem toWeakDual_inj (x' y' : StrongDual 𝕜 E) : toWeakDual x' = toWeakDual y' ↔ x' = y' :=
  (LinearEquiv.injective toWeakDual).eq_iff

end StrongDual

namespace WeakDual

section Semiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- For vector spaces `E`, there is a canonical map `WeakDual 𝕜 E → StrongDual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. Here it is implemented as the inverse of the linear
equivalence `StrongDual.toWeakDual` in the other direction. -/
def toStrongDual : WeakDual 𝕜 E ≃ₗ[𝕜] StrongDual 𝕜 E :=
  StrongDual.toWeakDual.symm

@[simp]
theorem toStrongDual_apply (x : WeakDual 𝕜 E) (y : E) : (toStrongDual x) y = x y := rfl

theorem coe_toStrongDual (x' : WeakDual 𝕜 E) : (toStrongDual x' : E → 𝕜) = x' := rfl

theorem toStrongDual_inj (x' y' : WeakDual 𝕜 E) : toStrongDual x' = toStrongDual y' ↔ x' = y' :=
  (LinearEquiv.injective toStrongDual).eq_iff


theorem coeFn_continuous : Continuous fun (x : WeakDual 𝕜 E) y => x y :=
  continuous_induced_dom

theorem eval_continuous (y : E) : Continuous fun x : WeakDual 𝕜 E => x y :=
  continuous_pi_iff.mp coeFn_continuous y

theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakDual 𝕜 E}
    (h : ∀ y, Continuous fun a => (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)

instance instT2Space [T2Space 𝕜] : T2Space (WeakDual 𝕜 E) :=
  (WeakBilin.isEmbedding ContinuousLinearMap.coe_injective).t2Space

end Semiring

section Ring

variable [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜] [ContinuousConstSMul 𝕜 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]

instance instAddCommGroup : AddCommGroup (WeakDual 𝕜 E) :=
  inferInstanceAs <| AddCommGroup (WeakBilin (topDualPairing 𝕜 E))

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (WeakDual 𝕜 E) :=
  WeakBilin.instIsTopologicalAddGroup (topDualPairing 𝕜 E)

end Ring

end WeakDual

section Semiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

theorem tendsto_iff_forall_eval_tendsto_topDualPairing {l : Filter α} {f : α → WeakDual 𝕜 E}
    {x : WeakDual 𝕜 E} :
    Tendsto f l (𝓝 x) ↔
      ∀ y, Tendsto (fun i => topDualPairing 𝕜 E (f i) y) l (𝓝 (topDualPairing 𝕜 E x y)) :=
  WeakBilin.tendsto_iff_forall_eval_tendsto _ ContinuousLinearMap.coe_injective

end Semiring
