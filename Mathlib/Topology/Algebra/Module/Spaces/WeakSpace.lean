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
# Weak topology

This file defines the weak topology on a topological vector space `E`.
It is the coarsest topology on `E` such that all continuous linear functionals
`fun x => v x` for `v : E →L[𝕜] 𝕜` remain continuous.

## Main definitions

* `WeakSpace 𝕜 E` is a type synonym for `E`.
* The instance `WeakSpace.instTopologicalSpace` is the weak topology on `E`, i.e., the
  coarsest topology such that all `v : E →L[𝕜] 𝕜` remain continuous.
* `toWeakSpace`: The canonical linear equivalence `E ≃ₗ[𝕜] WeakSpace 𝕜 E`.
* `toWeakSpaceCLM`: The identity mapping as a continuous linear map `E →L[𝕜] WeakSpace 𝕜 E`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

weak topology, duality
-/

@[expose] public section

noncomputable section

open Filter Topology

variable {α 𝕜 𝕝 E F : Type*}

/-- The weak topology is the topology coarsest topology on `E` such that all functionals
`fun x => v x` are continuous. -/
def WeakSpace (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E).flip
deriving AddCommMonoid, Module 𝕜, TopologicalSpace, ContinuousAdd

section Semiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

namespace WeakSpace

instance instModule' [CommSemiring 𝕝] [Module 𝕝 E] : Module 𝕝 (WeakSpace 𝕜 E) :=
  inferInstanceAs <| Module 𝕝 (WeakBilin (topDualPairing 𝕜 E).flip)

instance instIsScalarTower [CommSemiring 𝕝] [Module 𝕝 𝕜] [Module 𝕝 E] [IsScalarTower 𝕝 𝕜 E] :
    IsScalarTower 𝕝 𝕜 (WeakSpace 𝕜 E) :=
  WeakBilin.instIsScalarTower (topDualPairing 𝕜 E).flip

instance instContinuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (WeakSpace 𝕜 E) :=
  WeakBilin.instContinuousSMul _

variable [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

/-- A continuous linear map from `E` to `F` is still continuous when `E` and `F` are equipped with
their weak topologies. -/
def map (f : E →L[𝕜] F) : WeakSpace 𝕜 E →L[𝕜] WeakSpace 𝕜 F :=
  { f with
    cont :=
      WeakBilin.continuous_of_continuous_eval _ fun l => WeakBilin.eval_continuous _ (l ∘L f) }

theorem map_apply (f : E →L[𝕜] F) (x : E) : WeakSpace.map f x = f x :=
  rfl

@[simp]
theorem coe_map (f : E →L[𝕜] F) : (WeakSpace.map f : E → F) = f :=
  rfl

end WeakSpace

variable (𝕜 E) in
/-- There is a canonical map `E → WeakSpace 𝕜 E` (the "identity"
mapping). It is a linear equivalence. -/
def toWeakSpace : E ≃ₗ[𝕜] WeakSpace 𝕜 E := LinearEquiv.refl 𝕜 E

variable (𝕜 E) in
/-- For a topological vector space `E`, "identity mapping" `E → WeakSpace 𝕜 E` is continuous.
This definition implements it as a continuous linear map. -/
def toWeakSpaceCLM : E →L[𝕜] WeakSpace 𝕜 E where
  __ := toWeakSpace 𝕜 E
  cont := by
    apply WeakBilin.continuous_of_continuous_eval
    exact ContinuousLinearMap.continuous

variable (𝕜 E) in
@[simp]
theorem toWeakSpaceCLM_eq_toWeakSpace (x : E) :
    toWeakSpaceCLM 𝕜 E x = toWeakSpace 𝕜 E x := by rfl

theorem toWeakSpaceCLM_bijective :
    Function.Bijective (toWeakSpaceCLM 𝕜 E) :=
  (toWeakSpace 𝕜 E).bijective

/-- The canonical map from `WeakSpace 𝕜 E` to `E` is an open map. -/
theorem isOpenMap_toWeakSpace_symm : IsOpenMap (toWeakSpace 𝕜 E).symm :=
  IsOpenMap.of_inverse (toWeakSpaceCLM 𝕜 E).cont
    (toWeakSpace 𝕜 E).left_inv (toWeakSpace 𝕜 E).right_inv

/-- A set in `E` which is open in the weak topology is open. -/
theorem WeakSpace.isOpen_of_isOpen (V : Set E)
    (hV : IsOpen ((toWeakSpaceCLM 𝕜 E) '' V : Set (WeakSpace 𝕜 E))) : IsOpen V := by
  simpa [Set.image_image] using isOpenMap_toWeakSpace_symm _ hV

end Semiring

section Ring

namespace WeakSpace

variable [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜] [ContinuousConstSMul 𝕜 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]

instance instAddCommGroup : AddCommGroup (WeakSpace 𝕜 E) :=
  inferInstanceAs <| AddCommGroup (WeakBilin (topDualPairing 𝕜 E).flip)

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (WeakSpace 𝕜 E) :=
  WeakBilin.instIsTopologicalAddGroup (topDualPairing 𝕜 E).flip

end WeakSpace

end Ring
