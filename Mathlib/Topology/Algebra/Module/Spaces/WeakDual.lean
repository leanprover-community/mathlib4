/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Moritz Doll
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin

/-!
# Weak dual topology

We continue in the setting of `Mathlib/Topology/Algebra/Module/WeakBilin.lean`,
which defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`𝕜` and a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `fun x => B x y` is continuous.

In this file, we consider two special cases.
In the case that `F = E →L[𝕜] 𝕜` and `B` being the canonical pairing, we obtain the weak-\*
topology, `WeakDual 𝕜 E := (E →L[𝕜] 𝕜)`. Interchanging the arguments in the bilinear form yields the
weak topology `WeakSpace 𝕜 E := E`.

## Main definitions

The main definitions are the types `WeakDual 𝕜 E` and `WeakSpace 𝕜 E`,
with the respective topology instances on it.

* `WeakDual 𝕜 E` is a type synonym for `Dual 𝕜 E` (when the latter is defined): both are equal to
  the type `E →L[𝕜] 𝕜` of continuous linear maps from a module `E` over `𝕜` to the ring `𝕜`.
* The instance `WeakDual.instTopologicalSpace` is the weak-\* topology on `WeakDual 𝕜 E`, i.e., the
  coarsest topology making the evaluation maps at all `z : E` continuous.
* `WeakSpace 𝕜 E` is a type synonym for `E` (when the latter is defined).
* The instance `WeakSpace.instTopologicalSpace` is the weak topology on `E`, i.e., the
  coarsest topology such that all `v : dual 𝕜 E` remain continuous.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

weak-star, weak dual, duality

-/

@[expose] public section


noncomputable section

open Filter Topology LinearMap

variable {α 𝕜 𝕝 E F : Type*}

/-- The weak star topology is the topology coarsest topology on `E →L[𝕜] 𝕜` such that all
functionals `fun v => v x` are continuous. -/
def WeakDual (𝕜 E : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E)
deriving AddCommMonoid, TopologicalSpace, ContinuousAdd, Inhabited,
  FunLike, ContinuousLinearMapClass, Module 𝕜

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
theorem symm_toStrongDual :
    (toStrongDual (𝕜 := 𝕜) (E := E)).symm = StrongDual.toWeakDual :=
  rfl

@[simp]
theorem _root_.StrongDual.symm_toWeakDual :
    (StrongDual.toWeakDual (𝕜 := 𝕜) (E := E)).symm = toStrongDual :=
  rfl

@[simp]
theorem _root_.StrongDual.toStrongDual_toWeakDual (x : StrongDual 𝕜 E) :
    x.toWeakDual.toStrongDual = x :=
  rfl

@[simp]
theorem toWeakDual_toStrongDual (x : WeakDual 𝕜 E) : x.toStrongDual.toWeakDual = x :=
  rfl

@[simp]
theorem toStrongDual_apply (x : WeakDual 𝕜 E) (y : E) : (toStrongDual x) y = x y := rfl

theorem coe_toStrongDual (x' : WeakDual 𝕜 E) : (toStrongDual x' : E → 𝕜) = x' := rfl

theorem toStrongDual_inj (x' y' : WeakDual 𝕜 E) : toStrongDual x' = toStrongDual y' ↔ x' = y' :=
  (LinearEquiv.injective toStrongDual).eq_iff

variable (𝕜 E) in
/-- The canonical bilinear pairing between an element `f : WeakDual 𝕜 E` and `x : E` given by
the evaluation `f x`. -/
@[simps! -isSimp]
def pairing : WeakDual 𝕜 E →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  StrongDual.toWeakDual.arrowCongr (.refl ..) (topDualPairing 𝕜 E)

@[simp]
lemma pairing_apply_apply (f : WeakDual 𝕜 E) (x : E) :
    pairing 𝕜 E f x = f x :=
  rfl

instance isWeak : (pairing 𝕜 E).IsWeak where eq_induced := rfl

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts on `WeakDual 𝕜 E`. -/
instance instMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : MulAction M (WeakDual 𝕜 E) :=
  inferInstanceAs <| MulAction M (E →L[𝕜] 𝕜)

instance (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : IsSMulApply M (WeakDual 𝕜 E) E 𝕜 where
  smul_apply _ _ _ := rfl

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts distributively on `WeakDual 𝕜 E`. -/
instance instDistribMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : DistribMulAction M (WeakDual 𝕜 E) :=
  inferInstanceAs <| DistribMulAction M (E →L[𝕜] 𝕜)

theorem coeFn_continuous : Continuous fun (x : WeakDual 𝕜 E) y => x y :=
  IsWeak.coeFn_continuous (pairing 𝕜 E)

@[fun_prop]
theorem continuous_eval {α : Type*} [TopologicalSpace α] {f : α → WeakDual 𝕜 E} (hf : Continuous f)
    (y : E) : Continuous fun x ↦ f x y :=
  IsWeak.continuous_eval (pairing 𝕜 E) y |>.comp hf

@[deprecated continuous_eval (since := "2026-06-15")]
theorem eval_continuous (y : E) : Continuous fun x : WeakDual 𝕜 E => x y :=
  continuous_pi_iff.mp coeFn_continuous y

@[fun_prop]
theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakDual 𝕜 E}
    (h : ∀ y, Continuous fun a ↦ g a y) : Continuous g :=
  IsWeak.continuous_of_continuous_eval (pairing 𝕜 E) h

instance instContinuousConstSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : ContinuousConstSMul M (WeakDual 𝕜 E) where
  continuous_const_smul _ := IsWeak.continuous_of_continuous_eval (pairing 𝕜 E) <| by
    simp only [pairing_apply_apply, _root_.smul_apply]; fun_prop

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it continuously acts on `WeakDual 𝕜 E`. -/
instance instContinuousSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [TopologicalSpace M] [ContinuousSMul M 𝕜] : ContinuousSMul M (WeakDual 𝕜 E) where
  continuous_smul := IsWeak.continuous_of_continuous_eval (pairing 𝕜 E) <| by
    simp only [pairing_apply_apply, _root_.smul_apply]; fun_prop

/-- If `𝕜` is a topological module over a semiring `R` and scalar multiplication commutes with the
multiplication on `𝕜`, then `WeakDual 𝕜 E` is a module over `R`. -/
instance (priority := 950) instModule'
    (R : Type*) [Semiring R] [Module R 𝕜] [SMulCommClass 𝕜 R 𝕜] [ContinuousConstSMul R 𝕜] :
    Module R (WeakDual 𝕜 E) :=
  inferInstanceAs <| Module R (E →L[𝕜] 𝕜)

instance instT2Space [T2Space 𝕜] : T2Space (WeakDual 𝕜 E) :=
  IsWeak.isEmbedding (B := pairing 𝕜 E) ContinuousLinearMap.coe_injective |>.t2Space

end Semiring

section Ring

variable [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜] [ContinuousConstSMul 𝕜 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]

instance instAddCommGroup : AddCommGroup (WeakDual 𝕜 E) :=
  inferInstanceAs <| AddCommGroup (WeakBilin (topDualPairing 𝕜 E))

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (WeakDual 𝕜 E) :=
  IsWeak.isTopologicalAddGroup (pairing 𝕜 E)

end Ring

end WeakDual

/-- The weak topology is the topology coarsest topology on `E` such that all functionals
`fun x => v x` are continuous. -/
def WeakSpace (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E).flip
deriving AddCommMonoid, TopologicalSpace, ContinuousAdd, Module 𝕜

section Semiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

variable (𝕜 E) in
/-- There is a canonical map `E → WeakSpace 𝕜 E` (the "identity"
mapping). It is a linear equivalence. -/
def toWeakSpace : E ≃ₗ[𝕜] WeakSpace 𝕜 E := LinearEquiv.refl 𝕜 E

namespace WeakSpace

variable (𝕜 E) in
/-- The canonical bilinear pairing between an element `x : WeakSpace 𝕜 E` and `f : StrongDual 𝕜 E`
given by the evaluation `f ((toWeakSpace 𝕜 E).symm x)`. -/
@[simps!]
def pairing : WeakSpace 𝕜 E →ₗ[𝕜] StrongDual 𝕜 E →ₗ[𝕜] 𝕜 :=
  (toWeakSpace 𝕜 E).arrowCongr (.refl ..) (topDualPairing 𝕜 E).flip

variable (𝕜 E) in
instance isWeak : (pairing 𝕜 E).IsWeak where eq_induced := rfl

@[fun_prop]
theorem continuous_eval {α : Type*} [TopologicalSpace α] {x : α → WeakSpace 𝕜 E} (hx : Continuous x)
    (f : StrongDual 𝕜 E) : Continuous fun a ↦ f ((toWeakSpace 𝕜 E).symm (x a)) :=
  IsWeak.continuous_eval (pairing 𝕜 E) f |>.comp hx

@[fun_prop] -- this `fun_prop` lemma doesn't work. :(
theorem continuous_of_continuous_eval [TopologicalSpace α] {x : α → WeakSpace 𝕜 E}
    (h : ∀ f : StrongDual 𝕜 E, Continuous fun a ↦ f ((toWeakSpace 𝕜 E).symm (x a))) :
    Continuous x :=
  IsWeak.continuous_of_continuous_eval (pairing 𝕜 E) h

@[fun_prop]
lemma continuous_toWeakSpace : Continuous (toWeakSpace 𝕜 E) :=
  continuous_of_continuous_eval fun f => by simp only [LinearEquiv.symm_apply_apply]; fun_prop

instance instModule' [CommSemiring 𝕝] [Module 𝕝 E] : Module 𝕝 (WeakSpace 𝕜 E) :=
  inferInstanceAs <| Module 𝕝 (WeakBilin (topDualPairing 𝕜 E).flip)

instance instIsScalarTower [CommSemiring 𝕝] [Module 𝕝 𝕜] [Module 𝕝 E] [IsScalarTower 𝕝 𝕜 E] :
    IsScalarTower 𝕝 𝕜 (WeakSpace 𝕜 E) :=
  WeakBilin.instIsScalarTower (topDualPairing 𝕜 E).flip

instance instContinuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (WeakSpace 𝕜 E) :=
  isWeak 𝕜 E |>.continuousSMul

variable [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

/-- A continuous linear map from `E` to `F` is still continuous when `E` and `F` are equipped with
their weak topologies. -/
def map (f : E →L[𝕜] F) : WeakSpace 𝕜 E →L[𝕜] WeakSpace 𝕜 F :=
  { (toWeakSpace 𝕜 E).arrowCongr (toWeakSpace 𝕜 F) f with
    cont := continuous_of_continuous_eval fun l ↦ continuous_eval (by fun_prop) (l ∘L f) }

theorem map_apply (f : E →L[𝕜] F) (x : E) :
    WeakSpace.map f x = (toWeakSpace 𝕜 F) (f ((toWeakSpace 𝕜 E).symm x)) :=
  rfl

@[deprecated map_apply "this lemma should not be used, it constitutes abuse of
definitional equality" (since := "2026-06-15")]
theorem coe_map (f : E →L[𝕜] F) : (WeakSpace.map f : E → F) = f :=
  rfl

end WeakSpace

variable (𝕜 E) in
/-- For a topological vector space `E`, "identity mapping" `E → WeakSpace 𝕜 E` is continuous.
This definition implements it as a continuous linear map. -/
def toWeakSpaceCLM : E →L[𝕜] WeakSpace 𝕜 E where
  __ := toWeakSpace 𝕜 E

variable (𝕜 E) in
@[simp]
theorem toWeakSpaceCLM_apply (x : E) :
    toWeakSpaceCLM 𝕜 E x = toWeakSpace 𝕜 E x :=
  rfl

@[deprecated toWeakSpaceCLM_eq_toWeakSpace (since := "2026-06-15")]
alias toWeakSpaceCLM_eq_toWeakSpace := toWeakSpaceCLM_apply

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

@[deprecated IsWeak.tendsto_iff_forall_eval_tendsto (since := "2026-06-15")]
theorem tendsto_iff_forall_eval_tendsto_topDualPairing {l : Filter α} {f : α → WeakDual 𝕜 E}
    {x : WeakDual 𝕜 E} :
    Tendsto f l (𝓝 x) ↔
      ∀ y, Tendsto (fun i => topDualPairing 𝕜 E (f i) y) l (𝓝 (topDualPairing 𝕜 E x y)) :=
  IsWeak.tendsto_iff_forall_eval_tendsto (B := WeakDual.pairing 𝕜 E)
    ContinuousLinearMap.coe_injective

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
