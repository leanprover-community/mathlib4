/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# The weak operator topology

This file defines a type copy of `E →L[𝕜] F` (where `E` and `F` are topological vector spaces)
which is endowed with the weak operator topology (WOT) rather than the topology of bounded
convergence (which is the usual one induced by the operator norm in the normed setting).
The WOT is defined as the coarsest topology such that the functional `fun A => y (A x)` is
continuous for any `x : E` and `y : StrongDual 𝕜 F`. Equivalently, a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `y (f a x)` tends to `y (A x)` along the same filter.

Basic non-topological properties of `E →L[𝕜] F` (such as the module structure) are copied over to
the type copy.

We also prove that the WOT is induced by the family of seminorms `‖y (A x)‖` for `x : E` and
`y : StrongDual 𝕜 F`.

## Main declarations

* `ContinuousLinearMapWOT σ E F`: The type copy of `E →SL[σ] F` endowed with the weak operator
  topology.
* `ContinuousLinearMapWOT.tendsto_iff_forall_dual_apply_tendsto`: a function `f` tends to
  `A : E →WOT[𝕜] F` along filter `l` iff `y ((f a) x)` tends to `y (A x)` along the same filter.
* `ContinuousLinearMap.toWOT`: the inclusion map from `E →SL[σ] F` to the type copy
* `ContinuousLinearMap.continuous_toWOT`: the inclusion map is continuous, i.e. the WOT is coarser
  than the norm topology.
* `ContinuousLinearMapWOT.withSeminorms`: the WOT is induced by the family of seminorms
  `‖y (A x)‖` for `x : E` and `y : StrongDual 𝕜 F`.

## Notation

* The type copy of `E →L[𝕜] F` endowed with the weak operator topology is denoted by
  `E →WOT[𝕜] F` and the copy of `E →SL[σ] F` is denoted by `E →SWOT[σ] F`.
* We locally use the notation `F⋆` for `StrongDual 𝕜 F`.

## Implementation notes

In most of the literature, the WOT is defined on maps between Banach spaces. Here, we only assume
that the domain and codomains are topological vector spaces over a normed field.
-/

@[expose] public section

open Topology

/-- The type copy of `E →SL[σ] F` endowed with the weak operator topology, denoted as
`E →SWOT[σ] F`. Likewise, when `σ := RingHom.id 𝕜`, the notation `E →WOT[𝕜] F` is available. -/
structure ContinuousLinearMapWOT {𝕜₁ 𝕜₂ : Type*} [Semiring 𝕜₁] [Semiring 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂)
    (E F : Type*) [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E] [AddCommGroup F]
    [TopologicalSpace F] [Module 𝕜₂ F] where
  /-- Construct an element of `E →SWOT[σ] F` from a continuous linear map. -/
  ofCLM ::
  /-- The continuous linear map underlying an element of `E →SWOT[σ] F`. -/
  toCLM : E →SL[σ] F


namespace ContinuousLinearMapWOT

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `ofCLM A` being printed as `{ toCLM := x }` by `delabStructureInstance`. -/
@[app_delab ContinuousLinearMapWOT.ofCLM]
meta def delabOfCLM : Delab := delabApp

@[inherit_doc]
notation:25 E " →SWOT[" σ "] " F => ContinuousLinearMapWOT σ E F

@[inherit_doc]
notation:25 E " →WOT[" 𝕜 "] " F => ContinuousLinearMapWOT (RingHom.id 𝕜) E F

end Notation

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂}
  {E F : Type*}
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜₂ F]

local notation X "⋆" => StrongDual 𝕜₂ X

/-!
### Basic properties common with `E →L[𝕜] F`

The section copies basic non-topological properties of `E →L[𝕜] F` over to `E →WOT[𝕜] F`, such as
the module structure, `FunLike`, etc.
-/
section Basic

/-- The equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps]
def equiv : (E →SWOT[σ] F) ≃ (E →SL[σ] F) where
  toFun := toCLM
  invFun := ofCLM
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma toCLM_injective : Function.Injective (toCLM : (E →SWOT[σ] F) → E →SL[σ] F) :=
  equiv.injective

@[simp]
lemma toCLM_surjective : Function.Surjective (toCLM : (E →SWOT[σ] F) → E →SL[σ] F) :=
  equiv.surjective

lemma toCLM_bijective : Function.Bijective (toCLM : (E →SWOT[σ] F) → E →SL[σ] F) :=
  equiv.bijective

@[simp]
lemma ofCLM_injective : Function.Injective (ofCLM : (E →SL[σ] F) → E →SWOT[σ] F) :=
  equiv.symm.injective

@[simp]
lemma ofCLM_surjective : Function.Surjective (ofCLM : (E →SL[σ] F) → E →SWOT[σ] F) :=
  equiv.symm.surjective

lemma ofCLM_bijective : Function.Bijective (ofCLM : (E →SL[σ] F) → E →SWOT[σ] F) :=
  equiv.symm.bijective

instance instAddCommGroup [IsTopologicalAddGroup F] :
    AddCommGroup (E →SWOT[σ] F) :=
  equiv.addCommGroup

instance instSMul {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [ContinuousConstSMul S F] :
    SMul S (E →SWOT[σ] F) :=
  equiv.smul S

instance instModule {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [IsTopologicalAddGroup F] :
    Module S (E →SWOT[σ] F) :=
  equiv.module S

instance instIsScalarTower {S T : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [DistribSMul T F] [SMulCommClass 𝕜₂ T F]
    [ContinuousConstSMul T F] [SMul S T] [IsScalarTower S T F] :
    IsScalarTower S T (E →SWOT[σ] F) :=
  equiv.isScalarTower S T

instance instSMulCommClass {S T : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [DistribSMul T F] [SMulCommClass 𝕜₂ T F]
    [ContinuousConstSMul T F] [SMulCommClass S T F] :
    SMulCommClass S T (E →SWOT[σ] F) :=
  equiv.smulCommClass S T

instance instIsCentralScalar {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [Module Sᵐᵒᵖ F] [IsCentralScalar S F] :
    IsCentralScalar S (E →SWOT[σ] F) :=
  equiv.isCentralScalar S

instance instRing [IsTopologicalAddGroup E] : Ring (E →WOT[𝕜₁] E) :=
  equiv.ring

instance instAlgebra {S : Type*} [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] [SMul S 𝕜₁]
    [IsScalarTower S 𝕜₁ E] [ContinuousConstSMul S E] [IsTopologicalAddGroup E] :
    Algebra S (E →WOT[𝕜₁] E) :=
  equiv.algebra S

/-- The additive group equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
def addEquiv [IsTopologicalAddGroup F] : (E →SWOT[σ] F) ≃+ (E →SL[σ] F) :=
  equiv.addEquiv

/-- The linear equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
def linearEquiv (S : Type*) [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [IsTopologicalAddGroup F] :
    (E →SWOT[σ] F) ≃ₗ[S] (E →SL[σ] F) :=
  equiv.linearEquiv S

/-- The ring equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
def ringEquiv [IsTopologicalAddGroup E] : (E →WOT[𝕜₁] E) ≃+* (E →L[𝕜₁] E) :=
  equiv.ringEquiv

/-- The algebra equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
def algEquiv (S : Type*) [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] [SMul S 𝕜₁]
    [IsScalarTower S 𝕜₁ E] [ContinuousConstSMul S E] [IsTopologicalAddGroup E] :
    (E →WOT[𝕜₁] E) ≃ₐ[S] (E →L[𝕜₁] E) :=
  equiv.algEquiv S

instance instFunLike : FunLike (E →SWOT[σ] F) E F where
  coe f := toCLM f
  coe_injective' := DFunLike.coe_injective.comp toCLM_injective

@[simp]
lemma coe_toCLM (A : E →SWOT[σ] F) : ⇑(toCLM A : E →SL[σ] F) = A := rfl

@[simp]
lemma coe_ofCLM (A : E →SL[σ] F) : ⇑(ofCLM A : E →SWOT[σ] F) = A := rfl

instance instContinuousLinearMapClass : ContinuousSemilinearMapClass (E →SWOT[σ] F) σ E F where
  map_add f x y := by simp [← coe_toCLM]
  map_smulₛₗ f r x := by simp [← coe_toCLM]
  map_continuous f := f.toCLM.continuous

@[simp]
lemma ofCLM_toCLM (A : E →SWOT[σ] F) : ofCLM (toCLM A) = A := rfl

-- not marked `simp` because Lean just sees `A` on the left-hand side
lemma toCLM_ofCLM (A : E →SL[σ] F) : toCLM (ofCLM A) = A := rfl

@[simp]
lemma toCLM_apply {A : E →SWOT[σ] F} {x : E} : toCLM A x = A x := rfl

@[simp]
lemma ofCLM_apply {A : E →SL[σ] F} {x : E} : ofCLM A x = A x := rfl

@[deprecated (since := "2026-04-10")] alias _root_.ContinuousLinearMap.toWOT_apply := ofCLM_apply

@[ext]
lemma ext {A B : E →SWOT[σ] F} (h : ∀ x, A x = B x) : A = B :=
  toCLM_injective <| ContinuousLinearMap.ext h

-- This `ext` lemma is set at a lower priority than the default of 1000, so that the
-- version with an inner product (`ContinuousLinearMapWOT.ext_inner`) takes precedence
-- in the case of Hilbert spaces.
@[ext 900]
lemma ext_dual [H : SeparatingDual 𝕜₂ F] {A B : E →SWOT[σ] F}
    (h : ∀ x (y : F⋆), y (A x) = y (B x)) : A = B := by
  simp_rw [ContinuousLinearMapWOT.ext_iff, ← (separatingDual_iff_injective.mp H).eq_iff,
    LinearMap.ext_iff]
  exact h

section SMul

variable {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [ContinuousConstSMul S F]

@[simp] lemma ofCLM_smul {c : S} {f : E →SL[σ] F} : ofCLM (c • f) = c • ofCLM f := rfl
@[simp] lemma toCLM_smul {c : S} {f : E →SWOT[σ] F} : toCLM (c • f) = c • toCLM f := rfl
@[simp] lemma smul_apply {f : E →SWOT[σ] F} (c : S) (x : E) : (c • f) x = c • (f x) := rfl

end SMul

section Algebra

variable {S : Type*} [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] [SMul S 𝕜₁]
    [IsScalarTower S 𝕜₁ E] [ContinuousConstSMul S E] [IsTopologicalAddGroup E]

@[simp] lemma toCLM_algebraMap (c : S) :
    toCLM (algebraMap S (E →WOT[𝕜₁] E) c) = algebraMap S (E →L[𝕜₁] E) c :=
  rfl

@[simp] lemma ofCLM_algebraMap (c : S) :
    ofCLM (algebraMap S (E →L[𝕜₁] E) c) = algebraMap S (E →WOT[𝕜₁] E) c :=
  rfl

@[simp] lemma algebraMapCLM_apply (c : S) (x : E) :
    (algebraMap S (E →WOT[𝕜₁] E) c) x = c • x :=
  rfl

end Algebra

variable [IsTopologicalAddGroup F]

@[simp] lemma ofCLM_zero : ofCLM (0 : E →SL[σ] F) = 0 := rfl
@[simp] lemma ofCLM_add {f g : E →SL[σ] F} : ofCLM (f + g) = ofCLM f + ofCLM g := rfl
@[simp] lemma ofCLM_sub {f g : E →SL[σ] F} : ofCLM (f - g) = ofCLM f - ofCLM g := rfl
@[simp] lemma ofCLM_neg {f : E →SL[σ] F} : ofCLM (-f) = -ofCLM f := rfl
@[simp] lemma ofCLM_mul (f g : F →L[𝕜₂] F) : ofCLM (f * g) = ofCLM f * ofCLM g := rfl
@[simp] lemma ofCLM_one : ofCLM (1 : F →L[𝕜₂] F) = 1 := rfl
@[simp] lemma ofCLM_pow (f : F →L[𝕜₂] F) (n : ℕ) : ofCLM (f ^ n) = ofCLM f ^ n := rfl
@[simp] lemma ofCLM_natCast (n : ℕ) : ofCLM (n : F →L[𝕜₂] F) = n := rfl
@[simp] lemma ofCLM_intCast (n : ℤ) : ofCLM (n : F →L[𝕜₂] F) = n := rfl

@[simp] lemma toCLM_zero : toCLM (0 : E →SWOT[σ] F) = 0 := rfl
@[simp] lemma toCLM_add {f g : E →SWOT[σ] F} : toCLM (f + g) = toCLM f + toCLM g := rfl
@[simp] lemma toCLM_sub {f g : E →SWOT[σ] F} : toCLM (f - g) = toCLM f - toCLM g := rfl
@[simp] lemma toCLM_neg {f : E →SWOT[σ] F} : toCLM (-f) = -toCLM f := rfl
@[simp] lemma toCLM_mul (f g : F →WOT[𝕜₂] F) : toCLM (f * g) = toCLM f * toCLM g := rfl
@[simp] lemma toCLM_one : toCLM (1 : F →WOT[𝕜₂] F) = 1 := rfl
@[simp] lemma toCLM_pow (f : F →WOT[𝕜₂] F) (n : ℕ) : (f ^ n).toCLM = f.toCLM ^ n := rfl
@[simp] lemma toCLM_natCast (n : ℕ) : (n : F →WOT[𝕜₂] F).toCLM = n := rfl
@[simp] lemma toCLM_intCast (n : ℤ) : (n : F →WOT[𝕜₂] F).toCLM = n := rfl

@[simp] lemma zero_apply (x : E) : (0 : E →SWOT[σ] F) x = 0 := rfl
@[simp] lemma add_apply {f g : E →SWOT[σ] F} (x : E) : (f + g) x = f x + g x := rfl
@[simp] lemma sub_apply {f g : E →SWOT[σ] F} (x : E) : (f - g) x = f x - g x := rfl
@[simp] lemma neg_apply {f : E →SWOT[σ] F} (x : E) : (-f) x = -(f x) := rfl
@[simp] lemma mul_apply (f g : F →WOT[𝕜₂] F) (x : F) : (f * g) x = f (g x) := rfl
@[simp] lemma one_apply (x : F) : (1 : F →WOT[𝕜₂] F) x = x := rfl
@[simp] lemma natCast_apply (n : ℕ) (x : F) : (n : F →WOT[𝕜₂] F) x = n • x := rfl
@[simp] lemma intCast_apply (n : ℤ) (x : F) : (n : F →WOT[𝕜₂] F) x = n • x := rfl

end Basic

/-!
### The topology of `E →WOT[𝕜] F`

The section endows `E →WOT[𝕜] F` with the weak operator topology and shows the basic properties
of this topology. In particular, we show that it is a topological vector space.
-/
section Topology

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]

variable (σ E F) in
/-- The function that induces the topology on `E →WOT[𝕜] F`, namely the function that takes
an `A` and maps it to `fun ⟨x, y⟩ => y (A x)` in `E × F⋆ → 𝕜`, bundled as a linear map to make
it easier to prove that it is a TVS. -/
def inducingFn : (E →SWOT[σ] F) →ₗ[𝕜₂] (E × F⋆ → 𝕜₂) where
  toFun := fun A ⟨x, y⟩ => y (A x)
  map_add' := fun x y => by ext; simp
  map_smul' := fun x y => by ext; simp

@[simp]
lemma inducingFn_apply {f : E →SWOT[σ] F} {x : E} {y : F⋆} :
    inducingFn σ E F f (x, y) = y (f x) :=
  rfl

/-- The weak operator topology is the coarsest topology such that `fun A => y (A x)` is
continuous for all `x, y`. -/
instance instTopologicalSpace : TopologicalSpace (E →SWOT[σ] F) :=
  .induced (inducingFn _ _ _) Pi.topologicalSpace

@[fun_prop]
lemma continuous_inducingFn : Continuous (inducingFn σ E F) :=
  continuous_induced_dom

lemma continuous_dual_apply (x : E) (y : F⋆) : Continuous fun (A : E →SWOT[σ] F) => y (A x) := by
  refine (continuous_pi_iff.mp continuous_inducingFn) ⟨x, y⟩

@[fun_prop]
lemma continuous_of_dual_apply_continuous {α : Type*} [TopologicalSpace α] {g : α → E →SWOT[σ] F}
    (h : ∀ x (y : F⋆), Continuous fun a => y (g a x)) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr fun p => h p.1 p.2)

@[fun_prop]
lemma isInducing_inducingFn : IsInducing (inducingFn σ E F) := ⟨rfl⟩

@[fun_prop]
lemma isEmbedding_inducingFn [SeparatingDual 𝕜₂ F] : IsEmbedding (inducingFn σ E F) := by
  refine Function.Injective.isEmbedding_induced fun A B hAB => ?_
  rw [ContinuousLinearMapWOT.ext_dual_iff]
  simpa [funext_iff] using hAB

open Filter in
/-- The defining property of the weak operator topology: a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `y (f a x)` tends to `y (A x)` along the same filter. -/
lemma tendsto_iff_forall_dual_apply_tendsto {α : Type*} {l : Filter α} {f : α → E →SWOT[σ] F}
    {A : E →SWOT[σ] F} :
    Tendsto f l (𝓝 A) ↔ ∀ x (y : F⋆), Tendsto (fun a => y (f a x)) l (𝓝 (y (A x))) := by
  simp [isInducing_inducingFn.tendsto_nhds_iff, tendsto_pi_nhds]

lemma le_nhds_iff_forall_dual_apply_le_nhds {l : Filter (E →SWOT[σ] F)} {A : E →SWOT[σ] F} :
    l ≤ 𝓝 A ↔ ∀ x (y : F⋆), l.map (fun T => y (T x)) ≤ 𝓝 (y (A x)) :=
  tendsto_iff_forall_dual_apply_tendsto (f := id)

instance instT3Space [SeparatingDual 𝕜₂ F] : T3Space (E →SWOT[σ] F) :=
  isEmbedding_inducingFn.t3Space

instance {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [ContinuousConstSMul S F]
    [SMul S 𝕜₂] [IsScalarTower S 𝕜₂ 𝕜₂] [IsScalarTower S 𝕜₂ F] :
    ContinuousConstSMul S (F →WOT[𝕜₂] F) where
  continuous_const_smul c := by
    apply continuous_of_dual_apply_continuous fun _ _ ↦ ?_
    simp only [smul_apply, ContinuousLinearMap.map_smul_of_tower]
    exact continuous_const_smul c |>.comp <| continuous_dual_apply ..

instance instContinuousSMul {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [Module S 𝕜₂] [IsScalarTower S 𝕜₂ F] [IsScalarTower S 𝕜₂ 𝕜₂] [ContinuousConstSMul S F]
    [TopologicalSpace S] [ContinuousSMul S 𝕜₂] :
  ContinuousSMul S (E →SWOT[σ] F) := .induced <| (inducingFn σ E F).restrictScalars S

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (E →SWOT[σ] F) where
  toContinuousAdd := .induced (inducingFn σ E F)
  toContinuousNeg := .induced (inducingFn σ E F)

instance instUniformSpace : UniformSpace (E →SWOT[σ] F) := .comap (inducingFn σ E F) inferInstance

instance instIsUniformAddGroup : IsUniformAddGroup (E →SWOT[σ] F) := .comap (inducingFn σ E F)

end Topology

/-! ### The WOT is induced by a family of seminorms -/
section Seminorms

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]

/-- The family of seminorms that induce the weak operator topology, namely `‖y (A x)‖` for
all `x` and `y`. -/
def seminorm (x : E) (y : F⋆) : Seminorm 𝕜₂ (E →SWOT[σ] F) where
  toFun A := ‖y (A x)‖
  map_zero' := by simp
  add_le' A B := by simpa using norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp

variable (σ E F) in
/-- The family of seminorms that induce the weak operator topology, namely `‖y (A x)‖` for
all `x` and `y`. -/
def seminormFamily : SeminormFamily 𝕜₂ (E →SWOT[σ] F) (E × F⋆) :=
  fun ⟨x, y⟩ => seminorm x y

lemma withSeminorms : WithSeminorms (seminormFamily σ E F) :=
  let e : E × F⋆ ≃ (Σ _ : E × F⋆, Fin 1) := .symm <| .sigmaUnique _ _
  isInducing_inducingFn.withSeminorms <| withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜₂ 𝕜₂)
    |>.congr_equiv e

lemma hasBasis_seminorms :
    (𝓝 (0 : E →SWOT[σ] F)).HasBasis (· ∈ (seminormFamily σ E F).basisSets) id :=
  withSeminorms.hasBasis

instance instLocallyConvexSpace [NormedSpace ℝ 𝕜₂] [Module ℝ (E →SWOT[σ] F)]
    [IsScalarTower ℝ 𝕜₂ (E →SWOT[σ] F)] :
    LocallyConvexSpace ℝ (E →SWOT[σ] F) :=
  withSeminorms.toLocallyConvexSpace

end Seminorms

section toWOT_continuous

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F] [ContinuousSMul 𝕜₁ E]

/-- The weak operator topology is coarser than the bounded convergence topology, i.e. the inclusion
map is continuous. -/
@[continuity, fun_prop]
lemma continuous_ofCLM :
    Continuous (ofCLM : (E →SL[σ] F) → (E →SWOT[σ] F)) :=
  ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x y ↦
    y.cont.comp <| continuous_eval_const x

@[deprecated (since := "2026-04-10")] alias ContinuousLinearMap.continuous_toWOT := continuous_ofCLM

/-- The inclusion map from `E →[𝕜] F` to `E →WOT[𝕜] F`, bundled as a continuous linear map. -/
def _root_.ContinuousLinearMap.WOTofCLM : (E →SL[σ] F) →L[𝕜₂] (E →SWOT[σ] F) where
  toLinearMap := linearEquiv 𝕜₂ |>.symm.toLinearMap
  cont := continuous_ofCLM

@[deprecated (since := "2026-04-10")]
alias ContinuousLinearMap.toWOTCLM := ContinuousLinearMap.WOTofCLM

end toWOT_continuous


section Comp

variable {𝕜₁ 𝕜₂ 𝕜₃ 𝕜₄ : Type*} {E F G H : Type*}
    [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] [NormedField 𝕜₄]
    {σ₁₂ : 𝕜₁ →+* 𝕜₂} {σ₁₃ : 𝕜₁ →+* 𝕜₃} {σ₁₄ : 𝕜₁ →+* 𝕜₄}
    {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₂₄ : 𝕜₂ →+* 𝕜₄} {σ₃₄ : 𝕜₃ →+* 𝕜₄}
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
    [AddCommGroup F] [TopologicalSpace F] [Module 𝕜₂ F]
    [AddCommGroup G] [TopologicalSpace G] [Module 𝕜₃ G]
    [AddCommGroup H] [TopologicalSpace H] [Module 𝕜₄ H]

variable (𝕜₂ F) in
/-- The identity as a continuous linear map on the type synonym equipped with the weak operator
topology -/
protected def id : F →WOT[𝕜₂] F := ofCLM <| .id 𝕜₂ F

@[simp]
lemma toCLM_id : (.id 𝕜₂ F : F →WOT[𝕜₂] F).toCLM = .id 𝕜₂ F := rfl

/-- Composition of continuous linear maps on the type synonym equipped with the weak operator
topology. -/
def comp (g : F →SWOT[σ₂₃] G) (f : E →SWOT[σ₁₂] F) : E →SWOT[σ₁₃] G :=
  ofCLM <| g.toCLM.comp f.toCLM

@[simp]
lemma comp_apply (g : F →SWOT[σ₂₃] G) (f : E →SWOT[σ₁₂] F) (x : E) :
    g.comp f x = g (f x) := by
  simp [comp]

@[simp] lemma toCLM_comp (g : F →SWOT[σ₂₃] G) (f : E →SWOT[σ₁₂] F) :
    (g.comp f).toCLM = g.toCLM.comp f.toCLM :=
  rfl

@[simp] lemma comp_id (f : E →SWOT[σ₁₂] F) : comp (.id 𝕜₂ F) f = f := by simp [comp]
@[simp] lemma id_comp (g : F →SWOT[σ₂₃] G) : comp g (.id 𝕜₂ F) = g := by simp [comp]

lemma comp_assoc (g₃₄ : G →SWOT[σ₃₄] H) (g₂₃ : F →SWOT[σ₂₃] G) (g₁₂ : E →SWOT[σ₁₂] F) :
    (g₃₄.comp g₂₃).comp g₁₂ = g₃₄.comp (g₂₃.comp g₁₂) := by
  simp only [comp, ContinuousLinearMap.comp_assoc]

lemma mul_eq_comp [IsTopologicalAddGroup F] (f g : F →WOT[𝕜₂] F) : f * g = f.comp g := rfl

@[fun_prop]
lemma continuous_precomp [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] (f : E →SWOT[σ₁₂] F) :
    Continuous (fun g : F →SWOT[σ₂₃] G ↦ g.comp f) :=
  continuous_of_dual_apply_continuous fun _ _ ↦ continuous_dual_apply ..

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]
variable [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]

/-- While `RingHomSurjective σ₂₃` is not a strict requirement, there are obstructions to
this without any assumption on `σ₂₃` (in particular, on the dimension of the extension of `𝕜₃` over
`σ₂₃(𝕜₂)`), and in the only common case, which is when `σ₂₃` is conjugation, this type class is
guaranteed. Likewise, it would suffice if `RingHomIsometric` were replaced with the weaker
`Continuous σ₂₃`, but we opt for this because we have these type classes available. -/
@[fun_prop]
lemma continuous_postcomp [RingHomSurjective σ₂₃] [RingHomIsometric σ₂₃] (g : F →SWOT[σ₂₃] G) :
    Continuous (fun f : E →SWOT[σ₁₂] F ↦ g.comp f) := by
  refine continuous_of_dual_apply_continuous fun x z ↦ ?_
  have σ_bij : Function.Bijective σ₂₃ := ⟨σ₂₃.injective, RingHomSurjective.is_surjective⟩
  let σ_equiv : 𝕜₂ ≃+* 𝕜₃ := RingEquiv.ofBijective σ₂₃ σ_bij
  let invPair : RingHomInvPair σ₂₃ σ_equiv.symm := RingHomInvPair.of_ringEquiv σ_equiv
  let invPair_symm := invPair.symm
  let σ_li : 𝕜₂ ≃ₛₗᵢ[σ₂₃] 𝕜₃ :=
    { toLinearEquiv := .ofBijective σ₂₃.toSemilinearMap σ_bij
      norm_map' _ := RingHomIsometric.norm_map }
  conv => enter [1, a]; rw [← σ_li.apply_symm_apply (z _), comp_apply, ← toCLM_apply]
  apply σ_li.continuous.comp
  exact continuous_dual_apply x <| σ_li.symm.toLinearIsometry.toContinuousLinearMap.comp <|
    z.comp g.toCLM

/-- Precomposition by a fixed continuous linear map, as a continuous linear map when all spaces
of continuous linear maps are equipped with the weak operator topology. -/
@[simps]
def precompCLM (f : E →SWOT[σ₁₂] F) : (F →SWOT[σ₂₃] G) →L[𝕜₃] (E →SWOT[σ₁₃] G) where
  toFun g := g.comp f
  map_add' := by simp [comp]
  map_smul' := by simp [comp]

/-- Precomposition by a fixed continuous linear map, as a continuous linear map when all spaces
of continuous linear maps are equipped with the weak operator topology. -/
@[simps]
def postcompCLM [RingHomSurjective σ₂₃] [RingHomIsometric σ₂₃] (g : F →SWOT[σ₂₃] G) :
    (E →SWOT[σ₁₂] F) →SL[σ₂₃] (E →SWOT[σ₁₃] G) where
  toFun f := g.comp f
  map_add' := by simp [comp]
  map_smul' := by simp [comp]

instance : IsSemitopologicalRing (F →WOT[𝕜₂] F) where
  continuous_const_mul {_} := by simp_rw [mul_eq_comp]; fun_prop
  continuous_mul_const {_} := by simp_rw [mul_eq_comp]; fun_prop

end Comp

end ContinuousLinearMapWOT
